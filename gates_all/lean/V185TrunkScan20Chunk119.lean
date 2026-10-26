import V185TrunkScan20Chunk118

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_724112 : List Nat := [2, 1, 1, 1, 1, 1, 4, 9]
def baseStart_724112 : Nat := 118140960795 + 724112 * 2 ^ 59
def prefixEnd_724112 : Nat := 4983230072969 + 3 ^ 40 * 724112 * 2
def baseEnd_724112 : Nat := 110168149241059597679963

theorem tailTrace_724112 : CollatzResearch.WordTrace tailWord_724112 prefixEnd_724112 110168149241059597679963 := by
  unfold tailWord_724112
  simp only [CollatzResearch.WordTrace]
  refine ⟨13205267176336683664479295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17607022901782244885972393 13205267176336683664479295)
  ·
    refine ⟨19807900764505025496718943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13205267176336683664479295 19807900764505025496718943)
    ·
      refine ⟨29711851146757538245078415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19807900764505025496718943 29711851146757538245078415)
      ·
        refine ⟨44567776720136307367617623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29711851146757538245078415 44567776720136307367617623)
        ·
          refine ⟨66851665080204461051426435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44567776720136307367617623 66851665080204461051426435)
          ·
            refine ⟨100277497620306691577139653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66851665080204461051426435 100277497620306691577139653)
            ·
              refine ⟨18802030803807504670713685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100277497620306691577139653 18802030803807504670713685)
              ·
                refine ⟨110168149241059597679963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18802030803807504670713685 110168149241059597679963)
                ·
                  rfl

theorem cell20_724112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_724112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724112 prefixEnd_724112 := by exact prefixLift 724112
  have htrace : WordTrace (prefixWord ++ tailWord_724112) baseStart_724112 baseEnd_724112 := by
    simpa [prefixWord, tailWord_724112, baseEnd_724112] using wordTrace_append hprefix tailTrace_724112
  have hstable : (prefixWord ++ tailWord_724112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724112).length < 2 ^ (prefixWord ++ tailWord_724112).sum := by decide
  have hdescent : baseEnd_724112 < baseStart_724112 := by decide
  rcases family_descends (prefixWord ++ tailWord_724112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724122 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_724122 : Nat := 118140960795 + 724122 * 2 ^ 59
def prefixEnd_724122 : Nat := 4983230072969 + 3 ^ 40 * 724122 * 2
def baseEnd_724122 : Nat := 330509011995663202706515

theorem tailTrace_724122 : CollatzResearch.WordTrace tailWord_724122 prefixEnd_724122 330509011995663202706515 := by
  unfold tailWord_724122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6602724770659284759205655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17607266055091426024548413 6602724770659284759205655)
  ·
    refine ⟨9904087155988927138808483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6602724770659284759205655 9904087155988927138808483)
    ·
      refine ⟨14856130733983390708212725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9904087155988927138808483 14856130733983390708212725)
      ·
        refine ⟨1392762256310942878894943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14856130733983390708212725 1392762256310942878894943)
        ·
          refine ⟨2089143384466414318342415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392762256310942878894943 2089143384466414318342415)
          ·
            refine ⟨3133715076699621477513623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089143384466414318342415 3133715076699621477513623)
            ·
              refine ⟨4700572615049432216270435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3133715076699621477513623 4700572615049432216270435)
              ·
                refine ⟨7050858922574148324405653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700572615049432216270435 7050858922574148324405653)
                ·
                  refine ⟨330509011995663202706515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7050858922574148324405653 330509011995663202706515)
                  ·
                    rfl

theorem cell20_724122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_724122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724122 prefixEnd_724122 := by exact prefixLift 724122
  have htrace : WordTrace (prefixWord ++ tailWord_724122) baseStart_724122 baseEnd_724122 := by
    simpa [prefixWord, tailWord_724122, baseEnd_724122] using wordTrace_append hprefix tailTrace_724122
  have hstable : (prefixWord ++ tailWord_724122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724122).length < 2 ^ (prefixWord ++ tailWord_724122).sum := by decide
  have hdescent : baseEnd_724122 < baseStart_724122 := by decide
  rcases family_descends (prefixWord ++ tailWord_724122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724153 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 3]
def baseStart_724153 : Nat := 118140960795 + 724153 * 2 ^ 59
def prefixEnd_724153 : Nat := 4983230072969 + 3 ^ 40 * 724153 * 2
def baseEnd_724153 : Nat := 330523161240364872673055

theorem tailTrace_724153 : CollatzResearch.WordTrace tailWord_724153 prefixEnd_724153 330523161240364872673055 := by
  unfold tailWord_724153
  simp only [CollatzResearch.WordTrace]
  refine ⟨26412029745524831331201113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17608019830349887554134075 26412029745524831331201113)
  ·
    refine ⟨19809022309143623498400835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26412029745524831331201113 19809022309143623498400835)
    ·
      refine ⟨29713533463715435247601253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19809022309143623498400835 29713533463715435247601253)
      ·
        refine ⟨5571287524446644108925235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29713533463715435247601253 5571287524446644108925235)
        ·
          refine ⟨8356931286669966163387853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571287524446644108925235 8356931286669966163387853)
          ·
            refine ⟨3133849232501237311270445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8356931286669966163387853 3133849232501237311270445)
            ·
              refine ⟨1175193462187963991726417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3133849232501237311270445 1175193462187963991726417)
              ·
                refine ⟨881395096640972993794813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175193462187963991726417 881395096640972993794813)
                ·
                  refine ⟨330523161240364872673055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881395096640972993794813 330523161240364872673055)
                  ·
                    rfl

theorem cell20_724153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_724153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724153 prefixEnd_724153 := by exact prefixLift 724153
  have htrace : WordTrace (prefixWord ++ tailWord_724153) baseStart_724153 baseEnd_724153 := by
    simpa [prefixWord, tailWord_724153, baseEnd_724153] using wordTrace_append hprefix tailTrace_724153
  have hstable : (prefixWord ++ tailWord_724153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724153).length < 2 ^ (prefixWord ++ tailWord_724153).sum := by decide
  have hdescent : baseEnd_724153 < baseStart_724153 := by decide
  rcases family_descends (prefixWord ++ tailWord_724153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724170 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_724170 : Nat := 118140960795 + 724170 * 2 ^ 59
def prefixEnd_724170 : Nat := 4983230072969 + 3 ^ 40 * 724170 * 2
def baseEnd_724170 : Nat := 330530920503588369106319

theorem tailTrace_724170 : CollatzResearch.WordTrace tailWord_724170 prefixEnd_724170 330530920503588369106319 := by
  unfold tailWord_724170
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603162446615810808642491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17608433190975495489713309 6603162446615810808642491)
  ·
    refine ⟨9904743669923716212963737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6603162446615810808642491 9904743669923716212963737)
    ·
      refine ⟨7428557752442787159722803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9904743669923716212963737 7428557752442787159722803)
      ·
        refine ⟨11142836628664180739584205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428557752442787159722803 11142836628664180739584205)
        ·
          refine ⟨4178563735749067777344077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11142836628664180739584205 4178563735749067777344077)
          ·
            refine ⟨1566961400905900416504029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4178563735749067777344077 1566961400905900416504029)
            ·
              refine ⟨587610525339712656189011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1566961400905900416504029 587610525339712656189011)
              ·
                refine ⟨881415788009568984283517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587610525339712656189011 881415788009568984283517)
                ·
                  refine ⟨330530920503588369106319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881415788009568984283517 330530920503588369106319)
                  ·
                    rfl

theorem cell20_724170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_724170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724170 prefixEnd_724170 := by exact prefixLift 724170
  have htrace : WordTrace (prefixWord ++ tailWord_724170) baseStart_724170 baseEnd_724170 := by
    simpa [prefixWord, tailWord_724170, baseEnd_724170] using wordTrace_append hprefix tailTrace_724170
  have hstable : (prefixWord ++ tailWord_724170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724170).length < 2 ^ (prefixWord ++ tailWord_724170).sum := by decide
  have hdescent : baseEnd_724170 < baseStart_724170 := by decide
  rcases family_descends (prefixWord ++ tailWord_724170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724180 : List Nat := [2, 4, 1, 4, 1, 2, 2, 4]
def baseStart_724180 : Nat := 118140960795 + 724180 * 2 ^ 59
def prefixEnd_724180 : Nat := 4983230072969 + 3 ^ 40 * 724180 * 2
def baseEnd_724180 : Nat := 110178494925357592924315

theorem tailTrace_724180 : CollatzResearch.WordTrace tailWord_724180 prefixEnd_724180 110178494925357592924315 := by
  unfold tailWord_724180
  simp only [CollatzResearch.WordTrace]
  refine ⟨13206507258213507471216997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17608676344284676628289329 13206507258213507471216997)
  ·
    refine ⟨2476220110915032650853187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13206507258213507471216997 2476220110915032650853187)
    ·
      refine ⟨3714330166372548976279781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2476220110915032650853187 3714330166372548976279781)
      ·
        refine ⟨696436906194852933052459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3714330166372548976279781 696436906194852933052459)
        ·
          refine ⟨1044655359292279399578689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696436906194852933052459 1044655359292279399578689)
          ·
            refine ⟨783491519469209549684017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044655359292279399578689 783491519469209549684017)
            ·
              refine ⟨587618639601907162263013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783491519469209549684017 587618639601907162263013)
              ·
                refine ⟨110178494925357592924315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587618639601907162263013 110178494925357592924315)
                ·
                  rfl

theorem cell20_724180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_724180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724180 prefixEnd_724180 := by exact prefixLift 724180
  have htrace : WordTrace (prefixWord ++ tailWord_724180) baseStart_724180 baseEnd_724180 := by
    simpa [prefixWord, tailWord_724180, baseEnd_724180] using wordTrace_append hprefix tailTrace_724180
  have hstable : (prefixWord ++ tailWord_724180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724180).length < 2 ^ (prefixWord ++ tailWord_724180).sum := by decide
  have hdescent : baseEnd_724180 < baseStart_724180 := by decide
  rcases family_descends (prefixWord ++ tailWord_724180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724205 : List Nat := [1, 5, 1, 2, 2, 1, 8]
def baseStart_724205 : Nat := 118140960795 + 724205 * 2 ^ 59
def prefixEnd_724205 : Nat := 4983230072969 + 3 ^ 40 * 724205 * 2
def baseEnd_724205 : Nat := 36727432828587089215501

theorem tailTrace_724205 : CollatzResearch.WordTrace tailWord_724205 prefixEnd_724205 36727432828587089215501 := by
  unfold tailWord_724205
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413926341336444212094069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17609284227557629474729379 26413926341336444212094069)
  ·
    refine ⟨2476305594500291644883819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26413926341336444212094069 2476305594500291644883819)
    ·
      refine ⟨3714458391750437467325729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2476305594500291644883819 3714458391750437467325729)
      ·
        refine ⟨2785843793812828100494297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714458391750437467325729 2785843793812828100494297)
        ·
          refine ⟨2089382845359621075370723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2785843793812828100494297 2089382845359621075370723)
          ·
            refine ⟨3134074268039431613056085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089382845359621075370723 3134074268039431613056085)
            ·
              refine ⟨36727432828587089215501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3134074268039431613056085 36727432828587089215501)
              ·
                rfl

theorem cell20_724205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_724205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724205 prefixEnd_724205 := by exact prefixLift 724205
  have htrace : WordTrace (prefixWord ++ tailWord_724205) baseStart_724205 baseEnd_724205 := by
    simpa [prefixWord, tailWord_724205, baseEnd_724205] using wordTrace_append hprefix tailTrace_724205
  have hstable : (prefixWord ++ tailWord_724205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724205).length < 2 ^ (prefixWord ++ tailWord_724205).sum := by decide
  have hdescent : baseEnd_724205 < baseStart_724205 := by decide
  rcases family_descends (prefixWord ++ tailWord_724205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724222 : List Nat := [4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_724222 : Nat := 118140960795 + 724222 * 2 ^ 59
def prefixEnd_724222 : Nat := 4983230072969 + 3 ^ 40 * 724222 * 2
def baseEnd_724222 : Nat := 110184884906835766457591

theorem tailTrace_724222 : CollatzResearch.WordTrace tailWord_724222 prefixEnd_724222 110184884906835766457591 := by
  unfold tailWord_724222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3301818297784357014432865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17609697588183237410308613 3301818297784357014432865)
  ·
    refine ⟨2476363723338267760824649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3301818297784357014432865 2476363723338267760824649)
    ·
      refine ⟨1857272792503700820618487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2476363723338267760824649 1857272792503700820618487)
      ·
        refine ⟨2785909188755551230927731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857272792503700820618487 2785909188755551230927731)
        ·
          refine ⟨4178863783133326846391597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2785909188755551230927731 4178863783133326846391597)
          ·
            refine ⟨1567073918674997567396849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4178863783133326846391597 1567073918674997567396849)
            ·
              refine ⟨1175305439006248175547637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567073918674997567396849 1175305439006248175547637)
              ·
                refine ⟨110184884906835766457591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1175305439006248175547637 110184884906835766457591)
                ·
                  rfl

theorem cell20_724222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_724222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724222 prefixEnd_724222 := by exact prefixLift 724222
  have htrace : WordTrace (prefixWord ++ tailWord_724222) baseStart_724222 baseEnd_724222 := by
    simpa [prefixWord, tailWord_724222, baseEnd_724222] using wordTrace_append hprefix tailTrace_724222
  have hstable : (prefixWord ++ tailWord_724222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724222).length < 2 ^ (prefixWord ++ tailWord_724222).sum := by decide
  have hdescent : baseEnd_724222 < baseStart_724222 := by decide
  rcases family_descends (prefixWord ++ tailWord_724222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724288 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 3]
def baseStart_724288 : Nat := 118140960795 + 724288 * 2 ^ 59
def prefixEnd_724288 : Nat := 4983230072969 + 3 ^ 40 * 724288 * 2
def baseEnd_724288 : Nat := 330584778918904403172503

theorem tailTrace_724288 : CollatzResearch.WordTrace tailWord_724288 prefixEnd_724288 330584778918904403172503 := by
  unfold tailWord_724288
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208476800017874693682759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17611302400023832924910345 13208476800017874693682759)
  ·
    refine ⟨19812715200026812040524139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13208476800017874693682759 19812715200026812040524139)
    ·
      refine ⟨29719072800040218060786209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19812715200026812040524139 29719072800040218060786209)
      ·
        refine ⟨22289304600030163545589657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29719072800040218060786209 22289304600030163545589657)
        ·
          refine ⟨16716978450022622659192243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22289304600030163545589657 16716978450022622659192243)
          ·
            refine ⟨25075467675033933988788365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16716978450022622659192243 25075467675033933988788365)
            ·
              refine ⟨9403300378137725245795637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25075467675033933988788365 9403300378137725245795637)
              ·
                refine ⟨881559410450411741793341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9403300378137725245795637 881559410450411741793341)
                ·
                  refine ⟨330584778918904403172503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881559410450411741793341 330584778918904403172503)
                  ·
                    rfl

theorem cell20_724288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_724288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724288 prefixEnd_724288 := by exact prefixLift 724288
  have htrace : WordTrace (prefixWord ++ tailWord_724288) baseStart_724288 baseEnd_724288 := by
    simpa [prefixWord, tailWord_724288, baseEnd_724288] using wordTrace_append hprefix tailTrace_724288
  have hstable : (prefixWord ++ tailWord_724288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724288).length < 2 ^ (prefixWord ++ tailWord_724288).sum := by decide
  have hdescent : baseEnd_724288 < baseStart_724288 := by decide
  rcases family_descends (prefixWord ++ tailWord_724288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724295 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_724295 : Nat := 118140960795 + 724295 * 2 ^ 59
def prefixEnd_724295 : Nat := 4983230072969 + 3 ^ 40 * 724295 * 2
def baseEnd_724295 : Nat := 330587973909643489939141

theorem tailTrace_724295 : CollatzResearch.WordTrace tailWord_724295 prefixEnd_724295 330587973909643489939141 := by
  unfold tailWord_724295
  simp only [CollatzResearch.WordTrace]
  refine ⟨26417208911010389582870339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17611472607340259721913559 26417208911010389582870339)
  ·
    refine ⟨39625813366515584374305509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26417208911010389582870339 39625813366515584374305509)
    ·
      refine ⟨7429840006221672070182283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39625813366515584374305509 7429840006221672070182283)
      ·
        refine ⟨11144760009332508105273425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7429840006221672070182283 11144760009332508105273425)
        ·
          refine ⟨8358570006999381078955069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11144760009332508105273425 8358570006999381078955069)
          ·
            refine ⟨3134463752624767904608151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8358570006999381078955069 3134463752624767904608151)
            ·
              refine ⟨4701695628937151856912227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3134463752624767904608151 4701695628937151856912227)
              ·
                refine ⟨7052543443405727785368341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4701695628937151856912227 7052543443405727785368341)
                ·
                  refine ⟨330587973909643489939141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7052543443405727785368341 330587973909643489939141)
                  ·
                    rfl

theorem cell20_724295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_724295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724295 prefixEnd_724295 := by exact prefixLift 724295
  have htrace : WordTrace (prefixWord ++ tailWord_724295) baseStart_724295 baseEnd_724295 := by
    simpa [prefixWord, tailWord_724295, baseEnd_724295] using wordTrace_append hprefix tailTrace_724295
  have hstable : (prefixWord ++ tailWord_724295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724295).length < 2 ^ (prefixWord ++ tailWord_724295).sum := by decide
  have hdescent : baseEnd_724295 < baseStart_724295 := by decide
  rcases family_descends (prefixWord ++ tailWord_724295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724343 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 3]
def baseStart_724343 : Nat := 118140960795 + 724343 * 2 ^ 59
def prefixEnd_724343 : Nat := 4983230072969 + 3 ^ 40 * 724343 * 2
def baseEnd_724343 : Nat := 330609882417568656338945

theorem tailTrace_724343 : CollatzResearch.WordTrace tailWord_724343 prefixEnd_724343 330609882417568656338945 := by
  unfold tailWord_724343
  simp only [CollatzResearch.WordTrace]
  refine ⟨26418959614836493780617683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17612639743224329187078455 26418959614836493780617683)
  ·
    refine ⟨39628439422254740670926525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26418959614836493780617683 39628439422254740670926525)
    ·
      refine ⟨14860664783345527751597447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39628439422254740670926525 14860664783345527751597447)
      ·
        refine ⟨22290997175018291627396171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14860664783345527751597447 22290997175018291627396171)
        ·
          refine ⟨33436495762527437441094257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22290997175018291627396171 33436495762527437441094257)
          ·
            refine ⟨25077371821895578080820693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33436495762527437441094257 25077371821895578080820693)
            ·
              refine ⟨587750902075677611269235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25077371821895578080820693 587750902075677611269235)
              ·
                refine ⟨881626353113516416903853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587750902075677611269235 881626353113516416903853)
                ·
                  refine ⟨330609882417568656338945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881626353113516416903853 330609882417568656338945)
                  ·
                    rfl

theorem cell20_724343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 3].length) (baseStart_724343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724343 prefixEnd_724343 := by exact prefixLift 724343
  have htrace : WordTrace (prefixWord ++ tailWord_724343) baseStart_724343 baseEnd_724343 := by
    simpa [prefixWord, tailWord_724343, baseEnd_724343] using wordTrace_append hprefix tailTrace_724343
  have hstable : (prefixWord ++ tailWord_724343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724343).length < 2 ^ (prefixWord ++ tailWord_724343).sum := by decide
  have hdescent : baseEnd_724343 < baseStart_724343 := by decide
  rcases family_descends (prefixWord ++ tailWord_724343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724353 : List Nat := [1, 2, 4, 3, 2, 2, 2, 4]
def baseStart_724353 : Nat := 118140960795 + 724353 * 2 ^ 59
def prefixEnd_724353 : Nat := 4983230072969 + 3 ^ 40 * 724353 * 2
def baseEnd_724353 : Nat := 110204815563351022001857

theorem tailTrace_724353 : CollatzResearch.WordTrace tailWord_724353 prefixEnd_724353 110204815563351022001857 := by
  unfold tailWord_724353
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419324344800265488481713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17612882896533510325654475 26419324344800265488481713)
  ·
    refine ⟨19814493258600199116361285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26419324344800265488481713 19814493258600199116361285)
    ·
      refine ⟨3715217485987537334317741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19814493258600199116361285 3715217485987537334317741)
      ·
        refine ⟨1393206557245326500369153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3715217485987537334317741 1393206557245326500369153)
        ·
          refine ⟨1044904917933994875276865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393206557245326500369153 1044904917933994875276865)
          ·
            refine ⟨783678688450496156457649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044904917933994875276865 783678688450496156457649)
            ·
              refine ⟨587759016337872117343237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 783678688450496156457649 587759016337872117343237)
              ·
                refine ⟨110204815563351022001857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587759016337872117343237 110204815563351022001857)
                ·
                  rfl

theorem cell20_724353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_724353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724353 prefixEnd_724353 := by exact prefixLift 724353
  have htrace : WordTrace (prefixWord ++ tailWord_724353) baseStart_724353 baseEnd_724353 := by
    simpa [prefixWord, tailWord_724353, baseEnd_724353] using wordTrace_append hprefix tailTrace_724353
  have hstable : (prefixWord ++ tailWord_724353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724353).length < 2 ^ (prefixWord ++ tailWord_724353).sum := by decide
  have hdescent : baseEnd_724353 < baseStart_724353 := by decide
  rcases family_descends (prefixWord ++ tailWord_724353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724357 : List Nat := [1, 3, 1, 1, 3, 1, 6, 4]
def baseStart_724357 : Nat := 118140960795 + 724357 * 2 ^ 59
def prefixEnd_724357 : Nat := 4983230072969 + 3 ^ 40 * 724357 * 2
def baseEnd_724357 : Nat := 110205424133015609957407

theorem tailTrace_724357 : CollatzResearch.WordTrace tailWord_724357 prefixEnd_724357 110205424133015609957407 := by
  unfold tailWord_724357
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419470236785774171627325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17612980157857182781084883 26419470236785774171627325)
  ·
    refine ⟨9907301338794665314360247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26419470236785774171627325 9907301338794665314360247)
    ·
      refine ⟨14860952008191997971540371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9907301338794665314360247 14860952008191997971540371)
      ·
        refine ⟨22291428012287996957310557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14860952008191997971540371 22291428012287996957310557)
        ·
          refine ⟨8359285504607998858991459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22291428012287996957310557 8359285504607998858991459)
          ·
            refine ⟨12538928256911998288487189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359285504607998858991459 12538928256911998288487189)
            ·
              refine ⟨587762262042749919772837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12538928256911998288487189 587762262042749919772837)
              ·
                refine ⟨110205424133015609957407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587762262042749919772837 110205424133015609957407)
                ·
                  rfl

theorem cell20_724357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_724357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724357 prefixEnd_724357 := by exact prefixLift 724357
  have htrace : WordTrace (prefixWord ++ tailWord_724357) baseStart_724357 baseEnd_724357 := by
    simpa [prefixWord, tailWord_724357, baseEnd_724357] using wordTrace_append hprefix tailTrace_724357
  have hstable : (prefixWord ++ tailWord_724357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724357).length < 2 ^ (prefixWord ++ tailWord_724357).sum := by decide
  have hdescent : baseEnd_724357 < baseStart_724357 := by decide
  rcases family_descends (prefixWord ++ tailWord_724357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724416 : List Nat := [2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_724416 : Nat := 118140960795 + 724416 * 2 ^ 59
def prefixEnd_724416 : Nat := 4983230072969 + 3 ^ 40 * 724416 * 2
def baseEnd_724416 : Nat := 110214400535568282301771

theorem tailTrace_724416 : CollatzResearch.WordTrace tailWord_724416 prefixEnd_724416 110214400535568282301771 := by
  unfold tailWord_724416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210811071786013624012551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17614414762381351498683401 13210811071786013624012551)
  ·
    refine ⟨19816216607679020436018827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13210811071786013624012551 19816216607679020436018827)
    ·
      refine ⟨29724324911518530654028241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19816216607679020436018827 29724324911518530654028241)
      ·
        refine ⟨22293243683638897990521181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29724324911518530654028241 22293243683638897990521181)
        ·
          refine ⟨8359966381364586746445443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22293243683638897990521181 8359966381364586746445443)
          ·
            refine ⟨12539949572046880119668165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8359966381364586746445443 12539949572046880119668165)
            ·
              refine ⟨2351240544758790022437781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12539949572046880119668165 2351240544758790022437781)
              ·
                refine ⟨110214400535568282301771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2351240544758790022437781 110214400535568282301771)
                ·
                  rfl

theorem cell20_724416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_724416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724416 prefixEnd_724416 := by exact prefixLift 724416
  have htrace : WordTrace (prefixWord ++ tailWord_724416) baseStart_724416 baseEnd_724416 := by
    simpa [prefixWord, tailWord_724416, baseEnd_724416] using wordTrace_append hprefix tailTrace_724416
  have hstable : (prefixWord ++ tailWord_724416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724416).length < 2 ^ (prefixWord ++ tailWord_724416).sum := by decide
  have hdescent : baseEnd_724416 < baseStart_724416 := by decide
  rcases family_descends (prefixWord ++ tailWord_724416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724436 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_724436 : Nat := 118140960795 + 724436 * 2 ^ 59
def prefixEnd_724436 : Nat := 4983230072969 + 3 ^ 40 * 724436 * 2
def baseEnd_724436 : Nat := 330652330151673666238565

theorem tailTrace_724436 : CollatzResearch.WordTrace tailWord_724436 prefixEnd_724436 330652330151673666238565 := by
  unfold tailWord_724436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211175801749785331876581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17614901068999713775835441 13211175801749785331876581)
  ·
    refine ⟨2477095462828084749726859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13211175801749785331876581 2477095462828084749726859)
    ·
      refine ⟨3715643194242127124590289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477095462828084749726859 3715643194242127124590289)
      ·
        refine ⟨2786732395681595343442717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3715643194242127124590289 2786732395681595343442717)
        ·
          refine ⟨1045024648380598253791019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2786732395681595343442717 1045024648380598253791019)
          ·
            refine ⟨1567536972570897380686529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045024648380598253791019 1567536972570897380686529)
            ·
              refine ⟨1175652729428173035514897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567536972570897380686529 1175652729428173035514897)
              ·
                refine ⟨881739547071129776636173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175652729428173035514897 881739547071129776636173)
                ·
                  refine ⟨330652330151673666238565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881739547071129776636173 330652330151673666238565)
                  ·
                    rfl

theorem cell20_724436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_724436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724436 prefixEnd_724436 := by exact prefixLift 724436
  have htrace : WordTrace (prefixWord ++ tailWord_724436) baseStart_724436 baseEnd_724436 := by
    simpa [prefixWord, tailWord_724436, baseEnd_724436] using wordTrace_append hprefix tailTrace_724436
  have hstable : (prefixWord ++ tailWord_724436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724436).length < 2 ^ (prefixWord ++ tailWord_724436).sum := by decide
  have hdescent : baseEnd_724436 < baseStart_724436 := by decide
  rcases family_descends (prefixWord ++ tailWord_724436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724440 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_724440 : Nat := 118140960795 + 724440 * 2 ^ 59
def prefixEnd_724440 : Nat := 4983230072969 + 3 ^ 40 * 724440 * 2
def baseEnd_724440 : Nat := 330654155860667430105215

theorem tailTrace_724440 : CollatzResearch.WordTrace tailWord_724440 prefixEnd_724440 330654155860667430105215 := by
  unfold tailWord_724440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211248747742539673449387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17614998330323386231265849 13211248747742539673449387)
  ·
    refine ⟨19816873121613809510174081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13211248747742539673449387 19816873121613809510174081)
    ·
      refine ⟨14862654841210357132630561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19816873121613809510174081 14862654841210357132630561)
      ·
        refine ⟨11146991130907767849472921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14862654841210357132630561 11146991130907767849472921)
        ·
          refine ⟨8360243348180825887104691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11146991130907767849472921 8360243348180825887104691)
          ·
            refine ⟨12540365022271238830657037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360243348180825887104691 12540365022271238830657037)
            ·
              refine ⟨4702636883351714561496389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12540365022271238830657037 4702636883351714561496389)
              ·
                refine ⟨881744415628446480280573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4702636883351714561496389 881744415628446480280573)
                ·
                  refine ⟨330654155860667430105215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881744415628446480280573 330654155860667430105215)
                  ·
                    rfl

theorem cell20_724440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_724440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724440 prefixEnd_724440 := by exact prefixLift 724440
  have htrace : WordTrace (prefixWord ++ tailWord_724440) baseStart_724440 baseEnd_724440 := by
    simpa [prefixWord, tailWord_724440, baseEnd_724440] using wordTrace_append hprefix tailTrace_724440
  have hstable : (prefixWord ++ tailWord_724440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724440).length < 2 ^ (prefixWord ++ tailWord_724440).sum := by decide
  have hdescent : baseEnd_724440 < baseStart_724440 := by decide
  rcases family_descends (prefixWord ++ tailWord_724440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724447 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_724447 : Nat := 118140960795 + 724447 * 2 ^ 59
def prefixEnd_724447 : Nat := 4983230072969 + 3 ^ 40 * 724447 * 2
def baseEnd_724447 : Nat := 330657350851406516871853

theorem tailTrace_724447 : CollatzResearch.WordTrace tailWord_724447 prefixEnd_724447 330657350851406516871853 := by
  unfold tailWord_724447
  simp only [CollatzResearch.WordTrace]
  refine ⟨26422752806459719542403595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17615168537639813028269063 26422752806459719542403595)
  ·
    refine ⟨39634129209689579313605393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26422752806459719542403595 39634129209689579313605393)
    ·
      refine ⟨29725596907267184485204045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39634129209689579313605393 29725596907267184485204045)
      ·
        refine ⟨11147098840225194181951517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29725596907267184485204045 11147098840225194181951517)
        ·
          refine ⟨4180162065084447818231819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11147098840225194181951517 4180162065084447818231819)
          ·
            refine ⟨6270243097626671727347729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180162065084447818231819 6270243097626671727347729)
            ·
              refine ⟨4702682323220003795510797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6270243097626671727347729 4702682323220003795510797)
              ·
                refine ⟨1763505871207501423316549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4702682323220003795510797 1763505871207501423316549)
                ·
                  refine ⟨330657350851406516871853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763505871207501423316549 330657350851406516871853)
                  ·
                    rfl

theorem cell20_724447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_724447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724447 prefixEnd_724447 := by exact prefixLift 724447
  have htrace : WordTrace (prefixWord ++ tailWord_724447) baseStart_724447 baseEnd_724447 := by
    simpa [prefixWord, tailWord_724447, baseEnd_724447] using wordTrace_append hprefix tailTrace_724447
  have hstable : (prefixWord ++ tailWord_724447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724447).length < 2 ^ (prefixWord ++ tailWord_724447).sum := by decide
  have hdescent : baseEnd_724447 < baseStart_724447 := by decide
  rcases family_descends (prefixWord ++ tailWord_724447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724512 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_724512 : Nat := 118140960795 + 724512 * 2 ^ 59
def prefixEnd_724512 : Nat := 4983230072969 + 3 ^ 40 * 724512 * 2
def baseEnd_724512 : Nat := 330687018622555179704921

theorem tailTrace_724512 : CollatzResearch.WordTrace tailWord_724512 prefixEnd_724512 330687018622555179704921 := by
  unfold tailWord_724512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212561775612117821759895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17616749034149490429013193 13212561775612117821759895)
  ·
    refine ⟨19818842663418176732639843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13212561775612117821759895 19818842663418176732639843)
    ·
      refine ⟨29728263995127265098959765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19818842663418176732639843 29728263995127265098959765)
      ·
        refine ⟨1393512374771590551513739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29728263995127265098959765 1393512374771590551513739)
        ·
          refine ⟨2090268562157385827270609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393512374771590551513739 2090268562157385827270609)
          ·
            refine ⟨1567701421618039370452957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2090268562157385827270609 1567701421618039370452957)
            ·
              refine ⟨587888033106764763919859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1567701421618039370452957 587888033106764763919859)
              ·
                refine ⟨881832049660147145879789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587888033106764763919859 881832049660147145879789)
                ·
                  refine ⟨330687018622555179704921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881832049660147145879789 330687018622555179704921)
                  ·
                    rfl

theorem cell20_724512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_724512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724512 prefixEnd_724512 := by exact prefixLift 724512
  have htrace : WordTrace (prefixWord ++ tailWord_724512) baseStart_724512 baseEnd_724512 := by
    simpa [prefixWord, tailWord_724512, baseEnd_724512] using wordTrace_append hprefix tailTrace_724512
  have hstable : (prefixWord ++ tailWord_724512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724512).length < 2 ^ (prefixWord ++ tailWord_724512).sum := by decide
  have hdescent : baseEnd_724512 < baseStart_724512 := by decide
  rcases family_descends (prefixWord ++ tailWord_724512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724526 : List Nat := [4, 1, 3, 1, 2, 1, 4, 4]
def baseStart_724526 : Nat := 118140960795 + 724526 * 2 ^ 59
def prefixEnd_724526 : Nat := 4983230072969 + 3 ^ 40 * 724526 * 2
def baseEnd_724526 : Nat := 110231136201344451079399

theorem tailTrace_724526 : CollatzResearch.WordTrace tailWord_724526 prefixEnd_724526 110231136201344451079399 := by
  unfold tailWord_724526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303204271646689504316179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17617089448782344023019621 3303204271646689504316179)
  ·
    refine ⟨4954806407470034256474269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3303204271646689504316179 4954806407470034256474269)
    ·
      refine ⟨1858052402801262846177851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4954806407470034256474269 1858052402801262846177851)
      ·
        refine ⟨2787078604201894269266777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858052402801262846177851 2787078604201894269266777)
        ·
          refine ⟨2090308953151420701950083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2787078604201894269266777 2090308953151420701950083)
          ·
            refine ⟨3135463429727131052925125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090308953151420701950083 3135463429727131052925125)
            ·
              refine ⟨587899393073837072423461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3135463429727131052925125 587899393073837072423461)
              ·
                refine ⟨110231136201344451079399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 587899393073837072423461 110231136201344451079399)
                ·
                  rfl

theorem cell20_724526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_724526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724526 prefixEnd_724526 := by exact prefixLift 724526
  have htrace : WordTrace (prefixWord ++ tailWord_724526) baseStart_724526 baseEnd_724526 := by
    simpa [prefixWord, tailWord_724526, baseEnd_724526] using wordTrace_append hprefix tailTrace_724526
  have hstable : (prefixWord ++ tailWord_724526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724526).length < 2 ^ (prefixWord ++ tailWord_724526).sum := by decide
  have hdescent : baseEnd_724526 < baseStart_724526 := by decide
  rcases family_descends (prefixWord ++ tailWord_724526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724554 : List Nat := [3, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_724554 : Nat := 118140960795 + 724554 * 2 ^ 59
def prefixEnd_724554 : Nat := 4983230072969 + 3 ^ 40 * 724554 * 2
def baseEnd_724554 : Nat := 330706188566989700304749

theorem tailTrace_724554 : CollatzResearch.WordTrace tailWord_724554 prefixEnd_724554 330706188566989700304749 := by
  unfold tailWord_724554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6606663854268019204137179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17617770278048051211032477 6606663854268019204137179)
  ·
    refine ⟨9909995781402028806205769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6606663854268019204137179 9909995781402028806205769)
    ·
      refine ⟨7432496836051521604654327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9909995781402028806205769 7432496836051521604654327)
      ·
        refine ⟨11148745254077282406981491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7432496836051521604654327 11148745254077282406981491)
        ·
          refine ⟨16723117881115923610472237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11148745254077282406981491 16723117881115923610472237)
          ·
            refine ⟨6271169205418471353927089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16723117881115923610472237 6271169205418471353927089)
            ·
              refine ⟨4703376904063853515445317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6271169205418471353927089 4703376904063853515445317)
              ·
                refine ⟨881883169511972534145997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4703376904063853515445317 881883169511972534145997)
                ·
                  refine ⟨330706188566989700304749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881883169511972534145997 330706188566989700304749)
                  ·
                    rfl

theorem cell20_724554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_724554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724554 prefixEnd_724554 := by exact prefixLift 724554
  have htrace : WordTrace (prefixWord ++ tailWord_724554) baseStart_724554 baseEnd_724554 := by
    simpa [prefixWord, tailWord_724554, baseEnd_724554] using wordTrace_append hprefix tailTrace_724554
  have hstable : (prefixWord ++ tailWord_724554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724554).length < 2 ^ (prefixWord ++ tailWord_724554).sum := by decide
  have hdescent : baseEnd_724554 < baseStart_724554 := by decide
  rcases family_descends (prefixWord ++ tailWord_724554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724609 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 3]
def baseStart_724609 : Nat := 118140960795 + 724609 * 2 ^ 59
def prefixEnd_724609 : Nat := 4983230072969 + 3 ^ 40 * 724609 * 2
def baseEnd_724609 : Nat := 330731292065653953471191

theorem tailTrace_724609 : CollatzResearch.WordTrace tailWord_724609 prefixEnd_724609 330731292065653953471191 := by
  unfold tailWord_724609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26428661431872821209800881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17619107621248547473200587 26428661431872821209800881)
  ·
    refine ⟨19821496073904615907350661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26428661431872821209800881 19821496073904615907350661)
    ·
      refine ⟨3716530513857115482628249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19821496073904615907350661 3716530513857115482628249)
      ·
        refine ⟨2787397885392836611971187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3716530513857115482628249 2787397885392836611971187)
        ·
          refine ⟨4181096828089254917956781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787397885392836611971187 4181096828089254917956781)
          ·
            refine ⟨1567911310533470594233793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4181096828089254917956781 1567911310533470594233793)
            ·
              refine ⟨1175933482900102945675345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567911310533470594233793 1175933482900102945675345)
              ·
                refine ⟨881950112175077209256509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175933482900102945675345 881950112175077209256509)
                ·
                  refine ⟨330731292065653953471191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881950112175077209256509 330731292065653953471191)
                  ·
                    rfl

theorem cell20_724609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_724609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724609 prefixEnd_724609 := by exact prefixLift 724609
  have htrace : WordTrace (prefixWord ++ tailWord_724609) baseStart_724609 baseEnd_724609 := by
    simpa [prefixWord, tailWord_724609, baseEnd_724609] using wordTrace_append hprefix tailTrace_724609
  have hstable : (prefixWord ++ tailWord_724609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724609).length < 2 ^ (prefixWord ++ tailWord_724609).sum := by decide
  have hdescent : baseEnd_724609 < baseStart_724609 := by decide
  rcases family_descends (prefixWord ++ tailWord_724609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724661 : List Nat := [1, 3, 3, 3, 2, 1, 7]
def baseStart_724661 : Nat := 118140960795 + 724661 * 2 ^ 59
def prefixEnd_724661 : Nat := 4983230072969 + 3 ^ 40 * 724661 * 2
def baseEnd_724661 : Nat := 36750558475841431526405

theorem tailTrace_724661 : CollatzResearch.WordTrace tailWord_724661 prefixEnd_724661 36750558475841431526405 := by
  unfold tailWord_724661
  simp only [CollatzResearch.WordTrace]
  refine ⟨26430558027684434090693837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17620372018456289393795891 26430558027684434090693837)
  ·
    refine ⟨9911459260381662784010189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26430558027684434090693837 9911459260381662784010189)
    ·
      refine ⟨3716797222643123544003821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9911459260381662784010189 3716797222643123544003821)
      ·
        refine ⟨1393798958491171329001433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3716797222643123544003821 1393798958491171329001433)
        ·
          refine ⟨1045349218868378496751075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393798958491171329001433 1045349218868378496751075)
          ·
            refine ⟨1568023828302567745126613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045349218868378496751075 1568023828302567745126613)
            ·
              refine ⟨36750558475841431526405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1568023828302567745126613 36750558475841431526405)
              ·
                rfl

theorem cell20_724661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_724661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724661 prefixEnd_724661 := by exact prefixLift 724661
  have htrace : WordTrace (prefixWord ++ tailWord_724661) baseStart_724661 baseEnd_724661 := by
    simpa [prefixWord, tailWord_724661, baseEnd_724661] using wordTrace_append hprefix tailTrace_724661
  have hstable : (prefixWord ++ tailWord_724661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724661).length < 2 ^ (prefixWord ++ tailWord_724661).sum := by decide
  have hdescent : baseEnd_724661 < baseStart_724661 := by decide
  rcases family_descends (prefixWord ++ tailWord_724661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724668 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_724668 : Nat := 118140960795 + 724668 * 2 ^ 59
def prefixEnd_724668 : Nat := 4983230072969 + 3 ^ 40 * 724668 * 2
def baseEnd_724668 : Nat := 330758221273311970504283

theorem tailTrace_724668 : CollatzResearch.WordTrace tailWord_724668 prefixEnd_724668 330758221273311970504283 := by
  unfold tailWord_724668
  simp only [CollatzResearch.WordTrace]
  refine ⟨13215406669329537143099329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17620542225772716190799105 13215406669329537143099329)
  ·
    refine ⟨9911555001997152857324497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13215406669329537143099329 9911555001997152857324497)
    ·
      refine ⟨7433666251497864642993373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9911555001997152857324497 7433666251497864642993373)
      ·
        refine ⟨2787624844311699241122515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7433666251497864642993373 2787624844311699241122515)
        ·
          refine ⟨4181437266467548861683773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787624844311699241122515 4181437266467548861683773)
          ·
            refine ⟨1568038974925330823131415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4181437266467548861683773 1568038974925330823131415)
            ·
              refine ⟨2352058462387996234697123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568038974925330823131415 2352058462387996234697123)
              ·
                refine ⟨3528087693581994352045685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352058462387996234697123 3528087693581994352045685)
                ·
                  refine ⟨330758221273311970504283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3528087693581994352045685 330758221273311970504283)
                  ·
                    rfl

theorem cell20_724668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_724668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724668 prefixEnd_724668 := by exact prefixLift 724668
  have htrace : WordTrace (prefixWord ++ tailWord_724668) baseStart_724668 baseEnd_724668 := by
    simpa [prefixWord, tailWord_724668, baseEnd_724668] using wordTrace_append hprefix tailTrace_724668
  have hstable : (prefixWord ++ tailWord_724668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724668).length < 2 ^ (prefixWord ++ tailWord_724668).sum := by decide
  have hdescent : baseEnd_724668 < baseStart_724668 := by decide
  rcases family_descends (prefixWord ++ tailWord_724668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724692 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_724692 : Nat := 118140960795 + 724692 * 2 ^ 59
def prefixEnd_724692 : Nat := 4983230072969 + 3 ^ 40 * 724692 * 2
def baseEnd_724692 : Nat := 330769175527274553704185

theorem tailTrace_724692 : CollatzResearch.WordTrace tailWord_724692 prefixEnd_724692 330769175527274553704185 := by
  unfold tailWord_724692
  simp only [CollatzResearch.WordTrace]
  refine ⟨13215844345286063192536165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17621125793714750923381553 13215844345286063192536165)
  ·
    refine ⟨2477970814741136848600531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13215844345286063192536165 2477970814741136848600531)
    ·
      refine ⟨3716956222111705272900797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477970814741136848600531 3716956222111705272900797)
      ·
        refine ⟨1393858583291889477337799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3716956222111705272900797 1393858583291889477337799)
        ·
          refine ⟨2090787874937834216006699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393858583291889477337799 2090787874937834216006699)
          ·
            refine ⟨3136181812406751324010049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090787874937834216006699 3136181812406751324010049)
            ·
              refine ⟨2352136359305063493007537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3136181812406751324010049 2352136359305063493007537)
              ·
                refine ⟨1764102269478797619755653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352136359305063493007537 1764102269478797619755653)
                ·
                  refine ⟨330769175527274553704185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1764102269478797619755653 330769175527274553704185)
                  ·
                    rfl

theorem cell20_724692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_724692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724692 prefixEnd_724692 := by exact prefixLift 724692
  have htrace : WordTrace (prefixWord ++ tailWord_724692) baseStart_724692 baseEnd_724692 := by
    simpa [prefixWord, tailWord_724692, baseEnd_724692] using wordTrace_append hprefix tailTrace_724692
  have hstable : (prefixWord ++ tailWord_724692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724692).length < 2 ^ (prefixWord ++ tailWord_724692).sum := by decide
  have hdescent : baseEnd_724692 < baseStart_724692 := by decide
  rcases family_descends (prefixWord ++ tailWord_724692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724726 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_724726 : Nat := 118140960795 + 724726 * 2 ^ 59
def prefixEnd_724726 : Nat := 4983230072969 + 3 ^ 40 * 724726 * 2
def baseEnd_724726 : Nat := 330784694053721546570713

theorem tailTrace_724726 : CollatzResearch.WordTrace tailWord_724726 prefixEnd_724726 330784694053721546570713 := by
  unfold tailWord_724726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652058048278059386988127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17621952514965966794540021 1652058048278059386988127)
  ·
    refine ⟨2478087072417089080482191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652058048278059386988127 2478087072417089080482191)
    ·
      refine ⟨3717130608625633620723287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478087072417089080482191 3717130608625633620723287)
      ·
        refine ⟨5575695912938450431084931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717130608625633620723287 5575695912938450431084931)
        ·
          refine ⟨8363543869407675646627397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5575695912938450431084931 8363543869407675646627397)
          ·
            refine ⟨1568164475513939183742637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8363543869407675646627397 1568164475513939183742637)
            ·
              refine ⟨588061678317727193903489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1568164475513939183742637 588061678317727193903489)
              ·
                refine ⟨441046258738295395427617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588061678317727193903489 441046258738295395427617)
                ·
                  refine ⟨330784694053721546570713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441046258738295395427617 330784694053721546570713)
                  ·
                    rfl

theorem cell20_724726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_724726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724726 prefixEnd_724726 := by exact prefixLift 724726
  have htrace : WordTrace (prefixWord ++ tailWord_724726) baseStart_724726 baseEnd_724726 := by
    simpa [prefixWord, tailWord_724726, baseEnd_724726] using wordTrace_append hprefix tailTrace_724726
  have hstable : (prefixWord ++ tailWord_724726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724726).length < 2 ^ (prefixWord ++ tailWord_724726).sum := by decide
  have hdescent : baseEnd_724726 < baseStart_724726 := by decide
  rcases family_descends (prefixWord ++ tailWord_724726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724727 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_724727 : Nat := 118140960795 + 724727 * 2 ^ 59
def prefixEnd_724727 : Nat := 4983230072969 + 3 ^ 40 * 724727 * 2
def baseEnd_724727 : Nat := 330785150480969987537375

theorem tailTrace_724727 : CollatzResearch.WordTrace tailWord_724727 prefixEnd_724727 330785150480969987537375 := by
  unfold tailWord_724727
  simp only [CollatzResearch.WordTrace]
  refine ⟨26432965245445327362596435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17621976830296884908397623 26432965245445327362596435)
  ·
    refine ⟨39649447868167991043894653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26432965245445327362596435 39649447868167991043894653)
    ·
      refine ⟨14868542950562996641460495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39649447868167991043894653 14868542950562996641460495)
      ·
        refine ⟨22302814425844494962190743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14868542950562996641460495 22302814425844494962190743)
        ·
          refine ⟨33454221638766742443286115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22302814425844494962190743 33454221638766742443286115)
          ·
            refine ⟨50181332458150113664929173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33454221638766742443286115 50181332458150113664929173)
            ·
              refine ⟨2352249958975786578043555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50181332458150113664929173 2352249958975786578043555)
              ·
                refine ⟨3528374938463679867065333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352249958975786578043555 3528374938463679867065333)
                ·
                  refine ⟨330785150480969987537375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3528374938463679867065333 330785150480969987537375)
                  ·
                    rfl

theorem cell20_724727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_724727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724727 prefixEnd_724727 := by exact prefixLift 724727
  have htrace : WordTrace (prefixWord ++ tailWord_724727) baseStart_724727 baseEnd_724727 := by
    simpa [prefixWord, tailWord_724727, baseEnd_724727] using wordTrace_append hprefix tailTrace_724727
  have hstable : (prefixWord ++ tailWord_724727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724727).length < 2 ^ (prefixWord ++ tailWord_724727).sum := by decide
  have hdescent : baseEnd_724727 < baseStart_724727 := by decide
  rcases family_descends (prefixWord ++ tailWord_724727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724740 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_724740 : Nat := 118140960795 + 724740 * 2 ^ 59
def prefixEnd_724740 : Nat := 4983230072969 + 3 ^ 40 * 724740 * 2
def baseEnd_724740 : Nat := 330791084035199720103989

theorem tailTrace_724740 : CollatzResearch.WordTrace tailWord_724740 prefixEnd_724740 330791084035199720103989 := by
  unfold tailWord_724740
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216719697199115291409837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17622292929598820388546449 13216719697199115291409837)
  ·
    refine ⟨4956269886449668234278689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13216719697199115291409837 4956269886449668234278689)
    ·
      refine ⟨3717202414837251175709017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4956269886449668234278689 3717202414837251175709017)
      ·
        refine ⟨2787901811127938381781763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3717202414837251175709017 2787901811127938381781763)
        ·
          refine ⟨4181852716691907572672645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787901811127938381781763 4181852716691907572672645)
          ·
            refine ⟨784097384379732669876121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4181852716691907572672645 784097384379732669876121)
            ·
              refine ⟨588073038284799502407091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784097384379732669876121 588073038284799502407091)
              ·
                refine ⟨882109557427199253610637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588073038284799502407091 882109557427199253610637)
                ·
                  refine ⟨330791084035199720103989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882109557427199253610637 330791084035199720103989)
                  ·
                    rfl

theorem cell20_724740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_724740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724740 prefixEnd_724740 := by exact prefixLift 724740
  have htrace : WordTrace (prefixWord ++ tailWord_724740) baseStart_724740 baseEnd_724740 := by
    simpa [prefixWord, tailWord_724740, baseEnd_724740] using wordTrace_append hprefix tailTrace_724740
  have hstable : (prefixWord ++ tailWord_724740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724740).length < 2 ^ (prefixWord ++ tailWord_724740).sum := by decide
  have hdescent : baseEnd_724740 < baseStart_724740 := by decide
  rcases family_descends (prefixWord ++ tailWord_724740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724744 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_724744 : Nat := 118140960795 + 724744 * 2 ^ 59
def prefixEnd_724744 : Nat := 4983230072969 + 3 ^ 40 * 724744 * 2
def baseEnd_724744 : Nat := 330792909744193483970639

theorem tailTrace_724744 : CollatzResearch.WordTrace tailWord_724744 prefixEnd_724744 330792909744193483970639 := by
  unfold tailWord_724744
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216792643191869632982643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17622390190922492843976857 13216792643191869632982643)
  ·
    refine ⟨19825188964787804449473965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13216792643191869632982643 19825188964787804449473965)
    ·
      refine ⟨7434445861795426668552737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19825188964787804449473965 7434445861795426668552737)
      ·
        refine ⟨5575834396346570001414553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7434445861795426668552737 5575834396346570001414553)
        ·
          refine ⟨4181875797259927501060915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5575834396346570001414553 4181875797259927501060915)
          ·
            refine ⟨6272813695889891251591373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4181875797259927501060915 6272813695889891251591373)
            ·
              refine ⟨2352305135958709219346765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6272813695889891251591373 2352305135958709219346765)
              ·
                refine ⟨882114425984515957255037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2352305135958709219346765 882114425984515957255037)
                ·
                  refine ⟨330792909744193483970639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882114425984515957255037 330792909744193483970639)
                  ·
                    rfl

theorem cell20_724744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_724744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724744 prefixEnd_724744 := by exact prefixLift 724744
  have htrace : WordTrace (prefixWord ++ tailWord_724744) baseStart_724744 baseEnd_724744 := by
    simpa [prefixWord, tailWord_724744, baseEnd_724744] using wordTrace_append hprefix tailTrace_724744
  have hstable : (prefixWord ++ tailWord_724744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724744).length < 2 ^ (prefixWord ++ tailWord_724744).sum := by decide
  have hdescent : baseEnd_724744 < baseStart_724744 := by decide
  rcases family_descends (prefixWord ++ tailWord_724744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724768 : List Nat := [2, 1, 1, 5, 1, 1, 2, 5, 2]
def baseStart_724768 : Nat := 118140960795 + 724768 * 2 ^ 59
def prefixEnd_724768 : Nat := 4983230072969 + 3 ^ 40 * 724768 * 2
def baseEnd_724768 : Nat := 330803863998156067170541

theorem tailTrace_724768 : CollatzResearch.WordTrace tailWord_724768 prefixEnd_724768 330803863998156067170541 := by
  unfold tailWord_724768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217230319148395682419479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17622973758864527576559305 13217230319148395682419479)
  ·
    refine ⟨19825845478722593523629219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13217230319148395682419479 19825845478722593523629219)
    ·
      refine ⟨29738768218083890285443829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19825845478722593523629219 29738768218083890285443829)
      ·
        refine ⟨2788009520445364714260359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29738768218083890285443829 2788009520445364714260359)
        ·
          refine ⟨4182014280668047071390539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2788009520445364714260359 4182014280668047071390539)
          ·
            refine ⟨6273021421002070607085809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4182014280668047071390539 6273021421002070607085809)
            ·
              refine ⟨4704766065751552955314357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6273021421002070607085809 4704766065751552955314357)
              ·
                refine ⟨441071818664208089560721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4704766065751552955314357 441071818664208089560721)
                ·
                  refine ⟨330803863998156067170541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441071818664208089560721 330803863998156067170541)
                  ·
                    rfl

theorem cell20_724768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 5, 2].length) (baseStart_724768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724768 prefixEnd_724768 := by exact prefixLift 724768
  have htrace : WordTrace (prefixWord ++ tailWord_724768) baseStart_724768 baseEnd_724768 := by
    simpa [prefixWord, tailWord_724768, baseEnd_724768] using wordTrace_append hprefix tailTrace_724768
  have hstable : (prefixWord ++ tailWord_724768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724768).length < 2 ^ (prefixWord ++ tailWord_724768).sum := by decide
  have hdescent : baseEnd_724768 < baseStart_724768 := by decide
  rcases family_descends (prefixWord ++ tailWord_724768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724785 : List Nat := [1, 2, 2, 3, 2, 2, 4, 2, 2]
def baseStart_724785 : Nat := 118140960795 + 724785 * 2 ^ 59
def prefixEnd_724785 : Nat := 4983230072969 + 3 ^ 40 * 724785 * 2
def baseEnd_724785 : Nat := 330811623261379563603805

theorem tailTrace_724785 : CollatzResearch.WordTrace tailWord_724785 prefixEnd_724785 330811623261379563603805 := by
  unfold tailWord_724785
  simp only [CollatzResearch.WordTrace]
  refine ⟨26435080679235203268207809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17623387119490135512138539 26435080679235203268207809)
  ·
    refine ⟨19826310509426402451155857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26435080679235203268207809 19826310509426402451155857)
    ·
      refine ⟨14869732882069801838366893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19826310509426402451155857 14869732882069801838366893)
      ·
        refine ⟨5576149830776175689387585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14869732882069801838366893 5576149830776175689387585)
        ·
          refine ⟨4182112373082131767040689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5576149830776175689387585 4182112373082131767040689)
          ·
            refine ⟨3136584279811598825280517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4182112373082131767040689 3136584279811598825280517)
            ·
              refine ⟨588109552464674779740097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3136584279811598825280517 588109552464674779740097)
              ·
                refine ⟨441082164348506084805073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588109552464674779740097 441082164348506084805073)
                ·
                  refine ⟨330811623261379563603805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441082164348506084805073 330811623261379563603805)
                  ·
                    rfl

theorem cell20_724785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_724785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724785 prefixEnd_724785 := by exact prefixLift 724785
  have htrace : WordTrace (prefixWord ++ tailWord_724785) baseStart_724785 baseEnd_724785 := by
    simpa [prefixWord, tailWord_724785, baseEnd_724785] using wordTrace_append hprefix tailTrace_724785
  have hstable : (prefixWord ++ tailWord_724785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724785).length < 2 ^ (prefixWord ++ tailWord_724785).sum := by decide
  have hdescent : baseEnd_724785 < baseStart_724785 := by decide
  rcases family_descends (prefixWord ++ tailWord_724785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724796 : List Nat := [2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_724796 : Nat := 118140960795 + 724796 * 2 ^ 59
def prefixEnd_724796 : Nat := 4983230072969 + 3 ^ 40 * 724796 * 2
def baseEnd_724796 : Nat := 110272214653704138079031

theorem tailTrace_724796 : CollatzResearch.WordTrace tailWord_724796 prefixEnd_724796 110272214653704138079031 := by
  unfold tailWord_724796
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217740941097676073429121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17623654588130234764572161 13217740941097676073429121)
  ·
    refine ⟨9913305705823257055071841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13217740941097676073429121 9913305705823257055071841)
    ·
      refine ⟨7434979279367442791303881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9913305705823257055071841 7434979279367442791303881)
      ·
        refine ⟨5576234459525582093477911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7434979279367442791303881 5576234459525582093477911)
        ·
          refine ⟨8364351689288373140216867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5576234459525582093477911 8364351689288373140216867)
          ·
            refine ⟨12546527533932559710325301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8364351689288373140216867 12546527533932559710325301)
            ·
              refine ⟨1176236956306177472842997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12546527533932559710325301 1176236956306177472842997)
              ·
                refine ⟨110272214653704138079031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1176236956306177472842997 110272214653704138079031)
                ·
                  rfl

theorem cell20_724796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_724796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724796 prefixEnd_724796 := by exact prefixLift 724796
  have htrace : WordTrace (prefixWord ++ tailWord_724796) baseStart_724796 baseEnd_724796 := by
    simpa [prefixWord, tailWord_724796, baseEnd_724796] using wordTrace_append hprefix tailTrace_724796
  have hstable : (prefixWord ++ tailWord_724796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724796).length < 2 ^ (prefixWord ++ tailWord_724796).sum := by decide
  have hdescent : baseEnd_724796 < baseStart_724796 := by decide
  rcases family_descends (prefixWord ++ tailWord_724796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724823 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 2]
def baseStart_724823 : Nat := 118140960795 + 724823 * 2 ^ 59
def prefixEnd_724823 : Nat := 4983230072969 + 3 ^ 40 * 724823 * 2
def baseEnd_724823 : Nat := 330828967496820320336983

theorem tailTrace_724823 : CollatzResearch.WordTrace tailWord_724823 prefixEnd_724823 330828967496820320336983 := by
  unfold tailWord_724823
  simp only [CollatzResearch.WordTrace]
  refine ⟨26436466653097535758091123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17624311102065023838727415 26436466653097535758091123)
  ·
    refine ⟨39654699979646303637136685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26436466653097535758091123 39654699979646303637136685)
    ·
      refine ⟨14870512492367363863926257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39654699979646303637136685 14870512492367363863926257)
      ·
        refine ⟨11152884369275522897944693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14870512492367363863926257 11152884369275522897944693)
        ·
          refine ⟨1045582909619580271682315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11152884369275522897944693 1045582909619580271682315)
          ·
            refine ⟨1568374364429370407523473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045582909619580271682315 1568374364429370407523473)
            ·
              refine ⟨1176280773322027805642605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568374364429370407523473 1176280773322027805642605)
              ·
                refine ⟨441105289995760427115977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176280773322027805642605 441105289995760427115977)
                ·
                  refine ⟨330828967496820320336983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441105289995760427115977 330828967496820320336983)
                  ·
                    rfl

theorem cell20_724823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 2].length) (baseStart_724823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724823 prefixEnd_724823 := by exact prefixLift 724823
  have htrace : WordTrace (prefixWord ++ tailWord_724823) baseStart_724823 baseEnd_724823 := by
    simpa [prefixWord, tailWord_724823, baseEnd_724823] using wordTrace_append hprefix tailTrace_724823
  have hstable : (prefixWord ++ tailWord_724823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724823).length < 2 ^ (prefixWord ++ tailWord_724823).sum := by decide
  have hdescent : baseEnd_724823 < baseStart_724823 := by decide
  rcases family_descends (prefixWord ++ tailWord_724823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724844 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 2]
def baseStart_724844 : Nat := 118140960795 + 724844 * 2 ^ 59
def prefixEnd_724844 : Nat := 4983230072969 + 3 ^ 40 * 724844 * 2
def baseEnd_724844 : Nat := 330838552469037580636897

theorem tailTrace_724844 : CollatzResearch.WordTrace tailWord_724844 prefixEnd_724844 330838552469037580636897 := by
  unfold tailWord_724844
  simp only [CollatzResearch.WordTrace]
  refine ⟨13218616293010728172302793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17624821724014304229737057 13218616293010728172302793)
  ·
    refine ⟨9913962219758046129227095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13218616293010728172302793 9913962219758046129227095)
    ·
      refine ⟨14870943329637069193840643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9913962219758046129227095 14870943329637069193840643)
      ·
        refine ⟨22306414994455603790760965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14870943329637069193840643 22306414994455603790760965)
        ·
          refine ⟨4182452811460425710767681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22306414994455603790760965 4182452811460425710767681)
          ·
            refine ⟨3136839608595319283075761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4182452811460425710767681 3136839608595319283075761)
            ·
              refine ⟨2352629706446489462306821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3136839608595319283075761 2352629706446489462306821)
              ·
                refine ⟨441118069958716774182529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2352629706446489462306821 441118069958716774182529)
                ·
                  refine ⟨330838552469037580636897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441118069958716774182529 330838552469037580636897)
                  ·
                    rfl

theorem cell20_724844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_724844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724844 prefixEnd_724844 := by exact prefixLift 724844
  have htrace : WordTrace (prefixWord ++ tailWord_724844) baseStart_724844 baseEnd_724844 := by
    simpa [prefixWord, tailWord_724844, baseEnd_724844] using wordTrace_append hprefix tailTrace_724844
  have hstable : (prefixWord ++ tailWord_724844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724844).length < 2 ^ (prefixWord ++ tailWord_724844).sum := by decide
  have hdescent : baseEnd_724844 < baseStart_724844 := by decide
  rcases family_descends (prefixWord ++ tailWord_724844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724913 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 3]
def baseStart_724913 : Nat := 118140960795 + 724913 * 2 ^ 59
def prefixEnd_724913 : Nat := 4983230072969 + 3 ^ 40 * 724913 * 2
def baseEnd_724913 : Nat := 330870045949180007336615

theorem tailTrace_724913 : CollatzResearch.WordTrace tailWord_724913 prefixEnd_724913 330870045949180007336615 := by
  unfold tailWord_724913
  simp only [CollatzResearch.WordTrace]
  refine ⟨26439749222771481128867393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17626499481847654085911595 26439749222771481128867393)
  ·
    refine ⟨19829811917078610846650545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26439749222771481128867393 19829811917078610846650545)
    ·
      refine ⟨14872358937808958134987909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19829811917078610846650545 14872358937808958134987909)
      ·
        refine ⟨2788567300839179650310233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14872358937808958134987909 2788567300839179650310233)
        ·
          refine ⟨2091425475629384737732675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788567300839179650310233 2091425475629384737732675)
          ·
            refine ⟨3137138213444077106599013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091425475629384737732675 3137138213444077106599013)
            ·
              refine ⟨588213415020764457487315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3137138213444077106599013 588213415020764457487315)
              ·
                refine ⟨882320122531146686230973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588213415020764457487315 882320122531146686230973)
                ·
                  refine ⟨330870045949180007336615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882320122531146686230973 330870045949180007336615)
                  ·
                    rfl

theorem cell20_724913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_724913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724913 prefixEnd_724913 := by exact prefixLift 724913
  have htrace : WordTrace (prefixWord ++ tailWord_724913) baseStart_724913 baseEnd_724913 := by
    simpa [prefixWord, tailWord_724913, baseEnd_724913] using wordTrace_append hprefix tailTrace_724913
  have hstable : (prefixWord ++ tailWord_724913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724913).length < 2 ^ (prefixWord ++ tailWord_724913).sum := by decide
  have hdescent : baseEnd_724913 < baseStart_724913 := by decide
  rcases family_descends (prefixWord ++ tailWord_724913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724950 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_724950 : Nat := 118140960795 + 724950 * 2 ^ 59
def prefixEnd_724950 : Nat := 4983230072969 + 3 ^ 40 * 724950 * 2
def baseEnd_724950 : Nat := 330886933757372323103131

theorem tailTrace_724950 : CollatzResearch.WordTrace tailWord_724950 prefixEnd_724950 330886933757372323103131 := by
  unfold tailWord_724950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652568670227339777997769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17627399149091624298642869 1652568670227339777997769)
  ·
    refine ⟨1239426502670504833498327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1652568670227339777997769 1239426502670504833498327)
    ·
      refine ⟨1859139754005757250247491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239426502670504833498327 1859139754005757250247491)
      ·
        refine ⟨2788709631008635875371237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859139754005757250247491 2788709631008635875371237)
        ·
          refine ⟨522883055814119226632107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2788709631008635875371237 522883055814119226632107)
          ·
            refine ⟨784324583721178839948161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522883055814119226632107 784324583721178839948161)
            ·
              refine ⟨588243437790884129961121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784324583721178839948161 588243437790884129961121)
              ·
                refine ⟨441182578343163097470841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588243437790884129961121 441182578343163097470841)
                ·
                  refine ⟨330886933757372323103131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441182578343163097470841 330886933757372323103131)
                  ·
                    rfl

theorem cell20_724950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_724950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724950 prefixEnd_724950 := by exact prefixLift 724950
  have htrace : WordTrace (prefixWord ++ tailWord_724950) baseStart_724950 baseEnd_724950 := by
    simpa [prefixWord, tailWord_724950, baseEnd_724950] using wordTrace_append hprefix tailTrace_724950
  have hstable : (prefixWord ++ tailWord_724950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724950).length < 2 ^ (prefixWord ++ tailWord_724950).sum := by decide
  have hdescent : baseEnd_724950 < baseStart_724950 := by decide
  rcases family_descends (prefixWord ++ tailWord_724950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724954 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_724954 : Nat := 118140960795 + 724954 * 2 ^ 59
def prefixEnd_724954 : Nat := 4983230072969 + 3 ^ 40 * 724954 * 2
def baseEnd_724954 : Nat := 330888759466366086969781

theorem tailTrace_724954 : CollatzResearch.WordTrace tailWord_724954 prefixEnd_724954 330888759466366086969781 := by
  unfold tailWord_724954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6610311153905736282777479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17627496410415296754073277 6610311153905736282777479)
  ·
    refine ⟨9915466730858604424166219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6610311153905736282777479 9915466730858604424166219)
    ·
      refine ⟨14873200096287906636249329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9915466730858604424166219 14873200096287906636249329)
      ·
        refine ⟨11154900072215929977186997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14873200096287906636249329 11154900072215929977186997)
        ·
          refine ⟨1045771881770243435361281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11154900072215929977186997 1045771881770243435361281)
          ·
            refine ⟨784328911327682576520961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1045771881770243435361281 784328911327682576520961)
            ·
              refine ⟨588246683495761932390721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784328911327682576520961 588246683495761932390721)
              ·
                refine ⟨441185012621821449293041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588246683495761932390721 441185012621821449293041)
                ·
                  refine ⟨330888759466366086969781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441185012621821449293041 330888759466366086969781)
                  ·
                    rfl

theorem cell20_724954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_724954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724954 prefixEnd_724954 := by exact prefixLift 724954
  have htrace : WordTrace (prefixWord ++ tailWord_724954) baseStart_724954 baseEnd_724954 := by
    simpa [prefixWord, tailWord_724954, baseEnd_724954] using wordTrace_append hprefix tailTrace_724954
  have hstable : (prefixWord ++ tailWord_724954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724954).length < 2 ^ (prefixWord ++ tailWord_724954).sum := by decide
  have hdescent : baseEnd_724954 < baseStart_724954 := by decide
  rcases family_descends (prefixWord ++ tailWord_724954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724982 : List Nat := [5, 1, 1, 1, 4, 1, 3, 4]
def baseStart_724982 : Nat := 118140960795 + 724982 * 2 ^ 59
def prefixEnd_724982 : Nat := 4983230072969 + 3 ^ 40 * 724982 * 2
def baseEnd_724982 : Nat := 110300513143107478012111

theorem tailTrace_724982 : CollatzResearch.WordTrace tailWord_724982 prefixEnd_724982 110300513143107478012111 := by
  unfold tailWord_724982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652641616220094119570575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17628177239681003942086133 1652641616220094119570575)
  ·
    refine ⟨2478962424330141179355863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652641616220094119570575 2478962424330141179355863)
    ·
      refine ⟨3718443636495211769033795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478962424330141179355863 3718443636495211769033795)
      ·
        refine ⟨5577665454742817653550693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3718443636495211769033795 5577665454742817653550693)
        ·
          refine ⟨1045812272764278310040755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5577665454742817653550693 1045812272764278310040755)
          ·
            refine ⟨1568718409146417465061133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045812272764278310040755 1568718409146417465061133)
            ·
              refine ⟨588269403429906549397925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1568718409146417465061133 588269403429906549397925)
              ·
                refine ⟨110300513143107478012111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588269403429906549397925 110300513143107478012111)
                ·
                  rfl

theorem cell20_724982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_724982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724982 prefixEnd_724982 := by exact prefixLift 724982
  have htrace : WordTrace (prefixWord ++ tailWord_724982) baseStart_724982 baseEnd_724982 := by
    simpa [prefixWord, tailWord_724982, baseEnd_724982] using wordTrace_append hprefix tailTrace_724982
  have hstable : (prefixWord ++ tailWord_724982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724982).length < 2 ^ (prefixWord ++ tailWord_724982).sum := by decide
  have hdescent : baseEnd_724982 < baseStart_724982 := by decide
  rcases family_descends (prefixWord ++ tailWord_724982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_724993 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_724993 : Nat := 118140960795 + 724993 * 2 ^ 59
def prefixEnd_724993 : Nat := 4983230072969 + 3 ^ 40 * 724993 * 2
def baseEnd_724993 : Nat := 330906560129055284669621

theorem tailTrace_724993 : CollatzResearch.WordTrace tailWord_724993 prefixEnd_724993 330906560129055284669621 := by
  unfold tailWord_724993
  simp only [CollatzResearch.WordTrace]
  refine ⟨26442667062481654791779633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17628444708321103194519755 26442667062481654791779633)
  ·
    refine ⟨19832000296861241093834725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26442667062481654791779633 19832000296861241093834725)
    ·
      refine ⟨3718500055661482705094011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19832000296861241093834725 3718500055661482705094011)
      ·
        refine ⟨5577750083492224057641017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3718500055661482705094011 5577750083492224057641017)
        ·
          refine ⟨4183312562619168043230763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5577750083492224057641017 4183312562619168043230763)
          ·
            refine ⟨6274968843928752064846145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4183312562619168043230763 6274968843928752064846145)
            ·
              refine ⟨4706226632946564048634609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6274968843928752064846145 4706226632946564048634609)
              ·
                refine ⟨3529669974709923036475957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4706226632946564048634609 3529669974709923036475957)
                ·
                  refine ⟨330906560129055284669621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3529669974709923036475957 330906560129055284669621)
                  ·
                    rfl

theorem cell20_724993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_724993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_724993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_724993 prefixEnd_724993 := by exact prefixLift 724993
  have htrace : WordTrace (prefixWord ++ tailWord_724993) baseStart_724993 baseEnd_724993 := by
    simpa [prefixWord, tailWord_724993, baseEnd_724993] using wordTrace_append hprefix tailTrace_724993
  have hstable : (prefixWord ++ tailWord_724993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_724993).length < 2 ^ (prefixWord ++ tailWord_724993).sum := by decide
  have hdescent : baseEnd_724993 < baseStart_724993 := by decide
  rcases family_descends (prefixWord ++ tailWord_724993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725000 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_725000 : Nat := 118140960795 + 725000 * 2 ^ 59
def prefixEnd_725000 : Nat := 4983230072969 + 3 ^ 40 * 725000 * 2
def baseEnd_725000 : Nat := 330909755119794371436259

theorem tailTrace_725000 : CollatzResearch.WordTrace tailWord_725000 prefixEnd_725000 330909755119794371436259 := by
  unfold tailWord_725000
  simp only [CollatzResearch.WordTrace]
  refine ⟨13221461186728147493642227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17628614915637529991522969 13221461186728147493642227)
  ·
    refine ⟨19832191780092221240463341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13221461186728147493642227 19832191780092221240463341)
    ·
      refine ⟨7437071917534582965173753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19832191780092221240463341 7437071917534582965173753)
      ·
        refine ⟨5577803938150937223880315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7437071917534582965173753 5577803938150937223880315)
        ·
          refine ⟨8366705907226405835820473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5577803938150937223880315 8366705907226405835820473)
          ·
            refine ⟨6275029430419804376865355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8366705907226405835820473 6275029430419804376865355)
            ·
              refine ⟨9412544145629706565298033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275029430419804376865355 9412544145629706565298033)
              ·
                refine ⟨7059408109222279923973525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9412544145629706565298033 7059408109222279923973525)
                ·
                  refine ⟨330909755119794371436259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7059408109222279923973525 330909755119794371436259)
                  ·
                    rfl

theorem cell20_725000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_725000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725000 prefixEnd_725000 := by exact prefixLift 725000
  have htrace : WordTrace (prefixWord ++ tailWord_725000) baseStart_725000 baseEnd_725000 := by
    simpa [prefixWord, tailWord_725000, baseEnd_725000] using wordTrace_append hprefix tailTrace_725000
  have hstable : (prefixWord ++ tailWord_725000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725000).length < 2 ^ (prefixWord ++ tailWord_725000).sum := by decide
  have hdescent : baseEnd_725000 < baseStart_725000 := by decide
  rcases family_descends (prefixWord ++ tailWord_725000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725041 : List Nat := [1, 2, 2, 3, 1, 5, 2, 4]
def baseStart_725041 : Nat := 118140960795 + 725041 * 2 ^ 59
def prefixEnd_725041 : Nat := 4983230072969 + 3 ^ 40 * 725041 * 2
def baseEnd_725041 : Nat := 110309489545660150356475

theorem tailTrace_725041 : CollatzResearch.WordTrace tailWord_725041 prefixEnd_725041 110309489545660150356475 := by
  unfold tailWord_725041
  simp only [CollatzResearch.WordTrace]
  refine ⟨26444417766307758989526977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17629611844205172659684651 26444417766307758989526977)
  ·
    refine ⟨19833313324730819242145233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26444417766307758989526977 19833313324730819242145233)
    ·
      refine ⟨14874984993548114431608925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19833313324730819242145233 14874984993548114431608925)
      ·
        refine ⟨5578119372580542911853347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14874984993548114431608925 5578119372580542911853347)
        ·
          refine ⟨8367179058870814367780021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5578119372580542911853347 8367179058870814367780021)
          ·
            refine ⟨784423036769138846979377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8367179058870814367780021 784423036769138846979377)
            ·
              refine ⟨588317277576854135234533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784423036769138846979377 588317277576854135234533)
              ·
                refine ⟨110309489545660150356475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588317277576854135234533 110309489545660150356475)
                ·
                  rfl

theorem cell20_725041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 4].length) (baseStart_725041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725041 prefixEnd_725041 := by exact prefixLift 725041
  have htrace : WordTrace (prefixWord ++ tailWord_725041) baseStart_725041 baseEnd_725041 := by
    simpa [prefixWord, tailWord_725041, baseEnd_725041] using wordTrace_append hprefix tailTrace_725041
  have hstable : (prefixWord ++ tailWord_725041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725041).length < 2 ^ (prefixWord ++ tailWord_725041).sum := by decide
  have hdescent : baseEnd_725041 < baseStart_725041 := by decide
  rcases family_descends (prefixWord ++ tailWord_725041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725121 : List Nat := [1, 2, 4, 2, 11]
def baseStart_725121 : Nat := 118140960795 + 725121 * 2 ^ 59
def prefixEnd_725121 : Nat := 4983230072969 + 3 ^ 40 * 725121 * 2
def baseEnd_725121 : Nat := 4085987442183404054351

theorem tailTrace_725121 : CollatzResearch.WordTrace tailWord_725121 prefixEnd_725121 4085987442183404054351 := by
  unfold tailWord_725121
  simp only [CollatzResearch.WordTrace]
  refine ⟨26447335606017932652439217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17631557070678621768292811 26447335606017932652439217)
  ·
    refine ⟨19835501704513449489329413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26447335606017932652439217 19835501704513449489329413)
    ·
      refine ⟨3719156569596271779249265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19835501704513449489329413 3719156569596271779249265)
      ·
        refine ⟨2789367427197203834436949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3719156569596271779249265 2789367427197203834436949)
        ·
          refine ⟨4085987442183404054351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2789367427197203834436949 4085987442183404054351)
          ·
            rfl

theorem cell20_725121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 11].length) (baseStart_725121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725121 prefixEnd_725121 := by exact prefixLift 725121
  have htrace : WordTrace (prefixWord ++ tailWord_725121) baseStart_725121 baseEnd_725121 := by
    simpa [prefixWord, tailWord_725121, baseEnd_725121] using wordTrace_append hprefix tailTrace_725121
  have hstable : (prefixWord ++ tailWord_725121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725121).length < 2 ^ (prefixWord ++ tailWord_725121).sum := by decide
  have hdescent : baseEnd_725121 < baseStart_725121 := by decide
  rcases family_descends (prefixWord ++ tailWord_725121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725124 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_725124 : Nat := 118140960795 + 725124 * 2 ^ 59
def prefixEnd_725124 : Nat := 4983230072969 + 3 ^ 40 * 725124 * 2
def baseEnd_725124 : Nat := 330966352098601051302419

theorem tailTrace_725124 : CollatzResearch.WordTrace tailWord_725124 prefixEnd_725124 330966352098601051302419 := by
  unfold tailWord_725124
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223722512503532082399213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17631630016671376109865617 13223722512503532082399213)
  ·
    refine ⟨4958895942188824530899705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13223722512503532082399213 4958895942188824530899705)
    ·
      refine ⟨3719171956641618398174779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4958895942188824530899705 3719171956641618398174779)
      ·
        refine ⟨5578757934962427597262169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719171956641618398174779 5578757934962427597262169)
        ·
          refine ⟨4184068451221820697946627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5578757934962427597262169 4184068451221820697946627)
          ·
            refine ⟨6276102676832731046919941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4184068451221820697946627 6276102676832731046919941)
            ·
              refine ⟨1176769251906137071297489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6276102676832731046919941 1176769251906137071297489)
              ·
                refine ⟨882576938929602803473117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176769251906137071297489 882576938929602803473117)
                ·
                  refine ⟨330966352098601051302419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882576938929602803473117 330966352098601051302419)
                  ·
                    rfl

theorem cell20_725124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_725124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725124 prefixEnd_725124 := by exact prefixLift 725124
  have htrace : WordTrace (prefixWord ++ tailWord_725124) baseStart_725124 baseEnd_725124 := by
    simpa [prefixWord, tailWord_725124, baseEnd_725124] using wordTrace_append hprefix tailTrace_725124
  have hstable : (prefixWord ++ tailWord_725124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725124).length < 2 ^ (prefixWord ++ tailWord_725124).sum := by decide
  have hdescent : baseEnd_725124 < baseStart_725124 := by decide
  rcases family_descends (prefixWord ++ tailWord_725124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725134 : List Nat := [4, 1, 1, 3, 4, 1, 1, 5]
def baseStart_725134 : Nat := 118140960795 + 725134 * 2 ^ 59
def prefixEnd_725134 : Nat := 4983230072969 + 3 ^ 40 * 725134 * 2
def baseEnd_725134 : Nat := 110323638790361820323015

theorem tailTrace_725134 : CollatzResearch.WordTrace tailWord_725134 prefixEnd_725134 110323638790361820323015 := by
  unfold tailWord_725134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3305976219371354484082807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17631873169980557248441637 3305976219371354484082807)
  ·
    refine ⟨4958964329057031726124211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3305976219371354484082807 4958964329057031726124211)
    ·
      refine ⟨7438446493585547589186317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4958964329057031726124211 7438446493585547589186317)
      ·
        refine ⟨2789417435094580345944869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7438446493585547589186317 2789417435094580345944869)
        ·
          refine ⟨523015769080233814864663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2789417435094580345944869 523015769080233814864663)
          ·
            refine ⟨784523653620350722296995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523015769080233814864663 784523653620350722296995)
            ·
              refine ⟨1176785480430526083445493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784523653620350722296995 1176785480430526083445493)
              ·
                refine ⟨110323638790361820323015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1176785480430526083445493 110323638790361820323015)
                ·
                  rfl

theorem cell20_725134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_725134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725134 prefixEnd_725134 := by exact prefixLift 725134
  have htrace : WordTrace (prefixWord ++ tailWord_725134) baseStart_725134 baseEnd_725134 := by
    simpa [prefixWord, tailWord_725134, baseEnd_725134] using wordTrace_append hprefix tailTrace_725134
  have hstable : (prefixWord ++ tailWord_725134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725134).length < 2 ^ (prefixWord ++ tailWord_725134).sum := by decide
  have hdescent : baseEnd_725134 < baseStart_725134 := by decide
  rcases family_descends (prefixWord ++ tailWord_725134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725152 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_725152 : Nat := 118140960795 + 725152 * 2 ^ 59
def prefixEnd_725152 : Nat := 4983230072969 + 3 ^ 40 * 725152 * 2
def baseEnd_725152 : Nat := 330979132061557398368971

theorem tailTrace_725152 : CollatzResearch.WordTrace tailWord_725152 prefixEnd_725152 330979132061557398368971 := by
  unfold tailWord_725152
  simp only [CollatzResearch.WordTrace]
  refine ⟨13224233134452812473408855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17632310845937083297878473 13224233134452812473408855)
  ·
    refine ⟨19836349701679218710113283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13224233134452812473408855 19836349701679218710113283)
    ·
      refine ⟨29754524552518828065169925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19836349701679218710113283 29754524552518828065169925)
      ·
        refine ⟨5578973353597280262219361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29754524552518828065169925 5578973353597280262219361)
        ·
          refine ⟨4184230015197960196664521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5578973353597280262219361 4184230015197960196664521)
          ·
            refine ⟨3138172511398470147498391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4184230015197960196664521 3138172511398470147498391)
            ·
              refine ⟨4707258767097705221247587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138172511398470147498391 4707258767097705221247587)
              ·
                refine ⟨7060888150646557831871381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4707258767097705221247587 7060888150646557831871381)
                ·
                  refine ⟨330979132061557398368971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7060888150646557831871381 330979132061557398368971)
                  ·
                    rfl

theorem cell20_725152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_725152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725152 prefixEnd_725152 := by exact prefixLift 725152
  have htrace : WordTrace (prefixWord ++ tailWord_725152) baseStart_725152 baseEnd_725152 := by
    simpa [prefixWord, tailWord_725152, baseEnd_725152] using wordTrace_append hprefix tailTrace_725152
  have hstable : (prefixWord ++ tailWord_725152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725152).length < 2 ^ (prefixWord ++ tailWord_725152).sum := by decide
  have hdescent : baseEnd_725152 < baseStart_725152 := by decide
  rcases family_descends (prefixWord ++ tailWord_725152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725165 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 2]
def baseStart_725165 : Nat := 118140960795 + 725165 * 2 ^ 59
def prefixEnd_725165 : Nat := 4983230072969 + 3 ^ 40 * 725165 * 2
def baseEnd_725165 : Nat := 330985065615787130935585

theorem tailTrace_725165 : CollatzResearch.WordTrace tailWord_725165 prefixEnd_725165 330985065615787130935585 := by
  unfold tailWord_725165
  simp only [CollatzResearch.WordTrace]
  refine ⟨26448940417858528167040949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17632626945239018778027299 26448940417858528167040949)
  ·
    refine ⟨2479588164174237015660089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26448940417858528167040949 2479588164174237015660089)
    ·
      refine ⟨1859691123130677761745067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2479588164174237015660089 1859691123130677761745067)
      ·
        refine ⟨2789536684696016642617601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859691123130677761745067 2789536684696016642617601)
        ·
          refine ⟨2092152513522012481963201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2789536684696016642617601 2092152513522012481963201)
          ·
            refine ⟨1569114385141509361472401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092152513522012481963201 1569114385141509361472401)
            ·
              refine ⟨1176835788856132021104301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569114385141509361472401 1176835788856132021104301)
              ·
                refine ⟨441313420821049507914113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176835788856132021104301 441313420821049507914113)
                ·
                  refine ⟨330985065615787130935585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441313420821049507914113 330985065615787130935585)
                  ·
                    rfl

theorem cell20_725165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_725165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725165 prefixEnd_725165 := by exact prefixLift 725165
  have htrace : WordTrace (prefixWord ++ tailWord_725165) baseStart_725165 baseEnd_725165 := by
    simpa [prefixWord, tailWord_725165, baseEnd_725165] using wordTrace_append hprefix tailTrace_725165
  have hstable : (prefixWord ++ tailWord_725165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725165).length < 2 ^ (prefixWord ++ tailWord_725165).sum := by decide
  have hdescent : baseEnd_725165 < baseStart_725165 := by decide
  rcases family_descends (prefixWord ++ tailWord_725165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725196 : List Nat := [2, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_725196 : Nat := 118140960795 + 725196 * 2 ^ 59
def prefixEnd_725196 : Nat := 4983230072969 + 3 ^ 40 * 725196 * 2
def baseEnd_725196 : Nat := 330999214860488800902125

theorem tailTrace_725196 : CollatzResearch.WordTrace tailWord_725196 prefixEnd_725196 330999214860488800902125 := by
  unfold tailWord_725196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13225035540373110230709721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17633380720497480307612961 13225035540373110230709721)
  ·
    refine ⟨9918776655279832673032291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13225035540373110230709721 9918776655279832673032291)
    ·
      refine ⟨14878164982919749009548437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9918776655279832673032291 14878164982919749009548437)
      ·
        refine ⟨697413983574363234822583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14878164982919749009548437 697413983574363234822583)
        ·
          refine ⟨1046120975361544852233875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697413983574363234822583 1046120975361544852233875)
          ·
            refine ⟨1569181463042317278350813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046120975361544852233875 1569181463042317278350813)
            ·
              refine ⟨588443048640868979381555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569181463042317278350813 588443048640868979381555)
              ·
                refine ⟨882664572961303469072333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588443048640868979381555 882664572961303469072333)
                ·
                  refine ⟨330999214860488800902125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882664572961303469072333 330999214860488800902125)
                  ·
                    rfl

theorem cell20_725196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_725196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725196 prefixEnd_725196 := by exact prefixLift 725196
  have htrace : WordTrace (prefixWord ++ tailWord_725196) baseStart_725196 baseEnd_725196 := by
    simpa [prefixWord, tailWord_725196, baseEnd_725196] using wordTrace_append hprefix tailTrace_725196
  have hstable : (prefixWord ++ tailWord_725196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725196).length < 2 ^ (prefixWord ++ tailWord_725196).sum := by decide
  have hdescent : baseEnd_725196 < baseStart_725196 := by decide
  rcases family_descends (prefixWord ++ tailWord_725196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725221 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 5]
def baseStart_725221 : Nat := 118140960795 + 725221 * 2 ^ 59
def prefixEnd_725221 : Nat := 4983230072969 + 3 ^ 40 * 725221 * 2
def baseEnd_725221 : Nat := 331010625541699825068689

theorem tailTrace_725221 : CollatzResearch.WordTrace tailWord_725221 prefixEnd_725221 331010625541699825068689 := by
  unfold tailWord_725221
  simp only [CollatzResearch.WordTrace]
  refine ⟨26450982905655649731079517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17633988603770433154053011 26450982905655649731079517)
  ·
    refine ⟨9919118589620868649154819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26450982905655649731079517 9919118589620868649154819)
    ·
      refine ⟨14878677884431302973732229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9919118589620868649154819 14878677884431302973732229)
      ·
        refine ⟨2789752103330869307574793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14878677884431302973732229 2789752103330869307574793)
        ·
          refine ⟨2092314077498151980681095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2789752103330869307574793 2092314077498151980681095)
          ·
            refine ⟨3138471116247227971021643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092314077498151980681095 3138471116247227971021643)
            ·
              refine ⟨4707706674370841956532465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138471116247227971021643 4707706674370841956532465)
              ·
                refine ⟨3530780005778131467399349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4707706674370841956532465 3530780005778131467399349)
                ·
                  refine ⟨331010625541699825068689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3530780005778131467399349 331010625541699825068689)
                  ·
                    rfl

theorem cell20_725221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_725221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725221 prefixEnd_725221 := by exact prefixLift 725221
  have htrace : WordTrace (prefixWord ++ tailWord_725221) baseStart_725221 baseEnd_725221 := by
    simpa [prefixWord, tailWord_725221, baseEnd_725221] using wordTrace_append hprefix tailTrace_725221
  have hstable : (prefixWord ++ tailWord_725221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725221).length < 2 ^ (prefixWord ++ tailWord_725221).sum := by decide
  have hdescent : baseEnd_725221 < baseStart_725221 := by decide
  rcases family_descends (prefixWord ++ tailWord_725221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725224 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 2]
def baseStart_725224 : Nat := 118140960795 + 725224 * 2 ^ 59
def prefixEnd_725224 : Nat := 4983230072969 + 3 ^ 40 * 725224 * 2
def baseEnd_725224 : Nat := 331011994823445147968677

theorem tailTrace_725224 : CollatzResearch.WordTrace tailWord_725224 prefixEnd_725224 331011994823445147968677 := by
  unfold tailWord_725224
  simp only [CollatzResearch.WordTrace]
  refine ⟨13225546162322390621719363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17634061549763187495625817 13225546162322390621719363)
  ·
    refine ⟨19838319243483585932579045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13225546162322390621719363 19838319243483585932579045)
    ·
      refine ⟨3719684858153172362358571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19838319243483585932579045 3719684858153172362358571)
      ·
        refine ⟨5579527287229758543537857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3719684858153172362358571 5579527287229758543537857)
        ·
          refine ⟨4184645465422318907653393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5579527287229758543537857 4184645465422318907653393)
          ·
            refine ⟨3138484099066739180740045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4184645465422318907653393 3138484099066739180740045)
            ·
              refine ⟨1176931537150027192777517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3138484099066739180740045 1176931537150027192777517)
              ·
                refine ⟨441349326431260197291569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176931537150027192777517 441349326431260197291569)
                ·
                  refine ⟨331011994823445147968677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441349326431260197291569 331011994823445147968677)
                  ·
                    rfl

theorem cell20_725224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_725224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725224 prefixEnd_725224 := by exact prefixLift 725224
  have htrace : WordTrace (prefixWord ++ tailWord_725224) baseStart_725224 baseEnd_725224 := by
    simpa [prefixWord, tailWord_725224, baseEnd_725224] using wordTrace_append hprefix tailTrace_725224
  have hstable : (prefixWord ++ tailWord_725224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725224).length < 2 ^ (prefixWord ++ tailWord_725224).sum := by decide
  have hdescent : baseEnd_725224 < baseStart_725224 := by decide
  rcases family_descends (prefixWord ++ tailWord_725224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725245 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 2]
def baseStart_725245 : Nat := 118140960795 + 725245 * 2 ^ 59
def prefixEnd_725245 : Nat := 4983230072969 + 3 ^ 40 * 725245 * 2
def baseEnd_725245 : Nat := 331021579795662408268591

theorem tailTrace_725245 : CollatzResearch.WordTrace tailWord_725245 prefixEnd_725245 331021579795662408268591 := by
  unfold tailWord_725245
  simp only [CollatzResearch.WordTrace]
  refine ⟨26451858257568701829953189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17634572171712467886635459 26451858257568701829953189)
  ·
    refine ⟨4959723423294131593116223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26451858257568701829953189 4959723423294131593116223)
    ·
      refine ⟨7439585134941197389674335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959723423294131593116223 7439585134941197389674335)
      ·
        refine ⟨11159377702411796084511503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7439585134941197389674335 11159377702411796084511503)
        ·
          refine ⟨16739066553617694126767255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11159377702411796084511503 16739066553617694126767255)
          ·
            refine ⟨25108599830426541190150883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16739066553617694126767255 25108599830426541190150883)
            ·
              refine ⟨37662899745639811785226325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25108599830426541190150883 37662899745639811785226325)
              ·
                refine ⟨441362106394216544358121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 37662899745639811785226325 441362106394216544358121)
                ·
                  refine ⟨331021579795662408268591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441362106394216544358121 331021579795662408268591)
                  ·
                    rfl

theorem cell20_725245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_725245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725245 prefixEnd_725245 := by exact prefixLift 725245
  have htrace : WordTrace (prefixWord ++ tailWord_725245) baseStart_725245 baseEnd_725245 := by
    simpa [prefixWord, tailWord_725245, baseEnd_725245] using wordTrace_append hprefix tailTrace_725245
  have hstable : (prefixWord ++ tailWord_725245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725245).length < 2 ^ (prefixWord ++ tailWord_725245).sum := by decide
  have hdescent : baseEnd_725245 < baseStart_725245 := by decide
  rcases family_descends (prefixWord ++ tailWord_725245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725255 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 3]
def baseStart_725255 : Nat := 118140960795 + 725255 * 2 ^ 59
def prefixEnd_725255 : Nat := 4983230072969 + 3 ^ 40 * 725255 * 2
def baseEnd_725255 : Nat := 331026144068146817935217

theorem tailTrace_725255 : CollatzResearch.WordTrace tailWord_725255 prefixEnd_725255 331026144068146817935217 := by
  unfold tailWord_725255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26452222987532473537817219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17634815325021649025211479 26452222987532473537817219)
  ·
    refine ⟨39678334481298710306725829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26452222987532473537817219 39678334481298710306725829)
    ·
      refine ⟨7439687715243508182511093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39678334481298710306725829 7439687715243508182511093)
      ·
        refine ⟨697470723304078892110415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7439687715243508182511093 697470723304078892110415)
        ·
          refine ⟨1046206084956118338165623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697470723304078892110415 1046206084956118338165623)
          ·
            refine ⟨1569309127434177507248435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046206084956118338165623 1569309127434177507248435)
            ·
              refine ⟨2353963691151266260872653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569309127434177507248435 2353963691151266260872653)
              ·
                refine ⟨882736384181724847827245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2353963691151266260872653 882736384181724847827245)
                ·
                  refine ⟨331026144068146817935217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882736384181724847827245 331026144068146817935217)
                  ·
                    rfl

theorem cell20_725255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 3].length) (baseStart_725255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725255 prefixEnd_725255 := by exact prefixLift 725255
  have htrace : WordTrace (prefixWord ++ tailWord_725255) baseStart_725255 baseEnd_725255 := by
    simpa [prefixWord, tailWord_725255, baseEnd_725255] using wordTrace_append hprefix tailTrace_725255
  have hstable : (prefixWord ++ tailWord_725255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725255).length < 2 ^ (prefixWord ++ tailWord_725255).sum := by decide
  have hdescent : baseEnd_725255 < baseStart_725255 := by decide
  rcases family_descends (prefixWord ++ tailWord_725255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725259 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_725259 : Nat := 118140960795 + 725259 * 2 ^ 59
def prefixEnd_725259 : Nat := 4983230072969 + 3 ^ 40 * 725259 * 2
def baseEnd_725259 : Nat := 331027969777140581801867

theorem tailTrace_725259 : CollatzResearch.WordTrace tailWord_725259 prefixEnd_725259 331027969777140581801867 := by
  unfold tailWord_725259
  simp only [CollatzResearch.WordTrace]
  refine ⟨26452368879517982220962831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17634912586345321480641887 26452368879517982220962831)
  ·
    refine ⟨39678553319276973331444247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26452368879517982220962831 39678553319276973331444247)
    ·
      refine ⟨59517829978915459997166371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39678553319276973331444247 59517829978915459997166371)
      ·
        refine ⟨89276744968373189995749557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59517829978915459997166371 89276744968373189995749557)
        ·
          refine ⟨8369694840784986562101521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89276744968373189995749557 8369694840784986562101521)
          ·
            refine ⟨6277271130588739921576141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8369694840784986562101521 6277271130588739921576141)
            ·
              refine ⟨2353976673970777470591053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6277271130588739921576141 2353976673970777470591053)
              ·
                refine ⟨882741252739041551471645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2353976673970777470591053 882741252739041551471645)
                ·
                  refine ⟨331027969777140581801867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882741252739041551471645 331027969777140581801867)
                  ·
                    rfl

theorem cell20_725259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_725259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725259 prefixEnd_725259 := by exact prefixLift 725259
  have htrace : WordTrace (prefixWord ++ tailWord_725259) baseStart_725259 baseEnd_725259 := by
    simpa [prefixWord, tailWord_725259, baseEnd_725259] using wordTrace_append hprefix tailTrace_725259
  have hstable : (prefixWord ++ tailWord_725259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725259).length < 2 ^ (prefixWord ++ tailWord_725259).sum := by decide
  have hdescent : baseEnd_725259 < baseStart_725259 := by decide
  rcases family_descends (prefixWord ++ tailWord_725259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725283 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 2]
def baseStart_725283 : Nat := 118140960795 + 725283 * 2 ^ 59
def prefixEnd_725283 : Nat := 4983230072969 + 3 ^ 40 * 725283 * 2
def baseEnd_725283 : Nat := 331038924031103165001769

theorem tailTrace_725283 : CollatzResearch.WordTrace tailWord_725283 prefixEnd_725283 331038924031103165001769 := by
  unfold tailWord_725283
  simp only [CollatzResearch.WordTrace]
  refine ⟨26453244231431034319836503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17635496154287356213224335 26453244231431034319836503)
  ·
    refine ⟨39679866347146551479754755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26453244231431034319836503 39679866347146551479754755)
    ·
      refine ⟨59519799520719827219632133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39679866347146551479754755 59519799520719827219632133)
      ·
        refine ⟨11159962410134967603681025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59519799520719827219632133 11159962410134967603681025)
        ·
          refine ⟨8369971807601225702760769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11159962410134967603681025 8369971807601225702760769)
          ·
            refine ⟨6277478855700919277070577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8369971807601225702760769 6277478855700919277070577)
            ·
              refine ⟨4708109141775689457802933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6277478855700919277070577 4708109141775689457802933)
              ·
                refine ⟨441385232041470886669025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4708109141775689457802933 441385232041470886669025)
                ·
                  refine ⟨331038924031103165001769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441385232041470886669025 331038924031103165001769)
                  ·
                    rfl

theorem cell20_725283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 2].length) (baseStart_725283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725283 prefixEnd_725283 := by exact prefixLift 725283
  have htrace : WordTrace (prefixWord ++ tailWord_725283) baseStart_725283 baseEnd_725283 := by
    simpa [prefixWord, tailWord_725283, baseEnd_725283] using wordTrace_append hprefix tailTrace_725283
  have hstable : (prefixWord ++ tailWord_725283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725283).length < 2 ^ (prefixWord ++ tailWord_725283).sum := by decide
  have hdescent : baseEnd_725283 < baseStart_725283 := by decide
  rcases family_descends (prefixWord ++ tailWord_725283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725290 : List Nat := [3, 1, 4, 2, 2, 8]
def baseStart_725290 : Nat := 118140960795 + 725290 * 2 ^ 59
def prefixEnd_725290 : Nat := 4983230072969 + 3 ^ 40 * 725290 * 2
def baseEnd_725290 : Nat := 12260819223031194509941

theorem tailTrace_725290 : CollatzResearch.WordTrace tailWord_725290 prefixEnd_725290 12260819223031194509941 := by
  unfold tailWord_725290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613374885601418628835331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17635666361603783010227549 6613374885601418628835331)
  ·
    refine ⟨9920062328402127943252997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6613374885601418628835331 9920062328402127943252997)
    ·
      refine ⟨1860011686575398989359937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9920062328402127943252997 1860011686575398989359937)
      ·
        refine ⟨1395008764931549242019953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860011686575398989359937 1395008764931549242019953)
        ·
          refine ⟨1046256573698661931514965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395008764931549242019953 1046256573698661931514965)
          ·
            refine ⟨12260819223031194509941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1046256573698661931514965 12260819223031194509941)
            ·
              rfl

theorem cell20_725290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 8].length) (baseStart_725290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725290 prefixEnd_725290 := by exact prefixLift 725290
  have htrace : WordTrace (prefixWord ++ tailWord_725290) baseStart_725290 baseEnd_725290 := by
    simpa [prefixWord, tailWord_725290, baseEnd_725290] using wordTrace_append hprefix tailTrace_725290
  have hstable : (prefixWord ++ tailWord_725290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725290).length < 2 ^ (prefixWord ++ tailWord_725290).sum := by decide
  have hdescent : baseEnd_725290 < baseStart_725290 := by decide
  rcases family_descends (prefixWord ++ tailWord_725290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725328 : List Nat := [2, 1, 1, 1, 1, 7, 3, 4]
def baseStart_725328 : Nat := 118140960795 + 725328 * 2 ^ 59
def prefixEnd_725328 : Nat := 4983230072969 + 3 ^ 40 * 725328 * 2
def baseEnd_725328 : Nat := 110353154419094336167195

theorem tailTrace_725328 : CollatzResearch.WordTrace tailWord_725328 prefixEnd_725328 110353154419094336167195 := by
  unfold tailWord_725328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227442758134003502612319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17636590344178671336816425 13227442758134003502612319)
  ·
    refine ⟨19841164137201005253918479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13227442758134003502612319 19841164137201005253918479)
    ·
      refine ⟨29761746205801507880877719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19841164137201005253918479 29761746205801507880877719)
      ·
        refine ⟨44642619308702261821316579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29761746205801507880877719 44642619308702261821316579)
        ·
          refine ⟨66963928963053392731974869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44642619308702261821316579 66963928963053392731974869)
          ·
            refine ⟨1569467085071563892155661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66963928963053392731974869 1569467085071563892155661)
            ·
              refine ⟨588550156901836459558373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1569467085071563892155661 588550156901836459558373)
              ·
                refine ⟨110353154419094336167195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 588550156901836459558373 110353154419094336167195)
                ·
                  rfl

theorem cell20_725328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_725328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725328 prefixEnd_725328 := by exact prefixLift 725328
  have htrace : WordTrace (prefixWord ++ tailWord_725328) baseStart_725328 baseEnd_725328 := by
    simpa [prefixWord, tailWord_725328, baseEnd_725328] using wordTrace_append hprefix tailTrace_725328
  have hstable : (prefixWord ++ tailWord_725328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725328).length < 2 ^ (prefixWord ++ tailWord_725328).sum := by decide
  have hdescent : baseEnd_725328 < baseStart_725328 := by decide
  rcases family_descends (prefixWord ++ tailWord_725328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725349 : List Nat := [1, 3, 1, 3, 1, 4, 7]
def baseStart_725349 : Nat := 118140960795 + 725349 * 2 ^ 59
def prefixEnd_725349 : Nat := 4983230072969 + 3 ^ 40 * 725349 * 2
def baseEnd_725349 : Nat := 36785449803277807644611

theorem tailTrace_725349 : CollatzResearch.WordTrace tailWord_725349 prefixEnd_725349 36785449803277807644611 := by
  unfold tailWord_725349
  simp only [CollatzResearch.WordTrace]
  refine ⟨26455651449191927591739101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17637100966127951727826067 26455651449191927591739101)
  ·
    refine ⟨9920869293446972846902163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26455651449191927591739101 9920869293446972846902163)
    ·
      refine ⟨14881303940170459270353245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9920869293446972846902163 14881303940170459270353245)
      ·
        refine ⟨5580488977563922226382467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14881303940170459270353245 5580488977563922226382467)
        ·
          refine ⟨8370733466345883339573701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580488977563922226382467 8370733466345883339573701)
          ·
            refine ⟨1569512524939853126170069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8370733466345883339573701 1569512524939853126170069)
            ·
              refine ⟨36785449803277807644611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1569512524939853126170069 36785449803277807644611)
              ·
                rfl

theorem cell20_725349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 7].length) (baseStart_725349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725349 prefixEnd_725349 := by exact prefixLift 725349
  have htrace : WordTrace (prefixWord ++ tailWord_725349) baseStart_725349 baseEnd_725349 := by
    simpa [prefixWord, tailWord_725349, baseEnd_725349] using wordTrace_append hprefix tailTrace_725349
  have hstable : (prefixWord ++ tailWord_725349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725349).length < 2 ^ (prefixWord ++ tailWord_725349).sum := by decide
  have hdescent : baseEnd_725349 < baseStart_725349 := by decide
  rcases family_descends (prefixWord ++ tailWord_725349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725352 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_725352 : Nat := 118140960795 + 725352 * 2 ^ 59
def prefixEnd_725352 : Nat := 4983230072969 + 3 ^ 40 * 725352 * 2
def baseEnd_725352 : Nat := 331070417511245591701487

theorem tailTrace_725352 : CollatzResearch.WordTrace tailWord_725352 prefixEnd_725352 331070417511245591701487 := by
  unfold tailWord_725352
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227880434090529552049155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17637173912120706069398873 13227880434090529552049155)
  ·
    refine ⟨19841820651135794328073733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13227880434090529552049155 19841820651135794328073733)
    ·
      refine ⟨3720341372087961436513825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19841820651135794328073733 3720341372087961436513825)
      ·
        refine ⟨2790256029065971077385369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3720341372087961436513825 2790256029065971077385369)
        ·
          refine ⟨2092692021799478308039027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2790256029065971077385369 2092692021799478308039027)
          ·
            refine ⟨3139038032699217462058541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092692021799478308039027 3139038032699217462058541)
            ·
              refine ⟨1177139262262206548271953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3139038032699217462058541 1177139262262206548271953)
              ·
                refine ⟨882854446696654911203965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177139262262206548271953 882854446696654911203965)
                ·
                  refine ⟨331070417511245591701487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882854446696654911203965 331070417511245591701487)
                  ·
                    rfl

theorem cell20_725352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_725352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725352 prefixEnd_725352 := by exact prefixLift 725352
  have htrace : WordTrace (prefixWord ++ tailWord_725352) baseStart_725352 baseEnd_725352 := by
    simpa [prefixWord, tailWord_725352, baseEnd_725352] using wordTrace_append hprefix tailTrace_725352
  have hstable : (prefixWord ++ tailWord_725352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725352).length < 2 ^ (prefixWord ++ tailWord_725352).sum := by decide
  have hdescent : baseEnd_725352 < baseStart_725352 := by decide
  rcases family_descends (prefixWord ++ tailWord_725352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725363 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_725363 : Nat := 118140960795 + 725363 * 2 ^ 59
def prefixEnd_725363 : Nat := 4983230072969 + 3 ^ 40 * 725363 * 2
def baseEnd_725363 : Nat := 331075438210978442334775

theorem tailTrace_725363 : CollatzResearch.WordTrace tailWord_725363 prefixEnd_725363 331075438210978442334775 := by
  unfold tailWord_725363
  simp only [CollatzResearch.WordTrace]
  refine ⟨26456162071141207982748743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17637441380760805321832495 26456162071141207982748743)
  ·
    refine ⟨39684243106711811974123115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26456162071141207982748743 39684243106711811974123115)
    ·
      refine ⟨59526364660067717961184673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39684243106711811974123115 59526364660067717961184673)
      ·
        refine ⟨44644773495050788470888505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59526364660067717961184673 44644773495050788470888505)
        ·
          refine ⟨33483580121288091353166379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44644773495050788470888505 33483580121288091353166379)
          ·
            refine ⟨50225370181932137029749569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33483580121288091353166379 50225370181932137029749569)
            ·
              refine ⟨37669027636449102772312177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50225370181932137029749569 37669027636449102772312177)
              ·
                refine ⟨28251770727336827079234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37669027636449102772312177 28251770727336827079234133)
                ·
                  refine ⟨331075438210978442334775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28251770727336827079234133 331075438210978442334775)
                  ·
                    rfl

theorem cell20_725363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_725363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725363 prefixEnd_725363 := by exact prefixLift 725363
  have htrace : WordTrace (prefixWord ++ tailWord_725363) baseStart_725363 baseEnd_725363 := by
    simpa [prefixWord, tailWord_725363, baseEnd_725363] using wordTrace_append hprefix tailTrace_725363
  have hstable : (prefixWord ++ tailWord_725363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725363).length < 2 ^ (prefixWord ++ tailWord_725363).sum := by decide
  have hdescent : baseEnd_725363 < baseStart_725363 := by decide
  rcases family_descends (prefixWord ++ tailWord_725363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725380 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_725380 : Nat := 118140960795 + 725380 * 2 ^ 59
def prefixEnd_725380 : Nat := 4983230072969 + 3 ^ 40 * 725380 * 2
def baseEnd_725380 : Nat := 331083197474201938768039

theorem tailTrace_725380 : CollatzResearch.WordTrace tailWord_725380 prefixEnd_725380 331083197474201938768039 := by
  unfold tailWord_725380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13228391056039809943058797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17637854741386413257411729 13228391056039809943058797)
  ·
    refine ⟨4960646646014928728647049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13228391056039809943058797 4960646646014928728647049)
    ·
      refine ⟨3720484984511196546485287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4960646646014928728647049 3720484984511196546485287)
      ·
        refine ⟨5580727476766794819727931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720484984511196546485287 5580727476766794819727931)
        ·
          refine ⟨8371091215150192229591897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5580727476766794819727931 8371091215150192229591897)
          ·
            refine ⟨6278318411362644172193923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8371091215150192229591897 6278318411362644172193923)
            ·
              refine ⟨9417477617043966258290885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6278318411362644172193923 9417477617043966258290885)
              ·
                refine ⟨1765777053195743673429541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9417477617043966258290885 1765777053195743673429541)
                ·
                  refine ⟨331083197474201938768039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765777053195743673429541 331083197474201938768039)
                  ·
                    rfl

theorem cell20_725380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_725380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725380 prefixEnd_725380 := by exact prefixLift 725380
  have htrace : WordTrace (prefixWord ++ tailWord_725380) baseStart_725380 baseEnd_725380 := by
    simpa [prefixWord, tailWord_725380, baseEnd_725380] using wordTrace_append hprefix tailTrace_725380
  have hstable : (prefixWord ++ tailWord_725380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725380).length < 2 ^ (prefixWord ++ tailWord_725380).sum := by decide
  have hdescent : baseEnd_725380 < baseStart_725380 := by decide
  rcases family_descends (prefixWord ++ tailWord_725380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725387 : List Nat := [1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_725387 : Nat := 118140960795 + 725387 * 2 ^ 59
def prefixEnd_725387 : Nat := 4983230072969 + 3 ^ 40 * 725387 * 2
def baseEnd_725387 : Nat := 110362130821647008511559

theorem tailTrace_725387 : CollatzResearch.WordTrace tailWord_725387 prefixEnd_725387 110362130821647008511559 := by
  unfold tailWord_725387
  simp only [CollatzResearch.WordTrace]
  refine ⟨26457037423054260081622415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17638024948702840054414943 26457037423054260081622415)
  ·
    refine ⟨39685556134581390122433623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26457037423054260081622415 39685556134581390122433623)
    ·
      refine ⟨59528334201872085183650435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39685556134581390122433623 59528334201872085183650435)
      ·
        refine ⟨89292501302808127775475653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59528334201872085183650435 89292501302808127775475653)
        ·
          refine ⟨16742343994276523957901685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89292501302808127775475653 16742343994276523957901685)
          ·
            refine ⟨1569594749463424121053283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16742343994276523957901685 1569594749463424121053283)
            ·
              refine ⟨2354392124195136181579925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569594749463424121053283 2354392124195136181579925)
              ·
                refine ⟨110362130821647008511559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2354392124195136181579925 110362130821647008511559)
                ·
                  rfl

theorem cell20_725387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_725387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725387 prefixEnd_725387 := by exact prefixLift 725387
  have htrace : WordTrace (prefixWord ++ tailWord_725387) baseStart_725387 baseEnd_725387 := by
    simpa [prefixWord, tailWord_725387, baseEnd_725387] using wordTrace_append hprefix tailTrace_725387
  have hstable : (prefixWord ++ tailWord_725387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725387).length < 2 ^ (prefixWord ++ tailWord_725387).sum := by decide
  have hdescent : baseEnd_725387 < baseStart_725387 := by decide
  rcases family_descends (prefixWord ++ tailWord_725387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725421 : List Nat := [1, 5, 2, 2, 2, 1, 2, 5]
def baseStart_725421 : Nat := 118140960795 + 725421 * 2 ^ 59
def prefixEnd_725421 : Nat := 4983230072969 + 3 ^ 40 * 725421 * 2
def baseEnd_725421 : Nat := 110367303663796006133735

theorem tailTrace_725421 : CollatzResearch.WordTrace tailWord_725421 prefixEnd_725421 110367303663796006133735 := by
  unfold tailWord_725421
  simp only [CollatzResearch.WordTrace]
  refine ⟨26458277504931083888360117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17638851669954055925573411 26458277504931083888360117)
  ·
    refine ⟨2480463516087289114533761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26458277504931083888360117 2480463516087289114533761)
    ·
      refine ⟨1860347637065466835900321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2480463516087289114533761 1860347637065466835900321)
      ·
        refine ⟨1395260727799100126925241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860347637065466835900321 1395260727799100126925241)
        ·
          refine ⟨1046445545849325095193931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395260727799100126925241 1046445545849325095193931)
          ·
            refine ⟨1569668318773987642790897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046445545849325095193931 1569668318773987642790897)
            ·
              refine ⟨1177251239080490732093173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569668318773987642790897 1177251239080490732093173)
              ·
                refine ⟨110367303663796006133735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1177251239080490732093173 110367303663796006133735)
                ·
                  rfl

theorem cell20_725421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_725421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725421 prefixEnd_725421 := by exact prefixLift 725421
  have htrace : WordTrace (prefixWord ++ tailWord_725421) baseStart_725421 baseEnd_725421 := by
    simpa [prefixWord, tailWord_725421, baseEnd_725421] using wordTrace_append hprefix tailTrace_725421
  have hstable : (prefixWord ++ tailWord_725421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725421).length < 2 ^ (prefixWord ++ tailWord_725421).sum := by decide
  have hdescent : baseEnd_725421 < baseStart_725421 := by decide
  rcases family_descends (prefixWord ++ tailWord_725421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725425 : List Nat := [1, 2, 2, 4, 1, 2, 1, 7]
def baseStart_725425 : Nat := 118140960795 + 725425 * 2 ^ 59
def prefixEnd_725425 : Nat := 4983230072969 + 3 ^ 40 * 725425 * 2
def baseEnd_725425 : Nat := 110367912233460594089285

theorem tailTrace_725425 : CollatzResearch.WordTrace tailWord_725425 prefixEnd_725425 110367912233460594089285 := by
  unfold tailWord_725425
  simp only [CollatzResearch.WordTrace]
  refine ⟨26458423396916592571505729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17638948931277728381003819 26458423396916592571505729)
  ·
    refine ⟨19843817547687444428629297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26458423396916592571505729 19843817547687444428629297)
    ·
      refine ⟨14882863160765583321471973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19843817547687444428629297 14882863160765583321471973)
      ·
        refine ⟨2790536842643546872775995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14882863160765583321471973 2790536842643546872775995)
        ·
          refine ⟨4185805263965320309163993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2790536842643546872775995 4185805263965320309163993)
          ·
            refine ⟨3139353947973990231872995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4185805263965320309163993 3139353947973990231872995)
            ·
              refine ⟨4709030921960985347809493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139353947973990231872995 4709030921960985347809493)
              ·
                refine ⟨110367912233460594089285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4709030921960985347809493 110367912233460594089285)
                ·
                  rfl

theorem cell20_725425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 7].length) (baseStart_725425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725425 prefixEnd_725425 := by exact prefixLift 725425
  have htrace : WordTrace (prefixWord ++ tailWord_725425) baseStart_725425 baseEnd_725425 := by
    simpa [prefixWord, tailWord_725425, baseEnd_725425] using wordTrace_append hprefix tailTrace_725425
  have hstable : (prefixWord ++ tailWord_725425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725425).length < 2 ^ (prefixWord ++ tailWord_725425).sum := by decide
  have hdescent : baseEnd_725425 < baseStart_725425 := by decide
  rcases family_descends (prefixWord ++ tailWord_725425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725473 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 2]
def baseStart_725473 : Nat := 118140960795 + 725473 * 2 ^ 59
def prefixEnd_725473 : Nat := 4983230072969 + 3 ^ 40 * 725473 * 2
def baseEnd_725473 : Nat := 331125645208306948667659

theorem tailTrace_725473 : CollatzResearch.WordTrace tailWord_725473 prefixEnd_725473 331125645208306948667659 := by
  unfold tailWord_725473
  simp only [CollatzResearch.WordTrace]
  refine ⟨26460174100742696769253073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17640116067161797846168715 26460174100742696769253073)
  ·
    refine ⟨19845130575557022576939805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26460174100742696769253073 19845130575557022576939805)
    ·
      refine ⟨7441923965833883466352427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19845130575557022576939805 7441923965833883466352427)
      ·
        refine ⟨11162885948750825199528641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441923965833883466352427 11162885948750825199528641)
        ·
          refine ⟨8372164461563118899646481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11162885948750825199528641 8372164461563118899646481)
          ·
            refine ⟨6279123346172339174734861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8372164461563118899646481 6279123346172339174734861)
            ·
              refine ⟨2354671254814627190525573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6279123346172339174734861 2354671254814627190525573)
              ·
                refine ⟨441500860277742598223545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2354671254814627190525573 441500860277742598223545)
                ·
                  refine ⟨331125645208306948667659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441500860277742598223545 331125645208306948667659)
                  ·
                    rfl

theorem cell20_725473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_725473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725473 prefixEnd_725473 := by exact prefixLift 725473
  have htrace : WordTrace (prefixWord ++ tailWord_725473) baseStart_725473 baseEnd_725473 := by
    simpa [prefixWord, tailWord_725473, baseEnd_725473] using wordTrace_append hprefix tailTrace_725473
  have hstable : (prefixWord ++ tailWord_725473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725473).length < 2 ^ (prefixWord ++ tailWord_725473).sum := by decide
  have hdescent : baseEnd_725473 < baseStart_725473 := by decide
  rcases family_descends (prefixWord ++ tailWord_725473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725480 : List Nat := [2, 1, 4, 1, 1, 5, 1, 5]
def baseStart_725480 : Nat := 118140960795 + 725480 * 2 ^ 59
def prefixEnd_725480 : Nat := 4983230072969 + 3 ^ 40 * 725480 * 2
def baseEnd_725480 : Nat := 110376280066348678478099

theorem tailTrace_725480 : CollatzResearch.WordTrace tailWord_725480 prefixEnd_725480 110376280066348678478099 := by
  unfold tailWord_725480
  simp only [CollatzResearch.WordTrace]
  refine ⟨13230214705858668482378947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17640286274478224643171929 13230214705858668482378947)
  ·
    refine ⟨19845322058788002723568421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13230214705858668482378947 19845322058788002723568421)
    ·
      refine ⟨3720997886022750510669079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19845322058788002723568421 3720997886022750510669079)
      ·
        refine ⟨5581496829034125766003619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3720997886022750510669079 5581496829034125766003619)
        ·
          refine ⟨8372245243551188649005429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581496829034125766003619 8372245243551188649005429)
          ·
            refine ⟨784897991582923935844259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8372245243551188649005429 784897991582923935844259)
            ·
              refine ⟨1177346987374385903766389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784897991582923935844259 1177346987374385903766389)
              ·
                refine ⟨110376280066348678478099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1177346987374385903766389 110376280066348678478099)
                ·
                  rfl

theorem cell20_725480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_725480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725480 prefixEnd_725480 := by exact prefixLift 725480
  have htrace : WordTrace (prefixWord ++ tailWord_725480) baseStart_725480 baseEnd_725480 := by
    simpa [prefixWord, tailWord_725480, baseEnd_725480] using wordTrace_append hprefix tailTrace_725480
  have hstable : (prefixWord ++ tailWord_725480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725480).length < 2 ^ (prefixWord ++ tailWord_725480).sum := by decide
  have hdescent : baseEnd_725480 < baseStart_725480 := by decide
  rcases family_descends (prefixWord ++ tailWord_725480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725532 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_725532 : Nat := 118140960795 + 725532 * 2 ^ 59
def prefixEnd_725532 : Nat := 4983230072969 + 3 ^ 40 * 725532 * 2
def baseEnd_725532 : Nat := 331152574415964965700751

theorem tailTrace_725532 : CollatzResearch.WordTrace tailWord_725532 prefixEnd_725532 331152574415964965700751 := by
  unfold tailWord_725532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13231163003764474922825425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17641550671685966563767233 13231163003764474922825425)
  ·
    refine ⟨9923372252823356192119069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13231163003764474922825425 9923372252823356192119069)
    ·
      refine ⟨3721264594808758572044651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9923372252823356192119069 3721264594808758572044651)
      ·
        refine ⟨5581896892213137858066977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3721264594808758572044651 5581896892213137858066977)
        ·
          refine ⟨4186422669159853393550233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5581896892213137858066977 4186422669159853393550233)
          ·
            refine ⟨3139817001869890045162675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4186422669159853393550233 3139817001869890045162675)
            ·
              refine ⟨4709725502804835067744013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139817001869890045162675 4709725502804835067744013)
              ·
                refine ⟨1766147063551813150404005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4709725502804835067744013 1766147063551813150404005)
                ·
                  refine ⟨331152574415964965700751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766147063551813150404005 331152574415964965700751)
                  ·
                    rfl

theorem cell20_725532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_725532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725532 prefixEnd_725532 := by exact prefixLift 725532
  have htrace : WordTrace (prefixWord ++ tailWord_725532) baseStart_725532 baseEnd_725532 := by
    simpa [prefixWord, tailWord_725532, baseEnd_725532] using wordTrace_append hprefix tailTrace_725532
  have hstable : (prefixWord ++ tailWord_725532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725532).length < 2 ^ (prefixWord ++ tailWord_725532).sum := by decide
  have hdescent : baseEnd_725532 < baseStart_725532 := by decide
  rcases family_descends (prefixWord ++ tailWord_725532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725601 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_725601 : Nat := 118140960795 + 725601 * 2 ^ 59
def prefixEnd_725601 : Nat := 4983230072969 + 3 ^ 40 * 725601 * 2
def baseEnd_725601 : Nat := 331184067896107392400469

theorem tailTrace_725601 : CollatzResearch.WordTrace tailWord_725601 prefixEnd_725601 331184067896107392400469 := by
  unfold tailWord_725601
  simp only [CollatzResearch.WordTrace]
  refine ⟨26464842644278974629912657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17643228429519316419941771 26464842644278974629912657)
  ·
    refine ⟨19848631983209230972434493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26464842644278974629912657 19848631983209230972434493)
    ·
      refine ⟨7443236993703461614662935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19848631983209230972434493 7443236993703461614662935)
      ·
        refine ⟨11164855490555192421994403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7443236993703461614662935 11164855490555192421994403)
        ·
          refine ⟨16747283235832788632991605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11164855490555192421994403 16747283235832788632991605)
          ·
            refine ⟨1570057803359323934342963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16747283235832788632991605 1570057803359323934342963)
            ·
              refine ⟨2355086705038985901514445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570057803359323934342963 2355086705038985901514445)
              ·
                refine ⟨883157514389619713067917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2355086705038985901514445 883157514389619713067917)
                ·
                  refine ⟨331184067896107392400469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883157514389619713067917 331184067896107392400469)
                  ·
                    rfl

theorem cell20_725601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_725601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725601 prefixEnd_725601 := by exact prefixLift 725601
  have htrace : WordTrace (prefixWord ++ tailWord_725601) baseStart_725601 baseEnd_725601 := by
    simpa [prefixWord, tailWord_725601, baseEnd_725601] using wordTrace_append hprefix tailTrace_725601
  have hstable : (prefixWord ++ tailWord_725601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725601).length < 2 ^ (prefixWord ++ tailWord_725601).sum := by decide
  have hdescent : baseEnd_725601 < baseStart_725601 := by decide
  rcases family_descends (prefixWord ++ tailWord_725601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725634 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_725634 : Nat := 118140960795 + 725634 * 2 ^ 59
def prefixEnd_725634 : Nat := 4983230072969 + 3 ^ 40 * 725634 * 2
def baseEnd_725634 : Nat := 331199129995305944300335

theorem tailTrace_725634 : CollatzResearch.WordTrace tailWord_725634 prefixEnd_725634 331199129995305944300335 := by
  unfold tailWord_725634
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616511563289855316465989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17644030835439614177242637 6616511563289855316465989)
  ·
    refine ⟨1240595918116847871837373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6616511563289855316465989 1240595918116847871837373)
    ·
      refine ⟨465223469293817951939015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1240595918116847871837373 465223469293817951939015)
      ·
        refine ⟨697835203940726927908523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465223469293817951939015 697835203940726927908523)
        ·
          refine ⟨1046752805911090391862785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697835203940726927908523 1046752805911090391862785)
          ·
            refine ⟨785064604433317793897089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046752805911090391862785 785064604433317793897089)
            ·
              refine ⟨588798453324988345422817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785064604433317793897089 588798453324988345422817)
              ·
                refine ⟨441598839993741259067113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588798453324988345422817 441598839993741259067113)
                ·
                  refine ⟨331199129995305944300335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441598839993741259067113 331199129995305944300335)
                  ·
                    rfl

theorem cell20_725634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_725634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725634 prefixEnd_725634 := by exact prefixLift 725634
  have htrace : WordTrace (prefixWord ++ tailWord_725634) baseStart_725634 baseEnd_725634 := by
    simpa [prefixWord, tailWord_725634, baseEnd_725634] using wordTrace_append hprefix tailTrace_725634
  have hstable : (prefixWord ++ tailWord_725634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725634).length < 2 ^ (prefixWord ++ tailWord_725634).sum := by decide
  have hdescent : baseEnd_725634 < baseStart_725634 := by decide
  rcases family_descends (prefixWord ++ tailWord_725634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725639 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 3]
def baseStart_725639 : Nat := 118140960795 + 725639 * 2 ^ 59
def prefixEnd_725639 : Nat := 4983230072969 + 3 ^ 40 * 725639 * 2
def baseEnd_725639 : Nat := 331201412131548149133647

theorem tailTrace_725639 : CollatzResearch.WordTrace tailWord_725639 prefixEnd_725639 331201412131548149133647 := by
  unfold tailWord_725639
  simp only [CollatzResearch.WordTrace]
  refine ⟨26466228618141307119795971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17644152412094204746530647 26466228618141307119795971)
  ·
    refine ⟨39699342927211960679693957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26466228618141307119795971 39699342927211960679693957)
    ·
      refine ⟨7443626798852242627442617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39699342927211960679693957 7443626798852242627442617)
      ·
        refine ⟨5582720099139181970581963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7443626798852242627442617 5582720099139181970581963)
        ·
          refine ⟨8374080148708772955872945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5582720099139181970581963 8374080148708772955872945)
          ·
            refine ⟨6280560111531579716904709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8374080148708772955872945 6280560111531579716904709)
            ·
              refine ⟨1177605020912171196919633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6280560111531579716904709 1177605020912171196919633)
              ·
                refine ⟨883203765684128397689725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177605020912171196919633 883203765684128397689725)
                ·
                  refine ⟨331201412131548149133647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883203765684128397689725 331201412131548149133647)
                  ·
                    rfl

theorem cell20_725639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 3].length) (baseStart_725639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725639 prefixEnd_725639 := by exact prefixLift 725639
  have htrace : WordTrace (prefixWord ++ tailWord_725639) baseStart_725639 baseEnd_725639 := by
    simpa [prefixWord, tailWord_725639, baseEnd_725639] using wordTrace_append hprefix tailTrace_725639
  have hstable : (prefixWord ++ tailWord_725639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725639).length < 2 ^ (prefixWord ++ tailWord_725639).sum := by decide
  have hdescent : baseEnd_725639 < baseStart_725639 := by decide
  rcases family_descends (prefixWord ++ tailWord_725639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725642 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_725642 : Nat := 118140960795 + 725642 * 2 ^ 59
def prefixEnd_725642 : Nat := 4983230072969 + 3 ^ 40 * 725642 * 2
def baseEnd_725642 : Nat := 331202781413293472033635

theorem tailTrace_725642 : CollatzResearch.WordTrace tailWord_725642 prefixEnd_725642 331202781413293472033635 := by
  unfold tailWord_725642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616584509282609658038795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17644225358086959088103453 6616584509282609658038795)
  ·
    refine ⟨9924876763923914487058193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6616584509282609658038795 9924876763923914487058193)
    ·
      refine ⟨7443657572942935865293645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9924876763923914487058193 7443657572942935865293645)
      ·
        refine ⟨2791371589853600949485117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7443657572942935865293645 2791371589853600949485117)
        ·
          refine ⟨1046764346195100356056919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2791371589853600949485117 1046764346195100356056919)
          ·
            refine ⟨1570146519292650534085379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046764346195100356056919 1570146519292650534085379)
            ·
              refine ⟨2355219778938975801128069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570146519292650534085379 2355219778938975801128069)
              ·
                refine ⟨441603708551057962711513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2355219778938975801128069 441603708551057962711513)
                ·
                  refine ⟨331202781413293472033635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441603708551057962711513 331202781413293472033635)
                  ·
                    rfl

theorem cell20_725642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_725642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725642 prefixEnd_725642 := by exact prefixLift 725642
  have htrace : WordTrace (prefixWord ++ tailWord_725642) baseStart_725642 baseEnd_725642 := by
    simpa [prefixWord, tailWord_725642, baseEnd_725642] using wordTrace_append hprefix tailTrace_725642
  have hstable : (prefixWord ++ tailWord_725642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725642).length < 2 ^ (prefixWord ++ tailWord_725642).sum := by decide
  have hdescent : baseEnd_725642 < baseStart_725642 := by decide
  rcases family_descends (prefixWord ++ tailWord_725642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725646 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_725646 : Nat := 118140960795 + 725646 * 2 ^ 59
def prefixEnd_725646 : Nat := 4983230072969 + 3 ^ 40 * 725646 * 2
def baseEnd_725646 : Nat := 331204607122287235900285

theorem tailTrace_725646 : CollatzResearch.WordTrace tailWord_725646 prefixEnd_725646 331204607122287235900285 := by
  unfold tailWord_725646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308310491139493414412599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17644322619410631543533861 3308310491139493414412599)
  ·
    refine ⟨4962465736709240121618899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3308310491139493414412599 4962465736709240121618899)
    ·
      refine ⟨7443698605063860182428349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4962465736709240121618899 7443698605063860182428349)
      ·
        refine ⟨2791386976898947568410631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7443698605063860182428349 2791386976898947568410631)
        ·
          refine ⟨4187080465348421352615947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791386976898947568410631 4187080465348421352615947)
          ·
            refine ⟨6280620698022632028923921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187080465348421352615947 6280620698022632028923921)
            ·
              refine ⟨4710465523516974021692941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6280620698022632028923921 4710465523516974021692941)
              ·
                refine ⟨1766424571318865258134853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4710465523516974021692941 1766424571318865258134853)
                ·
                  refine ⟨331204607122287235900285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766424571318865258134853 331204607122287235900285)
                  ·
                    rfl

theorem cell20_725646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_725646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725646 prefixEnd_725646 := by exact prefixLift 725646
  have htrace : WordTrace (prefixWord ++ tailWord_725646) baseStart_725646 baseEnd_725646 := by
    simpa [prefixWord, tailWord_725646, baseEnd_725646] using wordTrace_append hprefix tailTrace_725646
  have hstable : (prefixWord ++ tailWord_725646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725646).length < 2 ^ (prefixWord ++ tailWord_725646).sum := by decide
  have hdescent : baseEnd_725646 < baseStart_725646 := by decide
  rcases family_descends (prefixWord ++ tailWord_725646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725729 : List Nat := [1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_725729 : Nat := 118140960795 + 725729 * 2 ^ 59
def prefixEnd_725729 : Nat := 4983230072969 + 3 ^ 40 * 725729 * 2
def baseEnd_725729 : Nat := 110414163527969278711093

theorem tailTrace_725729 : CollatzResearch.WordTrace tailWord_725729 prefixEnd_725729 110414163527969278711093 := by
  unfold tailWord_725729
  simp only [CollatzResearch.WordTrace]
  refine ⟨26469511187815252490572241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17646340791876834993714827 26469511187815252490572241)
  ·
    refine ⟨19852133390861439367929181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26469511187815252490572241 19852133390861439367929181)
    ·
      refine ⟨7444550021573039762973443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19852133390861439367929181 7444550021573039762973443)
      ·
        refine ⟨11166825032359559644460165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7444550021573039762973443 11166825032359559644460165)
        ·
          refine ⟨2093779693567417433336281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11166825032359559644460165 2093779693567417433336281)
          ·
            refine ⟨1570334770175563075002211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2093779693567417433336281 1570334770175563075002211)
            ·
              refine ⟨2355502155263344612503317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570334770175563075002211 2355502155263344612503317)
              ·
                refine ⟨110414163527969278711093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2355502155263344612503317 110414163527969278711093)
                ·
                  rfl

theorem cell20_725729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_725729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725729 prefixEnd_725729 := by exact prefixLift 725729
  have htrace : WordTrace (prefixWord ++ tailWord_725729) baseStart_725729 baseEnd_725729 := by
    simpa [prefixWord, tailWord_725729, baseEnd_725729] using wordTrace_append hprefix tailTrace_725729
  have hstable : (prefixWord ++ tailWord_725729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725729).length < 2 ^ (prefixWord ++ tailWord_725729).sum := by decide
  have hdescent : baseEnd_725729 < baseStart_725729 := by decide
  rcases family_descends (prefixWord ++ tailWord_725729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725756 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 2]
def baseStart_725756 : Nat := 118140960795 + 725756 * 2 ^ 59
def prefixEnd_725756 : Nat := 4983230072969 + 3 ^ 40 * 725756 * 2
def baseEnd_725756 : Nat := 331254814119615742233169

theorem tailTrace_725756 : CollatzResearch.WordTrace tailWord_725756 prefixEnd_725756 331254814119615742233169 := by
  unfold tailWord_725756
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235247979358718050902561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17646997305811624067870081 13235247979358718050902561)
  ·
    refine ⟨9926435984519038538176921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13235247979358718050902561 9926435984519038538176921)
    ·
      refine ⟨7444826988389278903632691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9926435984519038538176921 7444826988389278903632691)
      ·
        refine ⟨11167240482583918355449037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7444826988389278903632691 11167240482583918355449037)
        ·
          refine ⟨4187715180968969383293389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11167240482583918355449037 4187715180968969383293389)
          ·
            refine ⟨1570393192863363518735021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4187715180968969383293389 1570393192863363518735021)
            ·
              refine ⟨588897447323761319525633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1570393192863363518735021 588897447323761319525633)
              ·
                refine ⟨441673085492820989644225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588897447323761319525633 441673085492820989644225)
                ·
                  refine ⟨331254814119615742233169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441673085492820989644225 331254814119615742233169)
                  ·
                    rfl

theorem cell20_725756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_725756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725756 prefixEnd_725756 := by exact prefixLift 725756
  have htrace : WordTrace (prefixWord ++ tailWord_725756) baseStart_725756 baseEnd_725756 := by
    simpa [prefixWord, tailWord_725756, baseEnd_725756] using wordTrace_append hprefix tailTrace_725756
  have hstable : (prefixWord ++ tailWord_725756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725756).length < 2 ^ (prefixWord ++ tailWord_725756).sum := by decide
  have hdescent : baseEnd_725756 < baseStart_725756 := by decide
  rcases family_descends (prefixWord ++ tailWord_725756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725767 : List Nat := [1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_725767 : Nat := 118140960795 + 725767 * 2 ^ 59
def prefixEnd_725767 : Nat := 4983230072969 + 3 ^ 40 * 725767 * 2
def baseEnd_725767 : Nat := 110419944939782864288819

theorem tailTrace_725767 : CollatzResearch.WordTrace tailWord_725767 prefixEnd_725767 110419944939782864288819 := by
  unfold tailWord_725767
  simp only [CollatzResearch.WordTrace]
  refine ⟨26470897161677584980455555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17647264774451723320303703 26470897161677584980455555)
  ·
    refine ⟨39706345742516377470683333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26470897161677584980455555 39706345742516377470683333)
    ·
      refine ⟨7444939826721820775753125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39706345742516377470683333 7444939826721820775753125)
      ·
        refine ⟨1395926217510341395453711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7444939826721820775753125 1395926217510341395453711)
        ·
          refine ⟨2093889326265512093180567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395926217510341395453711 2093889326265512093180567)
          ·
            refine ⟨3140833989398268139770851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093889326265512093180567 3140833989398268139770851)
            ·
              refine ⟨4711250984097402209656277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140833989398268139770851 4711250984097402209656277)
              ·
                refine ⟨110419944939782864288819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4711250984097402209656277 110419944939782864288819)
                ·
                  rfl

theorem cell20_725767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_725767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725767 prefixEnd_725767 := by exact prefixLift 725767
  have htrace : WordTrace (prefixWord ++ tailWord_725767) baseStart_725767 baseEnd_725767 := by
    simpa [prefixWord, tailWord_725767, baseEnd_725767] using wordTrace_append hprefix tailTrace_725767
  have hstable : (prefixWord ++ tailWord_725767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725767).length < 2 ^ (prefixWord ++ tailWord_725767).sum := by decide
  have hdescent : baseEnd_725767 < baseStart_725767 := by decide
  rcases family_descends (prefixWord ++ tailWord_725767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725781 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_725781 : Nat := 118140960795 + 725781 * 2 ^ 59
def prefixEnd_725781 : Nat := 4983230072969 + 3 ^ 40 * 725781 * 2
def baseEnd_725781 : Nat := 331266224800826766399733

theorem tailTrace_725781 : CollatzResearch.WordTrace tailWord_725781 prefixEnd_725781 331266224800826766399733 := by
  unfold tailWord_725781
  simp only [CollatzResearch.WordTrace]
  refine ⟨26471407783626865371465197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17647605189084576914310131 26471407783626865371465197)
  ·
    refine ⟨9926777918860074514299449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26471407783626865371465197 9926777918860074514299449)
    ·
      refine ⟨7445083439145055885724587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9926777918860074514299449 7445083439145055885724587)
      ·
        refine ⟨11167625158717583828586881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7445083439145055885724587 11167625158717583828586881)
        ·
          refine ⟨8375718869038187871440161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11167625158717583828586881 8375718869038187871440161)
          ·
            refine ⟨6281789151778640903580121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8375718869038187871440161 6281789151778640903580121)
            ·
              refine ⟨4711341863833980677685091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6281789151778640903580121 4711341863833980677685091)
              ·
                refine ⟨7067012795750971016527637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711341863833980677685091 7067012795750971016527637)
                ·
                  refine ⟨331266224800826766399733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7067012795750971016527637 331266224800826766399733)
                  ·
                    rfl

theorem cell20_725781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_725781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725781 prefixEnd_725781 := by exact prefixLift 725781
  have htrace : WordTrace (prefixWord ++ tailWord_725781) baseStart_725781 baseEnd_725781 := by
    simpa [prefixWord, tailWord_725781, baseEnd_725781] using wordTrace_append hprefix tailTrace_725781
  have hstable : (prefixWord ++ tailWord_725781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725781).length < 2 ^ (prefixWord ++ tailWord_725781).sum := by decide
  have hdescent : baseEnd_725781 < baseStart_725781 := by decide
  rcases family_descends (prefixWord ++ tailWord_725781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725836 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_725836 : Nat := 118140960795 + 725836 * 2 ^ 59
def prefixEnd_725836 : Nat := 4983230072969 + 3 ^ 40 * 725836 * 2
def baseEnd_725836 : Nat := 331291328299491019566175

theorem tailTrace_725836 : CollatzResearch.WordTrace tailWord_725836 prefixEnd_725836 331291328299491019566175 := by
  unfold tailWord_725836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13236706899213804882358681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17648942532285073176478241 13236706899213804882358681)
  ·
    refine ⟨9927530174410353661769011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13236706899213804882358681 9927530174410353661769011)
    ·
      refine ⟨14891295261615530492653517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9927530174410353661769011 14891295261615530492653517)
      ·
        refine ⟨5584235723105823934745069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14891295261615530492653517 5584235723105823934745069)
        ·
          refine ⟨2094088396164683975529401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5584235723105823934745069 2094088396164683975529401)
          ·
            refine ⟨1570566297123512981647051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094088396164683975529401 1570566297123512981647051)
            ·
              refine ⟨2355849445685269472470577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570566297123512981647051 2355849445685269472470577)
              ·
                refine ⟨1766887084263952104352933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355849445685269472470577 1766887084263952104352933)
                ·
                  refine ⟨331291328299491019566175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766887084263952104352933 331291328299491019566175)
                  ·
                    rfl

theorem cell20_725836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_725836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725836 prefixEnd_725836 := by exact prefixLift 725836
  have htrace : WordTrace (prefixWord ++ tailWord_725836) baseStart_725836 baseEnd_725836 := by
    simpa [prefixWord, tailWord_725836, baseEnd_725836] using wordTrace_append hprefix tailTrace_725836
  have hstable : (prefixWord ++ tailWord_725836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725836).length < 2 ^ (prefixWord ++ tailWord_725836).sum := by decide
  have hdescent : baseEnd_725836 < baseStart_725836 := by decide
  rcases family_descends (prefixWord ++ tailWord_725836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725898 : List Nat := [3, 1, 2, 4, 1, 1, 4, 4]
def baseStart_725898 : Nat := 118140960795 + 725898 * 2 ^ 59
def prefixEnd_725898 : Nat := 4983230072969 + 3 ^ 40 * 725898 * 2
def baseEnd_725898 : Nat := 110439875596298119833085

theorem tailTrace_725898 : CollatzResearch.WordTrace tailWord_725898 prefixEnd_725898 110439875596298119833085 := by
  unfold tailWord_725898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618918781050748588368587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17650450082801996235649565 6618918781050748588368587)
  ·
    refine ⟨9928378171576122882552881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6618918781050748588368587 9928378171576122882552881)
    ·
      refine ⟨7446283628682092161914661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9928378171576122882552881 7446283628682092161914661)
      ·
        refine ⟨1396178180377892280358999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7446283628682092161914661 1396178180377892280358999)
        ·
          refine ⟨2094267270566838420538499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396178180377892280358999 2094267270566838420538499)
          ·
            refine ⟨3141400905850257630807749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094267270566838420538499 3141400905850257630807749)
            ·
              refine ⟨589012669846923305776453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3141400905850257630807749 589012669846923305776453)
              ·
                refine ⟨110439875596298119833085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589012669846923305776453 110439875596298119833085)
                ·
                  rfl

theorem cell20_725898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_725898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725898 prefixEnd_725898 := by exact prefixLift 725898
  have htrace : WordTrace (prefixWord ++ tailWord_725898) baseStart_725898 baseEnd_725898 := by
    simpa [prefixWord, tailWord_725898, baseEnd_725898] using wordTrace_append hprefix tailTrace_725898
  have hstable : (prefixWord ++ tailWord_725898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725898).length < 2 ^ (prefixWord ++ tailWord_725898).sum := by decide
  have hdescent : baseEnd_725898 < baseStart_725898 := by decide
  rcases family_descends (prefixWord ++ tailWord_725898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725919 : List Nat := [1, 1, 2, 5, 2, 3, 6]
def baseStart_725919 : Nat := 118140960795 + 725919 * 2 ^ 59
def prefixEnd_725919 : Nat := 4983230072969 + 3 ^ 40 * 725919 * 2
def baseEnd_725919 : Nat := 36814356862345735533241

theorem tailTrace_725919 : CollatzResearch.WordTrace tailWord_725919 prefixEnd_725919 36814356862345735533241 := by
  unfold tailWord_725919
  simp only [CollatzResearch.WordTrace]
  refine ⟨26476441057126914939988811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17650960704751276626659207 26476441057126914939988811)
  ·
    refine ⟨39714661585690372409983217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26476441057126914939988811 39714661585690372409983217)
    ·
      refine ⟨29785996189267779307487413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39714661585690372409983217 29785996189267779307487413)
      ·
        refine ⟨2792437142743854310076945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29785996189267779307487413 2792437142743854310076945)
        ·
          refine ⟨2094327857057890732557709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2792437142743854310076945 2094327857057890732557709)
          ·
            refine ⟨785372946396709024709141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2094327857057890732557709 785372946396709024709141)
            ·
              refine ⟨36814356862345735533241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 785372946396709024709141 36814356862345735533241)
              ·
                rfl

theorem cell20_725919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_725919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725919 prefixEnd_725919 := by exact prefixLift 725919
  have htrace : WordTrace (prefixWord ++ tailWord_725919) baseStart_725919 baseEnd_725919 := by
    simpa [prefixWord, tailWord_725919, baseEnd_725919] using wordTrace_append hprefix tailTrace_725919
  have hstable : (prefixWord ++ tailWord_725919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725919).length < 2 ^ (prefixWord ++ tailWord_725919).sum := by decide
  have hdescent : baseEnd_725919 < baseStart_725919 := by decide
  rcases family_descends (prefixWord ++ tailWord_725919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725929 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 2]
def baseStart_725929 : Nat := 118140960795 + 725929 * 2 ^ 59
def prefixEnd_725929 : Nat := 4983230072969 + 3 ^ 40 * 725929 * 2
def baseEnd_725929 : Nat := 331333776033596029465795

theorem tailTrace_725929 : CollatzResearch.WordTrace tailWord_725929 prefixEnd_725929 331333776033596029465795 := by
  unfold tailWord_725929
  simp only [CollatzResearch.WordTrace]
  refine ⟨26476805787090686647852841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17651203858060457765235227 26476805787090686647852841)
  ·
    refine ⟨19857604340318014985889631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26476805787090686647852841 19857604340318014985889631)
    ·
      refine ⟨29786406510477022478834447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19857604340318014985889631 29786406510477022478834447)
      ·
        refine ⟨44679609765715533718251671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29786406510477022478834447 44679609765715533718251671)
        ·
          refine ⟨67019414648573300577377507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44679609765715533718251671 67019414648573300577377507)
          ·
            refine ⟨100529121972859950866066261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67019414648573300577377507 100529121972859950866066261)
            ·
              refine ⟨589037824059726274605857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 100529121972859950866066261 589037824059726274605857)
              ·
                refine ⟨441778368044794705954393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589037824059726274605857 441778368044794705954393)
                ·
                  refine ⟨331333776033596029465795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441778368044794705954393 331333776033596029465795)
                  ·
                    rfl

theorem cell20_725929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_725929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725929 prefixEnd_725929 := by exact prefixLift 725929
  have htrace : WordTrace (prefixWord ++ tailWord_725929) baseStart_725929 baseEnd_725929 := by
    simpa [prefixWord, tailWord_725929, baseEnd_725929] using wordTrace_append hprefix tailTrace_725929
  have hstable : (prefixWord ++ tailWord_725929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725929).length < 2 ^ (prefixWord ++ tailWord_725929).sum := by decide
  have hdescent : baseEnd_725929 < baseStart_725929 := by decide
  rcases family_descends (prefixWord ++ tailWord_725929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725943 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 3]
def baseStart_725943 : Nat := 118140960795 + 725943 * 2 ^ 59
def prefixEnd_725943 : Nat := 4983230072969 + 3 ^ 40 * 725943 * 2
def baseEnd_725943 : Nat := 331340166015074202999071

theorem tailTrace_725943 : CollatzResearch.WordTrace tailWord_725943 prefixEnd_725943 331340166015074202999071 := by
  unfold tailWord_725943
  simp only [CollatzResearch.WordTrace]
  refine ⟨26477316409039967038862483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17651544272693311359241655 26477316409039967038862483)
  ·
    refine ⟨39715974613559950558293725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26477316409039967038862483 39715974613559950558293725)
    ·
      refine ⟨14893490480084981459360147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39715974613559950558293725 14893490480084981459360147)
      ·
        refine ⟨22340235720127472189040221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14893490480084981459360147 22340235720127472189040221)
        ·
          refine ⟨8377588395047802070890083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22340235720127472189040221 8377588395047802070890083)
          ·
            refine ⟨12566382592571703106335125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8377588395047802070890083 12566382592571703106335125)
            ·
              refine ⟨589049184026798583109459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12566382592571703106335125 589049184026798583109459)
              ·
                refine ⟨883573776040197874664189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589049184026798583109459 883573776040197874664189)
                ·
                  refine ⟨331340166015074202999071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883573776040197874664189 331340166015074202999071)
                  ·
                    rfl

theorem cell20_725943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_725943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725943 prefixEnd_725943 := by exact prefixLift 725943
  have htrace : WordTrace (prefixWord ++ tailWord_725943) baseStart_725943 baseEnd_725943 := by
    simpa [prefixWord, tailWord_725943, baseEnd_725943] using wordTrace_append hprefix tailTrace_725943
  have hstable : (prefixWord ++ tailWord_725943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725943).length < 2 ^ (prefixWord ++ tailWord_725943).sum := by decide
  have hdescent : baseEnd_725943 < baseStart_725943 := by decide
  rcases family_descends (prefixWord ++ tailWord_725943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725978 : List Nat := [3, 1, 1, 2, 4, 9]
def baseStart_725978 : Nat := 118140960795 + 725978 * 2 ^ 59
def prefixEnd_725978 : Nat := 4983230072969 + 3 ^ 40 * 725978 * 2
def baseEnd_725978 : Nat := 12272449665509986549343

theorem tailTrace_725978 : CollatzResearch.WordTrace tailWord_725978 prefixEnd_725978 12272449665509986549343 := by
  unfold tailWord_725978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6619648240978292004096647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17652395309275445344257725 6619648240978292004096647)
  ·
    refine ⟨9929472361467438006144971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6619648240978292004096647 9929472361467438006144971)
    ·
      refine ⟨14894208542201157009217457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9929472361467438006144971 14894208542201157009217457)
      ·
        refine ⟨11170656406650867756913093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14894208542201157009217457 11170656406650867756913093)
        ·
          refine ⟨2094498076247037704421205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11170656406650867756913093 2094498076247037704421205)
          ·
            refine ⟨12272449665509986549343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2094498076247037704421205 12272449665509986549343)
            ·
              rfl

theorem cell20_725978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 9].length) (baseStart_725978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725978 prefixEnd_725978 := by exact prefixLift 725978
  have htrace : WordTrace (prefixWord ++ tailWord_725978) baseStart_725978 baseEnd_725978 := by
    simpa [prefixWord, tailWord_725978, baseEnd_725978] using wordTrace_append hprefix tailTrace_725978
  have hstable : (prefixWord ++ tailWord_725978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725978).length < 2 ^ (prefixWord ++ tailWord_725978).sum := by decide
  have hdescent : baseEnd_725978 < baseStart_725978 := by decide
  rcases family_descends (prefixWord ++ tailWord_725978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_725981 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 3]
def baseStart_725981 : Nat := 118140960795 + 725981 * 2 ^ 59
def prefixEnd_725981 : Nat := 4983230072969 + 3 ^ 40 * 725981 * 2
def baseEnd_725981 : Nat := 331357510250514959732249

theorem tailTrace_725981 : CollatzResearch.WordTrace tailWord_725981 prefixEnd_725981 331357510250514959732249 := by
  unfold tailWord_725981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478702382902299528745797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17652468255268199685830531 26478702382902299528745797)
  ·
    refine ⟨4964756696794181161639837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26478702382902299528745797 4964756696794181161639837)
    ·
      refine ⟨1861783761297817935614939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4964756696794181161639837 1861783761297817935614939)
      ·
        refine ⟨2792675641946726903422409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861783761297817935614939 2792675641946726903422409)
        ·
          refine ⟨2094506731460045177566807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2792675641946726903422409 2094506731460045177566807)
          ·
            refine ⟨3141760097190067766350211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094506731460045177566807 3141760097190067766350211)
            ·
              refine ⟨4712640145785101649525317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141760097190067766350211 4712640145785101649525317)
              ·
                refine ⟨883620027334706559285997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4712640145785101649525317 883620027334706559285997)
                ·
                  refine ⟨331357510250514959732249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883620027334706559285997 331357510250514959732249)
                  ·
                    rfl

theorem cell20_725981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_725981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_725981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_725981 prefixEnd_725981 := by exact prefixLift 725981
  have htrace : WordTrace (prefixWord ++ tailWord_725981) baseStart_725981 baseEnd_725981 := by
    simpa [prefixWord, tailWord_725981, baseEnd_725981] using wordTrace_append hprefix tailTrace_725981
  have hstable : (prefixWord ++ tailWord_725981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_725981).length < 2 ^ (prefixWord ++ tailWord_725981).sum := by decide
  have hdescent : baseEnd_725981 < baseStart_725981 := by decide
  rcases family_descends (prefixWord ++ tailWord_725981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726009 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_726009 : Nat := 118140960795 + 726009 * 2 ^ 59
def prefixEnd_726009 : Nat := 4983230072969 + 3 ^ 40 * 726009 * 2
def baseEnd_726009 : Nat := 331370290213471306798801

theorem tailTrace_726009 : CollatzResearch.WordTrace tailWord_726009 prefixEnd_726009 331370290213471306798801 := by
  unfold tailWord_726009
  simp only [CollatzResearch.WordTrace]
  refine ⟨26479723626800860310765081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17653149084533906873843387 26479723626800860310765081)
  ·
    refine ⟨19859792720100645233073811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26479723626800860310765081 19859792720100645233073811)
    ·
      refine ⟨29789689080150967849610717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19859792720100645233073811 29789689080150967849610717)
      ·
        refine ⟨11171133405056612943604019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29789689080150967849610717 11171133405056612943604019)
        ·
          refine ⟨16756700107584919415406029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11171133405056612943604019 16756700107584919415406029)
          ·
            refine ⟨6283762540344344780777261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16756700107584919415406029 6283762540344344780777261)
            ·
              refine ⟨2356410952629129292791473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6283762540344344780777261 2356410952629129292791473)
              ·
                refine ⟨1767308214471846969593605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356410952629129292791473 1767308214471846969593605)
                ·
                  refine ⟨331370290213471306798801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767308214471846969593605 331370290213471306798801)
                  ·
                    rfl

theorem cell20_726009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_726009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726009 prefixEnd_726009 := by exact prefixLift 726009
  have htrace : WordTrace (prefixWord ++ tailWord_726009) baseStart_726009 baseEnd_726009 := by
    simpa [prefixWord, tailWord_726009, baseEnd_726009] using wordTrace_append hprefix tailTrace_726009
  have hstable : (prefixWord ++ tailWord_726009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726009).length < 2 ^ (prefixWord ++ tailWord_726009).sum := by decide
  have hdescent : baseEnd_726009 < baseStart_726009 := by decide
  rcases family_descends (prefixWord ++ tailWord_726009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726040 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_726040 : Nat := 118140960795 + 726040 * 2 ^ 59
def prefixEnd_726040 : Nat := 4983230072969 + 3 ^ 40 * 726040 * 2
def baseEnd_726040 : Nat := 331384439458172976765341

theorem tailTrace_726040 : CollatzResearch.WordTrace tailWord_726040 prefixEnd_726040 331384439458172976765341 := by
  unfold tailWord_726040
  simp only [CollatzResearch.WordTrace]
  refine ⟨13240427144844276302571787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17653902859792368403429049 13240427144844276302571787)
  ·
    refine ⟨19860640717266414453857681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13240427144844276302571787 19860640717266414453857681)
    ·
      refine ⟨14895480537949810840393261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19860640717266414453857681 14895480537949810840393261)
      ·
        refine ⟨5585805201731179065147473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14895480537949810840393261 5585805201731179065147473)
        ·
          refine ⟨4189353901298384298860605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5585805201731179065147473 4189353901298384298860605)
          ·
            refine ⟨1571007712986894112072727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4189353901298384298860605 1571007712986894112072727)
            ·
              refine ⟨2356511569480341168109091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571007712986894112072727 2356511569480341168109091)
              ·
                refine ⟨3534767354220511752163637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356511569480341168109091 3534767354220511752163637)
                ·
                  refine ⟨331384439458172976765341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534767354220511752163637 331384439458172976765341)
                  ·
                    rfl

theorem cell20_726040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_726040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726040 prefixEnd_726040 := by exact prefixLift 726040
  have htrace : WordTrace (prefixWord ++ tailWord_726040) baseStart_726040 baseEnd_726040 := by
    simpa [prefixWord, tailWord_726040, baseEnd_726040] using wordTrace_append hprefix tailTrace_726040
  have hstable : (prefixWord ++ tailWord_726040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726040).length < 2 ^ (prefixWord ++ tailWord_726040).sum := by decide
  have hdescent : baseEnd_726040 < baseStart_726040 := by decide
  rcases family_descends (prefixWord ++ tailWord_726040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726047 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 4]
def baseStart_726047 : Nat := 118140960795 + 726047 * 2 ^ 59
def prefixEnd_726047 : Nat := 4983230072969 + 3 ^ 40 * 726047 * 2
def baseEnd_726047 : Nat := 331387634448912063531979

theorem tailTrace_726047 : CollatzResearch.WordTrace tailWord_726047 prefixEnd_726047 331387634448912063531979 := by
  unfold tailWord_726047
  simp only [CollatzResearch.WordTrace]
  refine ⟨26481109600663192800648395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17654073067108795200432263 26481109600663192800648395)
  ·
    refine ⟨39721664400994789200972593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26481109600663192800648395 39721664400994789200972593)
    ·
      refine ⟨29791248300746091900729445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39721664400994789200972593 29791248300746091900729445)
      ·
        refine ⟨5585859056389892231386771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29791248300746091900729445 5585859056389892231386771)
        ·
          refine ⟨8378788584584838347080157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5585859056389892231386771 8378788584584838347080157)
          ·
            refine ⟨3142045719219314380155059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8378788584584838347080157 3142045719219314380155059)
            ·
              refine ⟨4713068578828971570232589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142045719219314380155059 4713068578828971570232589)
              ·
                refine ⟨1767400717060864338837221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4713068578828971570232589 1767400717060864338837221)
                ·
                  refine ⟨331387634448912063531979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767400717060864338837221 331387634448912063531979)
                  ·
                    rfl

theorem cell20_726047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_726047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726047 prefixEnd_726047 := by exact prefixLift 726047
  have htrace : WordTrace (prefixWord ++ tailWord_726047) baseStart_726047 baseEnd_726047 := by
    simpa [prefixWord, tailWord_726047, baseEnd_726047] using wordTrace_append hprefix tailTrace_726047
  have hstable : (prefixWord ++ tailWord_726047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726047).length < 2 ^ (prefixWord ++ tailWord_726047).sum := by decide
  have hdescent : baseEnd_726047 < baseStart_726047 := by decide
  rcases family_descends (prefixWord ++ tailWord_726047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726098 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_726098 : Nat := 118140960795 + 726098 * 2 ^ 59
def prefixEnd_726098 : Nat := 4983230072969 + 3 ^ 40 * 726098 * 2
def baseEnd_726098 : Nat := 331410912238582552831771

theorem tailTrace_726098 : CollatzResearch.WordTrace tailWord_726098 prefixEnd_726098 331410912238582552831771 := by
  unfold tailWord_726098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620742430869607127688737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17655313148985619007169965 6620742430869607127688737)
  ·
    refine ⟨4965556823152205345766553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6620742430869607127688737 4965556823152205345766553)
    ·
      refine ⟨3724167617364154009324915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4965556823152205345766553 3724167617364154009324915)
      ·
        refine ⟨5586251426046231013987373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724167617364154009324915 5586251426046231013987373)
        ·
          refine ⟨2094844284767336630245265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5586251426046231013987373 2094844284767336630245265)
          ·
            refine ⟨1571133213575502472683949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094844284767336630245265 1571133213575502472683949)
            ·
              refine ⟨589174955090813427256481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1571133213575502472683949 589174955090813427256481)
              ·
                refine ⟨441881216318110070442361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589174955090813427256481 441881216318110070442361)
                ·
                  refine ⟨331410912238582552831771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441881216318110070442361 331410912238582552831771)
                  ·
                    rfl

theorem cell20_726098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_726098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726098 prefixEnd_726098 := by exact prefixLift 726098
  have htrace : WordTrace (prefixWord ++ tailWord_726098) baseStart_726098 baseEnd_726098 := by
    simpa [prefixWord, tailWord_726098, baseEnd_726098] using wordTrace_append hprefix tailTrace_726098
  have hstable : (prefixWord ++ tailWord_726098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726098).length < 2 ^ (prefixWord ++ tailWord_726098).sum := by decide
  have hdescent : baseEnd_726098 < baseStart_726098 := by decide
  rcases family_descends (prefixWord ++ tailWord_726098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726130 : List Nat := [3, 2, 1, 2, 2, 1, 1, 8]
def baseStart_726130 : Nat := 118140960795 + 726130 * 2 ^ 59
def prefixEnd_726130 : Nat := 4983230072969 + 3 ^ 40 * 726130 * 2
def baseEnd_726130 : Nat := 110475172636844221254991

theorem tailTrace_726130 : CollatzResearch.WordTrace tailWord_726130 prefixEnd_726130 110475172636844221254991 := by
  unfold tailWord_726130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621034214840624493979961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17656091239574998650613229 6621034214840624493979961)
  ·
    refine ⟨4965775661130468370484971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6621034214840624493979961 4965775661130468370484971)
    ·
      refine ⟨7448663491695702555727457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4965775661130468370484971 7448663491695702555727457)
      ·
        refine ⟨5586497618771776916795593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7448663491695702555727457 5586497618771776916795593)
        ·
          refine ⟨4189873214078832687596695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5586497618771776916795593 4189873214078832687596695)
          ·
            refine ⟨6284809821118249031395043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189873214078832687596695 6284809821118249031395043)
            ·
              refine ⟨9427214731677373547092565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284809821118249031395043 9427214731677373547092565)
              ·
                refine ⟨110475172636844221254991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9427214731677373547092565 110475172636844221254991)
                ·
                  rfl

theorem cell20_726130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_726130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726130 prefixEnd_726130 := by exact prefixLift 726130
  have htrace : WordTrace (prefixWord ++ tailWord_726130) baseStart_726130 baseEnd_726130 := by
    simpa [prefixWord, tailWord_726130, baseEnd_726130] using wordTrace_append hprefix tailTrace_726130
  have hstable : (prefixWord ++ tailWord_726130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726130).length < 2 ^ (prefixWord ++ tailWord_726130).sum := by decide
  have hdescent : baseEnd_726130 < baseStart_726130 := by decide
  rcases family_descends (prefixWord ++ tailWord_726130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726140 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 2]
def baseStart_726140 : Nat := 118140960795 + 726140 * 2 ^ 59
def prefixEnd_726140 : Nat := 4983230072969 + 3 ^ 40 * 726140 * 2
def baseEnd_726140 : Nat := 331430082183017073431599

theorem tailTrace_726140 : CollatzResearch.WordTrace tailWord_726140 prefixEnd_726140 331430082183017073431599 := by
  unfold tailWord_726140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13242250794663134841891937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17656334392884179789189249 13242250794663134841891937)
  ·
    refine ⟨9931688095997351131418953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13242250794663134841891937 9931688095997351131418953)
    ·
      refine ⟨7448766071998013348564215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9931688095997351131418953 7448766071998013348564215)
      ·
        refine ⟨11173149107997020022846323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7448766071998013348564215 11173149107997020022846323)
        ·
          refine ⟨16759723661995530034269485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11173149107997020022846323 16759723661995530034269485)
          ·
            refine ⟨6284896373248323762851057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16759723661995530034269485 6284896373248323762851057)
            ·
              refine ⟨4713672279936242822138293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6284896373248323762851057 4713672279936242822138293)
              ·
                refine ⟨441906776244022764575465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4713672279936242822138293 441906776244022764575465)
                ·
                  refine ⟨331430082183017073431599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441906776244022764575465 331430082183017073431599)
                  ·
                    rfl

theorem cell20_726140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_726140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726140 prefixEnd_726140 := by exact prefixLift 726140
  have htrace : WordTrace (prefixWord ++ tailWord_726140) baseStart_726140 baseEnd_726140 := by
    simpa [prefixWord, tailWord_726140, baseEnd_726140] using wordTrace_append hprefix tailTrace_726140
  have hstable : (prefixWord ++ tailWord_726140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726140).length < 2 ^ (prefixWord ++ tailWord_726140).sum := by decide
  have hdescent : baseEnd_726140 < baseStart_726140 := by decide
  rcases family_descends (prefixWord ++ tailWord_726140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726209 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 5]
def baseStart_726209 : Nat := 118140960795 + 726209 * 2 ^ 59
def prefixEnd_726209 : Nat := 4983230072969 + 3 ^ 40 * 726209 * 2
def baseEnd_726209 : Nat := 331461575663159500131317

theorem tailTrace_726209 : CollatzResearch.WordTrace tailWord_726209 prefixEnd_726209 331461575663159500131317 := by
  unfold tailWord_726209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26487018226076294468045681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17658012150717529645363787 26487018226076294468045681)
  ·
    refine ⟨19865263669557220851034261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26487018226076294468045681 19865263669557220851034261)
    ·
      refine ⟨931184234510494727392231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19865263669557220851034261 931184234510494727392231)
      ·
        refine ⟨1396776351765742091088347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931184234510494727392231 1396776351765742091088347)
        ·
          refine ⟨2095164527648613136632521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396776351765742091088347 2095164527648613136632521)
          ·
            refine ⟨1571373395736459852474391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095164527648613136632521 1571373395736459852474391)
            ·
              refine ⟨2357060093604689778711587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571373395736459852474391 2357060093604689778711587)
              ·
                refine ⟨3535590140407034668067381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357060093604689778711587 3535590140407034668067381)
                ·
                  refine ⟨331461575663159500131317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535590140407034668067381 331461575663159500131317)
                  ·
                    rfl

theorem cell20_726209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_726209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726209 prefixEnd_726209 := by exact prefixLift 726209
  have htrace : WordTrace (prefixWord ++ tailWord_726209) baseStart_726209 baseEnd_726209 := by
    simpa [prefixWord, tailWord_726209, baseEnd_726209] using wordTrace_append hprefix tailTrace_726209
  have hstable : (prefixWord ++ tailWord_726209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726209).length < 2 ^ (prefixWord ++ tailWord_726209).sum := by decide
  have hdescent : baseEnd_726209 < baseStart_726209 := by decide
  rcases family_descends (prefixWord ++ tailWord_726209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726216 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 2]
def baseStart_726216 : Nat := 118140960795 + 726216 * 2 ^ 59
def prefixEnd_726216 : Nat := 4983230072969 + 3 ^ 40 * 726216 * 2
def baseEnd_726216 : Nat := 331464770653898586897955

theorem tailTrace_726216 : CollatzResearch.WordTrace tailWord_726216 prefixEnd_726216 331464770653898586897955 := by
  unfold tailWord_726216
  simp only [CollatzResearch.WordTrace]
  refine ⟨13243636768525467331775251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17658182358033956442367001 13243636768525467331775251)
  ·
    refine ⟨19865455152788200997662877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13243636768525467331775251 19865455152788200997662877)
    ·
      refine ⟨7449545682295575374123579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19865455152788200997662877 7449545682295575374123579)
      ·
        refine ⟨11174318523443363061185369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7449545682295575374123579 11174318523443363061185369)
        ·
          refine ⟨8380738892582522295889027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11174318523443363061185369 8380738892582522295889027)
          ·
            refine ⟨12571108338873783443833541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8380738892582522295889027 12571108338873783443833541)
            ·
              refine ⟨2357082813538834395718789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12571108338873783443833541 2357082813538834395718789)
              ·
                refine ⟨441953027538531449197273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2357082813538834395718789 441953027538531449197273)
                ·
                  refine ⟨331464770653898586897955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441953027538531449197273 331464770653898586897955)
                  ·
                    rfl

theorem cell20_726216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_726216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726216 prefixEnd_726216 := by exact prefixLift 726216
  have htrace : WordTrace (prefixWord ++ tailWord_726216) baseStart_726216 baseEnd_726216 := by
    simpa [prefixWord, tailWord_726216, baseEnd_726216] using wordTrace_append hprefix tailTrace_726216
  have hstable : (prefixWord ++ tailWord_726216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726216).length < 2 ^ (prefixWord ++ tailWord_726216).sum := by decide
  have hdescent : baseEnd_726216 < baseStart_726216 := by decide
  rcases family_descends (prefixWord ++ tailWord_726216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726251 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 5]
def baseStart_726251 : Nat := 118140960795 + 726251 * 2 ^ 59
def prefixEnd_726251 : Nat := 4983230072969 + 3 ^ 40 * 726251 * 2
def baseEnd_726251 : Nat := 331480745607594020731145

theorem tailTrace_726251 : CollatzResearch.WordTrace tailWord_726251 prefixEnd_726251 331480745607594020731145 := by
  unfold tailWord_726251
  simp only [CollatzResearch.WordTrace]
  refine ⟨26488550091924135641074607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17659033394616090427383071 26488550091924135641074607)
  ·
    refine ⟨39732825137886203461611911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26488550091924135641074607 39732825137886203461611911)
    ·
      refine ⟨59599237706829305192417867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39732825137886203461611911 59599237706829305192417867)
      ·
        refine ⟨89398856560243957788626801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59599237706829305192417867 89398856560243957788626801)
        ·
          refine ⟨67049142420182968341470101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89398856560243957788626801 67049142420182968341470101)
          ·
            refine ⟨3142928550946076641006411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67049142420182968341470101 3142928550946076641006411)
            ·
              refine ⟨4714392826419114961509617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142928550946076641006411 4714392826419114961509617)
              ·
                refine ⟨3535794619814336221132213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714392826419114961509617 3535794619814336221132213)
                ·
                  refine ⟨331480745607594020731145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535794619814336221132213 331480745607594020731145)
                  ·
                    rfl

theorem cell20_726251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_726251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726251 prefixEnd_726251 := by exact prefixLift 726251
  have htrace : WordTrace (prefixWord ++ tailWord_726251) baseStart_726251 baseEnd_726251 := by
    simpa [prefixWord, tailWord_726251, baseEnd_726251] using wordTrace_append hprefix tailTrace_726251
  have hstable : (prefixWord ++ tailWord_726251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726251).length < 2 ^ (prefixWord ++ tailWord_726251).sum := by decide
  have hdescent : baseEnd_726251 < baseStart_726251 := by decide
  rcases family_descends (prefixWord ++ tailWord_726251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726271 : List Nat := [1, 1, 2, 2, 1, 6, 3, 2, 2]
def baseStart_726271 : Nat := 118140960795 + 726271 * 2 ^ 59
def prefixEnd_726271 : Nat := 4983230072969 + 3 ^ 40 * 726271 * 2
def baseEnd_726271 : Nat := 331489874152562840064397

theorem tailTrace_726271 : CollatzResearch.WordTrace tailWord_726271 prefixEnd_726271 331489874152562840064397 := by
  unfold tailWord_726271
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489279551851679056802667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17659519701234452704535111 26489279551851679056802667)
  ·
    refine ⟨39733919327777518585204001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26489279551851679056802667 39733919327777518585204001)
    ·
      refine ⟨29800439495833138938903001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39733919327777518585204001 29800439495833138938903001)
      ·
        refine ⟨22350329621874854204177251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29800439495833138938903001 22350329621874854204177251)
        ·
          refine ⟨33525494432812281306265877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22350329621874854204177251 33525494432812281306265877)
          ·
            refine ⟨1571507551538075686231213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33525494432812281306265877 1571507551538075686231213)
            ·
              refine ⟨589315331826778382336705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1571507551538075686231213 589315331826778382336705)
              ·
                refine ⟨441986498870083786752529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589315331826778382336705 441986498870083786752529)
                ·
                  refine ⟨331489874152562840064397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441986498870083786752529 331489874152562840064397)
                  ·
                    rfl

theorem cell20_726271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 2, 2].length) (baseStart_726271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726271 prefixEnd_726271 := by exact prefixLift 726271
  have htrace : WordTrace (prefixWord ++ tailWord_726271) baseStart_726271 baseEnd_726271 := by
    simpa [prefixWord, tailWord_726271, baseEnd_726271] using wordTrace_append hprefix tailTrace_726271
  have hstable : (prefixWord ++ tailWord_726271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726271).length < 2 ^ (prefixWord ++ tailWord_726271).sum := by decide
  have hdescent : baseEnd_726271 < baseStart_726271 := by decide
  rcases family_descends (prefixWord ++ tailWord_726271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726275 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_726275 : Nat := 118140960795 + 726275 * 2 ^ 59
def prefixEnd_726275 : Nat := 4983230072969 + 3 ^ 40 * 726275 * 2
def baseEnd_726275 : Nat := 331491699861556603931047

theorem tailTrace_726275 : CollatzResearch.WordTrace tailWord_726275 prefixEnd_726275 331491699861556603931047 := by
  unfold tailWord_726275
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489425443837187739948279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17659616962558125159965519 26489425443837187739948279)
  ·
    refine ⟨39734138165755781609922419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26489425443837187739948279 39734138165755781609922419)
    ·
      refine ⟨59601207248633672414883629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39734138165755781609922419 59601207248633672414883629)
      ·
        refine ⟨22350452718237627155581361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59601207248633672414883629 22350452718237627155581361)
        ·
          refine ⟨16762839538678220366686021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22350452718237627155581361 16762839538678220366686021)
          ·
            refine ⟨3143032413502166318753629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16762839538678220366686021 3143032413502166318753629)
            ·
              refine ⟨1178637155063312369532611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143032413502166318753629 1178637155063312369532611)
              ·
                refine ⟨1767955732594968554298917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178637155063312369532611 1767955732594968554298917)
                ·
                  refine ⟨331491699861556603931047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767955732594968554298917 331491699861556603931047)
                  ·
                    rfl

theorem cell20_726275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_726275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726275 prefixEnd_726275 := by exact prefixLift 726275
  have htrace : WordTrace (prefixWord ++ tailWord_726275) baseStart_726275 baseEnd_726275 := by
    simpa [prefixWord, tailWord_726275, baseEnd_726275] using wordTrace_append hprefix tailTrace_726275
  have hstable : (prefixWord ++ tailWord_726275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726275).length < 2 ^ (prefixWord ++ tailWord_726275).sum := by decide
  have hdescent : baseEnd_726275 < baseStart_726275 := by decide
  rcases family_descends (prefixWord ++ tailWord_726275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726330 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_726330 : Nat := 118140960795 + 726330 * 2 ^ 59
def prefixEnd_726330 : Nat := 4983230072969 + 3 ^ 40 * 726330 * 2
def baseEnd_726330 : Nat := 331516803360220857097489

theorem tailTrace_726330 : CollatzResearch.WordTrace tailWord_726330 prefixEnd_726330 331516803360220857097489 := by
  unfold tailWord_726330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6622857864659483033300111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17660954305758621422133629 6622857864659483033300111)
  ·
    refine ⟨9934286796989224549950167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6622857864659483033300111 9934286796989224549950167)
    ·
      refine ⟨14901430195483836824925251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9934286796989224549950167 14901430195483836824925251)
      ·
        refine ⟨22352145293225755237387877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14901430195483836824925251 22352145293225755237387877)
        ·
          refine ⟨4191027242479829107010227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22352145293225755237387877 4191027242479829107010227)
          ·
            refine ⟨6286540863719743660515341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191027242479829107010227 6286540863719743660515341)
            ·
              refine ⟨2357452823894903872693253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6286540863719743660515341 2357452823894903872693253)
              ·
                refine ⟨442022404480294476129985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2357452823894903872693253 442022404480294476129985)
                ·
                  refine ⟨331516803360220857097489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442022404480294476129985 331516803360220857097489)
                  ·
                    rfl

theorem cell20_726330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_726330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726330 prefixEnd_726330 := by exact prefixLift 726330
  have htrace : WordTrace (prefixWord ++ tailWord_726330) baseStart_726330 baseEnd_726330 := by
    simpa [prefixWord, tailWord_726330, baseEnd_726330] using wordTrace_append hprefix tailTrace_726330
  have hstable : (prefixWord ++ tailWord_726330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726330).length < 2 ^ (prefixWord ++ tailWord_726330).sum := by decide
  have hdescent : baseEnd_726330 < baseStart_726330 := by decide
  rcases family_descends (prefixWord ++ tailWord_726330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726333 : List Nat := [1, 4, 1, 5, 2, 1, 1, 5]
def baseStart_726333 : Nat := 118140960795 + 726333 * 2 ^ 59
def prefixEnd_726333 : Nat := 4983230072969 + 3 ^ 40 * 726333 * 2
def baseEnd_726333 : Nat := 110506057547322059999159

theorem tailTrace_726333 : CollatzResearch.WordTrace tailWord_726333 prefixEnd_726333 110506057547322059999159 := by
  unfold tailWord_726333
  simp only [CollatzResearch.WordTrace]
  refine ⟨26491540877627063645559653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17661027251751375763706435 26491540877627063645559653)
  ·
    refine ⟨4967163914555074433542435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26491540877627063645559653 4967163914555074433542435)
    ·
      refine ⟨7450745871832611650313653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4967163914555074433542435 7450745871832611650313653)
      ·
        refine ⟨698507425484307342216905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7450745871832611650313653 698507425484307342216905)
        ·
          refine ⟨523880569113230506662679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698507425484307342216905 523880569113230506662679)
          ·
            refine ⟨785820853669845759994019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523880569113230506662679 785820853669845759994019)
            ·
              refine ⟨1178731280504768639991029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785820853669845759994019 1178731280504768639991029)
              ·
                refine ⟨110506057547322059999159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1178731280504768639991029 110506057547322059999159)
                ·
                  rfl

theorem cell20_726333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].length) (baseStart_726333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726333 prefixEnd_726333 := by exact prefixLift 726333
  have htrace : WordTrace (prefixWord ++ tailWord_726333) baseStart_726333 baseEnd_726333 := by
    simpa [prefixWord, tailWord_726333, baseEnd_726333] using wordTrace_append hprefix tailTrace_726333
  have hstable : (prefixWord ++ tailWord_726333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726333).length < 2 ^ (prefixWord ++ tailWord_726333).sum := by decide
  have hdescent : baseEnd_726333 < baseStart_726333 := by decide
  rcases family_descends (prefixWord ++ tailWord_726333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726337 : List Nat := [1, 2, 5, 2, 1, 1, 3, 5]
def baseStart_726337 : Nat := 118140960795 + 726337 * 2 ^ 59
def prefixEnd_726337 : Nat := 4983230072969 + 3 ^ 40 * 726337 * 2
def baseEnd_726337 : Nat := 110506666116986647954709

theorem tailTrace_726337 : CollatzResearch.WordTrace tailWord_726337 prefixEnd_726337 110506666116986647954709 := by
  unfold tailWord_726337
  simp only [CollatzResearch.WordTrace]
  refine ⟨26491686769612572328705265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17661124513075048219136843 26491686769612572328705265)
  ·
    refine ⟨19868765077209429246528949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26491686769612572328705265 19868765077209429246528949)
    ·
      refine ⟨1862696725988383991862089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19868765077209429246528949 1862696725988383991862089)
      ·
        refine ⟨1397022544491287993896567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1862696725988383991862089 1397022544491287993896567)
        ·
          refine ⟨2095533816736931990844851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397022544491287993896567 2095533816736931990844851)
          ·
            refine ⟨3143300725105397986267277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095533816736931990844851 3143300725105397986267277)
            ·
              refine ⟨1178737771914524244850229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3143300725105397986267277 1178737771914524244850229)
              ·
                refine ⟨110506666116986647954709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1178737771914524244850229 110506666116986647954709)
                ·
                  rfl

theorem cell20_726337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 5].length) (baseStart_726337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726337 prefixEnd_726337 := by exact prefixLift 726337
  have htrace : WordTrace (prefixWord ++ tailWord_726337) baseStart_726337 baseEnd_726337 := by
    simpa [prefixWord, tailWord_726337, baseEnd_726337] using wordTrace_append hprefix tailTrace_726337
  have hstable : (prefixWord ++ tailWord_726337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726337).length < 2 ^ (prefixWord ++ tailWord_726337).sum := by decide
  have hdescent : baseEnd_726337 < baseStart_726337 := by decide
  rcases family_descends (prefixWord ++ tailWord_726337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726368 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 2]
def baseStart_726368 : Nat := 118140960795 + 726368 * 2 ^ 59
def prefixEnd_726368 : Nat := 4983230072969 + 3 ^ 40 * 726368 * 2
def baseEnd_726368 : Nat := 331534147595661613830667

theorem tailTrace_726368 : CollatzResearch.WordTrace tailWord_726368 prefixEnd_726368 331534147595661613830667 := by
  unfold tailWord_726368
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246408716250132311541879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17661878288333509748722505 13246408716250132311541879)
  ·
    refine ⟨19869613074375198467312819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13246408716250132311541879 19869613074375198467312819)
    ·
      refine ⟨29804419611562797700969229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19869613074375198467312819 29804419611562797700969229)
      ·
        refine ⟨11176657354336049137863461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29804419611562797700969229 11176657354336049137863461)
        ·
          refine ⟨2095623253938009213349399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11176657354336049137863461 2095623253938009213349399)
          ·
            refine ⟨3143434880907013820024099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095623253938009213349399 3143434880907013820024099)
            ·
              refine ⟨4715152321360520730036149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143434880907013820024099 4715152321360520730036149)
              ·
                refine ⟨442045530127548818440889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4715152321360520730036149 442045530127548818440889)
                ·
                  refine ⟨331534147595661613830667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442045530127548818440889 331534147595661613830667)
                  ·
                    rfl

theorem cell20_726368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_726368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726368 prefixEnd_726368 := by exact prefixLift 726368
  have htrace : WordTrace (prefixWord ++ tailWord_726368) baseStart_726368 baseEnd_726368 := by
    simpa [prefixWord, tailWord_726368, baseEnd_726368] using wordTrace_append hprefix tailTrace_726368
  have hstable : (prefixWord ++ tailWord_726368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726368).length < 2 ^ (prefixWord ++ tailWord_726368).sum := by decide
  have hdescent : baseEnd_726368 < baseStart_726368 := by decide
  rcases family_descends (prefixWord ++ tailWord_726368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726378 : List Nat := [3, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_726378 : Nat := 118140960795 + 726378 * 2 ^ 59
def prefixEnd_726378 : Nat := 4983230072969 + 3 ^ 40 * 726378 * 2
def baseEnd_726378 : Nat := 331538711868146023497293

theorem tailTrace_726378 : CollatzResearch.WordTrace tailWord_726378 prefixEnd_726378 331538711868146023497293 := by
  unfold tailWord_726378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623295540616009082736947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17662121441642690887298525 6623295540616009082736947)
  ·
    refine ⟨9934943310924013624105421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6623295540616009082736947 9934943310924013624105421)
    ·
      refine ⟨3725603741596505109039533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9934943310924013624105421 3725603741596505109039533)
      ·
        refine ⟨1397101403098689415889825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3725603741596505109039533 1397101403098689415889825)
        ·
          refine ⟨1047826052324017061917369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397101403098689415889825 1047826052324017061917369)
          ·
            refine ⟨785869539243012796438027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047826052324017061917369 785869539243012796438027)
            ·
              refine ⟨1178804308864519194657041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785869539243012796438027 1178804308864519194657041)
              ·
                refine ⟨884103231648389395992781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178804308864519194657041 884103231648389395992781)
                ·
                  refine ⟨331538711868146023497293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884103231648389395992781 331538711868146023497293)
                  ·
                    rfl

theorem cell20_726378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_726378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726378 prefixEnd_726378 := by exact prefixLift 726378
  have htrace : WordTrace (prefixWord ++ tailWord_726378) baseStart_726378 baseEnd_726378 := by
    simpa [prefixWord, tailWord_726378, baseEnd_726378] using wordTrace_append hprefix tailTrace_726378
  have hstable : (prefixWord ++ tailWord_726378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726378).length < 2 ^ (prefixWord ++ tailWord_726378).sum := by decide
  have hdescent : baseEnd_726378 < baseStart_726378 := by decide
  rcases family_descends (prefixWord ++ tailWord_726378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726417 : List Nat := [1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_726417 : Nat := 118140960795 + 726417 * 2 ^ 59
def prefixEnd_726417 : Nat := 4983230072969 + 3 ^ 40 * 726417 * 2
def baseEnd_726417 : Nat := 110518837510278407065711

theorem tailTrace_726417 : CollatzResearch.WordTrace tailWord_726417 prefixEnd_726417 110518837510278407065711 := by
  unfold tailWord_726417
  simp only [CollatzResearch.WordTrace]
  refine ⟨26494604609322745991617505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17663069739548497327745003 26494604609322745991617505)
  ·
    refine ⟨19870953456992059493713129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26494604609322745991617505 19870953456992059493713129)
    ·
      refine ⟨14903215092744044620284847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19870953456992059493713129 14903215092744044620284847)
      ·
        refine ⟨22354822639116066930427271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14903215092744044620284847 22354822639116066930427271)
        ·
          refine ⟨33532233958674100395640907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22354822639116066930427271 33532233958674100395640907)
          ·
            refine ⟨50298350938011150593461361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33532233958674100395640907 50298350938011150593461361)
            ·
              refine ⟨37723763203508362945096021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50298350938011150593461361 37723763203508362945096021)
              ·
                refine ⟨110518837510278407065711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37723763203508362945096021 110518837510278407065711)
                ·
                  rfl

theorem cell20_726417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_726417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726417 prefixEnd_726417 := by exact prefixLift 726417
  have htrace : WordTrace (prefixWord ++ tailWord_726417) baseStart_726417 baseEnd_726417 := by
    simpa [prefixWord, tailWord_726417, baseEnd_726417] using wordTrace_append hprefix tailTrace_726417
  have hstable : (prefixWord ++ tailWord_726417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726417).length < 2 ^ (prefixWord ++ tailWord_726417).sum := by decide
  have hdescent : baseEnd_726417 < baseStart_726417 := by decide
  rcases family_descends (prefixWord ++ tailWord_726417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726420 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_726420 : Nat := 118140960795 + 726420 * 2 ^ 59
def prefixEnd_726420 : Nat := 4983230072969 + 3 ^ 40 * 726420 * 2
def baseEnd_726420 : Nat := 331557881812580544097121

theorem tailTrace_726420 : CollatzResearch.WordTrace tailWord_726420 prefixEnd_726420 331557881812580544097121 := by
  unfold tailWord_726420
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247357014155938751988357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17663142685541251669317809 13247357014155938751988357)
  ·
    refine ⟨2483879440154238515997817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13247357014155938751988357 2483879440154238515997817)
    ·
      refine ⟨1862909580115678886998363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2483879440154238515997817 1862909580115678886998363)
      ·
        refine ⟨2794364370173518330497545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1862909580115678886998363 2794364370173518330497545)
        ·
          refine ⟨2095773277630138747873159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2794364370173518330497545 2095773277630138747873159)
          ·
            refine ⟨3143659916445208121809739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095773277630138747873159 3143659916445208121809739)
            ·
              refine ⟨4715489874667812182714609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3143659916445208121809739 4715489874667812182714609)
              ·
                refine ⟨3536617406000859137035957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4715489874667812182714609 3536617406000859137035957)
                ·
                  refine ⟨331557881812580544097121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3536617406000859137035957 331557881812580544097121)
                  ·
                    rfl

theorem cell20_726420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_726420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726420 prefixEnd_726420 := by exact prefixLift 726420
  have htrace : WordTrace (prefixWord ++ tailWord_726420) baseStart_726420 baseEnd_726420 := by
    simpa [prefixWord, tailWord_726420, baseEnd_726420] using wordTrace_append hprefix tailTrace_726420
  have hstable : (prefixWord ++ tailWord_726420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726420).length < 2 ^ (prefixWord ++ tailWord_726420).sum := by decide
  have hdescent : baseEnd_726420 < baseStart_726420 := by decide
  rcases family_descends (prefixWord ++ tailWord_726420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726430 : List Nat := [4, 3, 1, 2, 2, 2, 6]
def baseStart_726430 : Nat := 118140960795 + 726430 * 2 ^ 59
def prefixEnd_726430 : Nat := 4983230072969 + 3 ^ 40 * 726430 * 2
def baseEnd_726430 : Nat := 36840271787229439307083

theorem tailTrace_726430 : CollatzResearch.WordTrace tailWord_726430 prefixEnd_726430 36840271787229439307083 := by
  unfold tailWord_726430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311884844784456151480093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17663385838850432807893829 3311884844784456151480093)
  ·
    refine ⟨1241956816794171056805035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3311884844784456151480093 1241956816794171056805035)
    ·
      refine ⟨1862935225191256585207553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1241956816794171056805035 1862935225191256585207553)
      ·
        refine ⟨1397201418893442438905665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1862935225191256585207553 1397201418893442438905665)
        ·
          refine ⟨1047901064170081829179249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397201418893442438905665 1047901064170081829179249)
          ·
            refine ⟨785925798127561371884437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047901064170081829179249 785925798127561371884437)
            ·
              refine ⟨36840271787229439307083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 785925798127561371884437 36840271787229439307083)
              ·
                rfl

theorem cell20_726430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 6].length) (baseStart_726430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726430 prefixEnd_726430 := by exact prefixLift 726430
  have htrace : WordTrace (prefixWord ++ tailWord_726430) baseStart_726430 baseEnd_726430 := by
    simpa [prefixWord, tailWord_726430, baseEnd_726430] using wordTrace_append hprefix tailTrace_726430
  have hstable : (prefixWord ++ tailWord_726430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726430).length < 2 ^ (prefixWord ++ tailWord_726430).sum := by decide
  have hdescent : baseEnd_726430 < baseStart_726430 := by decide
  rcases family_descends (prefixWord ++ tailWord_726430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726434 : List Nat := [3, 3, 1, 2, 1, 2, 8]
def baseStart_726434 : Nat := 118140960795 + 726434 * 2 ^ 59
def prefixEnd_726434 : Nat := 4983230072969 + 3 ^ 40 * 726434 * 2
def baseEnd_726434 : Nat := 36840474643784301958933

theorem tailTrace_726434 : CollatzResearch.WordTrace tailWord_726434 prefixEnd_726434 36840474643784301958933 := by
  unfold tailWord_726434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623806162565289473746589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17663483100174105263324237 6623806162565289473746589)
  ·
    refine ⟨2483927310961983552654971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6623806162565289473746589 2483927310961983552654971)
    ·
      refine ⟨3725890966442975328982457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483927310961983552654971 3725890966442975328982457)
      ·
        refine ⟨2794418224832231496736843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3725890966442975328982457 2794418224832231496736843)
        ·
          refine ⟨4191627337248347245105265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794418224832231496736843 4191627337248347245105265)
          ·
            refine ⟨3143720502936260433828949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4191627337248347245105265 3143720502936260433828949)
            ·
              refine ⟨36840474643784301958933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3143720502936260433828949 36840474643784301958933)
              ·
                rfl

theorem cell20_726434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_726434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726434 prefixEnd_726434 := by exact prefixLift 726434
  have htrace : WordTrace (prefixWord ++ tailWord_726434) baseStart_726434 baseEnd_726434 := by
    simpa [prefixWord, tailWord_726434, baseEnd_726434] using wordTrace_append hprefix tailTrace_726434
  have hstable : (prefixWord ++ tailWord_726434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726434).length < 2 ^ (prefixWord ++ tailWord_726434).sum := by decide
  have hdescent : baseEnd_726434 < baseStart_726434 := by decide
  rcases family_descends (prefixWord ++ tailWord_726434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726440 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 4]
def baseStart_726440 : Nat := 118140960795 + 726440 * 2 ^ 59
def prefixEnd_726440 : Nat := 4983230072969 + 3 ^ 40 * 726440 * 2
def baseEnd_726440 : Nat := 331567010357549363430373

theorem tailTrace_726440 : CollatzResearch.WordTrace tailWord_726440 prefixEnd_726440 331567010357549363430373 := by
  unfold tailWord_726440
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247721744119710459852387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17663628992159613946469849 13247721744119710459852387)
  ·
    refine ⟨19871582616179565689778581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13247721744119710459852387 19871582616179565689778581)
    ·
      refine ⟨931480435133417141708371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19871582616179565689778581 931480435133417141708371)
      ·
        refine ⟨1397220652700125712562557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931480435133417141708371 1397220652700125712562557)
        ·
          refine ⟨523957744762547142210959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1397220652700125712562557 523957744762547142210959)
          ·
            refine ⟨785936617143820713316439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523957744762547142210959 785936617143820713316439)
            ·
              refine ⟨1178904925715731069974659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785936617143820713316439 1178904925715731069974659)
              ·
                refine ⟨1768357388573596604961989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178904925715731069974659 1768357388573596604961989)
                ·
                  refine ⟨331567010357549363430373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768357388573596604961989 331567010357549363430373)
                  ·
                    rfl

theorem cell20_726440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_726440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726440 prefixEnd_726440 := by exact prefixLift 726440
  have htrace : WordTrace (prefixWord ++ tailWord_726440) baseStart_726440 baseEnd_726440 := by
    simpa [prefixWord, tailWord_726440, baseEnd_726440] using wordTrace_append hprefix tailTrace_726440
  have hstable : (prefixWord ++ tailWord_726440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726440).length < 2 ^ (prefixWord ++ tailWord_726440).sum := by decide
  have hdescent : baseEnd_726440 < baseStart_726440 := by decide
  rcases family_descends (prefixWord ++ tailWord_726440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726448 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_726448 : Nat := 118140960795 + 726448 * 2 ^ 59
def prefixEnd_726448 : Nat := 4983230072969 + 3 ^ 40 * 726448 * 2
def baseEnd_726448 : Nat := 331570661775536891163673

theorem tailTrace_726448 : CollatzResearch.WordTrace tailWord_726448 prefixEnd_726448 331570661775536891163673 := by
  unfold tailWord_726448
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247867636105219142997999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17663823514806958857330665 13247867636105219142997999)
  ·
    refine ⟨19871801454157828714496999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13247867636105219142997999 19871801454157828714496999)
    ·
      refine ⟨29807702181236743071745499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19871801454157828714496999 29807702181236743071745499)
      ·
        refine ⟨44711553271855114607618249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29807702181236743071745499 44711553271855114607618249)
        ·
          refine ⟨33533664953891335955713687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44711553271855114607618249 33533664953891335955713687)
          ·
            refine ⟨50300497430837003933570531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33533664953891335955713687 50300497430837003933570531)
            ·
              refine ⟨75450746146255505900355797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50300497430837003933570531 75450746146255505900355797)
              ·
                refine ⟨1768376862802863419539589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 75450746146255505900355797 1768376862802863419539589)
                ·
                  refine ⟨331570661775536891163673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768376862802863419539589 331570661775536891163673)
                  ·
                    rfl

theorem cell20_726448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_726448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726448 prefixEnd_726448 := by exact prefixLift 726448
  have htrace : WordTrace (prefixWord ++ tailWord_726448) baseStart_726448 baseEnd_726448 := by
    simpa [prefixWord, tailWord_726448, baseEnd_726448] using wordTrace_append hprefix tailTrace_726448
  have hstable : (prefixWord ++ tailWord_726448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726448).length < 2 ^ (prefixWord ++ tailWord_726448).sum := by decide
  have hdescent : baseEnd_726448 < baseStart_726448 := by decide
  rcases family_descends (prefixWord ++ tailWord_726448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726499 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 2]
def baseStart_726499 : Nat := 118140960795 + 726499 * 2 ^ 59
def prefixEnd_726499 : Nat := 4983230072969 + 3 ^ 40 * 726499 * 2
def baseEnd_726499 : Nat := 331593939565207380463465

theorem tailTrace_726499 : CollatzResearch.WordTrace tailWord_726499 prefixEnd_726499 331593939565207380463465 := by
  unfold tailWord_726499
  simp only [CollatzResearch.WordTrace]
  refine ⟨26497595395025673996102551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17665063596683782664068367 26497595395025673996102551)
  ·
    refine ⟨39746393092538510994153827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26497595395025673996102551 39746393092538510994153827)
    ·
      refine ⟨59619589638807766491230741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39746393092538510994153827 59619589638807766491230741)
      ·
        refine ⟨2794668264319114054276441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59619589638807766491230741 2794668264319114054276441)
        ·
          refine ⟨2096001198239335540707331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2794668264319114054276441 2096001198239335540707331)
          ·
            refine ⟨3144001797359003311060997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096001198239335540707331 3144001797359003311060997)
            ·
              refine ⟨589500337004813120823937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3144001797359003311060997 589500337004813120823937)
              ·
                refine ⟨442125252753609840617953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589500337004813120823937 442125252753609840617953)
                ·
                  refine ⟨331593939565207380463465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442125252753609840617953 331593939565207380463465)
                  ·
                    rfl

theorem cell20_726499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 2].length) (baseStart_726499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726499 prefixEnd_726499 := by exact prefixLift 726499
  have htrace : WordTrace (prefixWord ++ tailWord_726499) baseStart_726499 baseEnd_726499 := by
    simpa [prefixWord, tailWord_726499, baseEnd_726499] using wordTrace_append hprefix tailTrace_726499
  have hstable : (prefixWord ++ tailWord_726499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726499).length < 2 ^ (prefixWord ++ tailWord_726499).sum := by decide
  have hdescent : baseEnd_726499 < baseStart_726499 := by decide
  rcases family_descends (prefixWord ++ tailWord_726499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726506 : List Nat := [3, 1, 3, 1, 5, 1, 1, 5]
def baseStart_726506 : Nat := 118140960795 + 726506 * 2 ^ 59
def prefixEnd_726506 : Nat := 4983230072969 + 3 ^ 40 * 726506 * 2
def baseEnd_726506 : Nat := 110532378185315489076701

theorem tailTrace_726506 : CollatzResearch.WordTrace tailWord_726506 prefixEnd_726506 110532378185315489076701 := by
  unfold tailWord_726506
  simp only [CollatzResearch.WordTrace]
  refine ⟨6624462676500078547901843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17665233804000209461071581 6624462676500078547901843)
  ·
    refine ⟨9936694014750117821852765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6624462676500078547901843 9936694014750117821852765)
    ·
      refine ⟨3726260255531294183194787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9936694014750117821852765 3726260255531294183194787)
      ·
        refine ⟨5589390383296941274792181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726260255531294183194787 5589390383296941274792181)
        ·
          refine ⟨524005348434088244511767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5589390383296941274792181 524005348434088244511767)
          ·
            refine ⟨786008022651132366767651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524005348434088244511767 786008022651132366767651)
            ·
              refine ⟨1179012033976698550151477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786008022651132366767651 1179012033976698550151477)
              ·
                refine ⟨110532378185315489076701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1179012033976698550151477 110532378185315489076701)
                ·
                  rfl

theorem cell20_726506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_726506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726506 prefixEnd_726506 := by exact prefixLift 726506
  have htrace : WordTrace (prefixWord ++ tailWord_726506) baseStart_726506 baseEnd_726506 := by
    simpa [prefixWord, tailWord_726506, baseEnd_726506] using wordTrace_append hprefix tailTrace_726506
  have hstable : (prefixWord ++ tailWord_726506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726506).length < 2 ^ (prefixWord ++ tailWord_726506).sum := by decide
  have hdescent : baseEnd_726506 < baseStart_726506 := by decide
  rcases family_descends (prefixWord ++ tailWord_726506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726524 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_726524 : Nat := 118140960795 + 726524 * 2 ^ 59
def prefixEnd_726524 : Nat := 4983230072969 + 3 ^ 40 * 726524 * 2
def baseEnd_726524 : Nat := 331605350246418404630029

theorem tailTrace_726524 : CollatzResearch.WordTrace tailWord_726524 prefixEnd_726524 331605350246418404630029 := by
  unfold tailWord_726524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249253609967551632881313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17665671479956735510508417 13249253609967551632881313)
  ·
    refine ⟨9936940207475663724660985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13249253609967551632881313 9936940207475663724660985)
    ·
      refine ⟨7452705155606747793495739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9936940207475663724660985 7452705155606747793495739)
      ·
        refine ⟨11179057733410121690243609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452705155606747793495739 11179057733410121690243609)
        ·
          refine ⟨8384293300057591267682707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11179057733410121690243609 8384293300057591267682707)
          ·
            refine ⟨12576439950086386901524061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8384293300057591267682707 12576439950086386901524061)
            ·
              refine ⟨4716164981282395088071523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12576439950086386901524061 4716164981282395088071523)
              ·
                refine ⟨7074247471923592632107285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716164981282395088071523 7074247471923592632107285)
                ·
                  refine ⟨331605350246418404630029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7074247471923592632107285 331605350246418404630029)
                  ·
                    rfl

theorem cell20_726524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_726524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726524 prefixEnd_726524 := by exact prefixLift 726524
  have htrace : WordTrace (prefixWord ++ tailWord_726524) baseStart_726524 baseEnd_726524 := by
    simpa [prefixWord, tailWord_726524, baseEnd_726524] using wordTrace_append hprefix tailTrace_726524
  have hstable : (prefixWord ++ tailWord_726524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726524).length < 2 ^ (prefixWord ++ tailWord_726524).sum := by decide
  have hdescent : baseEnd_726524 < baseStart_726524 := by decide
  rcases family_descends (prefixWord ++ tailWord_726524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726568 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 3]
def baseStart_726568 : Nat := 118140960795 + 726568 * 2 ^ 59
def prefixEnd_726568 : Nat := 4983230072969 + 3 ^ 40 * 726568 * 2
def baseEnd_726568 : Nat := 331625433045349807163183

theorem tailTrace_726568 : CollatzResearch.WordTrace tailWord_726568 prefixEnd_726568 331625433045349807163183 := by
  unfold tailWord_726568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13250056015887849390182179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17666741354517132520242905 13250056015887849390182179)
  ·
    refine ⟨19875084023831774085273269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13250056015887849390182179 19875084023831774085273269)
    ·
      refine ⟨1863289127234228820494369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19875084023831774085273269 1863289127234228820494369)
      ·
        refine ⟨1397466845425671615370777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863289127234228820494369 1397466845425671615370777)
        ·
          refine ⟨1048100134069253711528083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397466845425671615370777 1048100134069253711528083)
          ·
            refine ⟨1572150201103880567292125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048100134069253711528083 1572150201103880567292125)
            ·
              refine ⟨589556325413955212734547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1572150201103880567292125 589556325413955212734547)
              ·
                refine ⟨884334488120932819101821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589556325413955212734547 884334488120932819101821)
                ·
                  refine ⟨331625433045349807163183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884334488120932819101821 331625433045349807163183)
                  ·
                    rfl

theorem cell20_726568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_726568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726568 prefixEnd_726568 := by exact prefixLift 726568
  have htrace : WordTrace (prefixWord ++ tailWord_726568) baseStart_726568 baseEnd_726568 := by
    simpa [prefixWord, tailWord_726568, baseEnd_726568] using wordTrace_append hprefix tailTrace_726568
  have hstable : (prefixWord ++ tailWord_726568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726568).length < 2 ^ (prefixWord ++ tailWord_726568).sum := by decide
  have hdescent : baseEnd_726568 < baseStart_726568 := by decide
  rcases family_descends (prefixWord ++ tailWord_726568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726593 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 7]
def baseStart_726593 : Nat := 118140960795 + 726593 * 2 ^ 59
def prefixEnd_726593 : Nat := 4983230072969 + 3 ^ 40 * 726593 * 2
def baseEnd_726593 : Nat := 331636843726560831329747

theorem tailTrace_726593 : CollatzResearch.WordTrace tailWord_726593 prefixEnd_726593 331636843726560831329747 := by
  unfold tailWord_726593
  simp only [CollatzResearch.WordTrace]
  refine ⟨26501023856685128050024433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17667349237790085366682955 26501023856685128050024433)
  ·
    refine ⟨19875767892513846037518325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26501023856685128050024433 19875767892513846037518325)
    ·
      refine ⟨1863353239923173066017343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19875767892513846037518325 1863353239923173066017343)
      ·
        refine ⟨2795029859884759599026015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863353239923173066017343 2795029859884759599026015)
        ·
          refine ⟨4192544789827139398539023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795029859884759599026015 4192544789827139398539023)
          ·
            refine ⟨6288817184740709097808535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192544789827139398539023 6288817184740709097808535)
            ·
              refine ⟨9433225777111063646712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6288817184740709097808535 9433225777111063646712803)
              ·
                refine ⟨14149838665666595470069205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433225777111063646712803 14149838665666595470069205)
                ·
                  refine ⟨331636843726560831329747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14149838665666595470069205 331636843726560831329747)
                  ·
                    rfl

theorem cell20_726593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_726593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726593 prefixEnd_726593 := by exact prefixLift 726593
  have htrace : WordTrace (prefixWord ++ tailWord_726593) baseStart_726593 baseEnd_726593 := by
    simpa [prefixWord, tailWord_726593, baseEnd_726593] using wordTrace_append hprefix tailTrace_726593
  have hstable : (prefixWord ++ tailWord_726593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726593).length < 2 ^ (prefixWord ++ tailWord_726593).sum := by decide
  have hdescent : baseEnd_726593 < baseStart_726593 := by decide
  rcases family_descends (prefixWord ++ tailWord_726593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726617 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 2]
def baseStart_726617 : Nat := 118140960795 + 726617 * 2 ^ 59
def prefixEnd_726617 : Nat := 4983230072969 + 3 ^ 40 * 726617 * 2
def baseEnd_726617 : Nat := 331647797980523414529649

theorem tailTrace_726617 : CollatzResearch.WordTrace tailWord_726617 prefixEnd_726617 331647797980523414529649 := by
  unfold tailWord_726617
  simp only [CollatzResearch.WordTrace]
  refine ⟨26501899208598180148898105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17667932805732120099265403 26501899208598180148898105)
  ·
    refine ⟨19876424406448635111673579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26501899208598180148898105 19876424406448635111673579)
    ·
      refine ⟨29814636609672952667510369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19876424406448635111673579 29814636609672952667510369)
      ·
        refine ⟨22360977457254714500632777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29814636609672952667510369 22360977457254714500632777)
        ·
          refine ⟨16770733092941035875474583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22360977457254714500632777 16770733092941035875474583)
          ·
            refine ⟨25156099639411553813211875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16770733092941035875474583 25156099639411553813211875)
            ·
              refine ⟨37734149459117330719817813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25156099639411553813211875 37734149459117330719817813)
              ·
                refine ⟨442197063974031219372865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 37734149459117330719817813 442197063974031219372865)
                ·
                  refine ⟨331647797980523414529649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442197063974031219372865 331647797980523414529649)
                  ·
                    rfl

theorem cell20_726617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_726617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726617 prefixEnd_726617 := by exact prefixLift 726617
  have htrace : WordTrace (prefixWord ++ tailWord_726617) baseStart_726617 baseEnd_726617 := by
    simpa [prefixWord, tailWord_726617, baseEnd_726617] using wordTrace_append hprefix tailTrace_726617
  have hstable : (prefixWord ++ tailWord_726617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726617).length < 2 ^ (prefixWord ++ tailWord_726617).sum := by decide
  have hdescent : baseEnd_726617 < baseStart_726617 := by decide
  rcases family_descends (prefixWord ++ tailWord_726617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726627 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 3]
def baseStart_726627 : Nat := 118140960795 + 726627 * 2 ^ 59
def prefixEnd_726627 : Nat := 4983230072969 + 3 ^ 40 * 726627 * 2
def baseEnd_726627 : Nat := 331652362253007824196275

theorem tailTrace_726627 : CollatzResearch.WordTrace tailWord_726627 prefixEnd_726627 331652362253007824196275 := by
  unfold tailWord_726627
  simp only [CollatzResearch.WordTrace]
  refine ⟨26502263938561951856762135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17668175959041301237841423 26502263938561951856762135)
  ·
    refine ⟨39753395907842927785143203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26502263938561951856762135 39753395907842927785143203)
    ·
      refine ⟨59630093861764391677714805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39753395907842927785143203 59630093861764391677714805)
      ·
        refine ⟨5590321299540411719785763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59630093861764391677714805 5590321299540411719785763)
        ·
          refine ⟨8385481949310617579678645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5590321299540411719785763 8385481949310617579678645)
          ·
            refine ⟨786138932747870398094873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8385481949310617579678645 786138932747870398094873)
            ·
              refine ⟨589604199560902798571155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786138932747870398094873 589604199560902798571155)
              ·
                refine ⟨884406299341354197856733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589604199560902798571155 884406299341354197856733)
                ·
                  refine ⟨331652362253007824196275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884406299341354197856733 331652362253007824196275)
                  ·
                    rfl

theorem cell20_726627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_726627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726627 prefixEnd_726627 := by exact prefixLift 726627
  have htrace : WordTrace (prefixWord ++ tailWord_726627) baseStart_726627 baseEnd_726627 := by
    simpa [prefixWord, tailWord_726627, baseEnd_726627] using wordTrace_append hprefix tailTrace_726627
  have hstable : (prefixWord ++ tailWord_726627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726627).length < 2 ^ (prefixWord ++ tailWord_726627).sum := by decide
  have hdescent : baseEnd_726627 < baseStart_726627 := by decide
  rcases family_descends (prefixWord ++ tailWord_726627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726752 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_726752 : Nat := 118140960795 + 726752 * 2 ^ 59
def prefixEnd_726752 : Nat := 4983230072969 + 3 ^ 40 * 726752 * 2
def baseEnd_726752 : Nat := 331709415659062945029097

theorem tailTrace_726752 : CollatzResearch.WordTrace tailWord_726752 prefixEnd_726752 331709415659062945029097 := by
  unfold tailWord_726752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253411531554549102531255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17671215375406065470041673 13253411531554549102531255)
  ·
    refine ⟨19880117297331823653796883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13253411531554549102531255 19880117297331823653796883)
    ·
      refine ⟨29820175945997735480695325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19880117297331823653796883 29820175945997735480695325)
      ·
        refine ⟨11182565979749150805260747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29820175945997735480695325 11182565979749150805260747)
        ·
          refine ⟨16773848969623726207891121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11182565979749150805260747 16773848969623726207891121)
          ·
            refine ⟨12580386727217794655918341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16773848969623726207891121 12580386727217794655918341)
            ·
              refine ⟨2358822511353336497984689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12580386727217794655918341 2358822511353336497984689)
              ·
                refine ⟨1769116883515002373488517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358822511353336497984689 1769116883515002373488517)
                ·
                  refine ⟨331709415659062945029097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1769116883515002373488517 331709415659062945029097)
                  ·
                    rfl

theorem cell20_726752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_726752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726752 prefixEnd_726752 := by exact prefixLift 726752
  have htrace : WordTrace (prefixWord ++ tailWord_726752) baseStart_726752 baseEnd_726752 := by
    simpa [prefixWord, tailWord_726752, baseEnd_726752] using wordTrace_append hprefix tailTrace_726752
  have hstable : (prefixWord ++ tailWord_726752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726752).length < 2 ^ (prefixWord ++ tailWord_726752).sum := by decide
  have hdescent : baseEnd_726752 < baseStart_726752 := by decide
  rcases family_descends (prefixWord ++ tailWord_726752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726765 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 2]
def baseStart_726765 : Nat := 118140960795 + 726765 * 2 ^ 59
def prefixEnd_726765 : Nat := 4983230072969 + 3 ^ 40 * 726765 * 2
def baseEnd_726765 : Nat := 331715349213292677595711

theorem tailTrace_726765 : CollatzResearch.WordTrace tailWord_726765 prefixEnd_726765 331715349213292677595711 := by
  unfold tailWord_726765
  simp only [CollatzResearch.WordTrace]
  refine ⟨26507297212062001425285749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17671531474708000950190499 26507297212062001425285749)
  ·
    refine ⟨2485059113630812633620539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26507297212062001425285749 2485059113630812633620539)
    ·
      refine ⟨3727588670446218950430809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485059113630812633620539 3727588670446218950430809)
      ·
        refine ⟨2795691502834664212823107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3727588670446218950430809 2795691502834664212823107)
        ·
          refine ⟨4193537254251996319234661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795691502834664212823107 4193537254251996319234661)
          ·
            refine ⟨786288235172249309856499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4193537254251996319234661 786288235172249309856499)
            ·
              refine ⟨1179432352758373964784749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786288235172249309856499 1179432352758373964784749)
              ·
                refine ⟨442287132284390236794281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1179432352758373964784749 442287132284390236794281)
                ·
                  refine ⟨331715349213292677595711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442287132284390236794281 331715349213292677595711)
                  ·
                    rfl

theorem cell20_726765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_726765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726765 prefixEnd_726765 := by exact prefixLift 726765
  have htrace : WordTrace (prefixWord ++ tailWord_726765) baseStart_726765 baseEnd_726765 := by
    simpa [prefixWord, tailWord_726765, baseEnd_726765] using wordTrace_append hprefix tailTrace_726765
  have hstable : (prefixWord ++ tailWord_726765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726765).length < 2 ^ (prefixWord ++ tailWord_726765).sum := by decide
  have hdescent : baseEnd_726765 < baseStart_726765 := by decide
  rcases family_descends (prefixWord ++ tailWord_726765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726772 : List Nat := [2, 6, 1, 1, 1, 3, 6]
def baseStart_726772 : Nat := 118140960795 + 726772 * 2 ^ 59
def prefixEnd_726772 : Nat := 4983230072969 + 3 ^ 40 * 726772 * 2
def baseEnd_726772 : Nat := 36857616022670196040261

theorem tailTrace_726772 : CollatzResearch.WordTrace tailWord_726772 prefixEnd_726772 36857616022670196040261 := by
  unfold tailWord_726772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253776261518320810395285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17671701682024427747193713 13253776261518320810395285)
  ·
    refine ⟨621270762258671287987279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13253776261518320810395285 621270762258671287987279)
    ·
      refine ⟨931906143388006931980919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621270762258671287987279 931906143388006931980919)
      ·
        refine ⟨1397859215082010397971379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931906143388006931980919 1397859215082010397971379)
        ·
          refine ⟨2096788822623015596957069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397859215082010397971379 2096788822623015596957069)
          ·
            refine ⟨786295808483630848858901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2096788822623015596957069 786295808483630848858901)
            ·
              refine ⟨36857616022670196040261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 786295808483630848858901 36857616022670196040261)
              ·
                rfl

theorem cell20_726772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 6].length) (baseStart_726772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726772 prefixEnd_726772 := by exact prefixLift 726772
  have htrace : WordTrace (prefixWord ++ tailWord_726772) baseStart_726772 baseEnd_726772 := by
    simpa [prefixWord, tailWord_726772, baseEnd_726772] using wordTrace_append hprefix tailTrace_726772
  have hstable : (prefixWord ++ tailWord_726772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726772).length < 2 ^ (prefixWord ++ tailWord_726772).sum := by decide
  have hdescent : baseEnd_726772 < baseStart_726772 := by decide
  rcases family_descends (prefixWord ++ tailWord_726772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726782 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_726782 : Nat := 118140960795 + 726782 * 2 ^ 59
def prefixEnd_726782 : Nat := 4983230072969 + 3 ^ 40 * 726782 * 2
def baseEnd_726782 : Nat := 331723108476516174028975

theorem tailTrace_726782 : CollatzResearch.WordTrace tailWord_726782 prefixEnd_726782 331723108476516174028975 := by
  unfold tailWord_726782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3313489656625051666081825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17671944835333608885769733 3313489656625051666081825)
  ·
    refine ⟨2485117242468788749561369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3313489656625051666081825 2485117242468788749561369)
    ·
      refine ⟨1863837931851591562171027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2485117242468788749561369 1863837931851591562171027)
      ·
        refine ⟨2795756897777387343256541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863837931851591562171027 2795756897777387343256541)
        ·
          refine ⟨1048408836666520253721203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2795756897777387343256541 1048408836666520253721203)
          ·
            refine ⟨1572613254999780380581805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048408836666520253721203 1572613254999780380581805)
            ·
              refine ⟨589729970624917642718177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1572613254999780380581805 589729970624917642718177)
              ·
                refine ⟨442297477968688232038633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589729970624917642718177 442297477968688232038633)
                ·
                  refine ⟨331723108476516174028975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442297477968688232038633 331723108476516174028975)
                  ·
                    rfl

theorem cell20_726782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_726782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726782 prefixEnd_726782 := by exact prefixLift 726782
  have htrace : WordTrace (prefixWord ++ tailWord_726782) baseStart_726782 baseEnd_726782 := by
    simpa [prefixWord, tailWord_726782, baseEnd_726782] using wordTrace_append hprefix tailTrace_726782
  have hstable : (prefixWord ++ tailWord_726782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726782).length < 2 ^ (prefixWord ++ tailWord_726782).sum := by decide
  have hdescent : baseEnd_726782 < baseStart_726782 := by decide
  rcases family_descends (prefixWord ++ tailWord_726782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726835 : List Nat := [1, 1, 1, 2, 7, 8]
def baseStart_726835 : Nat := 118140960795 + 726835 * 2 ^ 59
def prefixEnd_726835 : Nat := 4983230072969 + 3 ^ 40 * 726835 * 2
def baseEnd_726835 : Nat := 12286937004469760935633

theorem tailTrace_726835 : CollatzResearch.WordTrace tailWord_726835 prefixEnd_726835 12286937004469760935633 := by
  unfold tailWord_726835
  simp only [CollatzResearch.WordTrace]
  refine ⟨26509850321808403380333959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17673233547872268920222639 26509850321808403380333959)
  ·
    refine ⟨39764775482712605070500939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26509850321808403380333959 39764775482712605070500939)
    ·
      refine ⟨59647163224068907605751409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39764775482712605070500939 59647163224068907605751409)
      ·
        refine ⟨44735372418051680704313557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59647163224068907605751409 44735372418051680704313557)
        ·
          refine ⟨1048485291048086266507349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 44735372418051680704313557 1048485291048086266507349)
          ·
            refine ⟨12286937004469760935633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1048485291048086266507349 12286937004469760935633)
            ·
              rfl

theorem cell20_726835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 8].length) (baseStart_726835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726835 prefixEnd_726835 := by exact prefixLift 726835
  have htrace : WordTrace (prefixWord ++ tailWord_726835) baseStart_726835 baseEnd_726835 := by
    simpa [prefixWord, tailWord_726835, baseEnd_726835] using wordTrace_append hprefix tailTrace_726835
  have hstable : (prefixWord ++ tailWord_726835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726835).length < 2 ^ (prefixWord ++ tailWord_726835).sum := by decide
  have hdescent : baseEnd_726835 < baseStart_726835 := by decide
  rcases family_descends (prefixWord ++ tailWord_726835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726841 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 2]
def baseStart_726841 : Nat := 118140960795 + 726841 * 2 ^ 59
def prefixEnd_726841 : Nat := 4983230072969 + 3 ^ 40 * 726841 * 2
def baseEnd_726841 : Nat := 331750037684174191062067

theorem tailTrace_726841 : CollatzResearch.WordTrace tailWord_726841 prefixEnd_726841 331750037684174191062067 := by
  unfold tailWord_726841
  simp only [CollatzResearch.WordTrace]
  refine ⟨26510069159786666405052377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17673379439857777603368251 26510069159786666405052377)
  ·
    refine ⟨19882551869839999803789283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26510069159786666405052377 19882551869839999803789283)
    ·
      refine ⟨29823827804759999705683925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19882551869839999803789283 29823827804759999705683925)
      ·
        refine ⟨698995964174062493101967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29823827804759999705683925 698995964174062493101967)
        ·
          refine ⟨1048493946261093739652951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698995964174062493101967 1048493946261093739652951)
          ·
            refine ⟨1572740919391640609479427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048493946261093739652951 1572740919391640609479427)
            ·
              refine ⟨2359111379087460914219141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572740919391640609479427 2359111379087460914219141)
              ·
                refine ⟨442333383578898921416089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2359111379087460914219141 442333383578898921416089)
                ·
                  refine ⟨331750037684174191062067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442333383578898921416089 331750037684174191062067)
                  ·
                    rfl

theorem cell20_726841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_726841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726841 prefixEnd_726841 := by exact prefixLift 726841
  have htrace : WordTrace (prefixWord ++ tailWord_726841) baseStart_726841 baseEnd_726841 := by
    simpa [prefixWord, tailWord_726841, baseEnd_726841] using wordTrace_append hprefix tailTrace_726841
  have hstable : (prefixWord ++ tailWord_726841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726841).length < 2 ^ (prefixWord ++ tailWord_726841).sum := by decide
  have hdescent : baseEnd_726841 < baseStart_726841 := by decide
  rcases family_descends (prefixWord ++ tailWord_726841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726866 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_726866 : Nat := 118140960795 + 726866 * 2 ^ 59
def prefixEnd_726866 : Nat := 4983230072969 + 3 ^ 40 * 726866 * 2
def baseEnd_726866 : Nat := 331761448365385215228631

theorem tailTrace_726866 : CollatzResearch.WordTrace tailWord_726866 prefixEnd_726866 331761448365385215228631 := by
  unfold tailWord_726866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6627745246174023918678113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17673987323130730449808301 6627745246174023918678113)
  ·
    refine ⟨4970808934630517939008585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6627745246174023918678113 4970808934630517939008585)
    ·
      refine ⟨3728106700972888454256439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4970808934630517939008585 3728106700972888454256439)
      ·
        refine ⟨5592160051459332681384659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728106700972888454256439 5592160051459332681384659)
        ·
          refine ⟨8388240077188999022076989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592160051459332681384659 8388240077188999022076989)
          ·
            refine ⟨3145590028945874633278871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8388240077188999022076989 3145590028945874633278871)
            ·
              refine ⟨4718385043418811949918307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145590028945874633278871 4718385043418811949918307)
              ·
                refine ⟨7077577565128217924877461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4718385043418811949918307 7077577565128217924877461)
                ·
                  refine ⟨331761448365385215228631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7077577565128217924877461 331761448365385215228631)
                  ·
                    rfl

theorem cell20_726866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_726866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726866 prefixEnd_726866 := by exact prefixLift 726866
  have htrace : WordTrace (prefixWord ++ tailWord_726866) baseStart_726866 baseEnd_726866 := by
    simpa [prefixWord, tailWord_726866, baseEnd_726866] using wordTrace_append hprefix tailTrace_726866
  have hstable : (prefixWord ++ tailWord_726866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726866).length < 2 ^ (prefixWord ++ tailWord_726866).sum := by decide
  have hdescent : baseEnd_726866 < baseStart_726866 := by decide
  rcases family_descends (prefixWord ++ tailWord_726866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726910 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_726910 : Nat := 118140960795 + 726910 * 2 ^ 59
def prefixEnd_726910 : Nat := 4983230072969 + 3 ^ 40 * 726910 * 2
def baseEnd_726910 : Nat := 331781531164316617761785

theorem tailTrace_726910 : CollatzResearch.WordTrace tailWord_726910 prefixEnd_726910 331781531164316617761785 := by
  unfold tailWord_726910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314073224567086398664273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17675057197691127459542789 3314073224567086398664273)
  ·
    refine ⟨2485554918425314798998205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3314073224567086398664273 2485554918425314798998205)
    ·
      refine ⟨932083094409493049624327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2485554918425314798998205 932083094409493049624327)
      ·
        refine ⟨1398124641614239574436491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932083094409493049624327 1398124641614239574436491)
        ·
          refine ⟨2097186962421359361654737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398124641614239574436491 2097186962421359361654737)
          ·
            refine ⟨1572890221816019521241053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097186962421359361654737 1572890221816019521241053)
            ·
              refine ⟨589833833181007320465395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1572890221816019521241053 589833833181007320465395)
              ·
                refine ⟨884750749771510980698093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589833833181007320465395 884750749771510980698093)
                ·
                  refine ⟨331781531164316617761785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884750749771510980698093 331781531164316617761785)
                  ·
                    rfl

theorem cell20_726910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_726910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726910 prefixEnd_726910 := by exact prefixLift 726910
  have htrace : WordTrace (prefixWord ++ tailWord_726910) baseStart_726910 baseEnd_726910 := by
    simpa [prefixWord, tailWord_726910, baseEnd_726910] using wordTrace_append hprefix tailTrace_726910
  have hstable : (prefixWord ++ tailWord_726910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726910).length < 2 ^ (prefixWord ++ tailWord_726910).sum := by decide
  have hdescent : baseEnd_726910 < baseStart_726910 := by decide
  rcases family_descends (prefixWord ++ tailWord_726910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726938 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_726938 : Nat := 118140960795 + 726938 * 2 ^ 59
def prefixEnd_726938 : Nat := 4983230072969 + 3 ^ 40 * 726938 * 2
def baseEnd_726938 : Nat := 331794311127272964828337

theorem tailTrace_726938 : CollatzResearch.WordTrace tailWord_726938 prefixEnd_726938 331794311127272964828337 := by
  unfold tailWord_726938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6628401760108812992833367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17675738026956834647555645 6628401760108812992833367)
  ·
    refine ⟨9942602640163219489250051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6628401760108812992833367 9942602640163219489250051)
    ·
      refine ⟨14913903960244829233875077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9942602640163219489250051 14913903960244829233875077)
      ·
        refine ⟨2796356992545905481351577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14913903960244829233875077 2796356992545905481351577)
        ·
          refine ⟨2097267744409429111013683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2796356992545905481351577 2097267744409429111013683)
          ·
            refine ⟨3145901616614143666520525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097267744409429111013683 3145901616614143666520525)
            ·
              refine ⟨1179713106230303874945197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3145901616614143666520525 1179713106230303874945197)
              ·
                refine ⟨442392414836363953104449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1179713106230303874945197 442392414836363953104449)
                ·
                  refine ⟨331794311127272964828337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442392414836363953104449 331794311127272964828337)
                  ·
                    rfl

theorem cell20_726938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_726938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726938 prefixEnd_726938 := by exact prefixLift 726938
  have htrace : WordTrace (prefixWord ++ tailWord_726938) baseStart_726938 baseEnd_726938 := by
    simpa [prefixWord, tailWord_726938, baseEnd_726938] using wordTrace_append hprefix tailTrace_726938
  have hstable : (prefixWord ++ tailWord_726938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726938).length < 2 ^ (prefixWord ++ tailWord_726938).sum := by decide
  have hdescent : baseEnd_726938 < baseStart_726938 := by decide
  rcases family_descends (prefixWord ++ tailWord_726938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_726945 : List Nat := [1, 2, 3, 4, 3, 1, 6]
def baseStart_726945 : Nat := 118140960795 + 726945 * 2 ^ 59
def prefixEnd_726945 : Nat := 4983230072969 + 3 ^ 40 * 726945 * 2
def baseEnd_726945 : Nat := 36866389568668005732775

theorem tailTrace_726945 : CollatzResearch.WordTrace tailWord_726945 prefixEnd_726945 36866389568668005732775 := by
  unfold tailWord_726945
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513862351409892166838289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17675908234273261444558859 26513862351409892166838289)
  ·
    refine ⟨19885396763557419125128717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26513862351409892166838289 19885396763557419125128717)
    ·
      refine ⟨7457023786334032171923269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19885396763557419125128717 7457023786334032171923269)
      ·
        refine ⟨1398191959937631032235613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7457023786334032171923269 1398191959937631032235613)
        ·
          refine ⟨524321984976611637088355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1398191959937631032235613 524321984976611637088355)
          ·
            refine ⟨786482977464917455632533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524321984976611637088355 786482977464917455632533)
            ·
              refine ⟨36866389568668005732775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 786482977464917455632533 36866389568668005732775)
              ·
                rfl

theorem cell20_726945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 6].length) (baseStart_726945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_726945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_726945 prefixEnd_726945 := by exact prefixLift 726945
  have htrace : WordTrace (prefixWord ++ tailWord_726945) baseStart_726945 baseEnd_726945 := by
    simpa [prefixWord, tailWord_726945, baseEnd_726945] using wordTrace_append hprefix tailTrace_726945
  have hstable : (prefixWord ++ tailWord_726945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_726945).length < 2 ^ (prefixWord ++ tailWord_726945).sum := by decide
  have hdescent : baseEnd_726945 < baseStart_726945 := by decide
  rcases family_descends (prefixWord ++ tailWord_726945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727011 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_727011 : Nat := 118140960795 + 727011 * 2 ^ 59
def prefixEnd_727011 : Nat := 4983230072969 + 3 ^ 40 * 727011 * 2
def baseEnd_727011 : Nat := 331827630316409155394705

theorem tailTrace_727011 : CollatzResearch.WordTrace tailWord_727011 prefixEnd_727011 331827630316409155394705 := by
  unfold tailWord_727011
  simp only [CollatzResearch.WordTrace]
  refine ⟨26516269569170785438740887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17677513046113856959160591 26516269569170785438740887)
  ·
    refine ⟨39774404353756178158111331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26516269569170785438740887 39774404353756178158111331)
    ·
      refine ⟨59661606530634267237166997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39774404353756178158111331 59661606530634267237166997)
      ·
        refine ⟨2796637806123481276742203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59661606530634267237166997 2796637806123481276742203)
        ·
          refine ⟨4194956709185221915113305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796637806123481276742203 4194956709185221915113305)
          ·
            refine ⟨3146217531888916436334979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194956709185221915113305 3146217531888916436334979)
            ·
              refine ⟨4719326297833374654502469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146217531888916436334979 4719326297833374654502469)
              ·
                refine ⟨884873680843757747719213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4719326297833374654502469 884873680843757747719213)
                ·
                  refine ⟨331827630316409155394705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884873680843757747719213 331827630316409155394705)
                  ·
                    rfl

theorem cell20_727011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_727011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727011 prefixEnd_727011 := by exact prefixLift 727011
  have htrace : WordTrace (prefixWord ++ tailWord_727011) baseStart_727011 baseEnd_727011 := by
    simpa [prefixWord, tailWord_727011, baseEnd_727011] using wordTrace_append hprefix tailTrace_727011
  have hstable : (prefixWord ++ tailWord_727011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727011).length < 2 ^ (prefixWord ++ tailWord_727011).sum := by decide
  have hdescent : baseEnd_727011 < baseStart_727011 := by decide
  rcases family_descends (prefixWord ++ tailWord_727011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727018 : List Nat := [3, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_727018 : Nat := 118140960795 + 727018 * 2 ^ 59
def prefixEnd_727018 : Nat := 4983230072969 + 3 ^ 40 * 727018 * 2
def baseEnd_727018 : Nat := 331830825307148242161343

theorem tailTrace_727018 : CollatzResearch.WordTrace tailWord_727018 prefixEnd_727018 331830825307148242161343 := by
  unfold tailWord_727018
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629131220036356408561427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17677683253430283756163805 6629131220036356408561427)
  ·
    refine ⟨9943696830054534612842141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629131220036356408561427 9943696830054534612842141)
    ·
      refine ⟨3728886311270450479815803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9943696830054534612842141 3728886311270450479815803)
      ·
        refine ⟨5593329466905675719723705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728886311270450479815803 5593329466905675719723705)
        ·
          refine ⟨4194997100179256789792779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5593329466905675719723705 4194997100179256789792779)
          ·
            refine ⟨6292495650268885184689169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194997100179256789792779 6292495650268885184689169)
            ·
              refine ⟨4719371737701663888516877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6292495650268885184689169 4719371737701663888516877)
              ·
                refine ⟨1769764401638123958193829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4719371737701663888516877 1769764401638123958193829)
                ·
                  refine ⟨331830825307148242161343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1769764401638123958193829 331830825307148242161343)
                  ·
                    rfl

theorem cell20_727018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_727018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727018 prefixEnd_727018 := by exact prefixLift 727018
  have htrace : WordTrace (prefixWord ++ tailWord_727018) baseStart_727018 baseEnd_727018 := by
    simpa [prefixWord, tailWord_727018, baseEnd_727018] using wordTrace_append hprefix tailTrace_727018
  have hstable : (prefixWord ++ tailWord_727018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727018).length < 2 ^ (prefixWord ++ tailWord_727018).sum := by decide
  have hdescent : baseEnd_727018 < baseStart_727018 := by decide
  rcases family_descends (prefixWord ++ tailWord_727018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727066 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 3]
def baseStart_727066 : Nat := 118140960795 + 727066 * 2 ^ 59
def prefixEnd_727066 : Nat := 4983230072969 + 3 ^ 40 * 727066 * 2
def baseEnd_727066 : Nat := 331852733815073408561147

theorem tailTrace_727066 : CollatzResearch.WordTrace tailWord_727066 prefixEnd_727066 331852733815073408561147 := by
  unfold tailWord_727066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6629568895992882457998263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17678850389314353221328701 6629568895992882457998263)
  ·
    refine ⟨9944353343989323686997395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6629568895992882457998263 9944353343989323686997395)
    ·
      refine ⟨14916530015983985530496093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9944353343989323686997395 14916530015983985530496093)
      ·
        refine ⟨5593698755993994573936035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14916530015983985530496093 5593698755993994573936035)
        ·
          refine ⟨8390548133990991860904053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5593698755993994573936035 8390548133990991860904053)
          ·
            refine ⟨786613887561655486959755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8390548133990991860904053 786613887561655486959755)
            ·
              refine ⟨1179920831342483230439633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786613887561655486959755 1179920831342483230439633)
              ·
                refine ⟨884940623506862422829725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179920831342483230439633 884940623506862422829725)
                ·
                  refine ⟨331852733815073408561147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884940623506862422829725 331852733815073408561147)
                  ·
                    rfl

theorem cell20_727066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_727066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727066 prefixEnd_727066 := by exact prefixLift 727066
  have htrace : WordTrace (prefixWord ++ tailWord_727066) baseStart_727066 baseEnd_727066 := by
    simpa [prefixWord, tailWord_727066, baseEnd_727066] using wordTrace_append hprefix tailTrace_727066
  have hstable : (prefixWord ++ tailWord_727066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727066).length < 2 ^ (prefixWord ++ tailWord_727066).sum := by decide
  have hdescent : baseEnd_727066 < baseStart_727066 := by decide
  rcases family_descends (prefixWord ++ tailWord_727066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727073 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 4]
def baseStart_727073 : Nat := 118140960795 + 727073 * 2 ^ 59
def prefixEnd_727073 : Nat := 4983230072969 + 3 ^ 40 * 727073 * 2
def baseEnd_727073 : Nat := 331855928805812495327785

theorem tailTrace_727073 : CollatzResearch.WordTrace tailWord_727073 prefixEnd_727073 331855928805812495327785 := by
  unfold tailWord_727073
  simp only [CollatzResearch.WordTrace]
  refine ⟨26518530894946170027497873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17679020596630780018331915 26518530894946170027497873)
  ·
    refine ⟨19888898171209627520623405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26518530894946170027497873 19888898171209627520623405)
    ·
      refine ⟨7458336814203610320233777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19888898171209627520623405 7458336814203610320233777)
      ·
        refine ⟨5593752610652707740175333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7458336814203610320233777 5593752610652707740175333)
        ·
          refine ⟨1048828614497382701282875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5593752610652707740175333 1048828614497382701282875)
          ·
            refine ⟨1573242921746074051924313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048828614497382701282875 1573242921746074051924313)
            ·
              refine ⟨1179932191309555538943235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573242921746074051924313 1179932191309555538943235)
              ·
                refine ⟨1769898286964333308414853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179932191309555538943235 1769898286964333308414853)
                ·
                  refine ⟨331855928805812495327785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1769898286964333308414853 331855928805812495327785)
                  ·
                    rfl

theorem cell20_727073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_727073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727073 prefixEnd_727073 := by exact prefixLift 727073
  have htrace : WordTrace (prefixWord ++ tailWord_727073) baseStart_727073 baseEnd_727073 := by
    simpa [prefixWord, tailWord_727073, baseEnd_727073] using wordTrace_append hprefix tailTrace_727073
  have hstable : (prefixWord ++ tailWord_727073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727073).length < 2 ^ (prefixWord ++ tailWord_727073).sum := by decide
  have hdescent : baseEnd_727073 < baseStart_727073 := by decide
  rcases family_descends (prefixWord ++ tailWord_727073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727097 : List Nat := [1, 2, 1, 5, 3, 2, 2, 4]
def baseStart_727097 : Nat := 118140960795 + 727097 * 2 ^ 59
def prefixEnd_727097 : Nat := 4983230072969 + 3 ^ 40 * 727097 * 2
def baseEnd_727097 : Nat := 110622294353258359509229

theorem tailTrace_727097 : CollatzResearch.WordTrace tailWord_727097 prefixEnd_727097 110622294353258359509229 := by
  unfold tailWord_727097
  simp only [CollatzResearch.WordTrace]
  refine ⟨26519406246859222126371545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17679604164572814750914363 26519406246859222126371545)
  ·
    refine ⟨19889554685144416594778659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26519406246859222126371545 19889554685144416594778659)
    ·
      refine ⟨29834332027716624892167989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19889554685144416594778659 29834332027716624892167989)
      ·
        refine ⟨2796968627598433583640749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29834332027716624892167989 2796968627598433583640749)
        ·
          refine ⟨1048863235349412593865281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2796968627598433583640749 1048863235349412593865281)
          ·
            refine ⟨786647426512059445398961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048863235349412593865281 786647426512059445398961)
            ·
              refine ⟨589985569884044584049221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786647426512059445398961 589985569884044584049221)
              ·
                refine ⟨110622294353258359509229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589985569884044584049221 110622294353258359509229)
                ·
                  rfl

theorem cell20_727097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_727097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727097 prefixEnd_727097 := by exact prefixLift 727097
  have htrace : WordTrace (prefixWord ++ tailWord_727097) baseStart_727097 baseEnd_727097 := by
    simpa [prefixWord, tailWord_727097, baseEnd_727097] using wordTrace_append hprefix tailTrace_727097
  have hstable : (prefixWord ++ tailWord_727097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727097).length < 2 ^ (prefixWord ++ tailWord_727097).sum := by decide
  have hdescent : baseEnd_727097 < baseStart_727097 := by decide
  rcases family_descends (prefixWord ++ tailWord_727097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727101 : List Nat := [1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_727101 : Nat := 118140960795 + 727101 * 2 ^ 59
def prefixEnd_727101 : Nat := 4983230072969 + 3 ^ 40 * 727101 * 2
def baseEnd_727101 : Nat := 110622902922922947464779

theorem tailTrace_727101 : CollatzResearch.WordTrace tailWord_727101 prefixEnd_727101 110622902922922947464779 := by
  unfold tailWord_727101
  simp only [CollatzResearch.WordTrace]
  refine ⟨26519552138844730809517157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17679701425896487206344771 26519552138844730809517157)
  ·
    refine ⟨4972416026033387026784467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26519552138844730809517157 4972416026033387026784467)
    ·
      refine ⟨7458624039050080540176701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972416026033387026784467 7458624039050080540176701)
      ·
        refine ⟨2796984014643780202566263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7458624039050080540176701 2796984014643780202566263)
        ·
          refine ⟨4195476021965670303849395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796984014643780202566263 4195476021965670303849395)
          ·
            refine ⟨6293214032948505455774093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4195476021965670303849395 6293214032948505455774093)
            ·
              refine ⟨2359955262355689545915285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6293214032948505455774093 2359955262355689545915285)
              ·
                refine ⟨110622902922922947464779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2359955262355689545915285 110622902922922947464779)
                ·
                  rfl

theorem cell20_727101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_727101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727101 prefixEnd_727101 := by exact prefixLift 727101
  have htrace : WordTrace (prefixWord ++ tailWord_727101) baseStart_727101 baseEnd_727101 := by
    simpa [prefixWord, tailWord_727101, baseEnd_727101] using wordTrace_append hprefix tailTrace_727101
  have hstable : (prefixWord ++ tailWord_727101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727101).length < 2 ^ (prefixWord ++ tailWord_727101).sum := by decide
  have hdescent : baseEnd_727101 < baseStart_727101 := by decide
  rcases family_descends (prefixWord ++ tailWord_727101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727128 : List Nat := [2, 1, 2, 2, 1, 5, 3, 2, 2]
def baseStart_727128 : Nat := 118140960795 + 727128 * 2 ^ 59
def prefixEnd_727128 : Nat := 4983230072969 + 3 ^ 40 * 727128 * 2
def baseEnd_727128 : Nat := 331881032304476748494227

theorem tailTrace_727128 : CollatzResearch.WordTrace tailWord_727128 prefixEnd_727128 331881032304476748494227 := by
  unfold tailWord_727128
  simp only [CollatzResearch.WordTrace]
  refine ⟨13260268454873457210375019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17680357939831276280500025 13260268454873457210375019)
  ·
    refine ⟨19890402682310185815562529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13260268454873457210375019 19890402682310185815562529)
    ·
      refine ⟨14917802011732639361671897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19890402682310185815562529 14917802011732639361671897)
      ·
        refine ⟨11188351508799479521253923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14917802011732639361671897 11188351508799479521253923)
        ·
          refine ⟨16782527263199219281880885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11188351508799479521253923 16782527263199219281880885)
          ·
            refine ⟨1573361930924926807676333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16782527263199219281880885 1573361930924926807676333)
            ·
              refine ⟨590010724096847552878625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1573361930924926807676333 590010724096847552878625)
              ·
                refine ⟨442508043072635664658969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590010724096847552878625 442508043072635664658969)
                ·
                  refine ⟨331881032304476748494227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442508043072635664658969 331881032304476748494227)
                  ·
                    rfl

theorem cell20_727128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_727128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727128 prefixEnd_727128 := by exact prefixLift 727128
  have htrace : WordTrace (prefixWord ++ tailWord_727128) baseStart_727128 baseEnd_727128 := by
    simpa [prefixWord, tailWord_727128, baseEnd_727128] using wordTrace_append hprefix tailTrace_727128
  have hstable : (prefixWord ++ tailWord_727128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727128).length < 2 ^ (prefixWord ++ tailWord_727128).sum := by decide
  have hdescent : baseEnd_727128 < baseStart_727128 := by decide
  rcases family_descends (prefixWord ++ tailWord_727128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727134 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_727134 : Nat := 118140960795 + 727134 * 2 ^ 59
def prefixEnd_727134 : Nat := 4983230072969 + 3 ^ 40 * 727134 * 2
def baseEnd_727134 : Nat := 331883770867967394294203

theorem tailTrace_727134 : CollatzResearch.WordTrace tailWord_727134 prefixEnd_727134 331883770867967394294203 := by
  unfold tailWord_727134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315094468465647180683557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17680503831816784963645637 3315094468465647180683557)
  ·
    refine ⟨621580212837308846378167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3315094468465647180683557 621580212837308846378167)
    ·
      refine ⟨932370319255963269567251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621580212837308846378167 932370319255963269567251)
      ·
        refine ⟨1398555478883944904350877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932370319255963269567251 1398555478883944904350877)
        ·
          refine ⟨524458304581479339131579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1398555478883944904350877 524458304581479339131579)
          ·
            refine ⟨786687456872219008697369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524458304581479339131579 786687456872219008697369)
            ·
              refine ⟨590015592654164256523027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786687456872219008697369 590015592654164256523027)
              ·
                refine ⟨885023388981246384784541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590015592654164256523027 885023388981246384784541)
                ·
                  refine ⟨331883770867967394294203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885023388981246384784541 331883770867967394294203)
                  ·
                    rfl

theorem cell20_727134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_727134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727134 prefixEnd_727134 := by exact prefixLift 727134
  have htrace : WordTrace (prefixWord ++ tailWord_727134) baseStart_727134 baseEnd_727134 := by
    simpa [prefixWord, tailWord_727134, baseEnd_727134] using wordTrace_append hprefix tailTrace_727134
  have hstable : (prefixWord ++ tailWord_727134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727134).length < 2 ^ (prefixWord ++ tailWord_727134).sum := by decide
  have hdescent : baseEnd_727134 < baseStart_727134 := by decide
  rcases family_descends (prefixWord ++ tailWord_727134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727138 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 3]
def baseStart_727138 : Nat := 118140960795 + 727138 * 2 ^ 59
def prefixEnd_727138 : Nat := 4983230072969 + 3 ^ 40 * 727138 * 2
def baseEnd_727138 : Nat := 331885596576961158160853

theorem tailTrace_727138 : CollatzResearch.WordTrace tailWord_727138 prefixEnd_727138 331885596576961158160853 := by
  unfold tailWord_727138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6630225409927671532153517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17680601093140457419076045 6630225409927671532153517)
  ·
    refine ⟨2486334528722876824557569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6630225409927671532153517 2486334528722876824557569)
    ·
      refine ⟨1864750896542157618418177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2486334528722876824557569 1864750896542157618418177)
      ·
        refine ⟨1398563172406618213813633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1864750896542157618418177 1398563172406618213813633)
        ·
          refine ⟨1048922379304963660360225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398563172406618213813633 1048922379304963660360225)
          ·
            refine ⟨786691784478722745270169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048922379304963660360225 786691784478722745270169)
            ·
              refine ⟨590018838359042058952627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786691784478722745270169 590018838359042058952627)
              ·
                refine ⟨885028257538563088428941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590018838359042058952627 885028257538563088428941)
                ·
                  refine ⟨331885596576961158160853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885028257538563088428941 331885596576961158160853)
                  ·
                    rfl

theorem cell20_727138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_727138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727138 prefixEnd_727138 := by exact prefixLift 727138
  have htrace : WordTrace (prefixWord ++ tailWord_727138) baseStart_727138 baseEnd_727138 := by
    simpa [prefixWord, tailWord_727138, baseEnd_727138] using wordTrace_append hprefix tailTrace_727138
  have hstable : (prefixWord ++ tailWord_727138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727138).length < 2 ^ (prefixWord ++ tailWord_727138).sum := by decide
  have hdescent : baseEnd_727138 < baseStart_727138 := by decide
  rcases family_descends (prefixWord ++ tailWord_727138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727153 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 6]
def baseStart_727153 : Nat := 118140960795 + 727153 * 2 ^ 59
def prefixEnd_727153 : Nat := 4983230072969 + 3 ^ 40 * 727153 * 2
def baseEnd_727153 : Nat := 331892442985687772660791

theorem tailTrace_727153 : CollatzResearch.WordTrace tailWord_727153 prefixEnd_727153 331892442985687772660791 := by
  unfold tailWord_727153
  simp only [CollatzResearch.WordTrace]
  refine ⟨26521448734656343690410113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17680965823104229126940075 26521448734656343690410113)
  ·
    refine ⟨19891086550992257767807585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26521448734656343690410113 19891086550992257767807585)
    ·
      refine ⟨14918314913244193325855689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19891086550992257767807585 14918314913244193325855689)
      ·
        refine ⟨11188736184933144994391767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14918314913244193325855689 11188736184933144994391767)
        ·
          refine ⟨16783104277399717491587651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11188736184933144994391767 16783104277399717491587651)
          ·
            refine ⟨25174656416099576237381477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16783104277399717491587651 25174656416099576237381477)
            ·
              refine ⟨4720248078018670544509027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25174656416099576237381477 4720248078018670544509027)
              ·
                refine ⟨7080372117028005816763541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720248078018670544509027 7080372117028005816763541)
                ·
                  refine ⟨331892442985687772660791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7080372117028005816763541 331892442985687772660791)
                  ·
                    rfl

theorem cell20_727153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_727153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727153 prefixEnd_727153 := by exact prefixLift 727153
  have htrace : WordTrace (prefixWord ++ tailWord_727153) baseStart_727153 baseEnd_727153 := by
    simpa [prefixWord, tailWord_727153, baseEnd_727153] using wordTrace_append hprefix tailTrace_727153
  have hstable : (prefixWord ++ tailWord_727153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727153).length < 2 ^ (prefixWord ++ tailWord_727153).sum := by decide
  have hdescent : baseEnd_727153 < baseStart_727153 := by decide
  rcases family_descends (prefixWord ++ tailWord_727153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727201 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 3]
def baseStart_727201 : Nat := 118140960795 + 727201 * 2 ^ 59
def prefixEnd_727201 : Nat := 4983230072969 + 3 ^ 40 * 727201 * 2
def baseEnd_727201 : Nat := 331914351493612939060595

theorem tailTrace_727201 : CollatzResearch.WordTrace tailWord_727201 prefixEnd_727201 331914351493612939060595 := by
  unfold tailWord_727201
  simp only [CollatzResearch.WordTrace]
  refine ⟨26523199438482447888157457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17682132958988298592104971 26523199438482447888157457)
  ·
    refine ⟨19892399578861835916118093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26523199438482447888157457 19892399578861835916118093)
    ·
      refine ⟨7459649842073188468544285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19892399578861835916118093 7459649842073188468544285)
      ·
        refine ⟨2797368690777445675704107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7459649842073188468544285 2797368690777445675704107)
        ·
          refine ⟨4196053036166168513556161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2797368690777445675704107 4196053036166168513556161)
          ·
            refine ⟨3147039777124626385167121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4196053036166168513556161 3147039777124626385167121)
            ·
              refine ⟨2360279832843469788875341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3147039777124626385167121 2360279832843469788875341)
              ·
                refine ⟨885104937316301170828253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2360279832843469788875341 885104937316301170828253)
                ·
                  refine ⟨331914351493612939060595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885104937316301170828253 331914351493612939060595)
                  ·
                    rfl

theorem cell20_727201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_727201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727201 prefixEnd_727201 := by exact prefixLift 727201
  have htrace : WordTrace (prefixWord ++ tailWord_727201) baseStart_727201 baseEnd_727201 := by
    simpa [prefixWord, tailWord_727201, baseEnd_727201] using wordTrace_append hprefix tailTrace_727201
  have hstable : (prefixWord ++ tailWord_727201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727201).length < 2 ^ (prefixWord ++ tailWord_727201).sum := by decide
  have hdescent : baseEnd_727201 < baseStart_727201 := by decide
  rcases family_descends (prefixWord ++ tailWord_727201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727221 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 2]
def baseStart_727221 : Nat := 118140960795 + 727221 * 2 ^ 59
def prefixEnd_727221 : Nat := 4983230072969 + 3 ^ 40 * 727221 * 2
def baseEnd_727221 : Nat := 331923480038581758393847

theorem tailTrace_727221 : CollatzResearch.WordTrace tailWord_727221 prefixEnd_727221 331923480038581758393847 := by
  unfold tailWord_727221
  simp only [CollatzResearch.WordTrace]
  refine ⟨26523928898409991303885517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17682619265606660869257011 26523928898409991303885517)
  ·
    refine ⟨9946473336903746738957069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26523928898409991303885517 9946473336903746738957069)
    ·
      refine ⟨3729927501338905027108901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9946473336903746738957069 3729927501338905027108901)
      ·
        refine ⟨699361406501044692582919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3729927501338905027108901 699361406501044692582919)
        ·
          refine ⟨1049042109751567038874379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699361406501044692582919 1049042109751567038874379)
          ·
            refine ⟨1573563164627350558311569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049042109751567038874379 1573563164627350558311569)
            ·
              refine ⟨1180172373470512918733677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573563164627350558311569 1180172373470512918733677)
              ·
                refine ⟨442564640051442344525129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1180172373470512918733677 442564640051442344525129)
                ·
                  refine ⟨331923480038581758393847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442564640051442344525129 331923480038581758393847)
                  ·
                    rfl

theorem cell20_727221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_727221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727221 prefixEnd_727221 := by exact prefixLift 727221
  have htrace : WordTrace (prefixWord ++ tailWord_727221) baseStart_727221 baseEnd_727221 := by
    simpa [prefixWord, tailWord_727221, baseEnd_727221] using wordTrace_append hprefix tailTrace_727221
  have hstable : (prefixWord ++ tailWord_727221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727221).length < 2 ^ (prefixWord ++ tailWord_727221).sum := by decide
  have hdescent : baseEnd_727221 < baseStart_727221 := by decide
  rcases family_descends (prefixWord ++ tailWord_727221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727225 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 2]
def baseStart_727225 : Nat := 118140960795 + 727225 * 2 ^ 59
def prefixEnd_727225 : Nat := 4983230072969 + 3 ^ 40 * 727225 * 2
def baseEnd_727225 : Nat := 331925305747575522260497

theorem tailTrace_727225 : CollatzResearch.WordTrace tailWord_727225 prefixEnd_727225 331925305747575522260497 := by
  unfold tailWord_727225
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524074790395499987031129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17682716526930333324687419 26524074790395499987031129)
  ·
    refine ⟨19893056092796624990273347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26524074790395499987031129 19893056092796624990273347)
    ·
      refine ⟨29839584139194937485410021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19893056092796624990273347 29839584139194937485410021)
      ·
        refine ⟨5594922026099050778514379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29839584139194937485410021 5594922026099050778514379)
        ·
          refine ⟨8392383039148576167771569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5594922026099050778514379 8392383039148576167771569)
          ·
            refine ⟨6294287279361432125828677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8392383039148576167771569 6294287279361432125828677)
            ·
              refine ⟨1180178864880268523592877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6294287279361432125828677 1180178864880268523592877)
              ·
                refine ⟨442567074330100696347329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1180178864880268523592877 442567074330100696347329)
                ·
                  refine ⟨331925305747575522260497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442567074330100696347329 331925305747575522260497)
                  ·
                    rfl

theorem cell20_727225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_727225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727225 prefixEnd_727225 := by exact prefixLift 727225
  have htrace : WordTrace (prefixWord ++ tailWord_727225) baseStart_727225 baseEnd_727225 := by
    simpa [prefixWord, tailWord_727225, baseEnd_727225] using wordTrace_append hprefix tailTrace_727225
  have hstable : (prefixWord ++ tailWord_727225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727225).length < 2 ^ (prefixWord ++ tailWord_727225).sum := by decide
  have hdescent : baseEnd_727225 < baseStart_727225 := by decide
  rcases family_descends (prefixWord ++ tailWord_727225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727229 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_727229 : Nat := 118140960795 + 727229 * 2 ^ 59
def prefixEnd_727229 : Nat := 4983230072969 + 3 ^ 40 * 727229 * 2
def baseEnd_727229 : Nat := 331927131456569286127147

theorem tailTrace_727229 : CollatzResearch.WordTrace tailWord_727229 prefixEnd_727229 331927131456569286127147 := by
  unfold tailWord_727229
  simp only [CollatzResearch.WordTrace]
  refine ⟨26524220682381008670176741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17682813788254005780117827 26524220682381008670176741)
  ·
    refine ⟨4973291377946439125658139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26524220682381008670176741 4973291377946439125658139)
    ·
      refine ⟨7459937066919658688487209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973291377946439125658139 7459937066919658688487209)
      ·
        refine ⟨5594952800189744016365407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7459937066919658688487209 5594952800189744016365407)
        ·
          refine ⟨8392429200284616024548111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5594952800189744016365407 8392429200284616024548111)
          ·
            refine ⟨12588643800426924036822167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8392429200284616024548111 12588643800426924036822167)
            ·
              refine ⟨18882965700640386055233251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12588643800426924036822167 18882965700640386055233251)
              ·
                refine ⟨28324448550960579082849877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18882965700640386055233251 28324448550960579082849877)
                ·
                  refine ⟨331927131456569286127147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28324448550960579082849877 331927131456569286127147)
                  ·
                    rfl

theorem cell20_727229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_727229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727229 prefixEnd_727229 := by exact prefixLift 727229
  have htrace : WordTrace (prefixWord ++ tailWord_727229) baseStart_727229 baseEnd_727229 := by
    simpa [prefixWord, tailWord_727229, baseEnd_727229] using wordTrace_append hprefix tailTrace_727229
  have hstable : (prefixWord ++ tailWord_727229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727229).length < 2 ^ (prefixWord ++ tailWord_727229).sum := by decide
  have hdescent : baseEnd_727229 < baseStart_727229 := by decide
  rcases family_descends (prefixWord ++ tailWord_727229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727246 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_727246 : Nat := 118140960795 + 727246 * 2 ^ 59
def prefixEnd_727246 : Nat := 4983230072969 + 3 ^ 40 * 727246 * 2
def baseEnd_727246 : Nat := 331934890719792782560411

theorem tailTrace_727246 : CollatzResearch.WordTrace tailWord_727246 prefixEnd_727246 331934890719792782560411 := by
  unfold tailWord_727246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315605090414927571693199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17683227148879613715697061 3315605090414927571693199)
  ·
    refine ⟨4973407635622391357539799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315605090414927571693199 4973407635622391357539799)
    ·
      refine ⟨7460111453433587036309699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973407635622391357539799 7460111453433587036309699)
      ·
        refine ⟨11190167180150380554464549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7460111453433587036309699 11190167180150380554464549)
        ·
          refine ⟨2098156346278196353962103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11190167180150380554464549 2098156346278196353962103)
          ·
            refine ⟨3147234519417294530943155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098156346278196353962103 3147234519417294530943155)
            ·
              refine ⟨4720851779125941796414733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147234519417294530943155 4720851779125941796414733)
              ·
                refine ⟨1770319417172228173655525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720851779125941796414733 1770319417172228173655525)
                ·
                  refine ⟨331934890719792782560411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770319417172228173655525 331934890719792782560411)
                  ·
                    rfl

theorem cell20_727246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_727246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727246 prefixEnd_727246 := by exact prefixLift 727246
  have htrace : WordTrace (prefixWord ++ tailWord_727246) baseStart_727246 baseEnd_727246 := by
    simpa [prefixWord, tailWord_727246, baseEnd_727246] using wordTrace_append hprefix tailTrace_727246
  have hstable : (prefixWord ++ tailWord_727246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727246).length < 2 ^ (prefixWord ++ tailWord_727246).sum := by decide
  have hdescent : baseEnd_727246 < baseStart_727246 := by decide
  rcases family_descends (prefixWord ++ tailWord_727246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727256 : List Nat := [2, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_727256 : Nat := 118140960795 + 727256 * 2 ^ 59
def prefixEnd_727256 : Nat := 4983230072969 + 3 ^ 40 * 727256 * 2
def baseEnd_727256 : Nat := 331939454992277192227037

theorem tailTrace_727256 : CollatzResearch.WordTrace tailWord_727256 prefixEnd_727256 331939454992277192227037 := by
  unfold tailWord_727256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13262602726641596140704811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17683470302188794854273081 13262602726641596140704811)
  ·
    refine ⟨19893904089962394211057217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13262602726641596140704811 19893904089962394211057217)
    ·
      refine ⟨14920428067471795658292913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19893904089962394211057217 14920428067471795658292913)
      ·
        refine ⟨11190321050603846743719685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14920428067471795658292913 11190321050603846743719685)
        ·
          refine ⟨2098185196988221264447441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11190321050603846743719685 2098185196988221264447441)
          ·
            refine ⟨1573638897741165948335581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2098185196988221264447441 1573638897741165948335581)
            ·
              refine ⟨590114586652937230625843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1573638897741165948335581 590114586652937230625843)
              ·
                refine ⟨885171879979405845938765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590114586652937230625843 885171879979405845938765)
                ·
                  refine ⟨331939454992277192227037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885171879979405845938765 331939454992277192227037)
                  ·
                    rfl

theorem cell20_727256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_727256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727256 prefixEnd_727256 := by exact prefixLift 727256
  have htrace : WordTrace (prefixWord ++ tailWord_727256) baseStart_727256 baseEnd_727256 := by
    simpa [prefixWord, tailWord_727256, baseEnd_727256] using wordTrace_append hprefix tailTrace_727256
  have hstable : (prefixWord ++ tailWord_727256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727256).length < 2 ^ (prefixWord ++ tailWord_727256).sum := by decide
  have hdescent : baseEnd_727256 < baseStart_727256 := by decide
  rcases family_descends (prefixWord ++ tailWord_727256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727266 : List Nat := [3, 3, 4, 1, 1, 1, 1, 6]
def baseStart_727266 : Nat := 118140960795 + 727266 * 2 ^ 59
def prefixEnd_727266 : Nat := 4983230072969 + 3 ^ 40 * 727266 * 2
def baseEnd_727266 : Nat := 110648006421587200631221

theorem tailTrace_727266 : CollatzResearch.WordTrace tailWord_727266 prefixEnd_727266 110648006421587200631221 := by
  unfold tailWord_727266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631392545811740997318413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17683713455497975992849101 6631392545811740997318413)
  ·
    refine ⟨2486772204679402873994405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6631392545811740997318413 2486772204679402873994405)
    ·
      refine ⟨466269788377388038873951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2486772204679402873994405 466269788377388038873951)
      ·
        refine ⟨699404682566082058310927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466269788377388038873951 699404682566082058310927)
        ·
          refine ⟨1049107023849123087466391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699404682566082058310927 1049107023849123087466391)
          ·
            refine ⟨1573660535773684631199587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049107023849123087466391 1573660535773684631199587)
            ·
              refine ⟨2360490803660526946799381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573660535773684631199587 2360490803660526946799381)
              ·
                refine ⟨110648006421587200631221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2360490803660526946799381 110648006421587200631221)
                ·
                  rfl

theorem cell20_727266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_727266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727266 prefixEnd_727266 := by exact prefixLift 727266
  have htrace : WordTrace (prefixWord ++ tailWord_727266) baseStart_727266 baseEnd_727266 := by
    simpa [prefixWord, tailWord_727266, baseEnd_727266] using wordTrace_append hprefix tailTrace_727266
  have hstable : (prefixWord ++ tailWord_727266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727266).length < 2 ^ (prefixWord ++ tailWord_727266).sum := by decide
  have hdescent : baseEnd_727266 < baseStart_727266 := by decide
  rcases family_descends (prefixWord ++ tailWord_727266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727353 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_727353 : Nat := 118140960795 + 727353 * 2 ^ 59
def prefixEnd_727353 : Nat := 4983230072969 + 3 ^ 40 * 727353 * 2
def baseEnd_727353 : Nat := 331983728435375965993307

theorem tailTrace_727353 : CollatzResearch.WordTrace tailWord_727353 prefixEnd_727353 331983728435375965993307 := by
  unfold tailWord_727353
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528743333931777847690713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17685828889287851898460475 26528743333931777847690713)
  ·
    refine ⟨19896557500448833385768035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26528743333931777847690713 19896557500448833385768035)
    ·
      refine ⟨29844836250673250078652053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19896557500448833385768035 29844836250673250078652053)
      ·
        refine ⟨1398976699250308597436815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29844836250673250078652053 1398976699250308597436815)
        ·
          refine ⟨2098465048875462896155223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398976699250308597436815 2098465048875462896155223)
          ·
            refine ⟨3147697573313194344232835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098465048875462896155223 3147697573313194344232835)
            ·
              refine ⟨4721546359969791516349253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147697573313194344232835 4721546359969791516349253)
              ·
                refine ⟨885289942494335909315485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4721546359969791516349253 885289942494335909315485)
                ·
                  refine ⟨331983728435375965993307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885289942494335909315485 331983728435375965993307)
                  ·
                    rfl

theorem cell20_727353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_727353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727353 prefixEnd_727353 := by exact prefixLift 727353
  have htrace : WordTrace (prefixWord ++ tailWord_727353) baseStart_727353 baseEnd_727353 := by
    simpa [prefixWord, tailWord_727353, baseEnd_727353] using wordTrace_append hprefix tailTrace_727353
  have hstable : (prefixWord ++ tailWord_727353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727353).length < 2 ^ (prefixWord ++ tailWord_727353).sum := by decide
  have hdescent : baseEnd_727353 < baseStart_727353 := by decide
  rcases family_descends (prefixWord ++ tailWord_727353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727394 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_727394 : Nat := 118140960795 + 727394 * 2 ^ 59
def prefixEnd_727394 : Nat := 4983230072969 + 3 ^ 40 * 727394 * 2
def baseEnd_727394 : Nat := 332002441952562045626473

theorem tailTrace_727394 : CollatzResearch.WordTrace tailWord_727394 prefixEnd_727394 332002441952562045626473 := by
  unfold tailWord_727394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6632559681695810462483309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17686825817855494566622157 6632559681695810462483309)
  ·
    refine ⟨2487209880635928923431241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6632559681695810462483309 2487209880635928923431241)
    ·
      refine ⟨1865407410476946692573431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2487209880635928923431241 1865407410476946692573431)
      ·
        refine ⟨2798111115715420038860147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865407410476946692573431 2798111115715420038860147)
        ·
          refine ⟨4197166673573130058290221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798111115715420038860147 4197166673573130058290221)
          ·
            refine ⟨1573937502589923771858833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4197166673573130058290221 1573937502589923771858833)
            ·
              refine ⟨1180453126942442828894125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573937502589923771858833 1180453126942442828894125)
              ·
                refine ⟨442669922603416060835297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1180453126942442828894125 442669922603416060835297)
                ·
                  refine ⟨332002441952562045626473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442669922603416060835297 332002441952562045626473)
                  ·
                    rfl

theorem cell20_727394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_727394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727394 prefixEnd_727394 := by exact prefixLift 727394
  have htrace : WordTrace (prefixWord ++ tailWord_727394) baseStart_727394 baseEnd_727394 := by
    simpa [prefixWord, tailWord_727394, baseEnd_727394] using wordTrace_append hprefix tailTrace_727394
  have hstable : (prefixWord ++ tailWord_727394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727394).length < 2 ^ (prefixWord ++ tailWord_727394).sum := by decide
  have hdescent : baseEnd_727394 < baseStart_727394 := by decide
  rcases family_descends (prefixWord ++ tailWord_727394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727419 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_727419 : Nat := 118140960795 + 727419 * 2 ^ 59
def prefixEnd_727419 : Nat := 4983230072969 + 3 ^ 40 * 727419 * 2
def baseEnd_727419 : Nat := 332013852633773069793037

theorem tailTrace_727419 : CollatzResearch.WordTrace tailWord_727419 prefixEnd_727419 332013852633773069793037 := by
  unfold tailWord_727419
  simp only [CollatzResearch.WordTrace]
  refine ⟨26531150551692671119593311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17687433701128447413062207 26531150551692671119593311)
  ·
    refine ⟨39796725827539006679389967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26531150551692671119593311 39796725827539006679389967)
    ·
      refine ⟨59695088741308510019084951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39796725827539006679389967 59695088741308510019084951)
      ·
        refine ⟨89542633111962765028627427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59695088741308510019084951 89542633111962765028627427)
        ·
          refine ⟨134313949667944147542941141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89542633111962765028627427 134313949667944147542941141)
          ·
            refine ⟨3147983195342440958037683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 134313949667944147542941141 3147983195342440958037683)
            ·
              refine ⟨4721974793013661437056525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147983195342440958037683 4721974793013661437056525)
              ·
                refine ⟨1770740547380123038896197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4721974793013661437056525 1770740547380123038896197)
                ·
                  refine ⟨332013852633773069793037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770740547380123038896197 332013852633773069793037)
                  ·
                    rfl

theorem cell20_727419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_727419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727419 prefixEnd_727419 := by exact prefixLift 727419
  have htrace : WordTrace (prefixWord ++ tailWord_727419) baseStart_727419 baseEnd_727419 := by
    simpa [prefixWord, tailWord_727419, baseEnd_727419] using wordTrace_append hprefix tailTrace_727419
  have hstable : (prefixWord ++ tailWord_727419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727419).length < 2 ^ (prefixWord ++ tailWord_727419).sum := by decide
  have hdescent : baseEnd_727419 < baseStart_727419 := by decide
  rcases family_descends (prefixWord ++ tailWord_727419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727450 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_727450 : Nat := 118140960795 + 727450 * 2 ^ 59
def prefixEnd_727450 : Nat := 4983230072969 + 3 ^ 40 * 727450 * 2
def baseEnd_727450 : Nat := 332028001878474739759577

theorem tailTrace_727450 : CollatzResearch.WordTrace tailWord_727450 prefixEnd_727450 332028001878474739759577 := by
  unfold tailWord_727450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633070303645090853492951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17688187476386908942647869 6633070303645090853492951)
  ·
    refine ⟨9949605455467636280239427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633070303645090853492951 9949605455467636280239427)
    ·
      refine ⟨14924408183201454420359141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9949605455467636280239427 14924408183201454420359141)
      ·
        refine ⟨2798326534350272703817339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14924408183201454420359141 2798326534350272703817339)
        ·
          refine ⟨4197489801525409055726009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798326534350272703817339 4197489801525409055726009)
          ·
            refine ⟨3148117351144056791794507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4197489801525409055726009 3148117351144056791794507)
            ·
              refine ⟨4722176026716085187691761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148117351144056791794507 4722176026716085187691761)
              ·
                refine ⟨3541632020037063890768821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4722176026716085187691761 3541632020037063890768821)
                ·
                  refine ⟨332028001878474739759577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3541632020037063890768821 332028001878474739759577)
                  ·
                    rfl

theorem cell20_727450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_727450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727450 prefixEnd_727450 := by exact prefixLift 727450
  have htrace : WordTrace (prefixWord ++ tailWord_727450) baseStart_727450 baseEnd_727450 := by
    simpa [prefixWord, tailWord_727450, baseEnd_727450] using wordTrace_append hprefix tailTrace_727450
  have hstable : (prefixWord ++ tailWord_727450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727450).length < 2 ^ (prefixWord ++ tailWord_727450).sum := by decide
  have hdescent : baseEnd_727450 < baseStart_727450 := by decide
  rcases family_descends (prefixWord ++ tailWord_727450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727466 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_727466 : Nat := 118140960795 + 727466 * 2 ^ 59
def prefixEnd_727466 : Nat := 4983230072969 + 3 ^ 40 * 727466 * 2
def baseEnd_727466 : Nat := 332035304714449795226179

theorem tailTrace_727466 : CollatzResearch.WordTrace tailWord_727466 prefixEnd_727466 332035304714449795226179 := by
  unfold tailWord_727466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633216195630599536638563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17688576521681598764369501 6633216195630599536638563)
  ·
    refine ⟨9949824293445899304957845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633216195630599536638563 9949824293445899304957845)
    ·
      refine ⟨466398013755276529919899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9949824293445899304957845 466398013755276529919899)
      ·
        refine ⟨699597020632914794879849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466398013755276529919899 699597020632914794879849)
        ·
          refine ⟨524697765474686096159887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699597020632914794879849 524697765474686096159887)
          ·
            refine ⟨787046648212029144239831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524697765474686096159887 787046648212029144239831)
            ·
              refine ⟨1180569972318043716359747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787046648212029144239831 1180569972318043716359747)
              ·
                refine ⟨1770854958477065574539621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180569972318043716359747 1770854958477065574539621)
                ·
                  refine ⟨332035304714449795226179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770854958477065574539621 332035304714449795226179)
                  ·
                    rfl

theorem cell20_727466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_727466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727466 prefixEnd_727466 := by exact prefixLift 727466
  have htrace : WordTrace (prefixWord ++ tailWord_727466) baseStart_727466 baseEnd_727466 := by
    simpa [prefixWord, tailWord_727466, baseEnd_727466] using wordTrace_append hprefix tailTrace_727466
  have hstable : (prefixWord ++ tailWord_727466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727466).length < 2 ^ (prefixWord ++ tailWord_727466).sum := by decide
  have hdescent : baseEnd_727466 < baseStart_727466 := by decide
  rcases family_descends (prefixWord ++ tailWord_727466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727481 : List Nat := [1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_727481 : Nat := 118140960795 + 727481 * 2 ^ 59
def prefixEnd_727481 : Nat := 4983230072969 + 3 ^ 40 * 727481 * 2
def baseEnd_727481 : Nat := 110680717041058803242039

theorem tailTrace_727481 : CollatzResearch.WordTrace tailWord_727481 prefixEnd_727481 110680717041058803242039 := by
  unfold tailWord_727481
  simp only [CollatzResearch.WordTrace]
  refine ⟨26533411877468055708350297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17688941251645370472233531 26533411877468055708350297)
  ·
    refine ⟨19900058908101041781262723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26533411877468055708350297 19900058908101041781262723)
    ·
      refine ⟨29850088362151562671894085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19900058908101041781262723 29850088362151562671894085)
      ·
        refine ⟨5596891567903418000980141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29850088362151562671894085 5596891567903418000980141)
        ·
          refine ⟨2098834337963781750367553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5596891567903418000980141 2098834337963781750367553)
          ·
            refine ⟨1574125753472836312775665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2098834337963781750367553 1574125753472836312775665)
            ·
              refine ⟨1180594315104627234581749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574125753472836312775665 1180594315104627234581749)
              ·
                refine ⟨110680717041058803242039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1180594315104627234581749 110680717041058803242039)
                ·
                  rfl

theorem cell20_727481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_727481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727481 prefixEnd_727481 := by exact prefixLift 727481
  have htrace : WordTrace (prefixWord ++ tailWord_727481) baseStart_727481 baseEnd_727481 := by
    simpa [prefixWord, tailWord_727481, baseEnd_727481] using wordTrace_append hprefix tailTrace_727481
  have hstable : (prefixWord ++ tailWord_727481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727481).length < 2 ^ (prefixWord ++ tailWord_727481).sum := by decide
  have hdescent : baseEnd_727481 < baseStart_727481 := by decide
  rcases family_descends (prefixWord ++ tailWord_727481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727484 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_727484 : Nat := 118140960795 + 727484 * 2 ^ 59
def prefixEnd_727484 : Nat := 4983230072969 + 3 ^ 40 * 727484 * 2
def baseEnd_727484 : Nat := 332043520404921732626105

theorem tailTrace_727484 : CollatzResearch.WordTrace tailWord_727484 prefixEnd_727484 332043520404921732626105 := by
  unfold tailWord_727484
  simp only [CollatzResearch.WordTrace]
  refine ⟨13266760648228593610354753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17689014197638124813806337 13266760648228593610354753)
  ·
    refine ⟨9950070486171445207766065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13266760648228593610354753 9950070486171445207766065)
    ·
      refine ⟨7462552864628583905824549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9950070486171445207766065 7462552864628583905824549)
      ·
        refine ⟨1399228662117859482342103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7462552864628583905824549 1399228662117859482342103)
        ·
          refine ⟨2098842993176789223513155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399228662117859482342103 2098842993176789223513155)
          ·
            refine ⟨3148264489765183835269733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098842993176789223513155 3148264489765183835269733)
            ·
              refine ⟨590299591830971969113075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3148264489765183835269733 590299591830971969113075)
              ·
                refine ⟨885449387746457953669613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590299591830971969113075 885449387746457953669613)
                ·
                  refine ⟨332043520404921732626105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885449387746457953669613 332043520404921732626105)
                  ·
                    rfl

theorem cell20_727484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_727484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727484 prefixEnd_727484 := by exact prefixLift 727484
  have htrace : WordTrace (prefixWord ++ tailWord_727484) baseStart_727484 baseEnd_727484 := by
    simpa [prefixWord, tailWord_727484, baseEnd_727484] using wordTrace_append hprefix tailTrace_727484
  have hstable : (prefixWord ++ tailWord_727484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727484).length < 2 ^ (prefixWord ++ tailWord_727484).sum := by decide
  have hdescent : baseEnd_727484 < baseStart_727484 := by decide
  rcases family_descends (prefixWord ++ tailWord_727484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727512 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 2]
def baseStart_727512 : Nat := 118140960795 + 727512 * 2 ^ 59
def prefixEnd_727512 : Nat := 4983230072969 + 3 ^ 40 * 727512 * 2
def baseEnd_727512 : Nat := 332056300367878079692657

theorem tailTrace_727512 : CollatzResearch.WordTrace tailWord_727512 prefixEnd_727512 332056300367878079692657 := by
  unfold tailWord_727512
  simp only [CollatzResearch.WordTrace]
  refine ⟨13267271270177874001364395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17689695026903832001819193 13267271270177874001364395)
  ·
    refine ⟨19900906905266811002046593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13267271270177874001364395 19900906905266811002046593)
    ·
      refine ⟨14925680178950108251534945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19900906905266811002046593 14925680178950108251534945)
      ·
        refine ⟨11194260134212581188651209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14925680178950108251534945 11194260134212581188651209)
        ·
          refine ⟨8395695100659435891488407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11194260134212581188651209 8395695100659435891488407)
          ·
            refine ⟨12593542650989153837232611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8395695100659435891488407 12593542650989153837232611)
            ·
              refine ⟨18890313976483730755848917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12593542650989153837232611 18890313976483730755848917)
              ·
                refine ⟨442741733823837439590209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18890313976483730755848917 442741733823837439590209)
                ·
                  refine ⟨332056300367878079692657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442741733823837439590209 332056300367878079692657)
                  ·
                    rfl

theorem cell20_727512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_727512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727512 prefixEnd_727512 := by exact prefixLift 727512
  have htrace : WordTrace (prefixWord ++ tailWord_727512) baseStart_727512 baseEnd_727512 := by
    simpa [prefixWord, tailWord_727512, baseEnd_727512] using wordTrace_append hprefix tailTrace_727512
  have hstable : (prefixWord ++ tailWord_727512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727512).length < 2 ^ (prefixWord ++ tailWord_727512).sum := by decide
  have hdescent : baseEnd_727512 < baseStart_727512 := by decide
  rcases family_descends (prefixWord ++ tailWord_727512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727525 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 2]
def baseStart_727525 : Nat := 118140960795 + 727525 * 2 ^ 59
def prefixEnd_727525 : Nat := 4983230072969 + 3 ^ 40 * 727525 * 2
def baseEnd_727525 : Nat := 332062233922107812259271

theorem tailTrace_727525 : CollatzResearch.WordTrace tailWord_727525 prefixEnd_727525 332062233922107812259271 := by
  unfold tailWord_727525
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535016689308651222952029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17690011126205767481968019 26535016689308651222952029)
  ·
    refine ⟨9950631258490744208607011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26535016689308651222952029 9950631258490744208607011)
    ·
      refine ⟨14925946887736116312910517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9950631258490744208607011 14925946887736116312910517)
      ·
        refine ⟨1399307520725260904335361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14925946887736116312910517 1399307520725260904335361)
        ·
          refine ⟨1049480640543945678251521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399307520725260904335361 1049480640543945678251521)
          ·
            refine ⟨787110480407959258688641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049480640543945678251521 787110480407959258688641)
            ·
              refine ⟨590332860305969444016481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787110480407959258688641 590332860305969444016481)
              ·
                refine ⟨442749645229477083012361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590332860305969444016481 442749645229477083012361)
                ·
                  refine ⟨332062233922107812259271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442749645229477083012361 332062233922107812259271)
                  ·
                    rfl

theorem cell20_727525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_727525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727525 prefixEnd_727525 := by exact prefixLift 727525
  have htrace : WordTrace (prefixWord ++ tailWord_727525) baseStart_727525 baseEnd_727525 := by
    simpa [prefixWord, tailWord_727525, baseEnd_727525] using wordTrace_append hprefix tailTrace_727525
  have hstable : (prefixWord ++ tailWord_727525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727525).length < 2 ^ (prefixWord ++ tailWord_727525).sum := by decide
  have hdescent : baseEnd_727525 < baseStart_727525 := by decide
  rcases family_descends (prefixWord ++ tailWord_727525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727581 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_727581 : Nat := 118140960795 + 727581 * 2 ^ 59
def prefixEnd_727581 : Nat := 4983230072969 + 3 ^ 40 * 727581 * 2
def baseEnd_727581 : Nat := 332087793848020506392375

theorem tailTrace_727581 : CollatzResearch.WordTrace tailWord_727581 prefixEnd_727581 332087793848020506392375 := by
  unfold tailWord_727581
  simp only [CollatzResearch.WordTrace]
  refine ⟨26537059177105772786990597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17691372784737181857993731 26537059177105772786990597)
  ·
    refine ⟨4975698595707332397560737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26537059177105772786990597 4975698595707332397560737)
    ·
      refine ⟨3731773946780499298170553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4975698595707332397560737 3731773946780499298170553)
      ·
        refine ⟨2798830460085374473627915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3731773946780499298170553 2798830460085374473627915)
        ·
          refine ⟨4198245690128061710441873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798830460085374473627915 4198245690128061710441873)
          ·
            refine ⟨3148684267596046282831405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4198245690128061710441873 3148684267596046282831405)
            ·
              refine ⟨1180756600348517356061777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3148684267596046282831405 1180756600348517356061777)
              ·
                refine ⟨885567450261388017046333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180756600348517356061777 885567450261388017046333)
                ·
                  refine ⟨332087793848020506392375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885567450261388017046333 332087793848020506392375)
                  ·
                    rfl

theorem cell20_727581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_727581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727581 prefixEnd_727581 := by exact prefixLift 727581
  have htrace : WordTrace (prefixWord ++ tailWord_727581) baseStart_727581 baseEnd_727581 := by
    simpa [prefixWord, tailWord_727581, baseEnd_727581] using wordTrace_append hprefix tailTrace_727581
  have hstable : (prefixWord ++ tailWord_727581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727581).length < 2 ^ (prefixWord ++ tailWord_727581).sum := by decide
  have hdescent : baseEnd_727581 < baseStart_727581 := by decide
  rcases family_descends (prefixWord ++ tailWord_727581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727602 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_727602 : Nat := 118140960795 + 727602 * 2 ^ 59
def prefixEnd_727602 : Nat := 4983230072969 + 3 ^ 40 * 727602 * 2
def baseEnd_727602 : Nat := 332097378820237766692289

theorem tailTrace_727602 : CollatzResearch.WordTrace tailWord_727602 prefixEnd_727602 332097378820237766692289 := by
  unfold tailWord_727602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634456277507423343376265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17691883406686462249003373 6634456277507423343376265)
  ·
    refine ⟨4975842208130567507532199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6634456277507423343376265 4975842208130567507532199)
    ·
      refine ⟨7463763312195851261298299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4975842208130567507532199 7463763312195851261298299)
      ·
        refine ⟨11195644968293776891947449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7463763312195851261298299 11195644968293776891947449)
        ·
          refine ⟨8396733726220332668960587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11195644968293776891947449 8396733726220332668960587)
          ·
            refine ⟨12595100589330499003440881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8396733726220332668960587 12595100589330499003440881)
            ·
              refine ⟨9446325441997874252580661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12595100589330499003440881 9446325441997874252580661)
              ·
                refine ⟨885593010187300711179437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9446325441997874252580661 885593010187300711179437)
                ·
                  refine ⟨332097378820237766692289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885593010187300711179437 332097378820237766692289)
                  ·
                    rfl

theorem cell20_727602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_727602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727602 prefixEnd_727602 := by exact prefixLift 727602
  have htrace : WordTrace (prefixWord ++ tailWord_727602) baseStart_727602 baseEnd_727602 := by
    simpa [prefixWord, tailWord_727602, baseEnd_727602] using wordTrace_append hprefix tailTrace_727602
  have hstable : (prefixWord ++ tailWord_727602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727602).length < 2 ^ (prefixWord ++ tailWord_727602).sum := by decide
  have hdescent : baseEnd_727602 < baseStart_727602 := by decide
  rcases family_descends (prefixWord ++ tailWord_727602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727609 : List Nat := [1, 2, 1, 5, 1, 1, 1, 4, 4]
def baseStart_727609 : Nat := 118140960795 + 727609 * 2 ^ 59
def prefixEnd_727609 : Nat := 4983230072969 + 3 ^ 40 * 727609 * 2
def baseEnd_727609 : Nat := 332100573810976853458927

theorem tailTrace_727609 : CollatzResearch.WordTrace tailWord_727609 prefixEnd_727609 332100573810976853458927 := by
  unfold tailWord_727609
  simp only [CollatzResearch.WordTrace]
  refine ⟨26538080421004333569009881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17692053614002889046006587 26538080421004333569009881)
  ·
    refine ⟨19903560315753250176757411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26538080421004333569009881 19903560315753250176757411)
    ·
      refine ⟨29855340473629875265136117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19903560315753250176757411 29855340473629875265136117)
      ·
        refine ⟨2798938169402800806106511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29855340473629875265136117 2798938169402800806106511)
        ·
          refine ⟨4198407254104201209159767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798938169402800806106511 4198407254104201209159767)
          ·
            refine ⟨6297610881156301813739651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198407254104201209159767 6297610881156301813739651)
            ·
              refine ⟨9446416321734452720609477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6297610881156301813739651 9446416321734452720609477)
              ·
                refine ⟨1771203060325209885114277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9446416321734452720609477 1771203060325209885114277)
                ·
                  refine ⟨332100573810976853458927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771203060325209885114277 332100573810976853458927)
                  ·
                    rfl

theorem cell20_727609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_727609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727609 prefixEnd_727609 := by exact prefixLift 727609
  have htrace : WordTrace (prefixWord ++ tailWord_727609) baseStart_727609 baseEnd_727609 := by
    simpa [prefixWord, tailWord_727609, baseEnd_727609] using wordTrace_append hprefix tailTrace_727609
  have hstable : (prefixWord ++ tailWord_727609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727609).length < 2 ^ (prefixWord ++ tailWord_727609).sum := by decide
  have hdescent : baseEnd_727609 < baseStart_727609 := by decide
  rcases family_descends (prefixWord ++ tailWord_727609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727612 : List Nat := [2, 2, 2, 2, 3, 3, 2, 4]
def baseStart_727612 : Nat := 118140960795 + 727612 * 2 ^ 59
def prefixEnd_727612 : Nat := 4983230072969 + 3 ^ 40 * 727612 * 2
def baseEnd_727612 : Nat := 110700647697574058786305

theorem tailTrace_727612 : CollatzResearch.WordTrace tailWord_727612 prefixEnd_727612 110700647697574058786305 := by
  unfold tailWord_727612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13269094919996732540684545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17692126559995643387579393 13269094919996732540684545)
  ·
    refine ⟨9951821189997549405513409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13269094919996732540684545 9951821189997549405513409)
    ·
      refine ⟨7463865892498162054135057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9951821189997549405513409 7463865892498162054135057)
      ·
        refine ⟨5597899419373621540601293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7463865892498162054135057 5597899419373621540601293)
        ·
          refine ⟨2099212282265108077725485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5597899419373621540601293 2099212282265108077725485)
          ·
            refine ⟨787204605849415529147057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2099212282265108077725485 787204605849415529147057)
            ·
              refine ⟨590403454387061646860293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787204605849415529147057 590403454387061646860293)
              ·
                refine ⟨110700647697574058786305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590403454387061646860293 110700647697574058786305)
                ·
                  rfl

theorem cell20_727612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_727612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727612 prefixEnd_727612 := by exact prefixLift 727612
  have htrace : WordTrace (prefixWord ++ tailWord_727612) baseStart_727612 baseEnd_727612 := by
    simpa [prefixWord, tailWord_727612, baseEnd_727612] using wordTrace_append hprefix tailTrace_727612
  have hstable : (prefixWord ++ tailWord_727612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727612).length < 2 ^ (prefixWord ++ tailWord_727612).sum := by decide
  have hdescent : baseEnd_727612 < baseStart_727612 := by decide
  rcases family_descends (prefixWord ++ tailWord_727612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727646 : List Nat := [4, 4, 1, 2, 1, 1, 2, 5]
def baseStart_727646 : Nat := 118140960795 + 727646 * 2 ^ 59
def prefixEnd_727646 : Nat := 4983230072969 + 3 ^ 40 * 727646 * 2
def baseEnd_727646 : Nat := 110705820539723056408481

theorem tailTrace_727646 : CollatzResearch.WordTrace tailWord_727646 prefixEnd_727646 110705820539723056408481 := by
  unfold tailWord_727646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317428740233786111013349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17692953281246859258737861 3317428740233786111013349)
  ·
    refine ⟨622017888793834895815003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3317428740233786111013349 622017888793834895815003)
    ·
      refine ⟨933026833190752343722505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622017888793834895815003 933026833190752343722505)
      ·
        refine ⟨699770124893064257791879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933026833190752343722505 699770124893064257791879)
        ·
          refine ⟨1049655187339596386687819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699770124893064257791879 1049655187339596386687819)
          ·
            refine ⟨1574482781009394580031729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049655187339596386687819 1574482781009394580031729)
            ·
              refine ⟨1180862085757045935023797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574482781009394580031729 1180862085757045935023797)
              ·
                refine ⟨110705820539723056408481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1180862085757045935023797 110705820539723056408481)
                ·
                  rfl

theorem cell20_727646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_727646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727646 prefixEnd_727646 := by exact prefixLift 727646
  have htrace : WordTrace (prefixWord ++ tailWord_727646) baseStart_727646 baseEnd_727646 := by
    simpa [prefixWord, tailWord_727646, baseEnd_727646] using wordTrace_append hprefix tailTrace_727646
  have hstable : (prefixWord ++ tailWord_727646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727646).length < 2 ^ (prefixWord ++ tailWord_727646).sum := by decide
  have hdescent : baseEnd_727646 < baseStart_727646 := by decide
  rcases family_descends (prefixWord ++ tailWord_727646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727653 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 3]
def baseStart_727653 : Nat := 118140960795 + 727653 * 2 ^ 59
def prefixEnd_727653 : Nat := 4983230072969 + 3 ^ 40 * 727653 * 2
def baseEnd_727653 : Nat := 332120656609908255992081

theorem tailTrace_727653 : CollatzResearch.WordTrace tailWord_727653 prefixEnd_727653 332120656609908255992081 := by
  unfold tailWord_727653
  simp only [CollatzResearch.WordTrace]
  refine ⟨26539685232844929083611613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17693123488563286055741075 26539685232844929083611613)
  ·
    refine ⟨9952381962316848406354355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26539685232844929083611613 9952381962316848406354355)
    ·
      refine ⟨14928572943475272609531533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9952381962316848406354355 14928572943475272609531533)
      ·
        refine ⟨5598214853803227228574325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14928572943475272609531533 5598214853803227228574325)
        ·
          refine ⟨524832642544052552678843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5598214853803227228574325 524832642544052552678843)
          ·
            refine ⟨787248963816078829018265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524832642544052552678843 787248963816078829018265)
            ·
              refine ⟨590436722862059121763699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787248963816078829018265 590436722862059121763699)
              ·
                refine ⟨885655084293088682645549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590436722862059121763699 885655084293088682645549)
                ·
                  refine ⟨332120656609908255992081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885655084293088682645549 332120656609908255992081)
                  ·
                    rfl

theorem cell20_727653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_727653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727653 prefixEnd_727653 := by exact prefixLift 727653
  have htrace : WordTrace (prefixWord ++ tailWord_727653) baseStart_727653 baseEnd_727653 := by
    simpa [prefixWord, tailWord_727653, baseEnd_727653] using wordTrace_append hprefix tailTrace_727653
  have hstable : (prefixWord ++ tailWord_727653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727653).length < 2 ^ (prefixWord ++ tailWord_727653).sum := by decide
  have hdescent : baseEnd_727653 < baseStart_727653 := by decide
  rcases family_descends (prefixWord ++ tailWord_727653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727698 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_727698 : Nat := 118140960795 + 727698 * 2 ^ 59
def prefixEnd_727698 : Nat := 4983230072969 + 3 ^ 40 * 727698 * 2
def baseEnd_727698 : Nat := 332141195836088099491897

theorem tailTrace_727698 : CollatzResearch.WordTrace tailWord_727698 prefixEnd_727698 332141195836088099491897 := by
  unfold tailWord_727698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635331629420475442249937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17694217678454601179333165 6635331629420475442249937)
  ·
    refine ⟨4976498722065356581687453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6635331629420475442249937 4976498722065356581687453)
    ·
      refine ⟨1866187020774508718132795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4976498722065356581687453 1866187020774508718132795)
      ·
        refine ⟨2799280531161763077199193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866187020774508718132795 2799280531161763077199193)
        ·
          refine ⟨2099460398371322307899395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2799280531161763077199193 2099460398371322307899395)
          ·
            refine ⟨3149190597556983461849093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099460398371322307899395 3149190597556983461849093)
            ·
              refine ⟨590473237041934399096705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3149190597556983461849093 590473237041934399096705)
              ·
                refine ⟨442854927781450799322529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590473237041934399096705 442854927781450799322529)
                ·
                  refine ⟨332141195836088099491897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442854927781450799322529 332141195836088099491897)
                  ·
                    rfl

theorem cell20_727698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_727698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727698 prefixEnd_727698 := by exact prefixLift 727698
  have htrace : WordTrace (prefixWord ++ tailWord_727698) baseStart_727698 baseEnd_727698 := by
    simpa [prefixWord, tailWord_727698, baseEnd_727698] using wordTrace_append hprefix tailTrace_727698
  have hstable : (prefixWord ++ tailWord_727698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727698).length < 2 ^ (prefixWord ++ tailWord_727698).sum := by decide
  have hdescent : baseEnd_727698 < baseStart_727698 := by decide
  rcases family_descends (prefixWord ++ tailWord_727698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727716 : List Nat := [2, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_727716 : Nat := 118140960795 + 727716 * 2 ^ 59
def prefixEnd_727716 : Nat := 4983230072969 + 3 ^ 40 * 727716 * 2
def baseEnd_727716 : Nat := 332149411526560036891823

theorem tailTrace_727716 : CollatzResearch.WordTrace tailWord_727716 prefixEnd_727716 332149411526560036891823 := by
  unfold tailWord_727716
  simp only [CollatzResearch.WordTrace]
  refine ⟨13270991515808345421577501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17694655354411127228770001 13270991515808345421577501)
  ·
    refine ⟨4976621818428129533091563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13270991515808345421577501 4976621818428129533091563)
    ·
      refine ⟨7464932727642194299637345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4976621818428129533091563 7464932727642194299637345)
      ·
        refine ⟨5598699545731645724728009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7464932727642194299637345 5598699545731645724728009)
        ·
          refine ⟨4199024659298734293546007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5598699545731645724728009 4199024659298734293546007)
          ·
            refine ⟨6298536988948101440319011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199024659298734293546007 6298536988948101440319011)
            ·
              refine ⟨9447805483422152160478517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298536988948101440319011 9447805483422152160478517)
              ·
                refine ⟨885731764070826765044861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9447805483422152160478517 885731764070826765044861)
                ·
                  refine ⟨332149411526560036891823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885731764070826765044861 332149411526560036891823)
                  ·
                    rfl

theorem cell20_727716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_727716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727716 prefixEnd_727716 := by exact prefixLift 727716
  have htrace : WordTrace (prefixWord ++ tailWord_727716) baseStart_727716 baseEnd_727716 := by
    simpa [prefixWord, tailWord_727716, baseEnd_727716] using wordTrace_append hprefix tailTrace_727716
  have hstable : (prefixWord ++ tailWord_727716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727716).length < 2 ^ (prefixWord ++ tailWord_727716).sum := by decide
  have hdescent : baseEnd_727716 < baseStart_727716 := by decide
  rcases family_descends (prefixWord ++ tailWord_727716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727719 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 4]
def baseStart_727719 : Nat := 118140960795 + 727719 * 2 ^ 59
def prefixEnd_727719 : Nat := 4983230072969 + 3 ^ 40 * 727719 * 2
def baseEnd_727719 : Nat := 332150780808305359791811

theorem tailTrace_727719 : CollatzResearch.WordTrace tailWord_727719 prefixEnd_727719 332150780808305359791811 := by
  unfold tailWord_727719
  simp only [CollatzResearch.WordTrace]
  refine ⟨26542092450605822355514211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17694728300403881570342807 26542092450605822355514211)
  ·
    refine ⟨39813138675908733533271317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26542092450605822355514211 39813138675908733533271317)
    ·
      refine ⟨1866240875433221884372093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39813138675908733533271317 1866240875433221884372093)
      ·
        refine ⟨699840328287458206639535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1866240875433221884372093 699840328287458206639535)
        ·
          refine ⟨1049760492431187309959303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699840328287458206639535 1049760492431187309959303)
          ·
            refine ⟨1574640738646780964938955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049760492431187309959303 1574640738646780964938955)
            ·
              refine ⟨2361961107970171447408433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574640738646780964938955 2361961107970171447408433)
              ·
                refine ⟨1771470830977628585556325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361961107970171447408433 1771470830977628585556325)
                ·
                  refine ⟨332150780808305359791811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771470830977628585556325 332150780808305359791811)
                  ·
                    rfl

theorem cell20_727719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_727719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727719 prefixEnd_727719 := by exact prefixLift 727719
  have htrace : WordTrace (prefixWord ++ tailWord_727719) baseStart_727719 baseEnd_727719 := by
    simpa [prefixWord, tailWord_727719, baseEnd_727719] using wordTrace_append hprefix tailTrace_727719
  have hstable : (prefixWord ++ tailWord_727719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727719).length < 2 ^ (prefixWord ++ tailWord_727719).sum := by decide
  have hdescent : baseEnd_727719 < baseStart_727719 := by decide
  rcases family_descends (prefixWord ++ tailWord_727719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727737 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_727737 : Nat := 118140960795 + 727737 * 2 ^ 59
def prefixEnd_727737 : Nat := 4983230072969 + 3 ^ 40 * 727737 * 2
def baseEnd_727737 : Nat := 332158996498777297191737

theorem tailTrace_727737 : CollatzResearch.WordTrace tailWord_727737 prefixEnd_727737 332158996498777297191737 := by
  unfold tailWord_727737
  simp only [CollatzResearch.WordTrace]
  refine ⟨26542748964540611429669465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17695165976360407619779643 26542748964540611429669465)
  ·
    refine ⟨19907061723405458572252099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26542748964540611429669465 19907061723405458572252099)
    ·
      refine ⟨29860592585108187858378149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19907061723405458572252099 29860592585108187858378149)
      ·
        refine ⟨5598861109707785223445903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29860592585108187858378149 5598861109707785223445903)
        ·
          refine ⟨8398291664561677835168855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598861109707785223445903 8398291664561677835168855)
          ·
            refine ⟨12597437496842516752753283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398291664561677835168855 12597437496842516752753283)
            ·
              refine ⟨18896156245263775129129925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597437496842516752753283 18896156245263775129129925)
              ·
                refine ⟨3543029295986957836711861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18896156245263775129129925 3543029295986957836711861)
                ·
                  refine ⟨332158996498777297191737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3543029295986957836711861 332158996498777297191737)
                  ·
                    rfl

theorem cell20_727737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_727737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727737 prefixEnd_727737 := by exact prefixLift 727737
  have htrace : WordTrace (prefixWord ++ tailWord_727737) baseStart_727737 baseEnd_727737 := by
    simpa [prefixWord, tailWord_727737, baseEnd_727737] using wordTrace_append hprefix tailTrace_727737
  have hstable : (prefixWord ++ tailWord_727737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727737).length < 2 ^ (prefixWord ++ tailWord_727737).sum := by decide
  have hdescent : baseEnd_727737 < baseStart_727737 := by decide
  rcases family_descends (prefixWord ++ tailWord_727737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727754 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_727754 : Nat := 118140960795 + 727754 * 2 ^ 59
def prefixEnd_727754 : Nat := 4983230072969 + 3 ^ 40 * 727754 * 2
def baseEnd_727754 : Nat := 332166755762000793625001

theorem tailTrace_727754 : CollatzResearch.WordTrace tailWord_727754 prefixEnd_727754 332166755762000793625001 := by
  unfold tailWord_727754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635842251369755833259579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17695579336986015555358877 6635842251369755833259579)
  ·
    refine ⟨9953763377054633749889369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6635842251369755833259579 9953763377054633749889369)
    ·
      refine ⟨7465322532790975312417027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9953763377054633749889369 7465322532790975312417027)
      ·
        refine ⟨11197983799186462968625541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7465322532790975312417027 11197983799186462968625541)
        ·
          refine ⟨2099621962347461806617289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11197983799186462968625541 2099621962347461806617289)
          ·
            refine ⟨1574716471760596354962967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2099621962347461806617289 1574716471760596354962967)
            ·
              refine ⟨2362074707640894532444451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574716471760596354962967 2362074707640894532444451)
              ·
                refine ⟨3543112061461341798666677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362074707640894532444451 3543112061461341798666677)
                ·
                  refine ⟨332166755762000793625001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3543112061461341798666677 332166755762000793625001)
                  ·
                    rfl

theorem cell20_727754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_727754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727754 prefixEnd_727754 := by exact prefixLift 727754
  have htrace : WordTrace (prefixWord ++ tailWord_727754) baseStart_727754 baseEnd_727754 := by
    simpa [prefixWord, tailWord_727754, baseEnd_727754] using wordTrace_append hprefix tailTrace_727754
  have hstable : (prefixWord ++ tailWord_727754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727754).length < 2 ^ (prefixWord ++ tailWord_727754).sum := by decide
  have hdescent : baseEnd_727754 < baseStart_727754 := by decide
  rcases family_descends (prefixWord ++ tailWord_727754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727761 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_727761 : Nat := 118140960795 + 727761 * 2 ^ 59
def prefixEnd_727761 : Nat := 4983230072969 + 3 ^ 40 * 727761 * 2
def baseEnd_727761 : Nat := 332169950752739880391639

theorem tailTrace_727761 : CollatzResearch.WordTrace tailWord_727761 prefixEnd_727761 332169950752739880391639 := by
  unfold tailWord_727761
  simp only [CollatzResearch.WordTrace]
  refine ⟨26543624316453663528543137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17695749544302442352362091 26543624316453663528543137)
  ·
    refine ⟨19907718237340247646407353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26543624316453663528543137 19907718237340247646407353)
    ·
      refine ⟨14930788678005185734805515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19907718237340247646407353 14930788678005185734805515)
      ·
        refine ⟨22396183017007778602208273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14930788678005185734805515 22396183017007778602208273)
        ·
          refine ⟨16797137262755833951656205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22396183017007778602208273 16797137262755833951656205)
          ·
            refine ⟨6298926473533437731871077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16797137262755833951656205 6298926473533437731871077)
            ·
              refine ⟨1181048713787519574725827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6298926473533437731871077 1181048713787519574725827)
              ·
                refine ⟨1771573070681279362088741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181048713787519574725827 1771573070681279362088741)
                ·
                  refine ⟨332169950752739880391639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771573070681279362088741 332169950752739880391639)
                  ·
                    rfl

theorem cell20_727761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_727761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727761 prefixEnd_727761 := by exact prefixLift 727761
  have htrace : WordTrace (prefixWord ++ tailWord_727761) baseStart_727761 baseEnd_727761 := by
    simpa [prefixWord, tailWord_727761, baseEnd_727761] using wordTrace_append hprefix tailTrace_727761
  have hstable : (prefixWord ++ tailWord_727761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727761).length < 2 ^ (prefixWord ++ tailWord_727761).sum := by decide
  have hdescent : baseEnd_727761 < baseStart_727761 := by decide
  rcases family_descends (prefixWord ++ tailWord_727761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727816 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 4]
def baseStart_727816 : Nat := 118140960795 + 727816 * 2 ^ 59
def prefixEnd_727816 : Nat := 4983230072969 + 3 ^ 40 * 727816 * 2
def baseEnd_727816 : Nat := 332195054251404133558081

theorem tailTrace_727816 : CollatzResearch.WordTrace tailWord_727816 prefixEnd_727816 332195054251404133558081 := by
  unfold tailWord_727816
  simp only [CollatzResearch.WordTrace]
  refine ⟨13272815165627203960897651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17697086887502938614530201 13272815165627203960897651)
  ·
    refine ⟨19909222748440805941346477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13272815165627203960897651 19909222748440805941346477)
    ·
      refine ⟨7465958530665302228004929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19909222748440805941346477 7465958530665302228004929)
      ·
        refine ⟨5599468897998976671003697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7465958530665302228004929 5599468897998976671003697)
        ·
          refine ⟨4199601673499232503252773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5599468897998976671003697 4199601673499232503252773)
          ·
            refine ⟨787425313781106094359895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4199601673499232503252773 787425313781106094359895)
            ·
              refine ⟨1181137970671659141539843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787425313781106094359895 1181137970671659141539843)
              ·
                refine ⟨1771706956007488712309765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181137970671659141539843 1771706956007488712309765)
                ·
                  refine ⟨332195054251404133558081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771706956007488712309765 332195054251404133558081)
                  ·
                    rfl

theorem cell20_727816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_727816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727816 prefixEnd_727816 := by exact prefixLift 727816
  have htrace : WordTrace (prefixWord ++ tailWord_727816) baseStart_727816 baseEnd_727816 := by
    simpa [prefixWord, tailWord_727816, baseEnd_727816] using wordTrace_append hprefix tailTrace_727816
  have hstable : (prefixWord ++ tailWord_727816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727816).length < 2 ^ (prefixWord ++ tailWord_727816).sum := by decide
  have hdescent : baseEnd_727816 < baseStart_727816 := by decide
  rcases family_descends (prefixWord ++ tailWord_727816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727826 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_727826 : Nat := 118140960795 + 727826 * 2 ^ 59
def prefixEnd_727826 : Nat := 4983230072969 + 3 ^ 40 * 727826 * 2
def baseEnd_727826 : Nat := 332199618523888543224707

theorem tailTrace_727826 : CollatzResearch.WordTrace tailWord_727826 prefixEnd_727826 332199618523888543224707 := by
  unfold tailWord_727826
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636498765304544907414833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17697330040812119753106221 6636498765304544907414833)
  ·
    refine ⟨4977374073978408680561125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6636498765304544907414833 4977374073978408680561125)
    ·
      refine ⟨933257638870951627605211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4977374073978408680561125 933257638870951627605211)
      ·
        refine ⟨1399886458306427441407817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933257638870951627605211 1399886458306427441407817)
        ·
          refine ⟨1049914843729820581055863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399886458306427441407817 1049914843729820581055863)
          ·
            refine ⟨1574872265594730871583795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049914843729820581055863 1574872265594730871583795)
            ·
              refine ⟨2362308398392096307375693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574872265594730871583795 2362308398392096307375693)
              ·
                refine ⟨885865649397036115265885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2362308398392096307375693 885865649397036115265885)
                ·
                  refine ⟨332199618523888543224707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885865649397036115265885 332199618523888543224707)
                  ·
                    rfl

theorem cell20_727826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_727826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727826 prefixEnd_727826 := by exact prefixLift 727826
  have htrace : WordTrace (prefixWord ++ tailWord_727826) baseStart_727826 baseEnd_727826 := by
    simpa [prefixWord, tailWord_727826, baseEnd_727826] using wordTrace_append hprefix tailTrace_727826
  have hstable : (prefixWord ++ tailWord_727826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727826).length < 2 ^ (prefixWord ++ tailWord_727826).sum := by decide
  have hdescent : baseEnd_727826 < baseStart_727826 := by decide
  rcases family_descends (prefixWord ++ tailWord_727826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727865 : List Nat := [1, 2, 1, 16]
def baseStart_727865 : Nat := 118140960795 + 727865 * 2 ^ 59
def prefixEnd_727865 : Nat := 4983230072969 + 3 ^ 40 * 727865 * 2
def baseEnd_727865 : Nat := 1367149873195793172529

theorem tailTrace_727865 : CollatzResearch.WordTrace tailWord_727865 prefixEnd_727865 1367149873195793172529 := by
  unfold tailWord_727865
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547417508076889290329049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17698278338717926193552699 26547417508076889290329049)
  ·
    refine ⟨19910563131057666967746787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26547417508076889290329049 19910563131057666967746787)
    ·
      refine ⟨29865844696586500451620181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19910563131057666967746787 29865844696586500451620181)
      ·
        refine ⟨1367149873195793172529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 29865844696586500451620181 1367149873195793172529)
        ·
          rfl

theorem cell20_727865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 16].length) (baseStart_727865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727865 prefixEnd_727865 := by exact prefixLift 727865
  have htrace : WordTrace (prefixWord ++ tailWord_727865) baseStart_727865 baseEnd_727865 := by
    simpa [prefixWord, tailWord_727865, baseEnd_727865] using wordTrace_append hprefix tailTrace_727865
  have hstable : (prefixWord ++ tailWord_727865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727865).length < 2 ^ (prefixWord ++ tailWord_727865).sum := by decide
  have hdescent : baseEnd_727865 < baseStart_727865 := by decide
  rcases family_descends (prefixWord ++ tailWord_727865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727871 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 2]
def baseStart_727871 : Nat := 118140960795 + 727871 * 2 ^ 59
def prefixEnd_727871 : Nat := 4983230072969 + 3 ^ 40 * 727871 * 2
def baseEnd_727871 : Nat := 332220157750068386724523

theorem tailTrace_727871 : CollatzResearch.WordTrace tailWord_727871 prefixEnd_727871 332220157750068386724523 := by
  unfold tailWord_727871
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547636346055152315047467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17698424230703434876698311 26547636346055152315047467)
  ·
    refine ⟨39821454519082728472571201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26547636346055152315047467 39821454519082728472571201)
    ·
      refine ⟨29866090889312046354428401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39821454519082728472571201 29866090889312046354428401)
      ·
        refine ⟨22399568166984034765821301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29866090889312046354428401 22399568166984034765821301)
        ·
          refine ⟨2099959515654753259295747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22399568166984034765821301 2099959515654753259295747)
          ·
            refine ⟨3149939273482129888943621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099959515654753259295747 3149939273482129888943621)
            ·
              refine ⟨590613613777899354176929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3149939273482129888943621 590613613777899354176929)
              ·
                refine ⟨442960210333424515632697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590613613777899354176929 442960210333424515632697)
                ·
                  refine ⟨332220157750068386724523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442960210333424515632697 332220157750068386724523)
                  ·
                    rfl

theorem cell20_727871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 2].length) (baseStart_727871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727871 prefixEnd_727871 := by exact prefixLift 727871
  have htrace : WordTrace (prefixWord ++ tailWord_727871) baseStart_727871 baseEnd_727871 := by
    simpa [prefixWord, tailWord_727871, baseEnd_727871] using wordTrace_append hprefix tailTrace_727871
  have hstable : (prefixWord ++ tailWord_727871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727871).length < 2 ^ (prefixWord ++ tailWord_727871).sum := by decide
  have hdescent : baseEnd_727871 < baseStart_727871 := by decide
  rcases family_descends (prefixWord ++ tailWord_727871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727892 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_727892 : Nat := 118140960795 + 727892 * 2 ^ 59
def prefixEnd_727892 : Nat := 4983230072969 + 3 ^ 40 * 727892 * 2
def baseEnd_727892 : Nat := 332229742722285647024437

theorem tailTrace_727892 : CollatzResearch.WordTrace tailWord_727892 prefixEnd_727892 332229742722285647024437 := by
  unfold tailWord_727892
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274201139489536450780965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17698934852652715267707953 13274201139489536450780965)
  ·
    refine ⟨2488912713654288084521431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13274201139489536450780965 2488912713654288084521431)
    ·
      refine ⟨3733369070481432126782147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488912713654288084521431 3733369070481432126782147)
      ·
        refine ⟨5600053605722148190173221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733369070481432126782147 5600053605722148190173221)
        ·
          refine ⟨1050010051072902785657479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5600053605722148190173221 1050010051072902785657479)
          ·
            refine ⟨1575015076609354178486219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050010051072902785657479 1575015076609354178486219)
            ·
              refine ⟨2362522614914031267729329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575015076609354178486219 2362522614914031267729329)
              ·
                refine ⟨1771891961185523450796997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362522614914031267729329 1771891961185523450796997)
                ·
                  refine ⟨332229742722285647024437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771891961185523450796997 332229742722285647024437)
                  ·
                    rfl

theorem cell20_727892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_727892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727892 prefixEnd_727892 := by exact prefixLift 727892
  have htrace : WordTrace (prefixWord ++ tailWord_727892) baseStart_727892 baseEnd_727892 := by
    simpa [prefixWord, tailWord_727892, baseEnd_727892] using wordTrace_append hprefix tailTrace_727892
  have hstable : (prefixWord ++ tailWord_727892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727892).length < 2 ^ (prefixWord ++ tailWord_727892).sum := by decide
  have hdescent : baseEnd_727892 < baseStart_727892 := by decide
  rcases family_descends (prefixWord ++ tailWord_727892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727964 : List Nat := [2, 2, 3, 3, 2, 2, 1, 3, 2]
def baseStart_727964 : Nat := 118140960795 + 727964 * 2 ^ 59
def prefixEnd_727964 : Nat := 4983230072969 + 3 ^ 40 * 727964 * 2
def baseEnd_727964 : Nat := 332262605484173396624143

theorem tailTrace_727964 : CollatzResearch.WordTrace tailWord_727964 prefixEnd_727964 332262605484173396624143 := by
  unfold tailWord_727964
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275514167359114599091473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17700685556478819465455297 13275514167359114599091473)
  ·
    refine ⟨9956635625519335949318605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13275514167359114599091473 9956635625519335949318605)
    ·
      refine ⟨3733738359569750980994477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9956635625519335949318605 3733738359569750980994477)
      ·
        refine ⟨1400151884838656617872929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3733738359569750980994477 1400151884838656617872929)
        ·
          refine ⟨1050113913628992463404697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400151884838656617872929 1050113913628992463404697)
          ·
            refine ⟨787585435221744347553523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050113913628992463404697 787585435221744347553523)
            ·
              refine ⟨1181378152832616521330285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787585435221744347553523 1181378152832616521330285)
              ·
                refine ⟨443016807312231195498857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181378152832616521330285 443016807312231195498857)
                ·
                  refine ⟨332262605484173396624143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443016807312231195498857 332262605484173396624143)
                  ·
                    rfl

theorem cell20_727964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_727964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727964 prefixEnd_727964 := by exact prefixLift 727964
  have htrace : WordTrace (prefixWord ++ tailWord_727964) baseStart_727964 baseEnd_727964 := by
    simpa [prefixWord, tailWord_727964, baseEnd_727964] using wordTrace_append hprefix tailTrace_727964
  have hstable : (prefixWord ++ tailWord_727964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727964).length < 2 ^ (prefixWord ++ tailWord_727964).sum := by decide
  have hdescent : baseEnd_727964 < baseStart_727964 := by decide
  rcases family_descends (prefixWord ++ tailWord_727964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727965 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_727965 : Nat := 118140960795 + 727965 * 2 ^ 59
def prefixEnd_727965 : Nat := 4983230072969 + 3 ^ 40 * 727965 * 2
def baseEnd_727965 : Nat := 332263061911421837590805

theorem tailTrace_727965 : CollatzResearch.WordTrace tailWord_727965 prefixEnd_727965 332263061911421837590805 := by
  unfold tailWord_727965
  simp only [CollatzResearch.WordTrace]
  refine ⟨26551064807714606368969349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17700709871809737579312899 26551064807714606368969349)
  ·
    refine ⟨4978324651446488694181753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26551064807714606368969349 4978324651446488694181753)
    ·
      refine ⟨3733743488584866520636315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4978324651446488694181753 3733743488584866520636315)
      ·
        refine ⟨5600615232877299780954473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733743488584866520636315 5600615232877299780954473)
        ·
          refine ⟨4200461424657974835715855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600615232877299780954473 4200461424657974835715855)
          ·
            refine ⟨6300692136986962253573783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200461424657974835715855 6300692136986962253573783)
            ·
              refine ⟨9451038205480443380360675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6300692136986962253573783 9451038205480443380360675)
              ·
                refine ⟨14176557308220665070541013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9451038205480443380360675 14176557308220665070541013)
                ·
                  refine ⟨332263061911421837590805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14176557308220665070541013 332263061911421837590805)
                  ·
                    rfl

theorem cell20_727965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_727965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727965 prefixEnd_727965 := by exact prefixLift 727965
  have htrace : WordTrace (prefixWord ++ tailWord_727965) baseStart_727965 baseEnd_727965 := by
    simpa [prefixWord, tailWord_727965, baseEnd_727965] using wordTrace_append hprefix tailTrace_727965
  have hstable : (prefixWord ++ tailWord_727965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727965).length < 2 ^ (prefixWord ++ tailWord_727965).sum := by decide
  have hdescent : baseEnd_727965 < baseStart_727965 := by decide
  rcases family_descends (prefixWord ++ tailWord_727965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727968 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 2]
def baseStart_727968 : Nat := 118140960795 + 727968 * 2 ^ 59
def prefixEnd_727968 : Nat := 4983230072969 + 3 ^ 40 * 727968 * 2
def baseEnd_727968 : Nat := 332264431193167160490793

theorem tailTrace_727968 : CollatzResearch.WordTrace tailWord_727968 prefixEnd_727968 332264431193167160490793 := by
  unfold tailWord_727968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275587113351868940664279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17700782817802491920885705 13275587113351868940664279)
  ·
    refine ⟨19913380670027803410996419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13275587113351868940664279 19913380670027803410996419)
    ·
      refine ⟨29870071005041705116494629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19913380670027803410996419 29870071005041705116494629)
      ·
        refine ⟨5600638313445319709342743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29870071005041705116494629 5600638313445319709342743)
        ·
          refine ⟨8400957470167979564014115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600638313445319709342743 8400957470167979564014115)
          ·
            refine ⟨12601436205251969346021173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400957470167979564014115 12601436205251969346021173)
            ·
              refine ⟨1181384644242372126189485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12601436205251969346021173 1181384644242372126189485)
              ·
                refine ⟨443019241590889547321057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181384644242372126189485 443019241590889547321057)
                ·
                  refine ⟨332264431193167160490793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443019241590889547321057 332264431193167160490793)
                  ·
                    rfl

theorem cell20_727968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_727968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727968 prefixEnd_727968 := by exact prefixLift 727968
  have htrace : WordTrace (prefixWord ++ tailWord_727968) baseStart_727968 baseEnd_727968 := by
    simpa [prefixWord, tailWord_727968, baseEnd_727968] using wordTrace_append hprefix tailTrace_727968
  have hstable : (prefixWord ++ tailWord_727968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727968).length < 2 ^ (prefixWord ++ tailWord_727968).sum := by decide
  have hdescent : baseEnd_727968 < baseStart_727968 := by decide
  rcases family_descends (prefixWord ++ tailWord_727968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727975 : List Nat := [1, 1, 6, 1, 3, 2, 6]
def baseStart_727975 : Nat := 118140960795 + 727975 * 2 ^ 59
def prefixEnd_727975 : Nat := 4983230072969 + 3 ^ 40 * 727975 * 2
def baseEnd_727975 : Nat := 36918625131545138584159

theorem tailTrace_727975 : CollatzResearch.WordTrace tailWord_727975 prefixEnd_727975 36918625131545138584159 := by
  unfold tailWord_727975
  simp only [CollatzResearch.WordTrace]
  refine ⟨26551429537678378076833379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17700953025118918717888919 26551429537678378076833379)
  ·
    refine ⟨39827144306517567115250069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26551429537678378076833379 39827144306517567115250069)
    ·
      refine ⟨1866897389368010958527347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39827144306517567115250069 1866897389368010958527347)
      ·
        refine ⟨2800346084052016437791021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866897389368010958527347 2800346084052016437791021)
        ·
          refine ⟨1050129781519506164171633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2800346084052016437791021 1050129781519506164171633)
          ·
            refine ⟨787597336139629623128725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050129781519506164171633 787597336139629623128725)
            ·
              refine ⟨36918625131545138584159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 787597336139629623128725 36918625131545138584159)
              ·
                rfl

theorem cell20_727975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 6].length) (baseStart_727975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727975 prefixEnd_727975 := by exact prefixLift 727975
  have htrace : WordTrace (prefixWord ++ tailWord_727975) baseStart_727975 baseEnd_727975 := by
    simpa [prefixWord, tailWord_727975, baseEnd_727975] using wordTrace_append hprefix tailTrace_727975
  have hstable : (prefixWord ++ tailWord_727975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727975).length < 2 ^ (prefixWord ++ tailWord_727975).sum := by decide
  have hdescent : baseEnd_727975 < baseStart_727975 := by decide
  rcases family_descends (prefixWord ++ tailWord_727975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727981 : List Nat := [1, 5, 2, 3, 1, 1, 3, 2, 2]
def baseStart_727981 : Nat := 118140960795 + 727981 * 2 ^ 59
def prefixEnd_727981 : Nat := 4983230072969 + 3 ^ 40 * 727981 * 2
def baseEnd_727981 : Nat := 332270364747396893057407

theorem tailTrace_727981 : CollatzResearch.WordTrace tailWord_727981 prefixEnd_727981 332270364747396893057407 := by
  unfold tailWord_727981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26551648375656641101551797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17701098917104427401034531 26551648375656641101551797)
  ·
    refine ⟨2489217035217810103270481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26551648375656641101551797 2489217035217810103270481)
    ·
      refine ⟨1866912776413357577452861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2489217035217810103270481 1866912776413357577452861)
      ·
        refine ⟨700092291155009091544823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1866912776413357577452861 700092291155009091544823)
        ·
          refine ⟨1050138436732513637317235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700092291155009091544823 1050138436732513637317235)
          ·
            refine ⟨1575207655098770455975853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050138436732513637317235 1575207655098770455975853)
            ·
              refine ⟨590702870662038920990945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1575207655098770455975853 590702870662038920990945)
              ·
                refine ⟨443027152996529190743209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590702870662038920990945 443027152996529190743209)
                ·
                  refine ⟨332270364747396893057407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443027152996529190743209 332270364747396893057407)
                  ·
                    rfl

theorem cell20_727981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_727981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727981 prefixEnd_727981 := by exact prefixLift 727981
  have htrace : WordTrace (prefixWord ++ tailWord_727981) baseStart_727981 baseEnd_727981 := by
    simpa [prefixWord, tailWord_727981, baseEnd_727981] using wordTrace_append hprefix tailTrace_727981
  have hstable : (prefixWord ++ tailWord_727981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727981).length < 2 ^ (prefixWord ++ tailWord_727981).sum := by decide
  have hdescent : baseEnd_727981 < baseStart_727981 := by decide
  rcases family_descends (prefixWord ++ tailWord_727981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_727985 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 4]
def baseStart_727985 : Nat := 118140960795 + 727985 * 2 ^ 59
def prefixEnd_727985 : Nat := 4983230072969 + 3 ^ 40 * 727985 * 2
def baseEnd_727985 : Nat := 332272190456390656924057

theorem tailTrace_727985 : CollatzResearch.WordTrace tailWord_727985 prefixEnd_727985 332272190456390656924057 := by
  unfold tailWord_727985
  simp only [CollatzResearch.WordTrace]
  refine ⟨26551794267642149784697409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17701196178428099856464939 26551794267642149784697409)
  ·
    refine ⟨19913845700731612338523057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26551794267642149784697409 19913845700731612338523057)
    ·
      refine ⟨14935384275548709253892293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19913845700731612338523057 14935384275548709253892293)
      ·
        refine ⟨2800384551665382985104805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14935384275548709253892293 2800384551665382985104805)
        ·
          refine ⟨525072103437259309707151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2800384551665382985104805 525072103437259309707151)
          ·
            refine ⟨787608155155888964560727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525072103437259309707151 787608155155888964560727)
            ·
              refine ⟨1181412232733833446841091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787608155155888964560727 1181412232733833446841091)
              ·
                refine ⟨1772118349100750170261637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181412232733833446841091 1772118349100750170261637)
                ·
                  refine ⟨332272190456390656924057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772118349100750170261637 332272190456390656924057)
                  ·
                    rfl

theorem cell20_727985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_727985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_727985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_727985 prefixEnd_727985 := by exact prefixLift 727985
  have htrace : WordTrace (prefixWord ++ tailWord_727985) baseStart_727985 baseEnd_727985 := by
    simpa [prefixWord, tailWord_727985, baseEnd_727985] using wordTrace_append hprefix tailTrace_727985
  have hstable : (prefixWord ++ tailWord_727985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_727985).length < 2 ^ (prefixWord ++ tailWord_727985).sum := by decide
  have hdescent : baseEnd_727985 < baseStart_727985 := by decide
  rcases family_descends (prefixWord ++ tailWord_727985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728003 : List Nat := [1, 1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_728003 : Nat := 118140960795 + 728003 * 2 ^ 59
def prefixEnd_728003 : Nat := 4983230072969 + 3 ^ 40 * 728003 * 2
def baseEnd_728003 : Nat := 332280406146862594323983

theorem tailTrace_728003 : CollatzResearch.WordTrace tailWord_728003 prefixEnd_728003 332280406146862594323983 := by
  unfold tailWord_728003
  simp only [CollatzResearch.WordTrace]
  refine ⟨26552450781576938858852663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17701633854384625905901775 26552450781576938858852663)
  ·
    refine ⟨39828676172365408288278995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26552450781576938858852663 39828676172365408288278995)
    ·
      refine ⟨59743014258548112432418493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39828676172365408288278995 59743014258548112432418493)
      ·
        refine ⟨22403630346955542162156935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59743014258548112432418493 22403630346955542162156935)
        ·
          refine ⟨33605445520433313243235403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22403630346955542162156935 33605445520433313243235403)
          ·
            refine ⟨50408168280649969864853105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33605445520433313243235403 50408168280649969864853105)
            ·
              refine ⟨37806126210487477398639829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50408168280649969864853105 37806126210487477398639829)
              ·
                refine ⟨886081083058300251530621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37806126210487477398639829 886081083058300251530621)
                ·
                  refine ⟨332280406146862594323983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886081083058300251530621 332280406146862594323983)
                  ·
                    rfl

theorem cell20_728003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_728003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728003 prefixEnd_728003 := by exact prefixLift 728003
  have htrace : WordTrace (prefixWord ++ tailWord_728003) baseStart_728003 baseEnd_728003 := by
    simpa [prefixWord, tailWord_728003, baseEnd_728003] using wordTrace_append hprefix tailTrace_728003
  have hstable : (prefixWord ++ tailWord_728003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728003).length < 2 ^ (prefixWord ++ tailWord_728003).sum := by decide
  have hdescent : baseEnd_728003 < baseStart_728003 := by decide
  rcases family_descends (prefixWord ++ tailWord_728003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728010 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_728010 : Nat := 118140960795 + 728010 * 2 ^ 59
def prefixEnd_728010 : Nat := 4983230072969 + 3 ^ 40 * 728010 * 2
def baseEnd_728010 : Nat := 332283601137601681090621

theorem tailTrace_728010 : CollatzResearch.WordTrace tailWord_728010 prefixEnd_728010 332283601137601681090621 := by
  unfold tailWord_728010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638176523137894763589371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17701804061701052702904989 6638176523137894763589371)
  ·
    refine ⟨9957264784706842145384057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6638176523137894763589371 9957264784706842145384057)
    ·
      refine ⟨7467948588530131609038043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9957264784706842145384057 7467948588530131609038043)
      ·
        refine ⟨11201922882795197413557065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467948588530131609038043 11201922882795197413557065)
        ·
          refine ⟨8401442162096398060167799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11201922882795197413557065 8401442162096398060167799)
          ·
            refine ⟨12602163243144597090251699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8401442162096398060167799 12602163243144597090251699)
            ·
              refine ⟨18903244864716895635377549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12602163243144597090251699 18903244864716895635377549)
              ·
                refine ⟨7088716824268835863266581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18903244864716895635377549 7088716824268835863266581)
                ·
                  refine ⟨332283601137601681090621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7088716824268835863266581 332283601137601681090621)
                  ·
                    rfl

theorem cell20_728010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_728010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728010 prefixEnd_728010 := by exact prefixLift 728010
  have htrace : WordTrace (prefixWord ++ tailWord_728010) baseStart_728010 baseEnd_728010 := by
    simpa [prefixWord, tailWord_728010, baseEnd_728010] using wordTrace_append hprefix tailTrace_728010
  have hstable : (prefixWord ++ tailWord_728010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728010).length < 2 ^ (prefixWord ++ tailWord_728010).sum := by decide
  have hdescent : baseEnd_728010 < baseStart_728010 := by decide
  rcases family_descends (prefixWord ++ tailWord_728010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728017 : List Nat := [1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_728017 : Nat := 118140960795 + 728017 * 2 ^ 59
def prefixEnd_728017 : Nat := 4983230072969 + 3 ^ 40 * 728017 * 2
def baseEnd_728017 : Nat := 110762265376113589285753

theorem tailTrace_728017 : CollatzResearch.WordTrace tailWord_728017 prefixEnd_728017 110762265376113589285753 := by
  unfold tailWord_728017
  simp only [CollatzResearch.WordTrace]
  refine ⟨26552961403526219249862305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17701974269017479499908203 26552961403526219249862305)
  ·
    refine ⟨19914721052644664437396729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26552961403526219249862305 19914721052644664437396729)
    ·
      refine ⟨14936040789483498328047547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19914721052644664437396729 14936040789483498328047547)
      ·
        refine ⟨22404061184225247492071321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14936040789483498328047547 22404061184225247492071321)
        ·
          refine ⟨16803045888168935619053491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22404061184225247492071321 16803045888168935619053491)
          ·
            refine ⟨25204568832253403428580237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16803045888168935619053491 25204568832253403428580237)
            ·
              refine ⟨9451713312095026285717589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25204568832253403428580237 9451713312095026285717589)
              ·
                refine ⟨110762265376113589285753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9451713312095026285717589 110762265376113589285753)
                ·
                  rfl

theorem cell20_728017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_728017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728017 prefixEnd_728017 := by exact prefixLift 728017
  have htrace : WordTrace (prefixWord ++ tailWord_728017) baseStart_728017 baseEnd_728017 := by
    simpa [prefixWord, tailWord_728017, baseEnd_728017] using wordTrace_append hprefix tailTrace_728017
  have hstable : (prefixWord ++ tailWord_728017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728017).length < 2 ^ (prefixWord ++ tailWord_728017).sum := by decide
  have hdescent : baseEnd_728017 < baseStart_728017 := by decide
  rcases family_descends (prefixWord ++ tailWord_728017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728048 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_728048 : Nat := 118140960795 + 728048 * 2 ^ 59
def prefixEnd_728048 : Nat := 4983230072969 + 3 ^ 40 * 728048 * 2
def baseEnd_728048 : Nat := 332300945373042437823799

theorem tailTrace_728048 : CollatzResearch.WordTrace tailWord_728048 prefixEnd_728048 332300945373042437823799 := by
  unfold tailWord_728048
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277046033206955772120399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17702728044275941029493865 13277046033206955772120399)
  ·
    refine ⟨19915569049810433658180599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13277046033206955772120399 19915569049810433658180599)
    ·
      refine ⟨29873353574715650487270899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19915569049810433658180599 29873353574715650487270899)
      ·
        refine ⟨44810030362073475730906349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29873353574715650487270899 44810030362073475730906349)
        ·
          refine ⟨16803761385777553399089881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44810030362073475730906349 16803761385777553399089881)
          ·
            refine ⟨12602821039333165049317411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16803761385777553399089881 12602821039333165049317411)
            ·
              refine ⟨18904231558999747573976117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12602821039333165049317411 18904231558999747573976117)
              ·
                refine ⟨1772271708656226335060261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18904231558999747573976117 1772271708656226335060261)
                ·
                  refine ⟨332300945373042437823799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772271708656226335060261 332300945373042437823799)
                  ·
                    rfl

theorem cell20_728048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_728048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728048 prefixEnd_728048 := by exact prefixLift 728048
  have htrace : WordTrace (prefixWord ++ tailWord_728048) baseStart_728048 baseEnd_728048 := by
    simpa [prefixWord, tailWord_728048, baseEnd_728048] using wordTrace_append hprefix tailTrace_728048
  have hstable : (prefixWord ++ tailWord_728048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728048).length < 2 ^ (prefixWord ++ tailWord_728048).sum := by decide
  have hdescent : baseEnd_728048 < baseStart_728048 := by decide
  rcases family_descends (prefixWord ++ tailWord_728048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728065 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 4]
def baseStart_728065 : Nat := 118140960795 + 728065 * 2 ^ 59
def prefixEnd_728065 : Nat := 4983230072969 + 3 ^ 40 * 728065 * 2
def baseEnd_728065 : Nat := 332308704636265934257063

theorem tailTrace_728065 : CollatzResearch.WordTrace tailWord_728065 prefixEnd_728065 332308704636265934257063 := by
  unfold tailWord_728065
  simp only [CollatzResearch.WordTrace]
  refine ⟨26554712107352323447609649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17703141404901548965073099 26554712107352323447609649)
  ·
    refine ⟨19916034080514242585707237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26554712107352323447609649 19916034080514242585707237)
    ·
      refine ⟨3734256390096420484820107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19916034080514242585707237 3734256390096420484820107)
      ·
        refine ⟨5601384585144630727230161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734256390096420484820107 5601384585144630727230161)
        ·
          refine ⟨4201038438858473045422621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5601384585144630727230161 4201038438858473045422621)
          ·
            refine ⟨1575389414571927392033483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4201038438858473045422621 1575389414571927392033483)
            ·
              refine ⟨2363084121857891088050225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575389414571927392033483 2363084121857891088050225)
              ·
                refine ⟨1772313091393418316037669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363084121857891088050225 1772313091393418316037669)
                ·
                  refine ⟨332308704636265934257063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772313091393418316037669 332308704636265934257063)
                  ·
                    rfl

theorem cell20_728065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_728065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728065 prefixEnd_728065 := by exact prefixLift 728065
  have htrace : WordTrace (prefixWord ++ tailWord_728065) baseStart_728065 baseEnd_728065 := by
    simpa [prefixWord, tailWord_728065, baseEnd_728065] using wordTrace_append hprefix tailTrace_728065
  have hstable : (prefixWord ++ tailWord_728065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728065).length < 2 ^ (prefixWord ++ tailWord_728065).sum := by decide
  have hdescent : baseEnd_728065 < baseStart_728065 := by decide
  rcases family_descends (prefixWord ++ tailWord_728065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728092 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 3]
def baseStart_728092 : Nat := 118140960795 + 728092 * 2 ^ 59
def prefixEnd_728092 : Nat := 4983230072969 + 3 ^ 40 * 728092 * 2
def baseEnd_728092 : Nat := 332321028171973840356953

theorem tailTrace_728092 : CollatzResearch.WordTrace tailWord_728092 prefixEnd_728092 332321028171973840356953 := by
  unfold tailWord_728092
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277848439127253529421265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17703797918836338039228353 13277848439127253529421265)
  ·
    refine ⟨9958386329345440147065949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13277848439127253529421265 9958386329345440147065949)
    ·
      refine ⟨3734394873504540055149731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9958386329345440147065949 3734394873504540055149731)
      ·
        refine ⟨5601592310256810082724597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734394873504540055149731 5601592310256810082724597)
        ·
          refine ⟨525149279086575945255431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5601592310256810082724597 525149279086575945255431)
          ·
            refine ⟨787723918629863917883147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525149279086575945255431 787723918629863917883147)
            ·
              refine ⟨1181585877944795876824721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787723918629863917883147 1181585877944795876824721)
              ·
                refine ⟨886189408458596907618541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181585877944795876824721 886189408458596907618541)
                ·
                  refine ⟨332321028171973840356953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886189408458596907618541 332321028171973840356953)
                  ·
                    rfl

theorem cell20_728092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_728092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728092 prefixEnd_728092 := by exact prefixLift 728092
  have htrace : WordTrace (prefixWord ++ tailWord_728092) baseStart_728092 baseEnd_728092 := by
    simpa [prefixWord, tailWord_728092, baseEnd_728092] using wordTrace_append hprefix tailTrace_728092
  have hstable : (prefixWord ++ tailWord_728092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728092).length < 2 ^ (prefixWord ++ tailWord_728092).sum := by decide
  have hdescent : baseEnd_728092 < baseStart_728092 := by decide
  rcases family_descends (prefixWord ++ tailWord_728092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728110 : List Nat := [4, 1, 3, 1, 1, 1, 2, 7]
def baseStart_728110 : Nat := 118140960795 + 728110 * 2 ^ 59
def prefixEnd_728110 : Nat := 4983230072969 + 3 ^ 40 * 728110 * 2
def baseEnd_728110 : Nat := 110776414620815259252293

theorem tailTrace_728110 : CollatzResearch.WordTrace tailWord_728110 prefixEnd_728110 110776414620815259252293 := by
  unfold tailWord_728110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319544174023662016624723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17704235594792864088665189 3319544174023662016624723)
  ·
    refine ⟨4979316261035493024937085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3319544174023662016624723 4979316261035493024937085)
    ·
      refine ⟨1867243597888309884351407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4979316261035493024937085 1867243597888309884351407)
      ·
        refine ⟨2800865396832464826527111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867243597888309884351407 2800865396832464826527111)
        ·
          refine ⟨4201298095248697239790667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800865396832464826527111 4201298095248697239790667)
          ·
            refine ⟨6301947142873045859686001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201298095248697239790667 6301947142873045859686001)
            ·
              refine ⟨4726460357154784394764501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301947142873045859686001 4726460357154784394764501)
              ·
                refine ⟨110776414620815259252293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4726460357154784394764501 110776414620815259252293)
                ·
                  rfl

theorem cell20_728110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_728110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728110 prefixEnd_728110 := by exact prefixLift 728110
  have htrace : WordTrace (prefixWord ++ tailWord_728110) baseStart_728110 baseEnd_728110 := by
    simpa [prefixWord, tailWord_728110, baseEnd_728110] using wordTrace_append hprefix tailTrace_728110
  have hstable : (prefixWord ++ tailWord_728110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728110).length < 2 ^ (prefixWord ++ tailWord_728110).sum := by decide
  have hdescent : baseEnd_728110 < baseStart_728110 := by decide
  rcases family_descends (prefixWord ++ tailWord_728110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728131 : List Nat := [1, 1, 1, 3, 1, 2, 5, 6]
def baseStart_728131 : Nat := 118140960795 + 728131 * 2 ^ 59
def prefixEnd_728131 : Nat := 4983230072969 + 3 ^ 40 * 728131 * 2
def baseEnd_728131 : Nat := 110779609611554346018931

theorem tailTrace_728131 : CollatzResearch.WordTrace tailWord_728131 prefixEnd_728131 110779609611554346018931 := by
  unfold tailWord_728131
  simp only [CollatzResearch.WordTrace]
  refine ⟨26557119325113216719512247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17704746216742144479674831 26557119325113216719512247)
  ·
    refine ⟨39835678987669825079268371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26557119325113216719512247 39835678987669825079268371)
    ·
      refine ⟨59753518481504737618902557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39835678987669825079268371 59753518481504737618902557)
      ·
        refine ⟨22407569430564276607088459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59753518481504737618902557 22407569430564276607088459)
        ·
          refine ⟨33611354145846414910632689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22407569430564276607088459 33611354145846414910632689)
          ·
            refine ⟨25208515609384811182974517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33611354145846414910632689 25208515609384811182974517)
            ·
              refine ⟨2363298338379826048403861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25208515609384811182974517 2363298338379826048403861)
              ·
                refine ⟨110779609611554346018931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2363298338379826048403861 110779609611554346018931)
                ·
                  rfl

theorem cell20_728131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 6].length) (baseStart_728131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728131 prefixEnd_728131 := by exact prefixLift 728131
  have htrace : WordTrace (prefixWord ++ tailWord_728131) baseStart_728131 baseEnd_728131 := by
    simpa [prefixWord, tailWord_728131, baseEnd_728131] using wordTrace_append hprefix tailTrace_728131
  have hstable : (prefixWord ++ tailWord_728131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728131).length < 2 ^ (prefixWord ++ tailWord_728131).sum := by decide
  have hdescent : baseEnd_728131 < baseStart_728131 := by decide
  rcases family_descends (prefixWord ++ tailWord_728131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728169 : List Nat := [1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_728169 : Nat := 118140960795 + 728169 * 2 ^ 59
def prefixEnd_728169 : Nat := 4983230072969 + 3 ^ 40 * 728169 * 2
def baseEnd_728169 : Nat := 110785391023367931596657

theorem tailTrace_728169 : CollatzResearch.WordTrace tailWord_728169 prefixEnd_728169 110785391023367931596657 := by
  unfold tailWord_728169
  simp only [CollatzResearch.WordTrace]
  refine ⟨26558505298975549209395561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17705670199317032806263707 26558505298975549209395561)
  ·
    refine ⟨19918878974231661907046671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26558505298975549209395561 19918878974231661907046671)
    ·
      refine ⟨29878318461347492860570007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19918878974231661907046671 29878318461347492860570007)
      ·
        refine ⟨44817477692021239290855011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29878318461347492860570007 44817477692021239290855011)
        ·
          refine ⟨67226216538031858936282517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44817477692021239290855011 67226216538031858936282517)
          ·
            refine ⟨3151228900220243387638243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67226216538031858936282517 3151228900220243387638243)
            ·
              refine ⟨4726843350330365081457365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151228900220243387638243 4726843350330365081457365)
              ·
                refine ⟨110785391023367931596657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4726843350330365081457365 110785391023367931596657)
                ·
                  rfl

theorem cell20_728169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_728169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728169 prefixEnd_728169 := by exact prefixLift 728169
  have htrace : WordTrace (prefixWord ++ tailWord_728169) baseStart_728169 baseEnd_728169 := by
    simpa [prefixWord, tailWord_728169, baseEnd_728169] using wordTrace_append hprefix tailTrace_728169
  have hstable : (prefixWord ++ tailWord_728169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728169).length < 2 ^ (prefixWord ++ tailWord_728169).sum := by decide
  have hdescent : baseEnd_728169 < baseStart_728169 := by decide
  rcases family_descends (prefixWord ++ tailWord_728169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728210 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_728210 : Nat := 118140960795 + 728210 * 2 ^ 59
def prefixEnd_728210 : Nat := 4983230072969 + 3 ^ 40 * 728210 * 2
def baseEnd_728210 : Nat := 332374886587289874423137

theorem tailTrace_728210 : CollatzResearch.WordTrace tailWord_728210 prefixEnd_728210 332374886587289874423137 := by
  unfold tailWord_728210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640000172956753302909521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17706667127884675474425389 6640000172956753302909521)
  ·
    refine ⟨4980000129717564977182141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6640000172956753302909521 4980000129717564977182141)
    ·
      refine ⟨1867500048644086866443303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4980000129717564977182141 1867500048644086866443303)
      ·
        refine ⟨2801250072966130299664955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867500048644086866443303 2801250072966130299664955)
        ·
          refine ⟨4201875109449195449497433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801250072966130299664955 4201875109449195449497433)
          ·
            refine ⟨3151406332086896587123075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4201875109449195449497433 3151406332086896587123075)
            ·
              refine ⟨4727109498130344880684613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151406332086896587123075 4727109498130344880684613)
              ·
                refine ⟨886333030899439665128365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4727109498130344880684613 886333030899439665128365)
                ·
                  refine ⟨332374886587289874423137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886333030899439665128365 332374886587289874423137)
                  ·
                    rfl

theorem cell20_728210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_728210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728210 prefixEnd_728210 := by exact prefixLift 728210
  have htrace : WordTrace (prefixWord ++ tailWord_728210) baseStart_728210 baseEnd_728210 := by
    simpa [prefixWord, tailWord_728210, baseEnd_728210] using wordTrace_append hprefix tailTrace_728210
  have hstable : (prefixWord ++ tailWord_728210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728210).length < 2 ^ (prefixWord ++ tailWord_728210).sum := by decide
  have hdescent : baseEnd_728210 < baseStart_728210 := by decide
  rcases family_descends (prefixWord ++ tailWord_728210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728234 : List Nat := [3, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_728234 : Nat := 118140960795 + 728234 * 2 ^ 59
def prefixEnd_728234 : Nat := 4983230072969 + 3 ^ 40 * 728234 * 2
def baseEnd_728234 : Nat := 332385840841252457623039

theorem tailTrace_728234 : CollatzResearch.WordTrace tailWord_728234 prefixEnd_728234 332385840841252457623039 := by
  unfold tailWord_728234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640219010935016327627939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17707250695826710207007837 6640219010935016327627939)
  ·
    refine ⟨9960328516402524491441909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640219010935016327627939 9960328516402524491441909)
    ·
      refine ⟨933780798412736671072679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9960328516402524491441909 933780798412736671072679)
      ·
        refine ⟨1400671197619105006609019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933780798412736671072679 1400671197619105006609019)
        ·
          refine ⟨2101006796428657509913529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400671197619105006609019 2101006796428657509913529)
          ·
            refine ⟨1575755097321493132435147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2101006796428657509913529 1575755097321493132435147)
            ·
              refine ⟨2363632645982239698652721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575755097321493132435147 2363632645982239698652721)
              ·
                refine ⟨1772724484486679773989541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363632645982239698652721 1772724484486679773989541)
                ·
                  refine ⟨332385840841252457623039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772724484486679773989541 332385840841252457623039)
                  ·
                    rfl

theorem cell20_728234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_728234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728234 prefixEnd_728234 := by exact prefixLift 728234
  have htrace : WordTrace (prefixWord ++ tailWord_728234) baseStart_728234 baseEnd_728234 := by
    simpa [prefixWord, tailWord_728234, baseEnd_728234] using wordTrace_append hprefix tailTrace_728234
  have hstable : (prefixWord ++ tailWord_728234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728234).length < 2 ^ (prefixWord ++ tailWord_728234).sum := by decide
  have hdescent : baseEnd_728234 < baseStart_728234 := by decide
  rcases family_descends (prefixWord ++ tailWord_728234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728241 : List Nat := [1, 2, 2, 5, 1, 2, 3, 4]
def baseStart_728241 : Nat := 118140960795 + 728241 * 2 ^ 59
def prefixEnd_728241 : Nat := 4983230072969 + 3 ^ 40 * 728241 * 2
def baseEnd_728241 : Nat := 110796345277330514796559

theorem tailTrace_728241 : CollatzResearch.WordTrace tailWord_728241 prefixEnd_728241 110796345277330514796559 := by
  unfold tailWord_728241
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561131354714705506016577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17707420903143137004011051 26561131354714705506016577)
  ·
    refine ⟨19920848516036029129512433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26561131354714705506016577 19920848516036029129512433)
    ·
      refine ⟨14940636387027021847134325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19920848516036029129512433 14940636387027021847134325)
      ·
        refine ⟨1400684661283783298168843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14940636387027021847134325 1400684661283783298168843)
        ·
          refine ⟨2101026991925674947253265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400684661283783298168843 2101026991925674947253265)
          ·
            refine ⟨1575770243944256210439949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2101026991925674947253265 1575770243944256210439949)
            ·
              refine ⟨590913841479096078914981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1575770243944256210439949 590913841479096078914981)
              ·
                refine ⟨110796345277330514796559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590913841479096078914981 110796345277330514796559)
                ·
                  rfl

theorem cell20_728241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_728241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728241 prefixEnd_728241 := by exact prefixLift 728241
  have htrace : WordTrace (prefixWord ++ tailWord_728241) baseStart_728241 baseEnd_728241 := by
    simpa [prefixWord, tailWord_728241, baseEnd_728241] using wordTrace_append hprefix tailTrace_728241
  have hstable : (prefixWord ++ tailWord_728241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728241).length < 2 ^ (prefixWord ++ tailWord_728241).sum := by decide
  have hdescent : baseEnd_728241 < baseStart_728241 := by decide
  rcases family_descends (prefixWord ++ tailWord_728241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728255 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 2]
def baseStart_728255 : Nat := 118140960795 + 728255 * 2 ^ 59
def prefixEnd_728255 : Nat := 4983230072969 + 3 ^ 40 * 728255 * 2
def baseEnd_728255 : Nat := 332395425813469717922953

theorem tailTrace_728255 : CollatzResearch.WordTrace tailWord_728255 prefixEnd_728255 332395425813469717922953 := by
  unfold tailWord_728255
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561641976663985897026219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17707761317775990598017479 26561641976663985897026219)
  ·
    refine ⟨39842462964995978845539329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26561641976663985897026219 39842462964995978845539329)
    ·
      refine ⟨29881847223746984134154497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39842462964995978845539329 29881847223746984134154497)
      ·
        refine ⟨22411385417810238100615873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29881847223746984134154497 22411385417810238100615873)
        ·
          refine ⟨16808539063357678575461905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22411385417810238100615873 16808539063357678575461905)
          ·
            refine ⟨12606404297518258931596429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16808539063357678575461905 12606404297518258931596429)
            ·
              refine ⟨4727401611569347099348661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12606404297518258931596429 4727401611569347099348661)
              ·
                refine ⟨443193901084626290563937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4727401611569347099348661 443193901084626290563937)
                ·
                  refine ⟨332395425813469717922953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443193901084626290563937 332395425813469717922953)
                  ·
                    rfl

theorem cell20_728255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 2].length) (baseStart_728255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728255 prefixEnd_728255 := by exact prefixLift 728255
  have htrace : WordTrace (prefixWord ++ tailWord_728255) baseStart_728255 baseEnd_728255 := by
    simpa [prefixWord, tailWord_728255, baseEnd_728255] using wordTrace_append hprefix tailTrace_728255
  have hstable : (prefixWord ++ tailWord_728255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728255).length < 2 ^ (prefixWord ++ tailWord_728255).sum := by decide
  have hdescent : baseEnd_728255 < baseStart_728255 := by decide
  rcases family_descends (prefixWord ++ tailWord_728255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728258 : List Nat := [3, 5, 1, 1, 2, 1, 7]
def baseStart_728258 : Nat := 118140960795 + 728258 * 2 ^ 59
def prefixEnd_728258 : Nat := 4983230072969 + 3 ^ 40 * 728258 * 2
def baseEnd_728258 : Nat := 36932977232801671202549

theorem tailTrace_728258 : CollatzResearch.WordTrace tailWord_728258 prefixEnd_728258 36932977232801671202549 := by
  unfold tailWord_728258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640437848913279352346357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17707834263768744939590285 6640437848913279352346357)
  ·
    refine ⟨622541048335619939282471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6640437848913279352346357 622541048335619939282471)
    ·
      refine ⟨933811572503429908923707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622541048335619939282471 933811572503429908923707)
      ·
        refine ⟨1400717358755144863385561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933811572503429908923707 1400717358755144863385561)
        ·
          refine ⟨1050538019066358647539171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400717358755144863385561 1050538019066358647539171)
          ·
            refine ⟨1575807028599537971308757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050538019066358647539171 1575807028599537971308757)
            ·
              refine ⟨36932977232801671202549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1575807028599537971308757 36932977232801671202549)
              ·
                rfl

theorem cell20_728258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 7].length) (baseStart_728258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728258 prefixEnd_728258 := by exact prefixLift 728258
  have htrace : WordTrace (prefixWord ++ tailWord_728258) baseStart_728258 baseEnd_728258 := by
    simpa [prefixWord, tailWord_728258, baseEnd_728258] using wordTrace_append hprefix tailTrace_728258
  have hstable : (prefixWord ++ tailWord_728258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728258).length < 2 ^ (prefixWord ++ tailWord_728258).sum := by decide
  have hdescent : baseEnd_728258 < baseStart_728258 := by decide
  rcases family_descends (prefixWord ++ tailWord_728258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728300 : List Nat := [2, 2, 1, 1, 2, 4, 4, 4]
def baseStart_728300 : Nat := 118140960795 + 728300 * 2 ^ 59
def prefixEnd_728300 : Nat := 4983230072969 + 3 ^ 40 * 728300 * 2
def baseEnd_728300 : Nat := 110805321679883187140923

theorem tailTrace_728300 : CollatzResearch.WordTrace tailWord_728300 prefixEnd_728300 110805321679883187140923 := by
  unfold tailWord_728300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13281641630750479291207177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17708855507667305721609569 13281641630750479291207177)
  ·
    refine ⟨9961231223062859468405383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13281641630750479291207177 9961231223062859468405383)
    ·
      refine ⟨14941846834594289202608075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9961231223062859468405383 14941846834594289202608075)
      ·
        refine ⟨22412770251891433803912113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14941846834594289202608075 22412770251891433803912113)
        ·
          refine ⟨16809577688918575352934085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22412770251891433803912113 16809577688918575352934085)
          ·
            refine ⟨3151795816672232878675141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16809577688918575352934085 3151795816672232878675141)
            ·
              refine ⟨590961715626043664751589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3151795816672232878675141 590961715626043664751589)
              ·
                refine ⟨110805321679883187140923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590961715626043664751589 110805321679883187140923)
                ·
                  rfl

theorem cell20_728300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_728300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728300 prefixEnd_728300 := by exact prefixLift 728300
  have htrace : WordTrace (prefixWord ++ tailWord_728300) baseStart_728300 baseEnd_728300 := by
    simpa [prefixWord, tailWord_728300, baseEnd_728300] using wordTrace_append hprefix tailTrace_728300
  have hstable : (prefixWord ++ tailWord_728300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728300).length < 2 ^ (prefixWord ++ tailWord_728300).sum := by decide
  have hdescent : baseEnd_728300 < baseStart_728300 := by decide
  rcases family_descends (prefixWord ++ tailWord_728300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728306 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_728306 : Nat := 118140960795 + 728306 * 2 ^ 59
def prefixEnd_728306 : Nat := 4983230072969 + 3 ^ 40 * 728306 * 2
def baseEnd_728306 : Nat := 332418703603140207222745

theorem tailTrace_728306 : CollatzResearch.WordTrace tailWord_728306 prefixEnd_728306 332418703603140207222745 := by
  unfold tailWord_728306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640875524869805401783193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17709001399652814404755181 6640875524869805401783193)
  ·
    refine ⟨4980656643652354051337395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6640875524869805401783193 4980656643652354051337395)
    ·
      refine ⟨7470984965478531077006093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980656643652354051337395 7470984965478531077006093)
      ·
        refine ⟨2801619362054449153877285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7470984965478531077006093 2801619362054449153877285)
        ·
          refine ⟨525303630385209216351991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2801619362054449153877285 525303630385209216351991)
          ·
            refine ⟨787955445577813824527987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525303630385209216351991 787955445577813824527987)
            ·
              refine ⟨1181933168366720736791981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787955445577813824527987 1181933168366720736791981)
              ·
                refine ⟨443224938137520276296993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181933168366720736791981 443224938137520276296993)
                ·
                  refine ⟨332418703603140207222745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443224938137520276296993 332418703603140207222745)
                  ·
                    rfl

theorem cell20_728306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_728306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728306 prefixEnd_728306 := by exact prefixLift 728306
  have htrace : WordTrace (prefixWord ++ tailWord_728306) baseStart_728306 baseEnd_728306 := by
    simpa [prefixWord, tailWord_728306, baseEnd_728306] using wordTrace_append hprefix tailTrace_728306
  have hstable : (prefixWord ++ tailWord_728306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728306).length < 2 ^ (prefixWord ++ tailWord_728306).sum := by decide
  have hdescent : baseEnd_728306 < baseStart_728306 := by decide
  rcases family_descends (prefixWord ++ tailWord_728306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728321 : List Nat := [1, 2, 4, 1, 1, 3, 8]
def baseStart_728321 : Nat := 118140960795 + 728321 * 2 ^ 59
def prefixEnd_728321 : Nat := 4983230072969 + 3 ^ 40 * 728321 * 2
def baseEnd_728321 : Nat := 36936172223540757969187

theorem tailTrace_728321 : CollatzResearch.WordTrace tailWord_728321 prefixEnd_728321 36936172223540757969187 := by
  unfold tailWord_728321
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564049194424879168928817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17709366129616586112619211 26564049194424879168928817)
  ·
    refine ⟨19923036895818659376696613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26564049194424879168928817 19923036895818659376696613)
    ·
      refine ⟨3735569417965998633130615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19923036895818659376696613 3735569417965998633130615)
      ·
        refine ⟨5603354126948997949695923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735569417965998633130615 5603354126948997949695923)
        ·
          refine ⟨8405031190423496924543885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603354126948997949695923 8405031190423496924543885)
          ·
            refine ⟨3151886696408811346703957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8405031190423496924543885 3151886696408811346703957)
            ·
              refine ⟨36936172223540757969187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3151886696408811346703957 36936172223540757969187)
              ·
                rfl

theorem cell20_728321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_728321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728321 prefixEnd_728321 := by exact prefixLift 728321
  have htrace : WordTrace (prefixWord ++ tailWord_728321) baseStart_728321 baseEnd_728321 := by
    simpa [prefixWord, tailWord_728321, baseEnd_728321] using wordTrace_append hprefix tailTrace_728321
  have hstable : (prefixWord ++ tailWord_728321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728321).length < 2 ^ (prefixWord ++ tailWord_728321).sum := by decide
  have hdescent : baseEnd_728321 < baseStart_728321 := by decide
  rcases family_descends (prefixWord ++ tailWord_728321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728331 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 4]
def baseStart_728331 : Nat := 118140960795 + 728331 * 2 ^ 59
def prefixEnd_728331 : Nat := 4983230072969 + 3 ^ 40 * 728331 * 2
def baseEnd_728331 : Nat := 332430114284351231389309

theorem tailTrace_728331 : CollatzResearch.WordTrace tailWord_728331 prefixEnd_728331 332430114284351231389309 := by
  unfold tailWord_728331
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564413924388650876792847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17709609282925767251195231 26564413924388650876792847)
  ·
    refine ⟨39846620886582976315189271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26564413924388650876792847 39846620886582976315189271)
    ·
      refine ⟨59769931329874464472783907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39846620886582976315189271 59769931329874464472783907)
      ·
        refine ⟨89654896994811696709175861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59769931329874464472783907 89654896994811696709175861)
        ·
          refine ⟨8405146593263596566485237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89654896994811696709175861 8405146593263596566485237)
          ·
            refine ⟨787982493118462178107991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8405146593263596566485237 787982493118462178107991)
            ·
              refine ⟨1181973739677693267161987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787982493118462178107991 1181973739677693267161987)
              ·
                refine ⟨1772960609516539900742981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181973739677693267161987 1772960609516539900742981)
                ·
                  refine ⟨332430114284351231389309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772960609516539900742981 332430114284351231389309)
                  ·
                    rfl

theorem cell20_728331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_728331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728331 prefixEnd_728331 := by exact prefixLift 728331
  have htrace : WordTrace (prefixWord ++ tailWord_728331) baseStart_728331 baseEnd_728331 := by
    simpa [prefixWord, tailWord_728331, baseEnd_728331] using wordTrace_append hprefix tailTrace_728331
  have hstable : (prefixWord ++ tailWord_728331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728331).length < 2 ^ (prefixWord ++ tailWord_728331).sum := by decide
  have hdescent : baseEnd_728331 < baseStart_728331 := by decide
  rcases family_descends (prefixWord ++ tailWord_728331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728383 : List Nat := [1, 1, 2, 2, 4, 2, 1, 4, 3]
def baseStart_728383 : Nat := 118140960795 + 728383 * 2 ^ 59
def prefixEnd_728383 : Nat := 4983230072969 + 3 ^ 40 * 728383 * 2
def baseEnd_728383 : Nat := 332453848501270161655763

theorem tailTrace_728383 : CollatzResearch.WordTrace tailWord_728383 prefixEnd_728383 332453848501270161655763 := by
  unfold tailWord_728383
  simp only [CollatzResearch.WordTrace]
  refine ⟨26566310520200263757685803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17710873680133509171790535 26566310520200263757685803)
  ·
    refine ⟨39849465780300395636528705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26566310520200263757685803 39849465780300395636528705)
    ·
      refine ⟨29887099335225296727396529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39849465780300395636528705 29887099335225296727396529)
      ·
        refine ⟨22415324501418972545547397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29887099335225296727396529 22415324501418972545547397)
        ·
          refine ⟨4202873344016057352290137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22415324501418972545547397 4202873344016057352290137)
          ·
            refine ⟨3152155008012043014217603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4202873344016057352290137 3152155008012043014217603)
            ·
              refine ⟨4728232512018064521326405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152155008012043014217603 4728232512018064521326405)
              ·
                refine ⟨886543596003387097748701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4728232512018064521326405 886543596003387097748701)
                ·
                  refine ⟨332453848501270161655763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886543596003387097748701 332453848501270161655763)
                  ·
                    rfl

theorem cell20_728383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4, 3].length) (baseStart_728383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728383 prefixEnd_728383 := by exact prefixLift 728383
  have htrace : WordTrace (prefixWord ++ tailWord_728383) baseStart_728383 baseEnd_728383 := by
    simpa [prefixWord, tailWord_728383, baseEnd_728383] using wordTrace_append hprefix tailTrace_728383
  have hstable : (prefixWord ++ tailWord_728383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728383).length < 2 ^ (prefixWord ++ tailWord_728383).sum := by decide
  have hdescent : baseEnd_728383 < baseStart_728383 := by decide
  rcases family_descends (prefixWord ++ tailWord_728383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728406 : List Nat := [5, 2, 3, 1, 1, 1, 3, 4]
def baseStart_728406 : Nat := 118140960795 + 728406 * 2 ^ 59
def prefixEnd_728406 : Nat := 4983230072969 + 3 ^ 40 * 728406 * 2
def baseEnd_728406 : Nat := 110821448775994767963001

theorem tailTrace_728406 : CollatzResearch.WordTrace tailWord_728406 prefixEnd_728406 110821448775994767963001 := by
  unfold tailWord_728406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660446837444808667860817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17711432932744625790515381 1660446837444808667860817)
  ·
    refine ⟨1245335128083606500895613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1660446837444808667860817 1245335128083606500895613)
    ·
      refine ⟨467000673031352437835855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1245335128083606500895613 467000673031352437835855)
      ·
        refine ⟨700501009547028656753783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467000673031352437835855 700501009547028656753783)
        ·
          refine ⟨1050751514320542985130675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700501009547028656753783 1050751514320542985130675)
          ·
            refine ⟨1576127271480814477696013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050751514320542985130675 1576127271480814477696013)
            ·
              refine ⟨591047726805305429136005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576127271480814477696013 591047726805305429136005)
              ·
                refine ⟨110821448775994767963001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591047726805305429136005 110821448775994767963001)
                ·
                  rfl

theorem cell20_728406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_728406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728406 prefixEnd_728406 := by exact prefixLift 728406
  have htrace : WordTrace (prefixWord ++ tailWord_728406) baseStart_728406 baseEnd_728406 := by
    simpa [prefixWord, tailWord_728406, baseEnd_728406] using wordTrace_append hprefix tailTrace_728406
  have hstable : (prefixWord ++ tailWord_728406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728406).length < 2 ^ (prefixWord ++ tailWord_728406).sum := by decide
  have hdescent : baseEnd_728406 < baseStart_728406 := by decide
  rcases family_descends (prefixWord ++ tailWord_728406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728442 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_728442 : Nat := 118140960795 + 728442 * 2 ^ 59
def prefixEnd_728442 : Nat := 4983230072969 + 3 ^ 40 * 728442 * 2
def baseEnd_728442 : Nat := 332480777708928178688855

theorem tailTrace_728442 : CollatzResearch.WordTrace tailWord_728442 prefixEnd_728442 332480777708928178688855 := by
  unfold tailWord_728442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642115606746629208520895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17712308284657677889389053 6642115606746629208520895)
  ·
    refine ⟨9963173410119943812781343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6642115606746629208520895 9963173410119943812781343)
    ·
      refine ⟨14944760115179915719172015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9963173410119943812781343 14944760115179915719172015)
      ·
        refine ⟨22417140172769873578758023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14944760115179915719172015 22417140172769873578758023)
        ·
          refine ⟨33625710259154810368137035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22417140172769873578758023 33625710259154810368137035)
          ·
            refine ⟨50438565388732215552205553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33625710259154810368137035 50438565388732215552205553)
            ·
              refine ⟨37828924041549161664154165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50438565388732215552205553 37828924041549161664154165)
              ·
                refine ⟨3546461628895233906014453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37828924041549161664154165 3546461628895233906014453)
                ·
                  refine ⟨332480777708928178688855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3546461628895233906014453 332480777708928178688855)
                  ·
                    rfl

theorem cell20_728442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_728442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728442 prefixEnd_728442 := by exact prefixLift 728442
  have htrace : WordTrace (prefixWord ++ tailWord_728442) baseStart_728442 baseEnd_728442 := by
    simpa [prefixWord, tailWord_728442, baseEnd_728442] using wordTrace_append hprefix tailTrace_728442
  have hstable : (prefixWord ++ tailWord_728442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728442).length < 2 ^ (prefixWord ++ tailWord_728442).sum := by decide
  have hdescent : baseEnd_728442 < baseStart_728442 := by decide
  rcases family_descends (prefixWord ++ tailWord_728442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728445 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 2]
def baseStart_728445 : Nat := 118140960795 + 728445 * 2 ^ 59
def prefixEnd_728445 : Nat := 4983230072969 + 3 ^ 40 * 728445 * 2
def baseEnd_728445 : Nat := 332482146990673501588843

theorem tailTrace_728445 : CollatzResearch.WordTrace tailWord_728445 prefixEnd_728445 332482146990673501588843 := by
  unfold tailWord_728445
  simp only [CollatzResearch.WordTrace]
  refine ⟨26568571845975648346442789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17712381230650432230961859 26568571845975648346442789)
  ·
    refine ⟨4981607221120434064958023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26568571845975648346442789 4981607221120434064958023)
    ·
      refine ⟨7472410831680651097437035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981607221120434064958023 7472410831680651097437035)
      ·
        refine ⟨11208616247520976646155553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7472410831680651097437035 11208616247520976646155553)
        ·
          refine ⟨8406462185640732484616665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11208616247520976646155553 8406462185640732484616665)
          ·
            refine ⟨6304846639230549363462499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8406462185640732484616665 6304846639230549363462499)
            ·
              refine ⟨9457269958845824045193749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304846639230549363462499 9457269958845824045193749)
              ·
                refine ⟨443309529320898002118457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9457269958845824045193749 443309529320898002118457)
                ·
                  refine ⟨332482146990673501588843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443309529320898002118457 332482146990673501588843)
                  ·
                    rfl

theorem cell20_728445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_728445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728445 prefixEnd_728445 := by exact prefixLift 728445
  have htrace : WordTrace (prefixWord ++ tailWord_728445) baseStart_728445 baseEnd_728445 := by
    simpa [prefixWord, tailWord_728445, baseEnd_728445] using wordTrace_append hprefix tailTrace_728445
  have hstable : (prefixWord ++ tailWord_728445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728445).length < 2 ^ (prefixWord ++ tailWord_728445).sum := by decide
  have hdescent : baseEnd_728445 < baseStart_728445 := by decide
  rcases family_descends (prefixWord ++ tailWord_728445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728473 : List Nat := [1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_728473 : Nat := 118140960795 + 728473 * 2 ^ 59
def prefixEnd_728473 : Nat := 4983230072969 + 3 ^ 40 * 728473 * 2
def baseEnd_728473 : Nat := 110831642317876616218465

theorem tailTrace_728473 : CollatzResearch.WordTrace tailWord_728473 prefixEnd_728473 110831642317876616218465 := by
  unfold tailWord_728473
  simp only [CollatzResearch.WordTrace]
  refine ⟨26569593089874209128462073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17713062059916139418974715 26569593089874209128462073)
  ·
    refine ⟨19927194817405656846346555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26569593089874209128462073 19927194817405656846346555)
    ·
      refine ⟨29890792226108485269519833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19927194817405656846346555 29890792226108485269519833)
      ·
        refine ⟨22418094169581363952139875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29890792226108485269519833 22418094169581363952139875)
        ·
          refine ⟨33627141254372045928209813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22418094169581363952139875 33627141254372045928209813)
          ·
            refine ⟨1576272246298689652884835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33627141254372045928209813 1576272246298689652884835)
            ·
              refine ⟨2364408369448034479327253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576272246298689652884835 2364408369448034479327253)
              ·
                refine ⟨110831642317876616218465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2364408369448034479327253 110831642317876616218465)
                ·
                  rfl

theorem cell20_728473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_728473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728473 prefixEnd_728473 := by exact prefixLift 728473
  have htrace : WordTrace (prefixWord ++ tailWord_728473) baseStart_728473 baseEnd_728473 := by
    simpa [prefixWord, tailWord_728473, baseEnd_728473] using wordTrace_append hprefix tailTrace_728473
  have hstable : (prefixWord ++ tailWord_728473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728473).length < 2 ^ (prefixWord ++ tailWord_728473).sum := by decide
  have hdescent : baseEnd_728473 < baseStart_728473 := by decide
  rcases family_descends (prefixWord ++ tailWord_728473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728480 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_728480 : Nat := 118140960795 + 728480 * 2 ^ 59
def prefixEnd_728480 : Nat := 4983230072969 + 3 ^ 40 * 728480 * 2
def baseEnd_728480 : Nat := 332498121944368935422033

theorem tailTrace_728480 : CollatzResearch.WordTrace tailWord_728480 prefixEnd_728480 332498121944368935422033 := by
  unfold tailWord_728480
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284924200424424661983447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17713232267232566215977929 13284924200424424661983447)
  ·
    refine ⟨19927386300636636992975171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13284924200424424661983447 19927386300636636992975171)
    ·
      refine ⟨29891079450954955489462757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19927386300636636992975171 29891079450954955489462757)
      ·
        refine ⟨5604577397054054154274267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29891079450954955489462757 5604577397054054154274267)
        ·
          refine ⟨8406866095581081231411401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604577397054054154274267 8406866095581081231411401)
          ·
            refine ⟨6305149571685810923558551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8406866095581081231411401 6305149571685810923558551)
            ·
              refine ⟨9457724357528716385337827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305149571685810923558551 9457724357528716385337827)
              ·
                refine ⟨14186586536293074578006741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9457724357528716385337827 14186586536293074578006741)
                ·
                  refine ⟨332498121944368935422033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14186586536293074578006741 332498121944368935422033)
                  ·
                    rfl

theorem cell20_728480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_728480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728480 prefixEnd_728480 := by exact prefixLift 728480
  have htrace : WordTrace (prefixWord ++ tailWord_728480) baseStart_728480 baseEnd_728480 := by
    simpa [prefixWord, tailWord_728480, baseEnd_728480] using wordTrace_append hprefix tailTrace_728480
  have hstable : (prefixWord ++ tailWord_728480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728480).length < 2 ^ (prefixWord ++ tailWord_728480).sum := by decide
  have hdescent : baseEnd_728480 < baseStart_728480 := by decide
  rcases family_descends (prefixWord ++ tailWord_728480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728497 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 3]
def baseStart_728497 : Nat := 118140960795 + 728497 * 2 ^ 59
def prefixEnd_728497 : Nat := 4983230072969 + 3 ^ 40 * 728497 * 2
def baseEnd_728497 : Nat := 332505881207592431855297

theorem tailTrace_728497 : CollatzResearch.WordTrace tailWord_728497 prefixEnd_728497 332505881207592431855297 := by
  unfold tailWord_728497
  simp only [CollatzResearch.WordTrace]
  refine ⟨26570468441787261227335745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17713645627858174151557163 26570468441787261227335745)
  ·
    refine ⟨19927851331340445920501809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26570468441787261227335745 19927851331340445920501809)
    ·
      refine ⟨14945888498505334440376357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19927851331340445920501809 14945888498505334440376357)
      ·
        refine ⟨2802354093469750207570567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14945888498505334440376357 2802354093469750207570567)
        ·
          refine ⟨4203531140204625311355851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802354093469750207570567 4203531140204625311355851)
          ·
            refine ⟨6305296710306937967033777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203531140204625311355851 6305296710306937967033777)
            ·
              refine ⟨4728972532730203475275333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6305296710306937967033777 4728972532730203475275333)
              ·
                refine ⟨886682349886913151614125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4728972532730203475275333 886682349886913151614125)
                ·
                  refine ⟨332505881207592431855297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886682349886913151614125 332505881207592431855297)
                  ·
                    rfl

theorem cell20_728497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_728497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728497 prefixEnd_728497 := by exact prefixLift 728497
  have htrace : WordTrace (prefixWord ++ tailWord_728497) baseStart_728497 baseEnd_728497 := by
    simpa [prefixWord, tailWord_728497, baseEnd_728497] using wordTrace_append hprefix tailTrace_728497
  have hstable : (prefixWord ++ tailWord_728497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728497).length < 2 ^ (prefixWord ++ tailWord_728497).sum := by decide
  have hdescent : baseEnd_728497 < baseStart_728497 := by decide
  rcases family_descends (prefixWord ++ tailWord_728497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728504 : List Nat := [2, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_728504 : Nat := 118140960795 + 728504 * 2 ^ 59
def prefixEnd_728504 : Nat := 4983230072969 + 3 ^ 40 * 728504 * 2
def baseEnd_728504 : Nat := 332509076198331518621935

theorem tailTrace_728504 : CollatzResearch.WordTrace tailWord_728504 prefixEnd_728504 332509076198331518621935 := by
  unfold tailWord_728504
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285361876380950711420283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17713815835174600948560377 13285361876380950711420283)
  ·
    refine ⟨19928042814571426067130425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13285361876380950711420283 19928042814571426067130425)
    ·
      refine ⟨14946032110928569550347819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19928042814571426067130425 14946032110928569550347819)
      ·
        refine ⟨22419048166392854325521729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14946032110928569550347819 22419048166392854325521729)
        ·
          refine ⟨16814286124794640744141297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22419048166392854325521729 16814286124794640744141297)
          ·
            refine ⟨12610714593595980558105973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16814286124794640744141297 12610714593595980558105973)
            ·
              refine ⟨1182254493149623177322435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12610714593595980558105973 1182254493149623177322435)
              ·
                refine ⟨1773381739724434765983653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182254493149623177322435 1773381739724434765983653)
                ·
                  refine ⟨332509076198331518621935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773381739724434765983653 332509076198331518621935)
                  ·
                    rfl

theorem cell20_728504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_728504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728504 prefixEnd_728504 := by exact prefixLift 728504
  have htrace : WordTrace (prefixWord ++ tailWord_728504) baseStart_728504 baseEnd_728504 := by
    simpa [prefixWord, tailWord_728504, baseEnd_728504] using wordTrace_append hprefix tailTrace_728504
  have hstable : (prefixWord ++ tailWord_728504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728504).length < 2 ^ (prefixWord ++ tailWord_728504).sum := by decide
  have hdescent : baseEnd_728504 < baseStart_728504 := by decide
  rcases family_descends (prefixWord ++ tailWord_728504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728549 : List Nat := [1, 3, 1, 5, 1, 9]
def baseStart_728549 : Nat := 118140960795 + 728549 * 2 ^ 59
def prefixEnd_728549 : Nat := 4983230072969 + 3 ^ 40 * 728549 * 2
def baseEnd_728549 : Nat := 12315911682389309708213

theorem tailTrace_728549 : CollatzResearch.WordTrace tailWord_728549 prefixEnd_728549 12315911682389309708213 := by
  unfold tailWord_728549
  simp only [CollatzResearch.WordTrace]
  refine ⟨26572365037598874108228701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17714910025065916072152467 26572365037598874108228701)
  ·
    refine ⟨9964636889099577790585763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26572365037598874108228701 9964636889099577790585763)
    ·
      refine ⟨14946955333649366685878645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9964636889099577790585763 14946955333649366685878645)
      ·
        refine ⟨1401277062529628126801123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14946955333649366685878645 1401277062529628126801123)
        ·
          refine ⟨2101915593794442190201685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401277062529628126801123 2101915593794442190201685)
          ·
            refine ⟨12315911682389309708213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2101915593794442190201685 12315911682389309708213)
            ·
              rfl

theorem cell20_728549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 9].length) (baseStart_728549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728549 prefixEnd_728549 := by exact prefixLift 728549
  have htrace : WordTrace (prefixWord ++ tailWord_728549) baseStart_728549 baseEnd_728549 := by
    simpa [prefixWord, tailWord_728549, baseEnd_728549] using wordTrace_append hprefix tailTrace_728549
  have hstable : (prefixWord ++ tailWord_728549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728549).length < 2 ^ (prefixWord ++ tailWord_728549).sum := by decide
  have hdescent : baseEnd_728549 < baseStart_728549 := by decide
  rcases family_descends (prefixWord ++ tailWord_728549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728566 : List Nat := [5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_728566 : Nat := 118140960795 + 728566 * 2 ^ 59
def prefixEnd_728566 : Nat := 4983230072969 + 3 ^ 40 * 728566 * 2
def baseEnd_728566 : Nat := 110845791562578286185005

theorem tailTrace_728566 : CollatzResearch.WordTrace tailWord_728566 prefixEnd_728566 110845791562578286185005 := by
  unfold tailWord_728566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660811567408580375724847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17715323385691524007731701 1660811567408580375724847)
  ·
    refine ⟨2491217351112870563587271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660811567408580375724847 2491217351112870563587271)
    ·
      refine ⟨3736826026669305845380907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491217351112870563587271 3736826026669305845380907)
      ·
        refine ⟨5605239040003958768071361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736826026669305845380907 5605239040003958768071361)
        ·
          refine ⟨4203929280002969076053521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605239040003958768071361 4203929280002969076053521)
          ·
            refine ⟨3152946960002226807040141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4203929280002969076053521 3152946960002226807040141)
            ·
              refine ⟨1182355110000835052640053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3152946960002226807040141 1182355110000835052640053)
              ·
                refine ⟨110845791562578286185005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1182355110000835052640053 110845791562578286185005)
                ·
                  rfl

theorem cell20_728566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_728566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728566 prefixEnd_728566 := by exact prefixLift 728566
  have htrace : WordTrace (prefixWord ++ tailWord_728566) baseStart_728566 baseEnd_728566 := by
    simpa [prefixWord, tailWord_728566, baseEnd_728566] using wordTrace_append hprefix tailTrace_728566
  have hstable : (prefixWord ++ tailWord_728566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728566).length < 2 ^ (prefixWord ++ tailWord_728566).sum := by decide
  have hdescent : baseEnd_728566 < baseStart_728566 := by decide
  rcases family_descends (prefixWord ++ tailWord_728566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728573 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 3]
def baseStart_728573 : Nat := 118140960795 + 728573 * 2 ^ 59
def prefixEnd_728573 : Nat := 4983230072969 + 3 ^ 40 * 728573 * 2
def baseEnd_728573 : Nat := 332540569678473945321653

theorem tailTrace_728573 : CollatzResearch.WordTrace tailWord_728573 prefixEnd_728573 332540569678473945321653 := by
  unfold tailWord_728573
  simp only [CollatzResearch.WordTrace]
  refine ⟨26573240389511926207102373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17715493593007950804734915 26573240389511926207102373)
  ·
    refine ⟨4982482573033486163831695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26573240389511926207102373 4982482573033486163831695)
    ·
      refine ⟨7473723859550229245747543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4982482573033486163831695 7473723859550229245747543)
      ·
        refine ⟨11210585789325343868621315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473723859550229245747543 11210585789325343868621315)
        ·
          refine ⟨16815878683988015802931973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11210585789325343868621315 16815878683988015802931973)
          ·
            refine ⟨3152977253247752963049745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16815878683988015802931973 3152977253247752963049745)
            ·
              refine ⟨2364732939935814722287309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3152977253247752963049745 2364732939935814722287309)
              ·
                refine ⟨886774852475930520857741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2364732939935814722287309 886774852475930520857741)
                ·
                  refine ⟨332540569678473945321653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886774852475930520857741 332540569678473945321653)
                  ·
                    rfl

theorem cell20_728573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_728573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728573 prefixEnd_728573 := by exact prefixLift 728573
  have htrace : WordTrace (prefixWord ++ tailWord_728573) baseStart_728573 baseEnd_728573 := by
    simpa [prefixWord, tailWord_728573, baseEnd_728573] using wordTrace_append hprefix tailTrace_728573
  have hstable : (prefixWord ++ tailWord_728573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728573).length < 2 ^ (prefixWord ++ tailWord_728573).sum := by decide
  have hdescent : baseEnd_728573 < baseStart_728573 := by decide
  rcases family_descends (prefixWord ++ tailWord_728573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728597 : List Nat := [1, 3, 2, 1, 3, 2, 1, 5, 2]
def baseStart_728597 : Nat := 118140960795 + 728597 * 2 ^ 59
def prefixEnd_728597 : Nat := 4983230072969 + 3 ^ 40 * 728597 * 2
def baseEnd_728597 : Nat := 332551523932436528521555

theorem tailTrace_728597 : CollatzResearch.WordTrace tailWord_728597 prefixEnd_728597 332551523932436528521555 := by
  unfold tailWord_728597
  simp only [CollatzResearch.WordTrace]
  refine ⟨26574115741424978305976045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17716077160949985537317363 26574115741424978305976045)
  ·
    refine ⟨9965293403034366864741017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26574115741424978305976045 9965293403034366864741017)
    ·
      refine ⟨7473970052275775148555763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9965293403034366864741017 7473970052275775148555763)
      ·
        refine ⟨11210955078413662722833645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473970052275775148555763 11210955078413662722833645)
        ·
          refine ⟨4204108154405123521062617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11210955078413662722833645 4204108154405123521062617)
          ·
            refine ⟨3153081115803842640796963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204108154405123521062617 3153081115803842640796963)
            ·
              refine ⟨4729621673705763961195445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153081115803842640796963 4729621673705763961195445)
              ·
                refine ⟨443402031909915371362073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4729621673705763961195445 443402031909915371362073)
                ·
                  refine ⟨332551523932436528521555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443402031909915371362073 332551523932436528521555)
                  ·
                    rfl

theorem cell20_728597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_728597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728597 prefixEnd_728597 := by exact prefixLift 728597
  have htrace : WordTrace (prefixWord ++ tailWord_728597) baseStart_728597 baseEnd_728597 := by
    simpa [prefixWord, tailWord_728597, baseEnd_728597] using wordTrace_append hprefix tailTrace_728597
  have hstable : (prefixWord ++ tailWord_728597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728597).length < 2 ^ (prefixWord ++ tailWord_728597).sum := by decide
  have hdescent : baseEnd_728597 < baseStart_728597 := by decide
  rcases family_descends (prefixWord ++ tailWord_728597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728611 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 5]
def baseStart_728611 : Nat := 118140960795 + 728611 * 2 ^ 59
def prefixEnd_728611 : Nat := 4983230072969 + 3 ^ 40 * 728611 * 2
def baseEnd_728611 : Nat := 332557913913914702054831

theorem tailTrace_728611 : CollatzResearch.WordTrace tailWord_728611 prefixEnd_728611 332557913913914702054831 := by
  unfold tailWord_728611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26574626363374258696985687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17716417575582839131323791 26574626363374258696985687)
  ·
    refine ⟨39861939545061388045478531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26574626363374258696985687 39861939545061388045478531)
    ·
      refine ⟨59792909317592082068217797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39861939545061388045478531 59792909317592082068217797)
      ·
        refine ⟨11211170497048515387790837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59792909317592082068217797 11211170497048515387790837)
        ·
          refine ⟨1051047234098298317605391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11211170497048515387790837 1051047234098298317605391)
          ·
            refine ⟨1576570851147447476408087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051047234098298317605391 1576570851147447476408087)
            ·
              refine ⟨2364856276721171214612131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576570851147447476408087 2364856276721171214612131)
              ·
                refine ⟨3547284415081756821918197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364856276721171214612131 3547284415081756821918197)
                ·
                  refine ⟨332557913913914702054831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3547284415081756821918197 332557913913914702054831)
                  ·
                    rfl

theorem cell20_728611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_728611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728611 prefixEnd_728611 := by exact prefixLift 728611
  have htrace : WordTrace (prefixWord ++ tailWord_728611) baseStart_728611 baseEnd_728611 := by
    simpa [prefixWord, tailWord_728611, baseEnd_728611] using wordTrace_append hprefix tailTrace_728611
  have hstable : (prefixWord ++ tailWord_728611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728611).length < 2 ^ (prefixWord ++ tailWord_728611).sum := by decide
  have hdescent : baseEnd_728611 < baseStart_728611 := by decide
  rcases family_descends (prefixWord ++ tailWord_728611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728652 : List Nat := [2, 2, 1, 3, 1, 5, 1, 3, 2]
def baseStart_728652 : Nat := 118140960795 + 728652 * 2 ^ 59
def prefixEnd_728652 : Nat := 4983230072969 + 3 ^ 40 * 728652 * 2
def baseEnd_728652 : Nat := 332576627431100781687997

theorem tailTrace_728652 : CollatzResearch.WordTrace tailWord_728652 prefixEnd_728652 332576627431100781687997 := by
  unfold tailWord_728652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13288060878112861349614105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17717414504150481799485473 13288060878112861349614105)
  ·
    refine ⟨9966045658584646012210579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13288060878112861349614105 9966045658584646012210579)
    ·
      refine ⟨14949068487876969018315869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9966045658584646012210579 14949068487876969018315869)
      ·
        refine ⟨5605900682953863381868451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14949068487876969018315869 5605900682953863381868451)
        ·
          refine ⟨8408851024430795072802677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5605900682953863381868451 8408851024430795072802677)
          ·
            refine ⟨788329783540387038075251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8408851024430795072802677 788329783540387038075251)
            ·
              refine ⟨1182494675310580557112877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788329783540387038075251 1182494675310580557112877)
              ·
                refine ⟨443435503241467708917329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182494675310580557112877 443435503241467708917329)
                ·
                  refine ⟨332576627431100781687997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443435503241467708917329 332576627431100781687997)
                  ·
                    rfl

theorem cell20_728652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_728652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728652 prefixEnd_728652 := by exact prefixLift 728652
  have htrace : WordTrace (prefixWord ++ tailWord_728652) baseStart_728652 baseEnd_728652 := by
    simpa [prefixWord, tailWord_728652, baseEnd_728652] using wordTrace_append hprefix tailTrace_728652
  have hstable : (prefixWord ++ tailWord_728652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728652).length < 2 ^ (prefixWord ++ tailWord_728652).sum := by decide
  have hdescent : baseEnd_728652 < baseStart_728652 := by decide
  rcases family_descends (prefixWord ++ tailWord_728652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728663 : List Nat := [1, 1, 3, 2, 2, 5, 6]
def baseStart_728663 : Nat := 118140960795 + 728663 * 2 ^ 59
def prefixEnd_728663 : Nat := 4983230072969 + 3 ^ 40 * 728663 * 2
def baseEnd_728663 : Nat := 36953516458981514702365

theorem tailTrace_728663 : CollatzResearch.WordTrace tailWord_728663 prefixEnd_728663 36953516458981514702365 := by
  unfold tailWord_728663
  simp only [CollatzResearch.WordTrace]
  refine ⟨26576522959185871577878643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17717681972790581051919095 26576522959185871577878643)
  ·
    refine ⟨39864784438778807366817965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26576522959185871577878643 39864784438778807366817965)
    ·
      refine ⟨14949294164542052762556737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39864784438778807366817965 14949294164542052762556737)
      ·
        refine ⟨11211970623406539571917553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14949294164542052762556737 11211970623406539571917553)
        ·
          refine ⟨8408977967554904678938165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11211970623406539571917553 8408977967554904678938165)
          ·
            refine ⟨788341684458272313650453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8408977967554904678938165 788341684458272313650453)
            ·
              refine ⟨36953516458981514702365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 788341684458272313650453 36953516458981514702365)
              ·
                rfl

theorem cell20_728663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_728663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728663 prefixEnd_728663 := by exact prefixLift 728663
  have htrace : WordTrace (prefixWord ++ tailWord_728663) baseStart_728663 baseEnd_728663 := by
    simpa [prefixWord, tailWord_728663, baseEnd_728663] using wordTrace_append hprefix tailTrace_728663
  have hstable : (prefixWord ++ tailWord_728663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728663).length < 2 ^ (prefixWord ++ tailWord_728663).sum := by decide
  have hdescent : baseEnd_728663 < baseStart_728663 := by decide
  rcases family_descends (prefixWord ++ tailWord_728663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728669 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 4]
def baseStart_728669 : Nat := 118140960795 + 728669 * 2 ^ 59
def prefixEnd_728669 : Nat := 4983230072969 + 3 ^ 40 * 728669 * 2
def baseEnd_728669 : Nat := 332584386694324278121261

theorem tailTrace_728669 : CollatzResearch.WordTrace tailWord_728669 prefixEnd_728669 332584386694324278121261 := by
  unfold tailWord_728669
  simp only [CollatzResearch.WordTrace]
  refine ⟨26576741797164134602597061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17717827864776089735064707 26576741797164134602597061)
  ·
    refine ⟨4983139086968275237986949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26576741797164134602597061 4983139086968275237986949)
    ·
      refine ⟨934338578806551607122553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4983139086968275237986949 934338578806551607122553)
      ·
        refine ⟨700753934104913705341915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 934338578806551607122553 700753934104913705341915)
        ·
          refine ⟨1051130901157370558012873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700753934104913705341915 1051130901157370558012873)
          ·
            refine ⟨788348175868027918509655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051130901157370558012873 788348175868027918509655)
            ·
              refine ⟨1182522263802041877764483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788348175868027918509655 1182522263802041877764483)
              ·
                refine ⟨1773783395703062816646725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182522263802041877764483 1773783395703062816646725)
                ·
                  refine ⟨332584386694324278121261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773783395703062816646725 332584386694324278121261)
                  ·
                    rfl

theorem cell20_728669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_728669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728669 prefixEnd_728669 := by exact prefixLift 728669
  have htrace : WordTrace (prefixWord ++ tailWord_728669) baseStart_728669 baseEnd_728669 := by
    simpa [prefixWord, tailWord_728669, baseEnd_728669] using wordTrace_append hprefix tailTrace_728669
  have hstable : (prefixWord ++ tailWord_728669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728669).length < 2 ^ (prefixWord ++ tailWord_728669).sum := by decide
  have hdescent : baseEnd_728669 < baseStart_728669 := by decide
  rcases family_descends (prefixWord ++ tailWord_728669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728680 : List Nat := [2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_728680 : Nat := 118140960795 + 728680 * 2 ^ 59
def prefixEnd_728680 : Nat := 4983230072969 + 3 ^ 40 * 728680 * 2
def baseEnd_728680 : Nat := 110863135798019042918183

theorem tailTrace_728680 : CollatzResearch.WordTrace tailWord_728680 prefixEnd_728680 110863135798019042918183 := by
  unfold tailWord_728680
  simp only [CollatzResearch.WordTrace]
  refine ⟨13288571500062141740623747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17718095333416188987498329 13288571500062141740623747)
  ·
    refine ⟨19932857250093212610935621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13288571500062141740623747 19932857250093212610935621)
    ·
      refine ⟨3737410734392477364550429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19932857250093212610935621 3737410734392477364550429)
      ·
        refine ⟨1401529025397179011706411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3737410734392477364550429 1401529025397179011706411)
        ·
          refine ⟨2102293538095768517559617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401529025397179011706411 2102293538095768517559617)
          ·
            refine ⟨1576720153571826388169713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2102293538095768517559617 1576720153571826388169713)
            ·
              refine ⟨1182540115178869791127285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576720153571826388169713 1182540115178869791127285)
              ·
                refine ⟨110863135798019042918183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1182540115178869791127285 110863135798019042918183)
                ·
                  rfl

theorem cell20_728680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_728680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728680 prefixEnd_728680 := by exact prefixLift 728680
  have htrace : WordTrace (prefixWord ++ tailWord_728680) baseStart_728680 baseEnd_728680 := by
    simpa [prefixWord, tailWord_728680, baseEnd_728680] using wordTrace_append hprefix tailTrace_728680
  have hstable : (prefixWord ++ tailWord_728680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728680).length < 2 ^ (prefixWord ++ tailWord_728680).sum := by decide
  have hdescent : baseEnd_728680 < baseStart_728680 := by decide
  rcases family_descends (prefixWord ++ tailWord_728680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728701 : List Nat := [1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_728701 : Nat := 118140960795 + 728701 * 2 ^ 59
def prefixEnd_728701 : Nat := 4983230072969 + 3 ^ 40 * 728701 * 2
def baseEnd_728701 : Nat := 110866330788758129684821

theorem tailTrace_728701 : CollatzResearch.WordTrace tailWord_728701 prefixEnd_728701 110866330788758129684821 := by
  unfold tailWord_728701
  simp only [CollatzResearch.WordTrace]
  refine ⟨26577908933048204067761957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17718605955365469378507971 26577908933048204067761957)
  ·
    refine ⟨4983357924946538262705367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26577908933048204067761957 4983357924946538262705367)
    ·
      refine ⟨7475036887419807394058051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4983357924946538262705367 7475036887419807394058051)
      ·
        refine ⟨11212555331129711091087077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475036887419807394058051 11212555331129711091087077)
        ·
          refine ⟨2102354124586820829578827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11212555331129711091087077 2102354124586820829578827)
          ·
            refine ⟨3153531186880231244368241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102354124586820829578827 3153531186880231244368241)
            ·
              refine ⟨2365148390160173433276181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153531186880231244368241 2365148390160173433276181)
              ·
                refine ⟨110866330788758129684821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2365148390160173433276181 110866330788758129684821)
                ·
                  rfl

theorem cell20_728701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_728701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728701 prefixEnd_728701 := by exact prefixLift 728701
  have htrace : WordTrace (prefixWord ++ tailWord_728701) baseStart_728701 baseEnd_728701 := by
    simpa [prefixWord, tailWord_728701, baseEnd_728701] using wordTrace_append hprefix tailTrace_728701
  have hstable : (prefixWord ++ tailWord_728701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728701).length < 2 ^ (prefixWord ++ tailWord_728701).sum := by decide
  have hdescent : baseEnd_728701 < baseStart_728701 := by decide
  rcases family_descends (prefixWord ++ tailWord_728701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728724 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 2]
def baseStart_728724 : Nat := 118140960795 + 728724 * 2 ^ 59
def prefixEnd_728724 : Nat := 4983230072969 + 3 ^ 40 * 728724 * 2
def baseEnd_728724 : Nat := 332609490192988531287703

theorem tailTrace_728724 : CollatzResearch.WordTrace tailWord_728724 prefixEnd_728724 332609490192988531287703 := by
  unfold tailWord_728724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13289373905982439497924613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17719165207976585997232817 13289373905982439497924613)
  ·
    refine ⟨2491757607371707405860865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13289373905982439497924613 2491757607371707405860865)
    ·
      refine ⟨1868818205528780554395649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2491757607371707405860865 1868818205528780554395649)
      ·
        refine ⟨1401613654146585415796737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1868818205528780554395649 1401613654146585415796737)
        ·
          refine ⟨1051210240609939061847553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1401613654146585415796737 1051210240609939061847553)
          ·
            refine ⟨788407680457454296385665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051210240609939061847553 788407680457454296385665)
            ·
              refine ⟨591305760343090722289249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788407680457454296385665 591305760343090722289249)
              ·
                refine ⟨443479320257318041716937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591305760343090722289249 443479320257318041716937)
                ·
                  refine ⟨332609490192988531287703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443479320257318041716937 332609490192988531287703)
                  ·
                    rfl

theorem cell20_728724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_728724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728724 prefixEnd_728724 := by exact prefixLift 728724
  have htrace : WordTrace (prefixWord ++ tailWord_728724) baseStart_728724 baseEnd_728724 := by
    simpa [prefixWord, tailWord_728724, baseEnd_728724] using wordTrace_append hprefix tailTrace_728724
  have hstable : (prefixWord ++ tailWord_728724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728724).length < 2 ^ (prefixWord ++ tailWord_728724).sum := by decide
  have hdescent : baseEnd_728724 < baseStart_728724 := by decide
  rcases family_descends (prefixWord ++ tailWord_728724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728728 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 2]
def baseStart_728728 : Nat := 118140960795 + 728728 * 2 ^ 59
def prefixEnd_728728 : Nat := 4983230072969 + 3 ^ 40 * 728728 * 2
def baseEnd_728728 : Nat := 332611315901982295154353

theorem tailTrace_728728 : CollatzResearch.WordTrace tailWord_728728 prefixEnd_728728 332611315901982295154353 := by
  unfold tailWord_728728
  simp only [CollatzResearch.WordTrace]
  refine ⟨13289446851975193839497419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17719262469300258452663225 13289446851975193839497419)
  ·
    refine ⟨19934170277962790759246129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13289446851975193839497419 19934170277962790759246129)
    ·
      refine ⟨14950627708472093069434597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19934170277962790759246129 14950627708472093069434597)
      ·
        refine ⟨2803242695338517450518987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14950627708472093069434597 2803242695338517450518987)
        ·
          refine ⟨4204864043007776175778481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803242695338517450518987 4204864043007776175778481)
          ·
            refine ⟨3153648032255832131833861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204864043007776175778481 3153648032255832131833861)
            ·
              refine ⟨591309006047968524718849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3153648032255832131833861 591309006047968524718849)
              ·
                refine ⟨443481754535976393539137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591309006047968524718849 443481754535976393539137)
                ·
                  refine ⟨332611315901982295154353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443481754535976393539137 332611315901982295154353)
                  ·
                    rfl

theorem cell20_728728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_728728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728728 prefixEnd_728728 := by exact prefixLift 728728
  have htrace : WordTrace (prefixWord ++ tailWord_728728) baseStart_728728 baseEnd_728728 := by
    simpa [prefixWord, tailWord_728728, baseEnd_728728] using wordTrace_append hprefix tailTrace_728728
  have hstable : (prefixWord ++ tailWord_728728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728728).length < 2 ^ (prefixWord ++ tailWord_728728).sum := by decide
  have hdescent : baseEnd_728728 < baseStart_728728 := by decide
  rcases family_descends (prefixWord ++ tailWord_728728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728735 : List Nat := [1, 1, 2, 7, 1, 2, 1, 5]
def baseStart_728735 : Nat := 118140960795 + 728735 * 2 ^ 59
def prefixEnd_728735 : Nat := 4983230072969 + 3 ^ 40 * 728735 * 2
def baseEnd_728735 : Nat := 110871503630907127306997

theorem tailTrace_728735 : CollatzResearch.WordTrace tailWord_728735 prefixEnd_728735 110871503630907127306997 := by
  unfold tailWord_728735
  simp only [CollatzResearch.WordTrace]
  refine ⟨26579149014925027874499659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17719432676616685249666439 26579149014925027874499659)
  ·
    refine ⟨39868723522387541811749489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26579149014925027874499659 39868723522387541811749489)
    ·
      refine ⟨29901542641790656358812117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39868723522387541811749489 29901542641790656358812117)
      ·
        refine ⟨700817405666968508409659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 29901542641790656358812117 700817405666968508409659)
        ·
          refine ⟨1051226108500452762614489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700817405666968508409659 1051226108500452762614489)
          ·
            refine ⟨788419581375339571960867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051226108500452762614489 788419581375339571960867)
            ·
              refine ⟨1182629372063009357941301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788419581375339571960867 1182629372063009357941301)
              ·
                refine ⟨110871503630907127306997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1182629372063009357941301 110871503630907127306997)
                ·
                  rfl

theorem cell20_728735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_728735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728735 prefixEnd_728735 := by exact prefixLift 728735
  have htrace : WordTrace (prefixWord ++ tailWord_728735) baseStart_728735 baseEnd_728735 := by
    simpa [prefixWord, tailWord_728735, baseEnd_728735] using wordTrace_append hprefix tailTrace_728735
  have hstable : (prefixWord ++ tailWord_728735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728735).length < 2 ^ (prefixWord ++ tailWord_728735).sum := by decide
  have hdescent : baseEnd_728735 < baseStart_728735 := by decide
  rcases family_descends (prefixWord ++ tailWord_728735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728760 : List Nat := [2, 1, 2, 1, 2, 1, 1, 10]
def baseStart_728760 : Nat := 118140960795 + 728760 * 2 ^ 59
def prefixEnd_728760 : Nat := 4983230072969 + 3 ^ 40 * 728760 * 2
def baseEnd_728760 : Nat := 110875307191310802029185

theorem tailTrace_728760 : CollatzResearch.WordTrace tailWord_728760 prefixEnd_728760 110875307191310802029185 := by
  unfold tailWord_728760
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290030419917228572079867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17720040559889638096106489 13290030419917228572079867)
  ·
    refine ⟨19935045629875842858119801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13290030419917228572079867 19935045629875842858119801)
    ·
      refine ⟨14951284222406882143589851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19935045629875842858119801 14951284222406882143589851)
      ·
        refine ⟨22426926333610323215384777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14951284222406882143589851 22426926333610323215384777)
        ·
          refine ⟨16820194750207742411538583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22426926333610323215384777 16820194750207742411538583)
          ·
            refine ⟨25230292125311613617307875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16820194750207742411538583 25230292125311613617307875)
            ·
              refine ⟨37845438187967420425961813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25230292125311613617307875 37845438187967420425961813)
              ·
                refine ⟨110875307191310802029185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37845438187967420425961813 110875307191310802029185)
                ·
                  rfl

theorem cell20_728760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_728760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728760 prefixEnd_728760 := by exact prefixLift 728760
  have htrace : WordTrace (prefixWord ++ tailWord_728760) baseStart_728760 baseEnd_728760 := by
    simpa [prefixWord, tailWord_728760, baseEnd_728760] using wordTrace_append hprefix tailTrace_728760
  have hstable : (prefixWord ++ tailWord_728760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728760).length < 2 ^ (prefixWord ++ tailWord_728760).sum := by decide
  have hdescent : baseEnd_728760 < baseStart_728760 := by decide
  rcases family_descends (prefixWord ++ tailWord_728760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728766 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_728766 : Nat := 118140960795 + 728766 * 2 ^ 59
def prefixEnd_728766 : Nat := 4983230072969 + 3 ^ 40 * 728766 * 2
def baseEnd_728766 : Nat := 332628660137423051887531

theorem tailTrace_728766 : CollatzResearch.WordTrace tailWord_728766 prefixEnd_728766 332628660137423051887531 := by
  unfold tailWord_728766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322534959726590021109769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17720186451875146779252101 3322534959726590021109769)
  ·
    refine ⟨2491901219794942515832327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3322534959726590021109769 2491901219794942515832327)
    ·
      refine ⟨3737851829692413773748491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491901219794942515832327 3737851829692413773748491)
      ·
        refine ⟨5606777744538620660622737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737851829692413773748491 5606777744538620660622737)
        ·
          refine ⟨4205083308403965495467053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606777744538620660622737 4205083308403965495467053)
          ·
            refine ⟨1576906240651487060800145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4205083308403965495467053 1576906240651487060800145)
            ·
              refine ⟨1182679680488615295600109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576906240651487060800145 1182679680488615295600109)
              ·
                refine ⟨443504880183230735850041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182679680488615295600109 443504880183230735850041)
                ·
                  refine ⟨332628660137423051887531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443504880183230735850041 332628660137423051887531)
                  ·
                    rfl

theorem cell20_728766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_728766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728766 prefixEnd_728766 := by exact prefixLift 728766
  have htrace : WordTrace (prefixWord ++ tailWord_728766) baseStart_728766 baseEnd_728766 := by
    simpa [prefixWord, tailWord_728766, baseEnd_728766] using wordTrace_append hprefix tailTrace_728766
  have hstable : (prefixWord ++ tailWord_728766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728766).length < 2 ^ (prefixWord ++ tailWord_728766).sum := by decide
  have hdescent : baseEnd_728766 < baseStart_728766 := by decide
  rcases family_descends (prefixWord ++ tailWord_728766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728784 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_728784 : Nat := 118140960795 + 728784 * 2 ^ 59
def prefixEnd_728784 : Nat := 4983230072969 + 3 ^ 40 * 728784 * 2
def baseEnd_728784 : Nat := 332636875827894989287457

theorem tailTrace_728784 : CollatzResearch.WordTrace tailWord_728784 prefixEnd_728784 332636875827894989287457 := by
  unfold tailWord_728784
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290468095873754621516703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17720624127831672828688937 13290468095873754621516703)
  ·
    refine ⟨19935702143810631932275055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13290468095873754621516703 19935702143810631932275055)
    ·
      refine ⟨29903553215715947898412583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19935702143810631932275055 29903553215715947898412583)
      ·
        refine ⟨44855329823573921847618875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29903553215715947898412583 44855329823573921847618875)
        ·
          refine ⟨67282994735360882771428313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44855329823573921847618875 67282994735360882771428313)
          ·
            refine ⟨50462246051520662078571235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67282994735360882771428313 50462246051520662078571235)
            ·
              refine ⟨75693369077280993117856853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50462246051520662078571235 75693369077280993117856853)
              ·
                refine ⟨887031668874386638099885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 75693369077280993117856853 887031668874386638099885)
                ·
                  refine ⟨332636875827894989287457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887031668874386638099885 332636875827894989287457)
                  ·
                    rfl

theorem cell20_728784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_728784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728784 prefixEnd_728784 := by exact prefixLift 728784
  have htrace : WordTrace (prefixWord ++ tailWord_728784) baseStart_728784 baseEnd_728784 := by
    simpa [prefixWord, tailWord_728784, baseEnd_728784] using wordTrace_append hprefix tailTrace_728784
  have hstable : (prefixWord ++ tailWord_728784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728784).length < 2 ^ (prefixWord ++ tailWord_728784).sum := by decide
  have hdescent : baseEnd_728784 < baseStart_728784 := by decide
  rcases family_descends (prefixWord ++ tailWord_728784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728808 : List Nat := [2, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_728808 : Nat := 118140960795 + 728808 * 2 ^ 59
def prefixEnd_728808 : Nat := 4983230072969 + 3 ^ 40 * 728808 * 2
def baseEnd_728808 : Nat := 332647830081857572487359

theorem tailTrace_728808 : CollatzResearch.WordTrace tailWord_728808 prefixEnd_728808 332647830081857572487359 := by
  unfold tailWord_728808
  simp only [CollatzResearch.WordTrace]
  refine ⟨13290905771830280670953539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17721207695773707561271385 13290905771830280670953539)
  ·
    refine ⟨19936358657745421006430309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13290905771830280670953539 19936358657745421006430309)
    ·
      refine ⟨3738067248327266438705683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19936358657745421006430309 3738067248327266438705683)
      ·
        refine ⟨5607100872490899658058525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3738067248327266438705683 5607100872490899658058525)
        ·
          refine ⟨2102662827184087371771947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5607100872490899658058525 2102662827184087371771947)
          ·
            refine ⟨3153994240776131057657921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102662827184087371771947 3153994240776131057657921)
            ·
              refine ⟨2365495680582098293243441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153994240776131057657921 2365495680582098293243441)
              ·
                refine ⟨1774121760436573719932581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2365495680582098293243441 1774121760436573719932581)
                ·
                  refine ⟨332647830081857572487359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774121760436573719932581 332647830081857572487359)
                  ·
                    rfl

theorem cell20_728808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_728808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728808 prefixEnd_728808 := by exact prefixLift 728808
  have htrace : WordTrace (prefixWord ++ tailWord_728808) baseStart_728808 baseEnd_728808 := by
    simpa [prefixWord, tailWord_728808, baseEnd_728808] using wordTrace_append hprefix tailTrace_728808
  have hstable : (prefixWord ++ tailWord_728808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728808).length < 2 ^ (prefixWord ++ tailWord_728808).sum := by decide
  have hdescent : baseEnd_728808 < baseStart_728808 := by decide
  rcases family_descends (prefixWord ++ tailWord_728808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728842 : List Nat := [3, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_728842 : Nat := 118140960795 + 728842 * 2 ^ 59
def prefixEnd_728842 : Nat := 4983230072969 + 3 ^ 40 * 728842 * 2
def baseEnd_728842 : Nat := 332663348608304565353887

theorem tailTrace_728842 : CollatzResearch.WordTrace tailWord_728842 prefixEnd_728842 332663348608304565353887 := by
  unfold tailWord_728842
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645762906384346287161195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17722034417024923432429853 6645762906384346287161195)
  ·
    refine ⟨9968644359576519430741793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6645762906384346287161195 9968644359576519430741793)
    ·
      refine ⟨7476483269682389573056345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9968644359576519430741793 7476483269682389573056345)
      ·
        refine ⟨5607362452261792179792259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7476483269682389573056345 5607362452261792179792259)
        ·
          refine ⟨8411043678392688269688389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607362452261792179792259 8411043678392688269688389)
          ·
            refine ⟨1577070689698629050566573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8411043678392688269688389 1577070689698629050566573)
            ·
              refine ⟨591401508636985893962465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1577070689698629050566573 591401508636985893962465)
              ·
                refine ⟨443551131477739420471849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591401508636985893962465 443551131477739420471849)
                ·
                  refine ⟨332663348608304565353887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443551131477739420471849 332663348608304565353887)
                  ·
                    rfl

theorem cell20_728842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_728842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728842 prefixEnd_728842 := by exact prefixLift 728842
  have htrace : WordTrace (prefixWord ++ tailWord_728842) baseStart_728842 baseEnd_728842 := by
    simpa [prefixWord, tailWord_728842, baseEnd_728842] using wordTrace_append hprefix tailTrace_728842
  have hstable : (prefixWord ++ tailWord_728842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728842).length < 2 ^ (prefixWord ++ tailWord_728842).sum := by decide
  have hdescent : baseEnd_728842 < baseStart_728842 := by decide
  rcases family_descends (prefixWord ++ tailWord_728842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728845 : List Nat := [1, 7, 2, 1, 1, 1, 2, 5]
def baseStart_728845 : Nat := 118140960795 + 728845 * 2 ^ 59
def prefixEnd_728845 : Nat := 4983230072969 + 3 ^ 40 * 728845 * 2
def baseEnd_728845 : Nat := 110888239296683296084625

theorem tailTrace_728845 : CollatzResearch.WordTrace tailWord_728845 prefixEnd_728845 110888239296683296084625 := by
  unfold tailWord_728845
  simp only [CollatzResearch.WordTrace]
  refine ⟨26583161044526516661003989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17722107363017677774002659 26583161044526516661003989)
  ·
    refine ⟨623042836981090234242281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26583161044526516661003989 623042836981090234242281)
    ·
      refine ⟨467282127735817675681711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 623042836981090234242281 467282127735817675681711)
      ·
        refine ⟨700923191603726513522567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467282127735817675681711 700923191603726513522567)
        ·
          refine ⟨1051384787405589770283851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700923191603726513522567 1051384787405589770283851)
          ·
            refine ⟨1577077181108384655425777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051384787405589770283851 1577077181108384655425777)
            ·
              refine ⟨1182807885831288491569333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577077181108384655425777 1182807885831288491569333)
              ·
                refine ⟨110888239296683296084625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1182807885831288491569333 110888239296683296084625)
                ·
                  rfl

theorem cell20_728845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].length) (baseStart_728845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728845 prefixEnd_728845 := by exact prefixLift 728845
  have htrace : WordTrace (prefixWord ++ tailWord_728845) baseStart_728845 baseEnd_728845 := by
    simpa [prefixWord, tailWord_728845, baseEnd_728845] using wordTrace_append hprefix tailTrace_728845
  have hstable : (prefixWord ++ tailWord_728845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728845).length < 2 ^ (prefixWord ++ tailWord_728845).sum := by decide
  have hdescent : baseEnd_728845 < baseStart_728845 := by decide
  rcases family_descends (prefixWord ++ tailWord_728845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728846 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_728846 : Nat := 118140960795 + 728846 * 2 ^ 59
def prefixEnd_728846 : Nat := 4983230072969 + 3 ^ 40 * 728846 * 2
def baseEnd_728846 : Nat := 332665174317298329220537

theorem tailTrace_728846 : CollatzResearch.WordTrace tailWord_728846 prefixEnd_728846 332665174317298329220537 := by
  unfold tailWord_728846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322899689690361728973799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17722131678348595887860261 3322899689690361728973799)
  ·
    refine ⟨4984349534535542593460699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3322899689690361728973799 4984349534535542593460699)
    ·
      refine ⟨7476524301803313890191049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4984349534535542593460699 7476524301803313890191049)
      ·
        refine ⟨5607393226352485417643287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7476524301803313890191049 5607393226352485417643287)
        ·
          refine ⟨8411089839528728126464931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607393226352485417643287 8411089839528728126464931)
          ·
            refine ⟨12616634759293092189697397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411089839528728126464931 12616634759293092189697397)
            ·
              refine ⟨1182809508683727392784131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12616634759293092189697397 1182809508683727392784131)
              ·
                refine ⟨1774214263025591089176197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182809508683727392784131 1774214263025591089176197)
                ·
                  refine ⟨332665174317298329220537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774214263025591089176197 332665174317298329220537)
                  ·
                    rfl

theorem cell20_728846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_728846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728846 prefixEnd_728846 := by exact prefixLift 728846
  have htrace : WordTrace (prefixWord ++ tailWord_728846) baseStart_728846 baseEnd_728846 := by
    simpa [prefixWord, tailWord_728846, baseEnd_728846] using wordTrace_append hprefix tailTrace_728846
  have hstable : (prefixWord ++ tailWord_728846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728846).length < 2 ^ (prefixWord ++ tailWord_728846).sum := by decide
  have hdescent : baseEnd_728846 < baseStart_728846 := by decide
  rcases family_descends (prefixWord ++ tailWord_728846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728852 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 3]
def baseStart_728852 : Nat := 118140960795 + 728852 * 2 ^ 59
def prefixEnd_728852 : Nat := 4983230072969 + 3 ^ 40 * 728852 * 2
def baseEnd_728852 : Nat := 332667912880788975020513

theorem tailTrace_728852 : CollatzResearch.WordTrace tailWord_728852 prefixEnd_728852 332667912880788975020513 := by
  unfold tailWord_728852
  simp only [CollatzResearch.WordTrace]
  refine ⟨13291708177750578428254405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17722277570334104571005873 13291708177750578428254405)
  ·
    refine ⟨2492195283328233455297701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13291708177750578428254405 2492195283328233455297701)
    ·
      refine ⟨467286615624043772868319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2492195283328233455297701 467286615624043772868319)
      ·
        refine ⟨700929923436065659302479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467286615624043772868319 700929923436065659302479)
        ·
          refine ⟨1051394885154098488953719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700929923436065659302479 1051394885154098488953719)
          ·
            refine ⟨1577092327731147733430579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051394885154098488953719 1577092327731147733430579)
            ·
              refine ⟨2365638491596721600145869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577092327731147733430579 2365638491596721600145869)
              ·
                refine ⟨887114434348770600054701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2365638491596721600145869 887114434348770600054701)
                ·
                  refine ⟨332667912880788975020513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887114434348770600054701 332667912880788975020513)
                  ·
                    rfl

theorem cell20_728852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_728852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728852 prefixEnd_728852 := by exact prefixLift 728852
  have htrace : WordTrace (prefixWord ++ tailWord_728852) baseStart_728852 baseEnd_728852 := by
    simpa [prefixWord, tailWord_728852, baseEnd_728852] using wordTrace_append hprefix tailTrace_728852
  have hstable : (prefixWord ++ tailWord_728852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728852).length < 2 ^ (prefixWord ++ tailWord_728852).sum := by decide
  have hdescent : baseEnd_728852 < baseStart_728852 := by decide
  rcases family_descends (prefixWord ++ tailWord_728852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728853 : List Nat := [1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_728853 : Nat := 118140960795 + 728853 * 2 ^ 59
def prefixEnd_728853 : Nat := 4983230072969 + 3 ^ 40 * 728853 * 2
def baseEnd_728853 : Nat := 110889456436012471995725

theorem tailTrace_728853 : CollatzResearch.WordTrace tailWord_728853 prefixEnd_728853 110889456436012471995725 := by
  unfold tailWord_728853
  simp only [CollatzResearch.WordTrace]
  refine ⟨26583452828497534027295213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17722301885665022684863475 26583452828497534027295213)
  ·
    refine ⟨9968794810686575260235705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26583452828497534027295213 9968794810686575260235705)
    ·
      refine ⟨7476596108014931445176779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9968794810686575260235705 7476596108014931445176779)
      ·
        refine ⟨11214894162022397167765169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7476596108014931445176779 11214894162022397167765169)
        ·
          refine ⟨8411170621516797875823877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11214894162022397167765169 8411170621516797875823877)
          ·
            refine ⟨1577094491534399601716977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8411170621516797875823877 1577094491534399601716977)
            ·
              refine ⟨1182820868650799701287733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577094491534399601716977 1182820868650799701287733)
              ·
                refine ⟨110889456436012471995725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1182820868650799701287733 110889456436012471995725)
                ·
                  rfl

theorem cell20_728853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_728853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728853 prefixEnd_728853 := by exact prefixLift 728853
  have htrace : WordTrace (prefixWord ++ tailWord_728853) baseStart_728853 baseEnd_728853 := by
    simpa [prefixWord, tailWord_728853, baseEnd_728853] using wordTrace_append hprefix tailTrace_728853
  have hstable : (prefixWord ++ tailWord_728853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728853).length < 2 ^ (prefixWord ++ tailWord_728853).sum := by decide
  have hdescent : baseEnd_728853 < baseStart_728853 := by decide
  rcases family_descends (prefixWord ++ tailWord_728853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728867 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_728867 : Nat := 118140960795 + 728867 * 2 ^ 59
def prefixEnd_728867 : Nat := 4983230072969 + 3 ^ 40 * 728867 * 2
def baseEnd_728867 : Nat := 332674759289515589520451

theorem tailTrace_728867 : CollatzResearch.WordTrace tailWord_728867 prefixEnd_728867 332674759289515589520451 := by
  unfold tailWord_728867
  simp only [CollatzResearch.WordTrace]
  refine ⟨26583963450446814418304855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17722642300297876278869903 26583963450446814418304855)
  ·
    refine ⟨39875945175670221627457283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26583963450446814418304855 39875945175670221627457283)
    ·
      refine ⟨59813917763505332441185925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39875945175670221627457283 59813917763505332441185925)
      ·
        refine ⟨11215109580657249832722361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59813917763505332441185925 11215109580657249832722361)
        ·
          refine ⟨8411332185492937374541771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11215109580657249832722361 8411332185492937374541771)
          ·
            refine ⟨12616998278239406061812657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411332185492937374541771 12616998278239406061812657)
            ·
              refine ⟨9462748708679554546359493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12616998278239406061812657 9462748708679554546359493)
              ·
                refine ⟨1774265382877416477442405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9462748708679554546359493 1774265382877416477442405)
                ·
                  refine ⟨332674759289515589520451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774265382877416477442405 332674759289515589520451)
                  ·
                    rfl

theorem cell20_728867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_728867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728867 prefixEnd_728867 := by exact prefixLift 728867
  have htrace : WordTrace (prefixWord ++ tailWord_728867) baseStart_728867 baseEnd_728867 := by
    simpa [prefixWord, tailWord_728867, baseEnd_728867] using wordTrace_append hprefix tailTrace_728867
  have hstable : (prefixWord ++ tailWord_728867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728867).length < 2 ^ (prefixWord ++ tailWord_728867).sum := by decide
  have hdescent : baseEnd_728867 < baseStart_728867 := by decide
  rcases family_descends (prefixWord ++ tailWord_728867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728894 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_728894 : Nat := 118140960795 + 728894 * 2 ^ 59
def prefixEnd_728894 : Nat := 4983230072969 + 3 ^ 40 * 728894 * 2
def baseEnd_728894 : Nat := 332687082825223495620341

theorem tailTrace_728894 : CollatzResearch.WordTrace tailWord_728894 prefixEnd_728894 332687082825223495620341 := by
  unfold tailWord_728894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323118527668624753692217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17723298814232665353025157 3323118527668624753692217)
  ·
    refine ⟨2492338895751468565269163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3323118527668624753692217 2492338895751468565269163)
    ·
      refine ⟨3738508343627202847903745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2492338895751468565269163 3738508343627202847903745)
      ·
        refine ⟨2803881257720402135927809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3738508343627202847903745 2803881257720402135927809)
        ·
          refine ⟨2102910943290301601945857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2803881257720402135927809 2102910943290301601945857)
          ·
            refine ⟨1577183207467726201459393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2102910943290301601945857 1577183207467726201459393)
            ·
              refine ⟨1182887405600794651094545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577183207467726201459393 1182887405600794651094545)
              ·
                refine ⟨887165554200595988320909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182887405600794651094545 887165554200595988320909)
                ·
                  refine ⟨332687082825223495620341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887165554200595988320909 332687082825223495620341)
                  ·
                    rfl

theorem cell20_728894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_728894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728894 prefixEnd_728894 := by exact prefixLift 728894
  have htrace : WordTrace (prefixWord ++ tailWord_728894) baseStart_728894 baseEnd_728894 := by
    simpa [prefixWord, tailWord_728894, baseEnd_728894] using wordTrace_append hprefix tailTrace_728894
  have hstable : (prefixWord ++ tailWord_728894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728894).length < 2 ^ (prefixWord ++ tailWord_728894).sum := by decide
  have hdescent : baseEnd_728894 < baseStart_728894 := by decide
  rcases family_descends (prefixWord ++ tailWord_728894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728905 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 4]
def baseStart_728905 : Nat := 118140960795 + 728905 * 2 ^ 59
def prefixEnd_728905 : Nat := 4983230072969 + 3 ^ 40 * 728905 * 2
def baseEnd_728905 : Nat := 332692103524956346253629

theorem tailTrace_728905 : CollatzResearch.WordTrace tailWord_728905 prefixEnd_728905 332692103524956346253629 := by
  unfold tailWord_728905
  simp only [CollatzResearch.WordTrace]
  refine ⟨26585349424309146908188169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17723566282872764605458779 26585349424309146908188169)
  ·
    refine ⟨19939012068231860181141127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26585349424309146908188169 19939012068231860181141127)
    ·
      refine ⟨29908518102347790271711691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19939012068231860181141127 29908518102347790271711691)
      ·
        refine ⟨44862777153521685407567537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29908518102347790271711691 44862777153521685407567537)
        ·
          refine ⟨33647082865141264055675653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44862777153521685407567537 33647082865141264055675653)
          ·
            refine ⟨6308828037213987010439185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33647082865141264055675653 6308828037213987010439185)
            ·
              refine ⟨4731621027910490257829389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6308828037213987010439185 4731621027910490257829389)
              ·
                refine ⟨1774357885466433846686021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731621027910490257829389 1774357885466433846686021)
                ·
                  refine ⟨332692103524956346253629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774357885466433846686021 332692103524956346253629)
                  ·
                    rfl

theorem cell20_728905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_728905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728905 prefixEnd_728905 := by exact prefixLift 728905
  have htrace : WordTrace (prefixWord ++ tailWord_728905) baseStart_728905 baseEnd_728905 := by
    simpa [prefixWord, tailWord_728905, baseEnd_728905] using wordTrace_append hprefix tailTrace_728905
  have hstable : (prefixWord ++ tailWord_728905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728905).length < 2 ^ (prefixWord ++ tailWord_728905).sum := by decide
  have hdescent : baseEnd_728905 < baseStart_728905 := by decide
  rcases family_descends (prefixWord ++ tailWord_728905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728908 : List Nat := [2, 2, 1, 3, 4, 2, 1, 5]
def baseStart_728908 : Nat := 118140960795 + 728908 * 2 ^ 59
def prefixEnd_728908 : Nat := 4983230072969 + 3 ^ 40 * 728908 * 2
def baseEnd_728908 : Nat := 110897824268900556384539

theorem tailTrace_728908 : CollatzResearch.WordTrace tailWord_728908 prefixEnd_728908 110897824268900556384539 := by
  unfold tailWord_728908
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292729421649139210273689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17723639228865518947031585 13292729421649139210273689)
  ·
    refine ⟨9969547066236854407705267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13292729421649139210273689 9969547066236854407705267)
    ·
      refine ⟨14954320599355281611557901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9969547066236854407705267 14954320599355281611557901)
      ·
        refine ⟨5607870224758230604334213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14954320599355281611557901 5607870224758230604334213)
        ·
          refine ⟨1051475667142168238312665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5607870224758230604334213 1051475667142168238312665)
          ·
            refine ⟨788606750356626178734499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051475667142168238312665 788606750356626178734499)
            ·
              refine ⟨1182910125534939268101749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788606750356626178734499 1182910125534939268101749)
              ·
                refine ⟨110897824268900556384539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1182910125534939268101749 110897824268900556384539)
                ·
                  rfl

theorem cell20_728908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_728908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728908 prefixEnd_728908 := by exact prefixLift 728908
  have htrace : WordTrace (prefixWord ++ tailWord_728908) baseStart_728908 baseEnd_728908 := by
    simpa [prefixWord, tailWord_728908, baseEnd_728908] using wordTrace_append hprefix tailTrace_728908
  have hstable : (prefixWord ++ tailWord_728908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728908).length < 2 ^ (prefixWord ++ tailWord_728908).sum := by decide
  have hdescent : baseEnd_728908 < baseStart_728908 := by decide
  rcases family_descends (prefixWord ++ tailWord_728908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728929 : List Nat := [1, 2, 3, 1, 1, 1, 7, 4]
def baseStart_728929 : Nat := 118140960795 + 728929 * 2 ^ 59
def prefixEnd_728929 : Nat := 4983230072969 + 3 ^ 40 * 728929 * 2
def baseEnd_728929 : Nat := 110901019259639643151177

theorem tailTrace_728929 : CollatzResearch.WordTrace tailWord_728929 prefixEnd_728929 110901019259639643151177 := by
  unfold tailWord_728929
  simp only [CollatzResearch.WordTrace]
  refine ⟨26586224776222199007061841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17724149850814799338041227 26586224776222199007061841)
  ·
    refine ⟨19939668582166649255296381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26586224776222199007061841 19939668582166649255296381)
    ·
      refine ⟨7477375718312493470736143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19939668582166649255296381 7477375718312493470736143)
      ·
        refine ⟨11216063577468740206104215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477375718312493470736143 11216063577468740206104215)
        ·
          refine ⟨16824095366203110309156323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216063577468740206104215 16824095366203110309156323)
          ·
            refine ⟨25236143049304665463734485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16824095366203110309156323 25236143049304665463734485)
            ·
              refine ⟨591472102718078096806277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 25236143049304665463734485 591472102718078096806277)
              ·
                refine ⟨110901019259639643151177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591472102718078096806277 110901019259639643151177)
                ·
                  rfl

theorem cell20_728929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 4].length) (baseStart_728929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728929 prefixEnd_728929 := by exact prefixLift 728929
  have htrace : WordTrace (prefixWord ++ tailWord_728929) baseStart_728929 baseEnd_728929 := by
    simpa [prefixWord, tailWord_728929, baseEnd_728929] using wordTrace_append hprefix tailTrace_728929
  have hstable : (prefixWord ++ tailWord_728929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728929).length < 2 ^ (prefixWord ++ tailWord_728929).sum := by decide
  have hdescent : baseEnd_728929 < baseStart_728929 := by decide
  rcases family_descends (prefixWord ++ tailWord_728929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728936 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_728936 : Nat := 118140960795 + 728936 * 2 ^ 59
def prefixEnd_728936 : Nat := 4983230072969 + 3 ^ 40 * 728936 * 2
def baseEnd_728936 : Nat := 332706252769658016220169

theorem tailTrace_728936 : CollatzResearch.WordTrace tailWord_728936 prefixEnd_728936 332706252769658016220169 := by
  unfold tailWord_728936
  simp only [CollatzResearch.WordTrace]
  refine ⟨13293240043598419601283331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17724320058131226135044441 13293240043598419601283331)
  ·
    refine ⟨19939860065397629401924997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13293240043598419601283331 19939860065397629401924997)
    ·
      refine ⟨3738723762262055512860937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19939860065397629401924997 3738723762262055512860937)
      ·
        refine ⟨2804042821696541634645703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3738723762262055512860937 2804042821696541634645703)
        ·
          refine ⟨4206064232544812451968555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2804042821696541634645703 4206064232544812451968555)
          ·
            refine ⟨6309096348817218677952833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206064232544812451968555 6309096348817218677952833)
            ·
              refine ⟨4731822261612914008464625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309096348817218677952833 4731822261612914008464625)
              ·
                refine ⟨3548866696209685506348469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4731822261612914008464625 3548866696209685506348469)
                ·
                  refine ⟨332706252769658016220169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3548866696209685506348469 332706252769658016220169)
                  ·
                    rfl

theorem cell20_728936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_728936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728936 prefixEnd_728936 := by exact prefixLift 728936
  have htrace : WordTrace (prefixWord ++ tailWord_728936) baseStart_728936 baseEnd_728936 := by
    simpa [prefixWord, tailWord_728936, baseEnd_728936] using wordTrace_append hprefix tailTrace_728936
  have hstable : (prefixWord ++ tailWord_728936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728936).length < 2 ^ (prefixWord ++ tailWord_728936).sum := by decide
  have hdescent : baseEnd_728936 < baseStart_728936 := by decide
  rcases family_descends (prefixWord ++ tailWord_728936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728960 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 2]
def baseStart_728960 : Nat := 118140960795 + 728960 * 2 ^ 59
def prefixEnd_728960 : Nat := 4983230072969 + 3 ^ 40 * 728960 * 2
def baseEnd_728960 : Nat := 332717207023620599420071

theorem tailTrace_728960 : CollatzResearch.WordTrace tailWord_728960 prefixEnd_728960 332717207023620599420071 := by
  unfold tailWord_728960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13293677719554945650720167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17724903626073260867626889 13293677719554945650720167)
  ·
    refine ⟨19940516579332418476080251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13293677719554945650720167 19940516579332418476080251)
    ·
      refine ⟨29910774868998627714120377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19940516579332418476080251 29910774868998627714120377)
      ·
        refine ⟨22433081151748970785590283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29910774868998627714120377 22433081151748970785590283)
        ·
          refine ⟨33649621727623456178385425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22433081151748970785590283 33649621727623456178385425)
          ·
            refine ⟨25237216295717592133789069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33649621727623456178385425 25237216295717592133789069)
            ·
              refine ⟨9463956110894097050170901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25237216295717592133789069 9463956110894097050170901)
              ·
                refine ⟨443622942698160799226761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9463956110894097050170901 443622942698160799226761)
                ·
                  refine ⟨332717207023620599420071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443622942698160799226761 332717207023620599420071)
                  ·
                    rfl

theorem cell20_728960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_728960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728960 prefixEnd_728960 := by exact prefixLift 728960
  have htrace : WordTrace (prefixWord ++ tailWord_728960) baseStart_728960 baseEnd_728960 := by
    simpa [prefixWord, tailWord_728960, baseEnd_728960] using wordTrace_append hprefix tailTrace_728960
  have hstable : (prefixWord ++ tailWord_728960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728960).length < 2 ^ (prefixWord ++ tailWord_728960).sum := by decide
  have hdescent : baseEnd_728960 < baseStart_728960 := by decide
  rcases family_descends (prefixWord ++ tailWord_728960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728981 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_728981 : Nat := 118140960795 + 728981 * 2 ^ 59
def prefixEnd_728981 : Nat := 4983230072969 + 3 ^ 40 * 728981 * 2
def baseEnd_728981 : Nat := 332726791995837859719985

theorem tailTrace_728981 : CollatzResearch.WordTrace tailWord_728981 prefixEnd_728981 332726791995837859719985 := by
  unfold tailWord_728981
  simp only [CollatzResearch.WordTrace]
  refine ⟨26588121372033811887954797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17725414248022541258636531 26588121372033811887954797)
  ·
    refine ⟨9970545514512679457983049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26588121372033811887954797 9970545514512679457983049)
    ·
      refine ⟨7477909135884509593487287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9970545514512679457983049 7477909135884509593487287)
      ·
        refine ⟨11216863703826764390230931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477909135884509593487287 11216863703826764390230931)
        ·
          refine ⟨16825295555740146585346397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216863703826764390230931 16825295555740146585346397)
          ·
            refine ⟨6309485833402554969504899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16825295555740146585346397 6309485833402554969504899)
            ·
              refine ⟨9464228750103832454257349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6309485833402554969504899 9464228750103832454257349)
              ·
                refine ⟨1774542890644468585173253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9464228750103832454257349 1774542890644468585173253)
                ·
                  refine ⟨332726791995837859719985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774542890644468585173253 332726791995837859719985)
                  ·
                    rfl

theorem cell20_728981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_728981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728981 prefixEnd_728981 := by exact prefixLift 728981
  have htrace : WordTrace (prefixWord ++ tailWord_728981) baseStart_728981 baseEnd_728981 := by
    simpa [prefixWord, tailWord_728981, baseEnd_728981] using wordTrace_append hprefix tailTrace_728981
  have hstable : (prefixWord ++ tailWord_728981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728981).length < 2 ^ (prefixWord ++ tailWord_728981).sum := by decide
  have hdescent : baseEnd_728981 < baseStart_728981 := by decide
  rcases family_descends (prefixWord ++ tailWord_728981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728984 : List Nat := [2, 1, 2, 6, 1, 1, 1, 6]
def baseStart_728984 : Nat := 118140960795 + 728984 * 2 ^ 59
def prefixEnd_728984 : Nat := 4983230072969 + 3 ^ 40 * 728984 * 2
def baseEnd_728984 : Nat := 110909387092527727539991

theorem tailTrace_728984 : CollatzResearch.WordTrace tailWord_728984 prefixEnd_728984 110909387092527727539991 := by
  unfold tailWord_728984
  simp only [CollatzResearch.WordTrace]
  refine ⟨13294115395511471700157003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17725487194015295600209337 13294115395511471700157003)
  ·
    refine ⟨19941173093267207550235505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13294115395511471700157003 19941173093267207550235505)
    ·
      refine ⟨14955879819950405662676629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19941173093267207550235505 14955879819950405662676629)
      ·
        refine ⟨701056866560175265437967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14955879819950405662676629 701056866560175265437967)
        ·
          refine ⟨1051585299840262898156951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701056866560175265437967 1051585299840262898156951)
          ·
            refine ⟨1577377949760394347235427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051585299840262898156951 1577377949760394347235427)
            ·
              refine ⟨2366066924640591520853141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577377949760394347235427 2366066924640591520853141)
              ·
                refine ⟨110909387092527727539991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2366066924640591520853141 110909387092527727539991)
                ·
                  rfl

theorem cell20_728984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_728984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728984 prefixEnd_728984 := by exact prefixLift 728984
  have htrace : WordTrace (prefixWord ++ tailWord_728984) baseStart_728984 baseEnd_728984 := by
    simpa [prefixWord, tailWord_728984, baseEnd_728984] using wordTrace_append hprefix tailTrace_728984
  have hstable : (prefixWord ++ tailWord_728984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728984).length < 2 ^ (prefixWord ++ tailWord_728984).sum := by decide
  have hdescent : baseEnd_728984 < baseStart_728984 := by decide
  rcases family_descends (prefixWord ++ tailWord_728984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_728990 : List Nat := [4, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_728990 : Nat := 118140960795 + 728990 * 2 ^ 59
def prefixEnd_728990 : Nat := 4983230072969 + 3 ^ 40 * 728990 * 2
def baseEnd_728990 : Nat := 332730899841073828419949

theorem tailTrace_728990 : CollatzResearch.WordTrace tailWord_728990 prefixEnd_728990 332730899841073828419949 := by
  unfold tailWord_728990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323556203625150803129053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17725633086000804283354949 3323556203625150803129053)
  ·
    refine ⟨1246333576359431551173395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3323556203625150803129053 1246333576359431551173395)
    ·
      refine ⟨1869500364539147326760093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1246333576359431551173395 1869500364539147326760093)
      ·
        refine ⟨701062636702180247535035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1869500364539147326760093 701062636702180247535035)
        ·
          refine ⟨1051593955053270371302553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701062636702180247535035 1051593955053270371302553)
          ·
            refine ⟨788695466289952778476915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051593955053270371302553 788695466289952778476915)
            ·
              refine ⟨1183043199434929167715373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788695466289952778476915 1183043199434929167715373)
              ·
                refine ⟨443641199788098437893265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183043199434929167715373 443641199788098437893265)
                ·
                  refine ⟨332730899841073828419949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443641199788098437893265 332730899841073828419949)
                  ·
                    rfl

theorem cell20_728990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_728990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_728990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_728990 prefixEnd_728990 := by exact prefixLift 728990
  have htrace : WordTrace (prefixWord ++ tailWord_728990) baseStart_728990 baseEnd_728990 := by
    simpa [prefixWord, tailWord_728990, baseEnd_728990] using wordTrace_append hprefix tailTrace_728990
  have hstable : (prefixWord ++ tailWord_728990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_728990).length < 2 ^ (prefixWord ++ tailWord_728990).sum := by decide
  have hdescent : baseEnd_728990 < baseStart_728990 := by decide
  rcases family_descends (prefixWord ++ tailWord_728990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729070 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_729070 : Nat := 118140960795 + 729070 * 2 ^ 59
def prefixEnd_729070 : Nat := 4983230072969 + 3 ^ 40 * 729070 * 2
def baseEnd_729070 : Nat := 332767414020949105752955

theorem tailTrace_729070 : CollatzResearch.WordTrace tailWord_729070 prefixEnd_729070 332767414020949105752955 := by
  unfold tailWord_729070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323920933588922510993083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17727578312474253391963109 3323920933588922510993083)
  ·
    refine ⟨4985881400383383766489625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323920933588922510993083 4985881400383383766489625)
    ·
      refine ⟨3739411050287537824867219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4985881400383383766489625 3739411050287537824867219)
      ·
        refine ⟨5609116575431306737300829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739411050287537824867219 5609116575431306737300829)
        ·
          refine ⟨2103418715786740026487811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5609116575431306737300829 2103418715786740026487811)
          ·
            refine ⟨3155128073680110039731717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103418715786740026487811 3155128073680110039731717)
            ·
              refine ⟨591586513815020632449697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3155128073680110039731717 591586513815020632449697)
              ·
                refine ⟨443689885361265474337273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591586513815020632449697 443689885361265474337273)
                ·
                  refine ⟨332767414020949105752955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443689885361265474337273 332767414020949105752955)
                  ·
                    rfl

theorem cell20_729070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_729070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729070 prefixEnd_729070 := by exact prefixLift 729070
  have htrace : WordTrace (prefixWord ++ tailWord_729070) baseStart_729070 baseEnd_729070 := by
    simpa [prefixWord, tailWord_729070, baseEnd_729070] using wordTrace_append hprefix tailTrace_729070
  have hstable : (prefixWord ++ tailWord_729070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729070).length < 2 ^ (prefixWord ++ tailWord_729070).sum := by decide
  have hdescent : baseEnd_729070 < baseStart_729070 := by decide
  rcases family_descends (prefixWord ++ tailWord_729070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729081 : List Nat := [1, 2, 1, 3, 1, 6, 1, 5]
def baseStart_729081 : Nat := 118140960795 + 729081 * 2 ^ 59
def prefixEnd_729081 : Nat := 4983230072969 + 3 ^ 40 * 729081 * 2
def baseEnd_729081 : Nat := 110924144906893985462081

theorem tailTrace_729081 : CollatzResearch.WordTrace tailWord_729081 prefixEnd_729081 110924144906893985462081 := by
  unfold tailWord_729081
  simp only [CollatzResearch.WordTrace]
  refine ⟨26591768671671528966595097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17727845781114352644396731 26591768671671528966595097)
  ·
    refine ⟨19943826503753646724946323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26591768671671528966595097 19943826503753646724946323)
    ·
      refine ⟨29915739755630470087419485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19943826503753646724946323 29915739755630470087419485)
      ·
        refine ⟨11218402408361426282782307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29915739755630470087419485 11218402408361426282782307)
        ·
          refine ⟨16827603612542139424173461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11218402408361426282782307 16827603612542139424173461)
          ·
            refine ⟨788793919337912785508131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16827603612542139424173461 788793919337912785508131)
            ·
              refine ⟨1183190879006869178262197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788793919337912785508131 1183190879006869178262197)
              ·
                refine ⟨110924144906893985462081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1183190879006869178262197 110924144906893985462081)
                ·
                  rfl

theorem cell20_729081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_729081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729081 prefixEnd_729081 := by exact prefixLift 729081
  have htrace : WordTrace (prefixWord ++ tailWord_729081) baseStart_729081 baseEnd_729081 := by
    simpa [prefixWord, tailWord_729081, baseEnd_729081] using wordTrace_append hprefix tailTrace_729081
  have hstable : (prefixWord ++ tailWord_729081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729081).length < 2 ^ (prefixWord ++ tailWord_729081).sum := by decide
  have hdescent : baseEnd_729081 < baseStart_729081 := by decide
  rcases family_descends (prefixWord ++ tailWord_729081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729095 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_729095 : Nat := 118140960795 + 729095 * 2 ^ 59
def prefixEnd_729095 : Nat := 4983230072969 + 3 ^ 40 * 729095 * 2
def baseEnd_729095 : Nat := 332778824702160129919519

theorem tailTrace_729095 : CollatzResearch.WordTrace tailWord_729095 prefixEnd_729095 332778824702160129919519 := by
  unfold tailWord_729095
  simp only [CollatzResearch.WordTrace]
  refine ⟨26592279293620809357604739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17728186195747206238403159 26592279293620809357604739)
  ·
    refine ⟨39888418940431214036407109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26592279293620809357604739 39888418940431214036407109)
    ·
      refine ⟨7479078551330852631826333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39888418940431214036407109 7479078551330852631826333)
      ·
        refine ⟨2804654456749069736934875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7479078551330852631826333 2804654456749069736934875)
        ·
          refine ⟨4206981685123604605402313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2804654456749069736934875 4206981685123604605402313)
          ·
            refine ⟨3155236263842703454051735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4206981685123604605402313 3155236263842703454051735)
            ·
              refine ⟨4732854395764055181077603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155236263842703454051735 4732854395764055181077603)
              ·
                refine ⟨7099281593646082771616405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732854395764055181077603 7099281593646082771616405)
                ·
                  refine ⟨332778824702160129919519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7099281593646082771616405 332778824702160129919519)
                  ·
                    rfl

theorem cell20_729095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_729095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729095 prefixEnd_729095 := by exact prefixLift 729095
  have htrace : WordTrace (prefixWord ++ tailWord_729095) baseStart_729095 baseEnd_729095 := by
    simpa [prefixWord, tailWord_729095, baseEnd_729095] using wordTrace_append hprefix tailTrace_729095
  have hstable : (prefixWord ++ tailWord_729095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729095).length < 2 ^ (prefixWord ++ tailWord_729095).sum := by decide
  have hdescent : baseEnd_729095 < baseStart_729095 := by decide
  rcases family_descends (prefixWord ++ tailWord_729095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729098 : List Nat := [3, 1, 2, 2, 4, 1, 3, 4]
def baseStart_729098 : Nat := 118140960795 + 729098 * 2 ^ 59
def prefixEnd_729098 : Nat := 4983230072969 + 3 ^ 40 * 729098 * 2
def baseEnd_729098 : Nat := 110926731327968484273169

theorem tailTrace_729098 : CollatzResearch.WordTrace tailWord_729098 prefixEnd_729098 110926731327968484273169 := by
  unfold tailWord_729098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6648097178152485217490987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17728259141739960579975965 6648097178152485217490987)
  ·
    refine ⟨9972145767228727826236481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6648097178152485217490987 9972145767228727826236481)
    ·
      refine ⟨7479109325421545869677361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9972145767228727826236481 7479109325421545869677361)
      ·
        refine ⟨5609331994066159402258021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7479109325421545869677361 5609331994066159402258021)
        ·
          refine ⟨1051749748887404887923379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5609331994066159402258021 1051749748887404887923379)
          ·
            refine ⟨1577624623331107331885069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051749748887404887923379 1577624623331107331885069)
            ·
              refine ⟨591609233749165249456901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1577624623331107331885069 591609233749165249456901)
              ·
                refine ⟨110926731327968484273169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591609233749165249456901 110926731327968484273169)
                ·
                  rfl

theorem cell20_729098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_729098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729098 prefixEnd_729098 := by exact prefixLift 729098
  have htrace : WordTrace (prefixWord ++ tailWord_729098) baseStart_729098 baseEnd_729098 := by
    simpa [prefixWord, tailWord_729098, baseEnd_729098] using wordTrace_append hprefix tailTrace_729098
  have hstable : (prefixWord ++ tailWord_729098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729098).length < 2 ^ (prefixWord ++ tailWord_729098).sum := by decide
  have hdescent : baseEnd_729098 < baseStart_729098 := by decide
  rcases family_descends (prefixWord ++ tailWord_729098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729174 : List Nat := [5, 2, 2, 1, 1, 1, 8]
def baseStart_729174 : Nat := 118140960795 + 729174 * 2 ^ 59
def prefixEnd_729174 : Nat := 4983230072969 + 3 ^ 40 * 729174 * 2
def baseEnd_729174 : Nat := 36979431383865218476207

theorem tailTrace_729174 : CollatzResearch.WordTrace tailWord_729174 prefixEnd_729174 36979431383865218476207 := by
  unfold tailWord_729174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662197541270912865608161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17730107106889737233153717 1662197541270912865608161)
  ·
    refine ⟨1246648155953184649206121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1662197541270912865608161 1246648155953184649206121)
    ·
      refine ⟨934986116964888486904591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1246648155953184649206121 934986116964888486904591)
      ·
        refine ⟨1402479175447332730356887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934986116964888486904591 1402479175447332730356887)
        ·
          refine ⟨2103718763170999095535331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402479175447332730356887 2103718763170999095535331)
          ·
            refine ⟨3155578144756498643302997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103718763170999095535331 3155578144756498643302997)
            ·
              refine ⟨36979431383865218476207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3155578144756498643302997 36979431383865218476207)
              ·
                rfl

theorem cell20_729174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 8].length) (baseStart_729174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729174 prefixEnd_729174 := by exact prefixLift 729174
  have htrace : WordTrace (prefixWord ++ tailWord_729174) baseStart_729174 baseEnd_729174 := by
    simpa [prefixWord, tailWord_729174, baseEnd_729174] using wordTrace_append hprefix tailTrace_729174
  have hstable : (prefixWord ++ tailWord_729174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729174).length < 2 ^ (prefixWord ++ tailWord_729174).sum := by decide
  have hdescent : baseEnd_729174 < baseStart_729174 := by decide
  rcases family_descends (prefixWord ++ tailWord_729174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729181 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 5]
def baseStart_729181 : Nat := 118140960795 + 729181 * 2 ^ 59
def prefixEnd_729181 : Nat := 4983230072969 + 3 ^ 40 * 729181 * 2
def baseEnd_729181 : Nat := 332818077445526053052501

theorem tailTrace_729181 : CollatzResearch.WordTrace tailWord_729181 prefixEnd_729181 332818077445526053052501 := by
  unfold tailWord_729181
  simp only [CollatzResearch.WordTrace]
  refine ⟨26595415971309246045235397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17730277314206164030156931 26595415971309246045235397)
  ·
    refine ⟨4986640494620483633481637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26595415971309246045235397 4986640494620483633481637)
    ·
      refine ⟨934995092741340681277807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4986640494620483633481637 934995092741340681277807)
      ·
        refine ⟨1402492639112011021916711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934995092741340681277807 1402492639112011021916711)
        ·
          refine ⟨2103738958668016532875067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402492639112011021916711 2103738958668016532875067)
          ·
            refine ⟨3155608438002024799312601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103738958668016532875067 3155608438002024799312601)
            ·
              refine ⟨2366706328501518599484451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155608438002024799312601 2366706328501518599484451)
              ·
                refine ⟨3550059492752277899226677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366706328501518599484451 3550059492752277899226677)
                ·
                  refine ⟨332818077445526053052501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550059492752277899226677 332818077445526053052501)
                  ·
                    rfl

theorem cell20_729181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_729181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729181 prefixEnd_729181 := by exact prefixLift 729181
  have htrace : WordTrace (prefixWord ++ tailWord_729181) baseStart_729181 baseEnd_729181 := by
    simpa [prefixWord, tailWord_729181, baseEnd_729181] using wordTrace_append hprefix tailTrace_729181
  have hstable : (prefixWord ++ tailWord_729181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729181).length < 2 ^ (prefixWord ++ tailWord_729181).sum := by decide
  have hdescent : baseEnd_729181 < baseStart_729181 := by decide
  rcases family_descends (prefixWord ++ tailWord_729181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729188 : List Nat := [2, 3, 1, 1, 2, 1, 2, 6, 2]
def baseStart_729188 : Nat := 118140960795 + 729188 * 2 ^ 59
def prefixEnd_729188 : Nat := 4983230072969 + 3 ^ 40 * 729188 * 2
def baseEnd_729188 : Nat := 332821272436265139819139

theorem tailTrace_729188 : CollatzResearch.WordTrace tailWord_729188 prefixEnd_729188 332821272436265139819139 := by
  unfold tailWord_729188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13297835641141943120370109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17730447521522590827160145 13297835641141943120370109)
  ·
    refine ⟨4986688365428228670138791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13297835641141943120370109 4986688365428228670138791)
    ·
      refine ⟨7480032548142343005208187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4986688365428228670138791 7480032548142343005208187)
      ·
        refine ⟨11220048822213514507812281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7480032548142343005208187 11220048822213514507812281)
        ·
          refine ⟨8415036616660135880859211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11220048822213514507812281 8415036616660135880859211)
          ·
            refine ⟨12622554924990203821288817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415036616660135880859211 12622554924990203821288817)
            ·
              refine ⟨9466916193742652865966613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12622554924990203821288817 9466916193742652865966613)
              ·
                refine ⟨443761696581686853092185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9466916193742652865966613 443761696581686853092185)
                ·
                  refine ⟨332821272436265139819139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443761696581686853092185 332821272436265139819139)
                  ·
                    rfl

theorem cell20_729188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_729188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729188 prefixEnd_729188 := by exact prefixLift 729188
  have htrace : WordTrace (prefixWord ++ tailWord_729188) baseStart_729188 baseEnd_729188 := by
    simpa [prefixWord, tailWord_729188, baseEnd_729188] using wordTrace_append hprefix tailTrace_729188
  have hstable : (prefixWord ++ tailWord_729188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729188).length < 2 ^ (prefixWord ++ tailWord_729188).sum := by decide
  have hdescent : baseEnd_729188 < baseStart_729188 := by decide
  rcases family_descends (prefixWord ++ tailWord_729188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729223 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 7]
def baseStart_729223 : Nat := 118140960795 + 729223 * 2 ^ 59
def prefixEnd_729223 : Nat := 4983230072969 + 3 ^ 40 * 729223 * 2
def baseEnd_729223 : Nat := 332837247389960573652329

theorem tailTrace_729223 : CollatzResearch.WordTrace tailWord_729223 prefixEnd_729223 332837247389960573652329 := by
  unfold tailWord_729223
  simp only [CollatzResearch.WordTrace]
  refine ⟨26596947837157087218264323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17731298558104724812176215 26596947837157087218264323)
  ·
    refine ⟨39895421755735630827396485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26596947837157087218264323 39895421755735630827396485)
    ·
      refine ⟨7480391579200430780136841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39895421755735630827396485 7480391579200430780136841)
      ·
        refine ⟨5610293684400323085102631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7480391579200430780136841 5610293684400323085102631)
        ·
          refine ⟨8415440526600484627653947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610293684400323085102631 8415440526600484627653947)
          ·
            refine ⟨12623160789900726941480921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415440526600484627653947 12623160789900726941480921)
            ·
              refine ⟨9467370592425545206110691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12623160789900726941480921 9467370592425545206110691)
              ·
                refine ⟨14201055888638317809166037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9467370592425545206110691 14201055888638317809166037)
                ·
                  refine ⟨332837247389960573652329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14201055888638317809166037 332837247389960573652329)
                  ·
                    rfl

theorem cell20_729223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_729223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729223 prefixEnd_729223 := by exact prefixLift 729223
  have htrace : WordTrace (prefixWord ++ tailWord_729223) baseStart_729223 baseEnd_729223 := by
    simpa [prefixWord, tailWord_729223, baseEnd_729223] using wordTrace_append hprefix tailTrace_729223
  have hstable : (prefixWord ++ tailWord_729223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729223).length < 2 ^ (prefixWord ++ tailWord_729223).sum := by decide
  have hdescent : baseEnd_729223 < baseStart_729223 := by decide
  rcases family_descends (prefixWord ++ tailWord_729223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729239 : List Nat := [1, 1, 3, 3, 5, 1, 2, 2, 2]
def baseStart_729239 : Nat := 118140960795 + 729239 * 2 ^ 59
def prefixEnd_729239 : Nat := 4983230072969 + 3 ^ 40 * 729239 * 2
def baseEnd_729239 : Nat := 332844550225935629118931

theorem tailTrace_729239 : CollatzResearch.WordTrace tailWord_729239 prefixEnd_729239 332844550225935629118931 := by
  unfold tailWord_729239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26597531405099121950846771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17731687603399414633897847 26597531405099121950846771)
  ·
    refine ⟨39896297107648682926270157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26597531405099121950846771 39896297107648682926270157)
    ·
      refine ⟨14961111415368256097351309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39896297107648682926270157 14961111415368256097351309)
      ·
        refine ⟨5610416780763096036506741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14961111415368256097351309 5610416780763096036506741)
        ·
          refine ⟨525976573196540253422507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5610416780763096036506741 525976573196540253422507)
          ·
            refine ⟨788964859794810380133761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525976573196540253422507 788964859794810380133761)
            ·
              refine ⟨591723644846107785100321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788964859794810380133761 591723644846107785100321)
              ·
                refine ⟨443792733634580838825241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591723644846107785100321 443792733634580838825241)
                ·
                  refine ⟨332844550225935629118931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443792733634580838825241 332844550225935629118931)
                  ·
                    rfl

theorem cell20_729239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 2].length) (baseStart_729239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729239 prefixEnd_729239 := by exact prefixLift 729239
  have htrace : WordTrace (prefixWord ++ tailWord_729239) baseStart_729239 baseEnd_729239 := by
    simpa [prefixWord, tailWord_729239, baseEnd_729239] using wordTrace_append hprefix tailTrace_729239
  have hstable : (prefixWord ++ tailWord_729239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729239).length < 2 ^ (prefixWord ++ tailWord_729239).sum := by decide
  have hdescent : baseEnd_729239 < baseStart_729239 := by decide
  rcases family_descends (prefixWord ++ tailWord_729239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729250 : List Nat := [3, 3, 1, 3, 1, 3, 1, 5]
def baseStart_729250 : Nat := 118140960795 + 729250 * 2 ^ 59
def prefixEnd_729250 : Nat := 4983230072969 + 3 ^ 40 * 729250 * 2
def baseEnd_729250 : Nat := 110949856975222826584073

theorem tailTrace_729250 : CollatzResearch.WordTrace tailWord_729250 prefixEnd_729250 110949856975222826584073 := by
  unfold tailWord_729250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649483152014817707374301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17731955072039513886331469 6649483152014817707374301)
  ·
    refine ⟨2493556182005556640265363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6649483152014817707374301 2493556182005556640265363)
    ·
      refine ⟨3740334273008334960398045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493556182005556640265363 3740334273008334960398045)
      ·
        refine ⟨1402625352378125610149267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3740334273008334960398045 1402625352378125610149267)
        ·
          refine ⟨2103938028567188415223901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402625352378125610149267 2103938028567188415223901)
          ·
            refine ⟨788976760712695655708963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2103938028567188415223901 788976760712695655708963)
            ·
              refine ⟨1183465141069043483563445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788976760712695655708963 1183465141069043483563445)
              ·
                refine ⟨110949856975222826584073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1183465141069043483563445 110949856975222826584073)
                ·
                  rfl

theorem cell20_729250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_729250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729250 prefixEnd_729250 := by exact prefixLift 729250
  have htrace : WordTrace (prefixWord ++ tailWord_729250) baseStart_729250 baseEnd_729250 := by
    simpa [prefixWord, tailWord_729250, baseEnd_729250] using wordTrace_append hprefix tailTrace_729250
  have hstable : (prefixWord ++ tailWord_729250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729250).length < 2 ^ (prefixWord ++ tailWord_729250).sum := by decide
  have hdescent : baseEnd_729250 < baseStart_729250 := by decide
  rcases family_descends (prefixWord ++ tailWord_729250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729271 : List Nat := [1, 1, 3, 1, 4, 3, 3, 4]
def baseStart_729271 : Nat := 118140960795 + 729271 * 2 ^ 59
def prefixEnd_729271 : Nat := 4983230072969 + 3 ^ 40 * 729271 * 2
def baseEnd_729271 : Nat := 110953051965961913350711

theorem tailTrace_729271 : CollatzResearch.WordTrace tailWord_729271 prefixEnd_729271 110953051965961913350711 := by
  unfold tailWord_729271
  simp only [CollatzResearch.WordTrace]
  refine ⟨26598698540983191416011667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17732465693988794277341111 26598698540983191416011667)
  ·
    refine ⟨39898047811474787124017501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26598698540983191416011667 39898047811474787124017501)
    ·
      refine ⟨14961767929303045171506563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39898047811474787124017501 14961767929303045171506563)
      ·
        refine ⟨22442651893954567757259845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14961767929303045171506563 22442651893954567757259845)
        ·
          refine ⟨4207997230116481454486221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22442651893954567757259845 4207997230116481454486221)
          ·
            refine ⟨1577998961293680545432333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4207997230116481454486221 1577998961293680545432333)
            ·
              refine ⟨591749610485130204537125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1577998961293680545432333 591749610485130204537125)
              ·
                refine ⟨110953051965961913350711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 591749610485130204537125 110953051965961913350711)
                ·
                  rfl

theorem cell20_729271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_729271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729271 prefixEnd_729271 := by exact prefixLift 729271
  have htrace : WordTrace (prefixWord ++ tailWord_729271) baseStart_729271 baseEnd_729271 := by
    simpa [prefixWord, tailWord_729271, baseEnd_729271] using wordTrace_append hprefix tailTrace_729271
  have hstable : (prefixWord ++ tailWord_729271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729271).length < 2 ^ (prefixWord ++ tailWord_729271).sum := by decide
  have hdescent : baseEnd_729271 < baseStart_729271 := by decide
  rcases family_descends (prefixWord ++ tailWord_729271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729344 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_729344 : Nat := 118140960795 + 729344 * 2 ^ 59
def prefixEnd_729344 : Nat := 4983230072969 + 3 ^ 40 * 729344 * 2
def baseEnd_729344 : Nat := 332892475087021930618501

theorem tailTrace_729344 : CollatzResearch.WordTrace tailWord_729344 prefixEnd_729344 332892475087021930618501 := by
  unfold tailWord_729344
  simp only [CollatzResearch.WordTrace]
  refine ⟨13300680534859362441709543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17734240713145816588946057 13300680534859362441709543)
  ·
    refine ⟨19951020802289043662564315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13300680534859362441709543 19951020802289043662564315)
    ·
      refine ⟨29926531203433565493846473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19951020802289043662564315 29926531203433565493846473)
      ·
        refine ⟨22444898402575174120384855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29926531203433565493846473 22444898402575174120384855)
        ·
          refine ⟨33667347603862761180577283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22444898402575174120384855 33667347603862761180577283)
          ·
            refine ⟨50501021405794141770865925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33667347603862761180577283 50501021405794141770865925)
            ·
              refine ⟨9468941513586401582037361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50501021405794141770865925 9468941513586401582037361)
              ·
                refine ⟨7101706135189801186528021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9468941513586401582037361 7101706135189801186528021)
                ·
                  refine ⟨332892475087021930618501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7101706135189801186528021 332892475087021930618501)
                  ·
                    rfl

theorem cell20_729344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_729344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729344 prefixEnd_729344 := by exact prefixLift 729344
  have htrace : WordTrace (prefixWord ++ tailWord_729344) baseStart_729344 baseEnd_729344 := by
    simpa [prefixWord, tailWord_729344, baseEnd_729344] using wordTrace_append hprefix tailTrace_729344
  have hstable : (prefixWord ++ tailWord_729344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729344).length < 2 ^ (prefixWord ++ tailWord_729344).sum := by decide
  have hdescent : baseEnd_729344 < baseStart_729344 := by decide
  rcases family_descends (prefixWord ++ tailWord_729344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729361 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_729361 : Nat := 118140960795 + 729361 * 2 ^ 59
def prefixEnd_729361 : Nat := 4983230072969 + 3 ^ 40 * 729361 * 2
def baseEnd_729361 : Nat := 332900234350245427051765

theorem tailTrace_729361 : CollatzResearch.WordTrace tailWord_729361 prefixEnd_729361 332900234350245427051765 := by
  unfold tailWord_729361
  simp only [CollatzResearch.WordTrace]
  refine ⟨26601981110657136786787937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17734654073771424524525291 26601981110657136786787937)
  ·
    refine ⟨19951485832992852590090953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26601981110657136786787937 19951485832992852590090953)
    ·
      refine ⟨14963614374744639442568215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19951485832992852590090953 14963614374744639442568215)
      ·
        refine ⟨22445421562116959163852323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963614374744639442568215 22445421562116959163852323)
        ·
          refine ⟨33668132343175438745778485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22445421562116959163852323 33668132343175438745778485)
          ·
            refine ⟨3156387407172697382416733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33668132343175438745778485 3156387407172697382416733)
            ·
              refine ⟨1183645277689761518406275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3156387407172697382416733 1183645277689761518406275)
              ·
                refine ⟨1775467916534642277609413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183645277689761518406275 1775467916534642277609413)
                ·
                  refine ⟨332900234350245427051765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775467916534642277609413 332900234350245427051765)
                  ·
                    rfl

theorem cell20_729361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_729361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729361 prefixEnd_729361 := by exact prefixLift 729361
  have htrace : WordTrace (prefixWord ++ tailWord_729361) baseStart_729361 baseEnd_729361 := by
    simpa [prefixWord, tailWord_729361, baseEnd_729361] using wordTrace_append hprefix tailTrace_729361
  have hstable : (prefixWord ++ tailWord_729361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729361).length < 2 ^ (prefixWord ++ tailWord_729361).sum := by decide
  have hdescent : baseEnd_729361 < baseStart_729361 := by decide
  rcases family_descends (prefixWord ++ tailWord_729361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729368 : List Nat := [2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_729368 : Nat := 118140960795 + 729368 * 2 ^ 59
def prefixEnd_729368 : Nat := 4983230072969 + 3 ^ 40 * 729368 * 2
def baseEnd_729368 : Nat := 110967809780328171272801

theorem tailTrace_729368 : CollatzResearch.WordTrace tailWord_729368 prefixEnd_729368 110967809780328171272801 := by
  unfold tailWord_729368
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301118210815888491146379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17734824281087851321528505 13301118210815888491146379)
  ·
    refine ⟨19951677316223832736719569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13301118210815888491146379 19951677316223832736719569)
    ·
      refine ⟨14963757987167874552539677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19951677316223832736719569 14963757987167874552539677)
      ·
        refine ⟨5611409245187952957202379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14963757987167874552539677 5611409245187952957202379)
        ·
          refine ⟨8417113867781929435803569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611409245187952957202379 8417113867781929435803569)
          ·
            refine ⟨6312835400836447076852677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8417113867781929435803569 6312835400836447076852677)
            ·
              refine ⟨1183656637656833826909877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6312835400836447076852677 1183656637656833826909877)
              ·
                refine ⟨110967809780328171272801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1183656637656833826909877 110967809780328171272801)
                ·
                  rfl

theorem cell20_729368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_729368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729368 prefixEnd_729368 := by exact prefixLift 729368
  have htrace : WordTrace (prefixWord ++ tailWord_729368) baseStart_729368 baseEnd_729368 := by
    simpa [prefixWord, tailWord_729368, baseEnd_729368] using wordTrace_append hprefix tailTrace_729368
  have hstable : (prefixWord ++ tailWord_729368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729368).length < 2 ^ (prefixWord ++ tailWord_729368).sum := by decide
  have hdescent : baseEnd_729368 < baseStart_729368 := by decide
  rcases family_descends (prefixWord ++ tailWord_729368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729406 : List Nat := [4, 2, 1, 2, 1, 10]
def baseStart_729406 : Nat := 118140960795 + 729406 * 2 ^ 59
def prefixEnd_729406 : Nat := 4983230072969 + 3 ^ 40 * 729406 * 2
def baseEnd_729406 : Nat := 12330399021349084094503

theorem tailTrace_729406 : CollatzResearch.WordTrace tailWord_729406 prefixEnd_729406 12330399021349084094503 := by
  unfold tailWord_729406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3325452799436763684022009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17735748263662739648117381 3325452799436763684022009)
  ·
    refine ⟨2494089599577572763016507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3325452799436763684022009 2494089599577572763016507)
    ·
      refine ⟨3741134399366359144524761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494089599577572763016507 3741134399366359144524761)
      ·
        refine ⟨2805850799524769358393571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3741134399366359144524761 2805850799524769358393571)
        ·
          refine ⟨4208776199287154037590357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805850799524769358393571 4208776199287154037590357)
          ·
            refine ⟨12330399021349084094503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4208776199287154037590357 12330399021349084094503)
            ·
              rfl

theorem cell20_729406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 10].length) (baseStart_729406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729406 prefixEnd_729406 := by exact prefixLift 729406
  have htrace : WordTrace (prefixWord ++ tailWord_729406) baseStart_729406 baseEnd_729406 := by
    simpa [prefixWord, tailWord_729406, baseEnd_729406] using wordTrace_append hprefix tailTrace_729406
  have hstable : (prefixWord ++ tailWord_729406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729406).length < 2 ^ (prefixWord ++ tailWord_729406).sum := by decide
  have hdescent : baseEnd_729406 < baseStart_729406 := by decide
  rcases family_descends (prefixWord ++ tailWord_729406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729412 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 2]
def baseStart_729412 : Nat := 118140960795 + 729412 * 2 ^ 59
def prefixEnd_729412 : Nat := 4983230072969 + 3 ^ 40 * 729412 * 2
def baseEnd_729412 : Nat := 332923512139915916351557

theorem tailTrace_729412 : CollatzResearch.WordTrace tailWord_729412 prefixEnd_729412 332923512139915916351557 := by
  unfold tailWord_729412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301920616736186248447245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17735894155648248331262993 13301920616736186248447245)
  ·
    refine ⟨4988220231276069843167717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13301920616736186248447245 4988220231276069843167717)
    ·
      refine ⟨935291293364263095593947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4988220231276069843167717 935291293364263095593947)
      ·
        refine ⟨1402936940046394643390921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935291293364263095593947 1402936940046394643390921)
        ·
          refine ⟨1052202705034795982543191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402936940046394643390921 1052202705034795982543191)
          ·
            refine ⟨1578304057552193973814787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052202705034795982543191 1578304057552193973814787)
            ·
              refine ⟨2367456086328290960722181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578304057552193973814787 2367456086328290960722181)
              ·
                refine ⟨443898016186554555135409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2367456086328290960722181 443898016186554555135409)
                ·
                  refine ⟨332923512139915916351557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443898016186554555135409 332923512139915916351557)
                  ·
                    rfl

theorem cell20_729412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_729412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729412 prefixEnd_729412 := by exact prefixLift 729412
  have htrace : WordTrace (prefixWord ++ tailWord_729412) baseStart_729412 baseEnd_729412 := by
    simpa [prefixWord, tailWord_729412, baseEnd_729412] using wordTrace_append hprefix tailTrace_729412
  have hstable : (prefixWord ++ tailWord_729412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729412).length < 2 ^ (prefixWord ++ tailWord_729412).sum := by decide
  have hdescent : baseEnd_729412 < baseStart_729412 := by decide
  rcases family_descends (prefixWord ++ tailWord_729412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729427 : List Nat := [1, 1, 1, 2, 1, 1, 4, 9]
def baseStart_729427 : Nat := 118140960795 + 729427 * 2 ^ 59
def prefixEnd_729427 : Nat := 4983230072969 + 3 ^ 40 * 729427 * 2
def baseEnd_729427 : Nat := 110976786182880843617165

theorem tailTrace_729427 : CollatzResearch.WordTrace tailWord_729427 prefixEnd_729427 110976786182880843617165 := by
  unfold tailWord_729427
  simp only [CollatzResearch.WordTrace]
  refine ⟨26604388328418030058690535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17736258885612020039127023 26604388328418030058690535)
  ·
    refine ⟨39906582492627045088035803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26604388328418030058690535 39906582492627045088035803)
    ·
      refine ⟨59859873738940567632053705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39906582492627045088035803 59859873738940567632053705)
      ·
        refine ⟨44894905304205425724040279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59859873738940567632053705 44894905304205425724040279)
        ·
          refine ⟨67342357956308138586060419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44894905304205425724040279 67342357956308138586060419)
          ·
            refine ⟨101013536934462207879090629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67342357956308138586060419 101013536934462207879090629)
            ·
              refine ⟨18940038175211663977329493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101013536934462207879090629 18940038175211663977329493)
              ·
                refine ⟨110976786182880843617165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18940038175211663977329493 110976786182880843617165)
                ·
                  rfl

theorem cell20_729427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 9].length) (baseStart_729427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729427 prefixEnd_729427 := by exact prefixLift 729427
  have htrace : WordTrace (prefixWord ++ tailWord_729427) baseStart_729427 baseEnd_729427 := by
    simpa [prefixWord, tailWord_729427, baseEnd_729427] using wordTrace_append hprefix tailTrace_729427
  have hstable : (prefixWord ++ tailWord_729427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729427).length < 2 ^ (prefixWord ++ tailWord_729427).sum := by decide
  have hdescent : baseEnd_729427 < baseStart_729427 := by decide
  rcases family_descends (prefixWord ++ tailWord_729427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729505 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 2]
def baseStart_729505 : Nat := 118140960795 + 729505 * 2 ^ 59
def prefixEnd_729505 : Nat := 4983230072969 + 3 ^ 40 * 729505 * 2
def baseEnd_729505 : Nat := 332965959874020926251177

theorem tailTrace_729505 : CollatzResearch.WordTrace tailWord_729505 prefixEnd_729505 332965959874020926251177 := by
  unfold tailWord_729505
  simp only [CollatzResearch.WordTrace]
  refine ⟨26607233222135449380029969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17738155481423632920019979 26607233222135449380029969)
  ·
    refine ⟨19955424916601587035022477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26607233222135449380029969 19955424916601587035022477)
    ·
      refine ⟨7483284343725595138133429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19955424916601587035022477 7483284343725595138133429)
      ·
        refine ⟨701557907224274544200009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7483284343725595138133429 701557907224274544200009)
        ·
          refine ⟨526168430418205908150007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701557907224274544200009 526168430418205908150007)
          ·
            refine ⟨789252645627308862225011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526168430418205908150007 789252645627308862225011)
            ·
              refine ⟨1183878968440963293337517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789252645627308862225011 1183878968440963293337517)
              ·
                refine ⟨443954613165361235001569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183878968440963293337517 443954613165361235001569)
                ·
                  refine ⟨332965959874020926251177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443954613165361235001569 332965959874020926251177)
                  ·
                    rfl

theorem cell20_729505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_729505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729505 prefixEnd_729505 := by exact prefixLift 729505
  have htrace : WordTrace (prefixWord ++ tailWord_729505) baseStart_729505 baseEnd_729505 := by
    simpa [prefixWord, tailWord_729505, baseEnd_729505] using wordTrace_append hprefix tailTrace_729505
  have hstable : (prefixWord ++ tailWord_729505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729505).length < 2 ^ (prefixWord ++ tailWord_729505).sum := by decide
  have hdescent : baseEnd_729505 < baseStart_729505 := by decide
  rcases family_descends (prefixWord ++ tailWord_729505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729527 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_729527 : Nat := 118140960795 + 729527 * 2 ^ 59
def prefixEnd_729527 : Nat := 4983230072969 + 3 ^ 40 * 729527 * 2
def baseEnd_729527 : Nat := 332976001273486627517753

theorem tailTrace_729527 : CollatzResearch.WordTrace tailWord_729527 prefixEnd_729527 332976001273486627517753 := by
  unfold tailWord_729527
  simp only [CollatzResearch.WordTrace]
  refine ⟨26608035628055747137330835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17738690418703831424887223 26608035628055747137330835)
  ·
    refine ⟨39912053442083620705996253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26608035628055747137330835 39912053442083620705996253)
    ·
      refine ⟨14967020040781357764748595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39912053442083620705996253 14967020040781357764748595)
      ·
        refine ⟨22450530061172036647122893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14967020040781357764748595 22450530061172036647122893)
        ·
          refine ⟨8418948772939513742671085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22450530061172036647122893 8418948772939513742671085)
          ·
            refine ⟨3157105789852317653501657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8418948772939513742671085 3157105789852317653501657)
            ·
              refine ⟨2367829342389238240126243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157105789852317653501657 2367829342389238240126243)
              ·
                refine ⟨3551744013583857360189365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367829342389238240126243 3551744013583857360189365)
                ·
                  refine ⟨332976001273486627517753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3551744013583857360189365 332976001273486627517753)
                  ·
                    rfl

theorem cell20_729527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_729527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729527 prefixEnd_729527 := by exact prefixLift 729527
  have htrace : WordTrace (prefixWord ++ tailWord_729527) baseStart_729527 baseEnd_729527 := by
    simpa [prefixWord, tailWord_729527, baseEnd_729527] using wordTrace_append hprefix tailTrace_729527
  have hstable : (prefixWord ++ tailWord_729527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729527).length < 2 ^ (prefixWord ++ tailWord_729527).sum := by decide
  have hdescent : baseEnd_729527 < baseStart_729527 := by decide
  rcases family_descends (prefixWord ++ tailWord_729527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729544 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 3]
def baseStart_729544 : Nat := 118140960795 + 729544 * 2 ^ 59
def prefixEnd_729544 : Nat := 4983230072969 + 3 ^ 40 * 729544 * 2
def baseEnd_729544 : Nat := 332983760536710123951017

theorem tailTrace_729544 : CollatzResearch.WordTrace tailWord_729544 prefixEnd_729544 332983760536710123951017 := by
  unfold tailWord_729544
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304327834497079520349843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17739103779329439360466457 13304327834497079520349843)
  ·
    refine ⟨19956491751745619280524765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13304327834497079520349843 19956491751745619280524765)
    ·
      refine ⟨7483684406904607230196787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19956491751745619280524765 7483684406904607230196787)
      ·
        refine ⟨11225526610356910845295181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7483684406904607230196787 11225526610356910845295181)
        ·
          refine ⟨4209572478883841566985693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11225526610356910845295181 4209572478883841566985693)
          ·
            refine ⟨1578589679581440587619635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4209572478883841566985693 1578589679581440587619635)
            ·
              refine ⟨2367884519372160881429453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578589679581440587619635 2367884519372160881429453)
              ·
                refine ⟨887956694764560330536045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2367884519372160881429453 887956694764560330536045)
                ·
                  refine ⟨332983760536710123951017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887956694764560330536045 332983760536710123951017)
                  ·
                    rfl

theorem cell20_729544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_729544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729544 prefixEnd_729544 := by exact prefixLift 729544
  have htrace : WordTrace (prefixWord ++ tailWord_729544) baseStart_729544 baseEnd_729544 := by
    simpa [prefixWord, tailWord_729544, baseEnd_729544] using wordTrace_append hprefix tailTrace_729544
  have hstable : (prefixWord ++ tailWord_729544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729544).length < 2 ^ (prefixWord ++ tailWord_729544).sum := by decide
  have hdescent : baseEnd_729544 < baseStart_729544 := by decide
  rcases family_descends (prefixWord ++ tailWord_729544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729582 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_729582 : Nat := 118140960795 + 729582 * 2 ^ 59
def prefixEnd_729582 : Nat := 4983230072969 + 3 ^ 40 * 729582 * 2
def baseEnd_729582 : Nat := 333001104772150880684195

theorem tailTrace_729582 : CollatzResearch.WordTrace tailWord_729582 prefixEnd_729582 333001104772150880684195 := by
  unfold tailWord_729582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326255205357061441322875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17740027761904327687055333 3326255205357061441322875)
  ·
    refine ⟨4989382808035592161984313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3326255205357061441322875 4989382808035592161984313)
    ·
      refine ⟨3742037106026694121488235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4989382808035592161984313 3742037106026694121488235)
      ·
        refine ⟨5613055659040041182232353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742037106026694121488235 5613055659040041182232353)
        ·
          refine ⟨4209791744280030886674265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5613055659040041182232353 4209791744280030886674265)
          ·
            refine ⟨3157343808210023165005699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4209791744280030886674265 3157343808210023165005699)
            ·
              refine ⟨4736015712315034747508549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157343808210023165005699 4736015712315034747508549)
              ·
                refine ⟨888002946059069015157853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4736015712315034747508549 888002946059069015157853)
                ·
                  refine ⟨333001104772150880684195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888002946059069015157853 333001104772150880684195)
                  ·
                    rfl

theorem cell20_729582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_729582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729582 prefixEnd_729582 := by exact prefixLift 729582
  have htrace : WordTrace (prefixWord ++ tailWord_729582) baseStart_729582 baseEnd_729582 := by
    simpa [prefixWord, tailWord_729582, baseEnd_729582] using wordTrace_append hprefix tailTrace_729582
  have hstable : (prefixWord ++ tailWord_729582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729582).length < 2 ^ (prefixWord ++ tailWord_729582).sum := by decide
  have hdescent : baseEnd_729582 < baseStart_729582 := by decide
  rcases family_descends (prefixWord ++ tailWord_729582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729603 : List Nat := [1, 1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_729603 : Nat := 118140960795 + 729603 * 2 ^ 59
def prefixEnd_729603 : Nat := 4983230072969 + 3 ^ 40 * 729603 * 2
def baseEnd_729603 : Nat := 333010689744368140984109

theorem tailTrace_729603 : CollatzResearch.WordTrace tailWord_729603 prefixEnd_729603 333010689744368140984109 := by
  unfold tailWord_729603
  simp only [CollatzResearch.WordTrace]
  refine ⟨26610807575780412117097463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17740538383853608078064975 26610807575780412117097463)
  ·
    refine ⟨39916211363670618175646195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26610807575780412117097463 39916211363670618175646195)
    ·
      refine ⟨59874317045505927263469293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39916211363670618175646195 59874317045505927263469293)
      ·
        refine ⟨22452868892064722723800985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59874317045505927263469293 22452868892064722723800985)
        ·
          refine ⟨16839651669048542042850739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22452868892064722723800985 16839651669048542042850739)
          ·
            refine ⟨25259477503572813064276109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16839651669048542042850739 25259477503572813064276109)
            ·
              refine ⟨9472304063839804899103541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25259477503572813064276109 9472304063839804899103541)
              ·
                refine ⟨888028505984981709290957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9472304063839804899103541 888028505984981709290957)
                ·
                  refine ⟨333010689744368140984109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888028505984981709290957 333010689744368140984109)
                  ·
                    rfl

theorem cell20_729603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_729603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729603 prefixEnd_729603 := by exact prefixLift 729603
  have htrace : WordTrace (prefixWord ++ tailWord_729603) baseStart_729603 baseEnd_729603 := by
    simpa [prefixWord, tailWord_729603, baseEnd_729603] using wordTrace_append hprefix tailTrace_729603
  have hstable : (prefixWord ++ tailWord_729603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729603).length < 2 ^ (prefixWord ++ tailWord_729603).sum := by decide
  have hdescent : baseEnd_729603 < baseStart_729603 := by decide
  rcases family_descends (prefixWord ++ tailWord_729603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729648 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_729648 : Nat := 118140960795 + 729648 * 2 ^ 59
def prefixEnd_729648 : Nat := 4983230072969 + 3 ^ 40 * 729648 * 2
def baseEnd_729648 : Nat := 333031228970547984483925

theorem tailTrace_729648 : CollatzResearch.WordTrace tailWord_729648 prefixEnd_729648 333031228970547984483925 := by
  unfold tailWord_729648
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306224430308692401242799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17741632573744923201657065 13306224430308692401242799)
  ·
    refine ⟨19959336645463038601864199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13306224430308692401242799 19959336645463038601864199)
    ·
      refine ⟨29939004968194557902796299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19959336645463038601864199 29939004968194557902796299)
      ·
        refine ⟨44908507452291836854194449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29939004968194557902796299 44908507452291836854194449)
        ·
          refine ⟨33681380589218877640645837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44908507452291836854194449 33681380589218877640645837)
          ·
            refine ⟨12630517720957079115242189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33681380589218877640645837 12630517720957079115242189)
            ·
              refine ⟨4736444145358904668215821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12630517720957079115242189 4736444145358904668215821)
              ·
                refine ⟨1776166554509589250580933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736444145358904668215821 1776166554509589250580933)
                ·
                  refine ⟨333031228970547984483925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776166554509589250580933 333031228970547984483925)
                  ·
                    rfl

theorem cell20_729648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_729648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729648 prefixEnd_729648 := by exact prefixLift 729648
  have htrace : WordTrace (prefixWord ++ tailWord_729648) baseStart_729648 baseEnd_729648 := by
    simpa [prefixWord, tailWord_729648, baseEnd_729648] using wordTrace_append hprefix tailTrace_729648
  have hstable : (prefixWord ++ tailWord_729648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729648).length < 2 ^ (prefixWord ++ tailWord_729648).sum := by decide
  have hdescent : baseEnd_729648 < baseStart_729648 := by decide
  rcases family_descends (prefixWord ++ tailWord_729648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729654 : List Nat := [5, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_729654 : Nat := 118140960795 + 729654 * 2 ^ 59
def prefixEnd_729654 : Nat := 4983230072969 + 3 ^ 40 * 729654 * 2
def baseEnd_729654 : Nat := 333033967534038630283901

theorem tailTrace_729654 : CollatzResearch.WordTrace tailWord_729654 prefixEnd_729654 333033967534038630283901 := by
  unfold tailWord_729654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663291731162227989200251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17741778465730431884802677 1663291731162227989200251)
  ·
    refine ⟨2494937596743341983800377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1663291731162227989200251 2494937596743341983800377)
    ·
      refine ⟨1871203197557506487850283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2494937596743341983800377 1871203197557506487850283)
      ·
        refine ⟨2806804796336259731775425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871203197557506487850283 2806804796336259731775425)
        ·
          refine ⟨2105103597252194798831569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2806804796336259731775425 2105103597252194798831569)
          ·
            refine ⟨1578827697939146099123677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2105103597252194798831569 1578827697939146099123677)
            ·
              refine ⟨592060386727179787171379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1578827697939146099123677 592060386727179787171379)
              ·
                refine ⟨888090580090769680757069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592060386727179787171379 888090580090769680757069)
                ·
                  refine ⟨333033967534038630283901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888090580090769680757069 333033967534038630283901)
                  ·
                    rfl

theorem cell20_729654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_729654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729654 prefixEnd_729654 := by exact prefixLift 729654
  have htrace : WordTrace (prefixWord ++ tailWord_729654) baseStart_729654 baseEnd_729654 := by
    simpa [prefixWord, tailWord_729654, baseEnd_729654] using wordTrace_append hprefix tailTrace_729654
  have hstable : (prefixWord ++ tailWord_729654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729654).length < 2 ^ (prefixWord ++ tailWord_729654).sum := by decide
  have hdescent : baseEnd_729654 < baseStart_729654 := by decide
  rcases family_descends (prefixWord ++ tailWord_729654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729655 : List Nat := [1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_729655 : Nat := 118140960795 + 729655 * 2 ^ 59
def prefixEnd_729655 : Nat := 4983230072969 + 3 ^ 40 * 729655 * 2
def baseEnd_729655 : Nat := 111011474653762357083521

theorem tailTrace_729655 : CollatzResearch.WordTrace tailWord_729655 prefixEnd_729655 111011474653762357083521 := by
  unfold tailWord_729655
  simp only [CollatzResearch.WordTrace]
  refine ⟨26612704171592024997990419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17741802781061349998660279 26612704171592024997990419)
  ·
    refine ⟨39919056257388037496985629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26612704171592024997990419 39919056257388037496985629)
    ·
      refine ⟨14969646096520514061369611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39919056257388037496985629 14969646096520514061369611)
      ·
        refine ⟨22454469144780771092054417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14969646096520514061369611 22454469144780771092054417)
        ·
          refine ⟨16840851858585578319040813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22454469144780771092054417 16840851858585578319040813)
          ·
            refine ⟨6315319446969591869640305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16840851858585578319040813 6315319446969591869640305)
            ·
              refine ⟨4736489585227193902230229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315319446969591869640305 4736489585227193902230229)
              ·
                refine ⟨111011474653762357083521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4736489585227193902230229 111011474653762357083521)
                ·
                  rfl

theorem cell20_729655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_729655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729655 prefixEnd_729655 := by exact prefixLift 729655
  have htrace : WordTrace (prefixWord ++ tailWord_729655) baseStart_729655 baseEnd_729655 := by
    simpa [prefixWord, tailWord_729655, baseEnd_729655] using wordTrace_append hprefix tailTrace_729655
  have hstable : (prefixWord ++ tailWord_729655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729655).length < 2 ^ (prefixWord ++ tailWord_729655).sum := by decide
  have hdescent : baseEnd_729655 < baseStart_729655 := by decide
  rcases family_descends (prefixWord ++ tailWord_729655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729665 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_729665 : Nat := 118140960795 + 729665 * 2 ^ 59
def prefixEnd_729665 : Nat := 4983230072969 + 3 ^ 40 * 729665 * 2
def baseEnd_729665 : Nat := 333038988233771480917189

theorem tailTrace_729665 : CollatzResearch.WordTrace tailWord_729665 prefixEnd_729665 333038988233771480917189 := by
  unfold tailWord_729665
  simp only [CollatzResearch.WordTrace]
  refine ⟨26613068901555796705854449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17742045934370531137236299 26613068901555796705854449)
  ·
    refine ⟨19959801676166847529390837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26613068901555796705854449 19959801676166847529390837)
    ·
      refine ⟨1871231407140641955880391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19959801676166847529390837 1871231407140641955880391)
      ·
        refine ⟨2806847110710962933820587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871231407140641955880391 2806847110710962933820587)
        ·
          refine ⟨4210270666066444400730881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2806847110710962933820587 4210270666066444400730881)
          ·
            refine ⟨3157702999549833300548161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4210270666066444400730881 3157702999549833300548161)
            ·
              refine ⟨2368277249662374975411121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157702999549833300548161 2368277249662374975411121)
              ·
                refine ⟨1776207937246781231558341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2368277249662374975411121 1776207937246781231558341)
                ·
                  refine ⟨333038988233771480917189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776207937246781231558341 333038988233771480917189)
                  ·
                    rfl

theorem cell20_729665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_729665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729665 prefixEnd_729665 := by exact prefixLift 729665
  have htrace : WordTrace (prefixWord ++ tailWord_729665) baseStart_729665 baseEnd_729665 := by
    simpa [prefixWord, tailWord_729665, baseEnd_729665] using wordTrace_append hprefix tailTrace_729665
  have hstable : (prefixWord ++ tailWord_729665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729665).length < 2 ^ (prefixWord ++ tailWord_729665).sum := by decide
  have hdescent : baseEnd_729665 < baseStart_729665 := by decide
  rcases family_descends (prefixWord ++ tailWord_729665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729710 : List Nat := [4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_729710 : Nat := 118140960795 + 729710 * 2 ^ 59
def prefixEnd_729710 : Nat := 4983230072969 + 3 ^ 40 * 729710 * 2
def baseEnd_729710 : Nat := 111019842486650441472335

theorem tailTrace_729710 : CollatzResearch.WordTrace tailWord_729710 prefixEnd_729710 111019842486650441472335 := by
  unfold tailWord_729710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3326838773299096173905323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17743140124261846260828389 3326838773299096173905323)
  ·
    refine ⟨4990258159948644260857985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3326838773299096173905323 4990258159948644260857985)
    ·
      refine ⟨3742693619961483195643489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4990258159948644260857985 3742693619961483195643489)
      ·
        refine ⟨2807020214971112396732617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3742693619961483195643489 2807020214971112396732617)
        ·
          refine ⟨2105265161228334297549463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807020214971112396732617 2105265161228334297549463)
          ·
            refine ⟨3157897741842501446324195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105265161228334297549463 3157897741842501446324195)
            ·
              refine ⟨4736846612763752169486293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157897741842501446324195 4736846612763752169486293)
              ·
                refine ⟨111019842486650441472335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4736846612763752169486293 111019842486650441472335)
                ·
                  rfl

theorem cell20_729710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_729710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729710 prefixEnd_729710 := by exact prefixLift 729710
  have htrace : WordTrace (prefixWord ++ tailWord_729710) baseStart_729710 baseEnd_729710 := by
    simpa [prefixWord, tailWord_729710, baseEnd_729710] using wordTrace_append hprefix tailTrace_729710
  have hstable : (prefixWord ++ tailWord_729710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729710).length < 2 ^ (prefixWord ++ tailWord_729710).sum := by decide
  have hdescent : baseEnd_729710 < baseStart_729710 := by decide
  rcases family_descends (prefixWord ++ tailWord_729710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729724 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 4]
def baseStart_729724 : Nat := 118140960795 + 729724 * 2 ^ 59
def prefixEnd_729724 : Nat := 4983230072969 + 3 ^ 40 * 729724 * 2
def baseEnd_729724 : Nat := 333065917441429497950281

theorem tailTrace_729724 : CollatzResearch.WordTrace tailWord_729724 prefixEnd_729724 333065917441429497950281 := by
  unfold tailWord_729724
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307610404171024891126113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17743480538894699854834817 13307610404171024891126113)
  ·
    refine ⟨9980707803128268668344585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13307610404171024891126113 9980707803128268668344585)
    ·
      refine ⟨7485530852346201501258439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9980707803128268668344585 7485530852346201501258439)
      ·
        refine ⟨11228296278519302251887659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7485530852346201501258439 11228296278519302251887659)
        ·
          refine ⟨16842444417778953377831489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11228296278519302251887659 16842444417778953377831489)
          ·
            refine ⟨12631833313334215033373617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16842444417778953377831489 12631833313334215033373617)
            ·
              refine ⟨9473874985000661275030213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12631833313334215033373617 9473874985000661275030213)
              ·
                refine ⟨1776351559687623989068165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9473874985000661275030213 1776351559687623989068165)
                ·
                  refine ⟨333065917441429497950281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776351559687623989068165 333065917441429497950281)
                  ·
                    rfl

theorem cell20_729724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_729724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729724 prefixEnd_729724 := by exact prefixLift 729724
  have htrace : WordTrace (prefixWord ++ tailWord_729724) baseStart_729724 baseEnd_729724 := by
    simpa [prefixWord, tailWord_729724, baseEnd_729724] using wordTrace_append hprefix tailTrace_729724
  have hstable : (prefixWord ++ tailWord_729724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729724).length < 2 ^ (prefixWord ++ tailWord_729724).sum := by decide
  have hdescent : baseEnd_729724 < baseStart_729724 := by decide
  rcases family_descends (prefixWord ++ tailWord_729724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729731 : List Nat := [1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_729731 : Nat := 118140960795 + 729731 * 2 ^ 59
def prefixEnd_729731 : Nat := 4983230072969 + 3 ^ 40 * 729731 * 2
def baseEnd_729731 : Nat := 111023037477389528238973

theorem tailTrace_729731 : CollatzResearch.WordTrace tailWord_729731 prefixEnd_729731 111023037477389528238973 := by
  unfold tailWord_729731
  simp only [CollatzResearch.WordTrace]
  refine ⟨26615476119316689977757047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17743650746211126651838031 26615476119316689977757047)
  ·
    refine ⟨39923214178975034966635571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26615476119316689977757047 39923214178975034966635571)
    ·
      refine ⟨59884821268462552449953357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39923214178975034966635571 59884821268462552449953357)
      ·
        refine ⟨22456807975673457168732509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59884821268462552449953357 22456807975673457168732509)
        ·
          refine ⟨8421302990877546438274691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22456807975673457168732509 8421302990877546438274691)
          ·
            refine ⟨12631954486316319657412037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8421302990877546438274691 12631954486316319657412037)
            ·
              refine ⟨2368491466184309935764757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12631954486316319657412037 2368491466184309935764757)
              ·
                refine ⟨111023037477389528238973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2368491466184309935764757 111023037477389528238973)
                ·
                  rfl

theorem cell20_729731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_729731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729731 prefixEnd_729731 := by exact prefixLift 729731
  have htrace : WordTrace (prefixWord ++ tailWord_729731) baseStart_729731 baseEnd_729731 := by
    simpa [prefixWord, tailWord_729731, baseEnd_729731] using wordTrace_append hprefix tailTrace_729731
  have hstable : (prefixWord ++ tailWord_729731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729731).length < 2 ^ (prefixWord ++ tailWord_729731).sum := by decide
  have hdescent : baseEnd_729731 < baseStart_729731 := by decide
  rcases family_descends (prefixWord ++ tailWord_729731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729748 : List Nat := [2, 4, 2, 2, 1, 9]
def baseStart_729748 : Nat := 118140960795 + 729748 * 2 ^ 59
def prefixEnd_729748 : Nat := 4983230072969 + 3 ^ 40 * 729748 * 2
def baseEnd_729748 : Nat := 12336180433162669672229

theorem tailTrace_729748 : CollatzResearch.WordTrace tailWord_729748 prefixEnd_729748 12336180433162669672229 := by
  unfold tailWord_729748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13308048080127550940562949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17744064106836734587417265 13308048080127550940562949)
  ·
    refine ⟨2495259015023915801355553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13308048080127550940562949 2495259015023915801355553)
    ·
      refine ⟨1871444261267936851016665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2495259015023915801355553 1871444261267936851016665)
      ·
        refine ⟨1403583195950952638262499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1871444261267936851016665 1403583195950952638262499)
        ·
          refine ⟨2105374793926428957393749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403583195950952638262499 2105374793926428957393749)
          ·
            refine ⟨12336180433162669672229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2105374793926428957393749 12336180433162669672229)
            ·
              rfl

theorem cell20_729748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 9].length) (baseStart_729748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729748 prefixEnd_729748 := by exact prefixLift 729748
  have htrace : WordTrace (prefixWord ++ tailWord_729748) baseStart_729748 baseEnd_729748 := by
    simpa [prefixWord, tailWord_729748, baseEnd_729748] using wordTrace_append hprefix tailTrace_729748
  have hstable : (prefixWord ++ tailWord_729748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729748).length < 2 ^ (prefixWord ++ tailWord_729748).sum := by decide
  have hdescent : baseEnd_729748 < baseStart_729748 := by decide
  rcases family_descends (prefixWord ++ tailWord_729748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_729776 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_729776 : Nat := 118140960795 + 729776 * 2 ^ 59
def prefixEnd_729776 : Nat := 4983230072969 + 3 ^ 40 * 729776 * 2
def baseEnd_729776 : Nat := 333089651658348428216735

theorem tailTrace_729776 : CollatzResearch.WordTrace tailWord_729776 prefixEnd_729776 333089651658348428216735 := by
  unfold tailWord_729776
  simp only [CollatzResearch.WordTrace]
  refine ⟨13308558702076831331572591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17744744936102441775430121 13308558702076831331572591)
  ·
    refine ⟨19962838053115246997358887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13308558702076831331572591 19962838053115246997358887)
    ·
      refine ⟨29944257079672870496038331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19962838053115246997358887 29944257079672870496038331)
      ·
        refine ⟨44916385619509305744057497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29944257079672870496038331 44916385619509305744057497)
        ·
          refine ⟨33687289214631979308043123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44916385619509305744057497 33687289214631979308043123)
          ·
            refine ⟨50530933821947968962064685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33687289214631979308043123 50530933821947968962064685)
            ·
              refine ⟨18949100183230488360774257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50530933821947968962064685 18949100183230488360774257)
              ·
                refine ⟨14211825137422866270580693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18949100183230488360774257 14211825137422866270580693)
                ·
                  refine ⟨333089651658348428216735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14211825137422866270580693 333089651658348428216735)
                  ·
                    rfl

theorem cell20_729776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_729776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_729776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_729776 prefixEnd_729776 := by exact prefixLift 729776
  have htrace : WordTrace (prefixWord ++ tailWord_729776) baseStart_729776 baseEnd_729776 := by
    simpa [prefixWord, tailWord_729776, baseEnd_729776] using wordTrace_append hprefix tailTrace_729776
  have hstable : (prefixWord ++ tailWord_729776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_729776).length < 2 ^ (prefixWord ++ tailWord_729776).sum := by decide
  have hdescent : baseEnd_729776 < baseStart_729776 := by decide
  rcases family_descends (prefixWord ++ tailWord_729776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
