import V185TrunkScan22Chunk410

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3663870 : List Nat := [4, 2, 2, 2, 1, 1, 1, 9]
def baseStart_3663870 : Nat := 118140960795 + 3663870 * 2 ^ 59
def prefixEnd_3663870 : Nat := 4983230072969 + 3 ^ 40 * 3663870 * 2
def baseEnd_3663870 : Nat := 139357508562124838924087

theorem tailTrace_3663870 : CollatzResearch.WordTrace tailWord_3663870 prefixEnd_3663870 139357508562124838924087 := by
  unfold tailWord_3663870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704039654554025502933633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89088211490954802682312709 16704039654554025502933633)
  ·
    refine ⟨12528029740915519127200225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16704039654554025502933633 12528029740915519127200225)
    ·
      refine ⟨9396022305686639345400169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12528029740915519127200225 9396022305686639345400169)
      ·
        refine ⟨7047016729264979509050127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9396022305686639345400169 7047016729264979509050127)
        ·
          refine ⟨10570525093897469263575191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047016729264979509050127 10570525093897469263575191)
          ·
            refine ⟨15855787640846203895362787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10570525093897469263575191 15855787640846203895362787)
            ·
              refine ⟨23783681461269305843044181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855787640846203895362787 23783681461269305843044181)
              ·
                refine ⟨139357508562124838924087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23783681461269305843044181 139357508562124838924087)
                ·
                  rfl

theorem cell22_3663870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_3663870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663870 prefixEnd_3663870 := by exact prefixLift 3663870
  have htrace : WordTrace (prefixWord ++ tailWord_3663870) baseStart_3663870 baseEnd_3663870 := by
    simpa [prefixWord, tailWord_3663870, baseEnd_3663870] using wordTrace_append hprefix tailTrace_3663870
  have hstable : (prefixWord ++ tailWord_3663870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663870).length < 2 ^ (prefixWord ++ tailWord_3663870).sum := by decide
  have hdescent : baseEnd_3663870 < baseStart_3663870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663945 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 1, 4]
def baseStart_3663945 : Nat := 118140960795 + 3663945 * 2 ^ 59
def prefixEnd_3663945 : Nat := 4983230072969 + 3 ^ 40 * 3663945 * 2
def baseEnd_3663945 : Nat := 1254243251091848354691553

theorem tailTrace_3663945 : CollatzResearch.WordTrace tailWord_3663945 prefixEnd_3663945 1254243251091848354691553 := by
  unfold tailWord_3663945
  simp only [CollatzResearch.WordTrace]
  refine ⟨133635052711160491832449289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89090035140773661221632859 133635052711160491832449289)
  ·
    refine ⟨100226289533370368874336967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133635052711160491832449289 100226289533370368874336967)
    ·
      refine ⟨150339434300055553311505451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100226289533370368874336967 150339434300055553311505451)
      ·
        refine ⟨225509151450083329967258177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150339434300055553311505451 225509151450083329967258177)
        ·
          refine ⟨169131863587562497475443633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225509151450083329967258177 169131863587562497475443633)
          ·
            refine ⟨126848897690671873106582725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169131863587562497475443633 126848897690671873106582725)
            ·
              refine ⟨23784168317000976207484261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126848897690671873106582725 23784168317000976207484261)
              ·
                refine ⟨4459531559437683038903299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23784168317000976207484261 4459531559437683038903299)
                ·
                  refine ⟨6689297339156524558354949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4459531559437683038903299 6689297339156524558354949)
                  ·
                    refine ⟨1254243251091848354691553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6689297339156524558354949 1254243251091848354691553)
                    ·
                      rfl

theorem cell22_3663945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_3663945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663945 prefixEnd_3663945 := by exact prefixLift 3663945
  have htrace : WordTrace (prefixWord ++ tailWord_3663945) baseStart_3663945 baseEnd_3663945 := by
    simpa [prefixWord, tailWord_3663945, baseEnd_3663945] using wordTrace_append hprefix tailTrace_3663945
  have hstable : (prefixWord ++ tailWord_3663945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663945).length < 2 ^ (prefixWord ++ tailWord_3663945).sum := by decide
  have hdescent : baseEnd_3663945 < baseStart_3663945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664005 : List Nat := [1, 3, 1, 1, 5, 2, 1, 8]
def baseStart_3664005 : Nat := 118140960795 + 3664005 * 2 ^ 59
def prefixEnd_3664005 : Nat := 4983230072969 + 3 ^ 40 * 3664005 * 2
def baseEnd_3664005 : Nat := 139362643368669799799041

theorem tailTrace_3664005 : CollatzResearch.WordTrace tailWord_3664005 prefixEnd_3664005 139362643368669799799041 := by
  unfold tailWord_3664005
  simp only [CollatzResearch.WordTrace]
  refine ⟨133637241090943122079633469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89091494060628748053088979 133637241090943122079633469)
  ·
    refine ⟨50113965409103670779862551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133637241090943122079633469 50113965409103670779862551)
    ·
      refine ⟨75170948113655506169793827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50113965409103670779862551 75170948113655506169793827)
      ·
        refine ⟨112756422170483259254690741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75170948113655506169793827 112756422170483259254690741)
        ·
          refine ⟨10570914578482805555127257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112756422170483259254690741 10570914578482805555127257)
          ·
            refine ⟨7928185933862104166345443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10570914578482805555127257 7928185933862104166345443)
            ·
              refine ⟨11892278900793156249518165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7928185933862104166345443 11892278900793156249518165)
              ·
                refine ⟨139362643368669799799041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11892278900793156249518165 139362643368669799799041)
                ·
                  rfl

theorem cell22_3664005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 8].length) (baseStart_3664005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664005 prefixEnd_3664005 := by exact prefixLift 3664005
  have htrace : WordTrace (prefixWord ++ tailWord_3664005) baseStart_3664005 baseEnd_3664005 := by
    simpa [prefixWord, tailWord_3664005, baseEnd_3664005] using wordTrace_append hprefix tailTrace_3664005
  have hstable : (prefixWord ++ tailWord_3664005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664005).length < 2 ^ (prefixWord ++ tailWord_3664005).sum := by decide
  have hdescent : baseEnd_3664005 < baseStart_3664005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664088 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 1, 3]
def baseStart_3664088 : Nat := 118140960795 + 3664088 * 2 ^ 59
def prefixEnd_3664088 : Nat := 4983230072969 + 3 ^ 40 * 3664088 * 2
def baseEnd_3664088 : Nat := 1254292202914243648366115

theorem tailTrace_3664088 : CollatzResearch.WordTrace tailWord_3664088 prefixEnd_3664088 1254292202914243648366115 := by
  unfold tailWord_3664088
  simp only [CollatzResearch.WordTrace]
  refine ⟨66820134174821213627452459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89093512233094951503269945 66820134174821213627452459)
  ·
    refine ⟨100230201262231820441178689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66820134174821213627452459 100230201262231820441178689)
    ·
      refine ⟨75172650946673865330884017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100230201262231820441178689 75172650946673865330884017)
      ·
        refine ⟨56379488210005398998163013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75172650946673865330884017 56379488210005398998163013)
        ·
          refine ⟨10571154039376012312155565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56379488210005398998163013 10571154039376012312155565)
          ·
            refine ⟨3964182764766004617058337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10571154039376012312155565 3964182764766004617058337)
            ·
              refine ⟨2973137073574503462793753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3964182764766004617058337 2973137073574503462793753)
              ·
                refine ⟨2229852805180877597095315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973137073574503462793753 2229852805180877597095315)
                ·
                  refine ⟨3344779207771316395642973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229852805180877597095315 3344779207771316395642973)
                  ·
                    refine ⟨1254292202914243648366115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344779207771316395642973 1254292202914243648366115)
                    ·
                      rfl

theorem cell22_3664088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_3664088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664088 prefixEnd_3664088 := by exact prefixLift 3664088
  have htrace : WordTrace (prefixWord ++ tailWord_3664088) baseStart_3664088 baseEnd_3664088 := by
    simpa [prefixWord, tailWord_3664088, baseEnd_3664088] using wordTrace_append hprefix tailTrace_3664088
  have hstable : (prefixWord ++ tailWord_3664088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664088).length < 2 ^ (prefixWord ++ tailWord_3664088).sum := by decide
  have hdescent : baseEnd_3664088 < baseStart_3664088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664095 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 6]
def baseStart_3664095 : Nat := 118140960795 + 3664095 * 2 ^ 59
def prefixEnd_3664095 : Nat := 4983230072969 + 3 ^ 40 * 3664095 * 2
def baseEnd_3664095 : Nat := 418098199719099321147031

theorem tailTrace_3664095 : CollatzResearch.WordTrace tailWord_3664095 prefixEnd_3664095 418098199719099321147031 := by
  unfold tailWord_3664095
  simp only [CollatzResearch.WordTrace]
  refine ⟨133640523660617067450409739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89093682440411378300273159 133640523660617067450409739)
  ·
    refine ⟨200460785490925601175614609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133640523660617067450409739 200460785490925601175614609)
    ·
      refine ⟨150345589118194200881710957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200460785490925601175614609 150345589118194200881710957)
      ·
        refine ⟨56379595919322825330641609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150345589118194200881710957 56379595919322825330641609)
        ·
          refine ⟨42284696939492118997981207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56379595919322825330641609 42284696939492118997981207)
          ·
            refine ⟨63427045409238178496971811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42284696939492118997981207 63427045409238178496971811)
            ·
              refine ⟨95140568113857267745457717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63427045409238178496971811 95140568113857267745457717)
              ·
                refine ⟨8919428260674118851136661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95140568113857267745457717 8919428260674118851136661)
                ·
                  refine ⟨418098199719099321147031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8919428260674118851136661 418098199719099321147031)
                  ·
                    rfl

theorem cell22_3664095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 6].length) (baseStart_3664095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664095 prefixEnd_3664095 := by exact prefixLift 3664095
  have htrace : WordTrace (prefixWord ++ tailWord_3664095) baseStart_3664095 baseEnd_3664095 := by
    simpa [prefixWord, tailWord_3664095, baseEnd_3664095] using wordTrace_append hprefix tailTrace_3664095
  have hstable : (prefixWord ++ tailWord_3664095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664095).length < 2 ^ (prefixWord ++ tailWord_3664095).sum := by decide
  have hdescent : baseEnd_3664095 < baseStart_3664095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664099 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 2, 5]
def baseStart_3664099 : Nat := 118140960795 + 3664099 * 2 ^ 59
def prefixEnd_3664099 : Nat := 4983230072969 + 3 ^ 40 * 3664099 * 2
def baseEnd_3664099 : Nat := 1254295968439043286341081

theorem tailTrace_3664099 : CollatzResearch.WordTrace tailWord_3664099 prefixEnd_3664099 1254295968439043286341081 := by
  unfold tailWord_3664099
  simp only [CollatzResearch.WordTrace]
  refine ⟨133640669552602576133555351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89093779701735050755703567 133640669552602576133555351)
  ·
    refine ⟨200461004328903864200333027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133640669552602576133555351 200461004328903864200333027)
    ·
      refine ⟨300691506493355796300499541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200461004328903864200333027 300691506493355796300499541)
      ·
        refine ⟨3523728591719013237896479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 300691506493355796300499541 3523728591719013237896479)
        ·
          refine ⟨5285592887578519856844719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523728591719013237896479 5285592887578519856844719)
          ·
            refine ⟨7928389331367779785267079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285592887578519856844719 7928389331367779785267079)
            ·
              refine ⟨11892583997051669677900619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7928389331367779785267079 11892583997051669677900619)
              ·
                refine ⟨17838875995577504516850929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11892583997051669677900619 17838875995577504516850929)
                ·
                  refine ⟨13379156996683128387638197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17838875995577504516850929 13379156996683128387638197)
                  ·
                    refine ⟨1254295968439043286341081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13379156996683128387638197 1254295968439043286341081)
                    ·
                      rfl

theorem cell22_3664099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 5].length) (baseStart_3664099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664099 prefixEnd_3664099 := by exact prefixLift 3664099
  have htrace : WordTrace (prefixWord ++ tailWord_3664099) baseStart_3664099 baseEnd_3664099 := by
    simpa [prefixWord, tailWord_3664099, baseEnd_3664099] using wordTrace_append hprefix tailTrace_3664099
  have hstable : (prefixWord ++ tailWord_3664099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664099).length < 2 ^ (prefixWord ++ tailWord_3664099).sum := by decide
  have hdescent : baseEnd_3664099 < baseStart_3664099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664127 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 4, 3]
def baseStart_3664127 : Nat := 118140960795 + 3664127 * 2 ^ 59
def prefixEnd_3664127 : Nat := 4983230072969 + 3 ^ 40 * 3664127 * 2
def baseEnd_3664127 : Nat := 1254305553411260546640995

theorem tailTrace_3664127 : CollatzResearch.WordTrace tailWord_3664127 prefixEnd_3664127 1254305553411260546640995 := by
  unfold tailWord_3664127
  simp only [CollatzResearch.WordTrace]
  refine ⟨133641690796501136915574635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89094460531000757943716423 133641690796501136915574635)
  ·
    refine ⟨200462536194751705373361953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133641690796501136915574635 200462536194751705373361953)
    ·
      refine ⟨150346902146063779030021465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200462536194751705373361953 150346902146063779030021465)
      ·
        refine ⟨112760176609547834272516099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150346902146063779030021465 112760176609547834272516099)
        ·
          refine ⟨169140264914321751408774149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112760176609547834272516099 169140264914321751408774149)
          ·
            refine ⟨31713799671435328389145153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169140264914321751408774149 31713799671435328389145153)
            ·
              refine ⟨23785349753576496291858865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31713799671435328389145153 23785349753576496291858865)
              ·
                refine ⟨17839012315182372218894149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23785349753576496291858865 17839012315182372218894149)
                ·
                  refine ⟨3344814809096694791042653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17839012315182372218894149 3344814809096694791042653)
                  ·
                    refine ⟨1254305553411260546640995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344814809096694791042653 1254305553411260546640995)
                    ·
                      rfl

theorem cell22_3664127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 3].length) (baseStart_3664127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664127 prefixEnd_3664127 := by exact prefixLift 3664127
  have htrace : WordTrace (prefixWord ++ tailWord_3664127) baseStart_3664127 baseEnd_3664127 := by
    simpa [prefixWord, tailWord_3664127, baseEnd_3664127] using wordTrace_append hprefix tailTrace_3664127
  have hstable : (prefixWord ++ tailWord_3664127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664127).length < 2 ^ (prefixWord ++ tailWord_3664127).sum := by decide
  have hdescent : baseEnd_3664127 < baseStart_3664127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664129 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 4]
def baseStart_3664129 : Nat := 118140960795 + 3664129 * 2 ^ 59
def prefixEnd_3664129 : Nat := 4983230072969 + 3 ^ 40 * 3664129 * 2
def baseEnd_3664129 : Nat := 418102079350711069363663

theorem tailTrace_3664129 : CollatzResearch.WordTrace tailWord_3664129 prefixEnd_3664129 418102079350711069363663 := by
  unfold tailWord_3664129
  simp only [CollatzResearch.WordTrace]
  refine ⟨133641763742493891257147441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89094509161662594171431627 133641763742493891257147441)
  ·
    refine ⟨100231322806870418442860581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133641763742493891257147441 100231322806870418442860581)
    ·
      refine ⟨18793373026288203458036359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100231322806870418442860581 18793373026288203458036359)
      ·
        refine ⟨28190059539432305187054539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18793373026288203458036359 28190059539432305187054539)
        ·
          refine ⟨42285089309148457780581809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190059539432305187054539 42285089309148457780581809)
          ·
            refine ⟨31713816981861343335436357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42285089309148457780581809 31713816981861343335436357)
            ·
              refine ⟨5946340684099001875394317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31713816981861343335436357 5946340684099001875394317)
              ·
                refine ⟨2229877756537125703272869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5946340684099001875394317 2229877756537125703272869)
                ·
                  refine ⟨418102079350711069363663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229877756537125703272869 418102079350711069363663)
                  ·
                    rfl

theorem cell22_3664129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 4].length) (baseStart_3664129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664129 prefixEnd_3664129 := by exact prefixLift 3664129
  have htrace : WordTrace (prefixWord ++ tailWord_3664129) baseStart_3664129 baseEnd_3664129 := by
    simpa [prefixWord, tailWord_3664129, baseEnd_3664129] using wordTrace_append hprefix tailTrace_3664129
  have hstable : (prefixWord ++ tailWord_3664129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664129).length < 2 ^ (prefixWord ++ tailWord_3664129).sum := by decide
  have hdescent : baseEnd_3664129 < baseStart_3664129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664140 : List Nat := [2, 2, 1, 2, 2, 2, 11]
def baseStart_3664140 : Nat := 118140960795 + 3664140 * 2 ^ 59
def prefixEnd_3664140 : Nat := 4983230072969 + 3 ^ 40 * 3664140 * 2
def baseEnd_3664140 : Nat := 46455926058404920224665

theorem tailTrace_3664140 : CollatzResearch.WordTrace tailWord_3664140 prefixEnd_3664140 46455926058404920224665 := by
  unfold tailWord_3664140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66821082472727020067898937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89094776630302693423865249 66821082472727020067898937)
  ·
    refine ⟨50115811854545265050924203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66821082472727020067898937 50115811854545265050924203)
    ·
      refine ⟨75173717781817897576386305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50115811854545265050924203 75173717781817897576386305)
      ·
        refine ⟨56380288336363423182289729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75173717781817897576386305 56380288336363423182289729)
        ·
          refine ⟨42285216252272567386717297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56380288336363423182289729 42285216252272567386717297)
          ·
            refine ⟨31713912189204425540037973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42285216252272567386717297 31713912189204425540037973)
            ·
              refine ⟨46455926058404920224665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31713912189204425540037973 46455926058404920224665)
              ·
                rfl

theorem cell22_3664140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 11].length) (baseStart_3664140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664140 prefixEnd_3664140 := by exact prefixLift 3664140
  have htrace : WordTrace (prefixWord ++ tailWord_3664140) baseStart_3664140 baseEnd_3664140 := by
    simpa [prefixWord, tailWord_3664140, baseEnd_3664140] using wordTrace_append hprefix tailTrace_3664140
  have hstable : (prefixWord ++ tailWord_3664140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664140).length < 2 ^ (prefixWord ++ tailWord_3664140).sum := by decide
  have hdescent : baseEnd_3664140 < baseStart_3664140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664142 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3664142 : Nat := 118140960795 + 3664142 * 2 ^ 59
def prefixEnd_3664142 : Nat := 4983230072969 + 3 ^ 40 * 3664142 * 2
def baseEnd_3664142 : Nat := 1254310688217805507515949

theorem tailTrace_3664142 : CollatzResearch.WordTrace tailWord_3664142 prefixEnd_3664142 1254310688217805507515949 := by
  unfold tailWord_3664142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16705279736430849309671335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89094825260964529651580453 16705279736430849309671335)
  ·
    refine ⟨25057919604646273964507003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16705279736430849309671335 25057919604646273964507003)
    ·
      refine ⟨37586879406969410946760505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25057919604646273964507003 37586879406969410946760505)
      ·
        refine ⟨28190159555227058210070379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37586879406969410946760505 28190159555227058210070379)
        ·
          refine ⟨42285239332840587315105569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28190159555227058210070379 42285239332840587315105569)
          ·
            refine ⟨31713929499630440486329177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42285239332840587315105569 31713929499630440486329177)
            ·
              refine ⟨23785447124722830364746883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31713929499630440486329177 23785447124722830364746883)
              ·
                refine ⟨35678170687084245547120325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23785447124722830364746883 35678170687084245547120325)
                ·
                  refine ⟨6689657003828296040085061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35678170687084245547120325 6689657003828296040085061)
                  ·
                    refine ⟨1254310688217805507515949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6689657003828296040085061 1254310688217805507515949)
                    ·
                      rfl

theorem cell22_3664142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3664142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664142 prefixEnd_3664142 := by exact prefixLift 3664142
  have htrace : WordTrace (prefixWord ++ tailWord_3664142) baseStart_3664142 baseEnd_3664142 := by
    simpa [prefixWord, tailWord_3664142, baseEnd_3664142] using wordTrace_append hprefix tailTrace_3664142
  have hstable : (prefixWord ++ tailWord_3664142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664142).length < 2 ^ (prefixWord ++ tailWord_3664142).sum := by decide
  have hdescent : baseEnd_3664142 < baseStart_3664142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664277 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 1, 6]
def baseStart_3664277 : Nat := 118140960795 + 3664277 * 2 ^ 59
def prefixEnd_3664277 : Nat := 4983230072969 + 3 ^ 40 * 3664277 * 2
def baseEnd_3664277 : Nat := 1254356901476710155390535

theorem tailTrace_3664277 : CollatzResearch.WordTrace tailWord_3664277 prefixEnd_3664277 1254356901476710155390535 := by
  unfold tailWord_3664277
  simp only [CollatzResearch.WordTrace]
  refine ⟨133647161745957712533535085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89098107830638475022356723 133647161745957712533535085)
  ·
    refine ⟨50117685654734142200075657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133647161745957712533535085 50117685654734142200075657)
    ·
      refine ⟨37588264241050606650056743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50117685654734142200075657 37588264241050606650056743)
      ·
        refine ⟨56382396361575909975085115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37588264241050606650056743 56382396361575909975085115)
        ·
          refine ⟨84573594542363864962627673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56382396361575909975085115 84573594542363864962627673)
          ·
            refine ⟨63430195906772898721970755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84573594542363864962627673 63430195906772898721970755)
            ·
              refine ⟨95145293860159348082956133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63430195906772898721970755 95145293860159348082956133)
              ·
                refine ⟨17839742598779877765554275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95145293860159348082956133 17839742598779877765554275)
                ·
                  refine ⟨26759613898169816648331413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17839742598779877765554275 26759613898169816648331413)
                  ·
                    refine ⟨1254356901476710155390535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26759613898169816648331413 1254356901476710155390535)
                    ·
                      rfl

theorem cell22_3664277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_3664277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664277 prefixEnd_3664277 := by exact prefixLift 3664277
  have htrace : WordTrace (prefixWord ++ tailWord_3664277) baseStart_3664277 baseEnd_3664277 := by
    simpa [prefixWord, tailWord_3664277, baseEnd_3664277] using wordTrace_append hprefix tailTrace_3664277
  have hstable : (prefixWord ++ tailWord_3664277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664277).length < 2 ^ (prefixWord ++ tailWord_3664277).sum := by decide
  have hdescent : baseEnd_3664277 < baseStart_3664277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664292 : List Nat := [2, 3, 1, 2, 1, 1, 2, 10]
def baseStart_3664292 : Nat := 118140960795 + 3664292 * 2 ^ 59
def prefixEnd_3664292 : Nat := 4983230072969 + 3 ^ 40 * 3664292 * 2
def baseEnd_3664292 : Nat := 139373559587028346251721

theorem tailTrace_3664292 : CollatzResearch.WordTrace tailWord_3664292 prefixEnd_3664292 139373559587028346251721 := by
  unfold tailWord_3664292
  simp only [CollatzResearch.WordTrace]
  refine ⟨66823854420451685047665565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89098472560602246730220753 66823854420451685047665565)
  ·
    refine ⟨25058945407669381892874587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66823854420451685047665565 25058945407669381892874587)
    ·
      refine ⟨37588418111504072839311881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25058945407669381892874587 37588418111504072839311881)
      ·
        refine ⟨28191313583628054629483911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37588418111504072839311881 28191313583628054629483911)
        ·
          refine ⟨42286970375442081944225867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28191313583628054629483911 42286970375442081944225867)
          ·
            refine ⟨63430455563163122916338801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42286970375442081944225867 63430455563163122916338801)
            ·
              refine ⟨47572841672372342187254101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63430455563163122916338801 47572841672372342187254101)
              ·
                refine ⟨139373559587028346251721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47572841672372342187254101 139373559587028346251721)
                ·
                  rfl

theorem cell22_3664292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_3664292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664292 prefixEnd_3664292 := by exact prefixLift 3664292
  have htrace : WordTrace (prefixWord ++ tailWord_3664292) baseStart_3664292 baseEnd_3664292 := by
    simpa [prefixWord, tailWord_3664292, baseEnd_3664292] using wordTrace_append hprefix tailTrace_3664292
  have hstable : (prefixWord ++ tailWord_3664292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664292).length < 2 ^ (prefixWord ++ tailWord_3664292).sum := by decide
  have hdescent : baseEnd_3664292 < baseStart_3664292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664296 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_3664296 : Nat := 118140960795 + 3664296 * 2 ^ 59
def prefixEnd_3664296 : Nat := 4983230072969 + 3 ^ 40 * 3664296 * 2
def baseEnd_3664296 : Nat := 1254363405565000439165477

theorem tailTrace_3664296 : CollatzResearch.WordTrace tailWord_3664296 prefixEnd_3664296 1254363405565000439165477 := by
  unfold tailWord_3664296
  simp only [CollatzResearch.WordTrace]
  refine ⟨66823927366444439389238371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89098569821925919185651161 66823927366444439389238371)
  ·
    refine ⟨100235891049666659083857557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66823927366444439389238371 100235891049666659083857557)
    ·
      refine ⟨4698557392953124644555823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100235891049666659083857557 4698557392953124644555823)
      ·
        refine ⟨7047836089429686966833735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4698557392953124644555823 7047836089429686966833735)
        ·
          refine ⟨10571754134144530450250603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7047836089429686966833735 10571754134144530450250603)
          ·
            refine ⟨15857631201216795675375905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10571754134144530450250603 15857631201216795675375905)
            ·
              refine ⟨11893223400912596756531929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15857631201216795675375905 11893223400912596756531929)
              ·
                refine ⟨8919917550684447567398947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11893223400912596756531929 8919917550684447567398947)
                ·
                  refine ⟨13379876326026671351098421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8919917550684447567398947 13379876326026671351098421)
                  ·
                    refine ⟨1254363405565000439165477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13379876326026671351098421 1254363405565000439165477)
                    ·
                      rfl

theorem cell22_3664296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_3664296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664296 prefixEnd_3664296 := by exact prefixLift 3664296
  have htrace : WordTrace (prefixWord ++ tailWord_3664296) baseStart_3664296 baseEnd_3664296 := by
    simpa [prefixWord, tailWord_3664296, baseEnd_3664296] using wordTrace_append hprefix tailTrace_3664296
  have hstable : (prefixWord ++ tailWord_3664296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664296).length < 2 ^ (prefixWord ++ tailWord_3664296).sum := by decide
  have hdescent : baseEnd_3664296 < baseStart_3664296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664309 : List Nat := [1, 3, 3, 2, 3, 1, 9]
def baseStart_3664309 : Nat := 118140960795 + 3664309 * 2 ^ 59
def prefixEnd_3664309 : Nat := 4983230072969 + 3 ^ 40 * 3664309 * 2
def baseEnd_3664309 : Nat := 46458068730765656984831

theorem tailTrace_3664309 : CollatzResearch.WordTrace tailWord_3664309 prefixEnd_3664309 46458068730765656984831 := by
  unfold tailWord_3664309
  simp only [CollatzResearch.WordTrace]
  refine ⟨133648328881841781998699981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89098885921227854665799987 133648328881841781998699981)
  ·
    refine ⟨50118123330690668249512493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133648328881841781998699981 50118123330690668249512493)
    ·
      refine ⟨18794296249009000593567185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50118123330690668249512493 18794296249009000593567185)
      ·
        refine ⟨14095722186756750445175389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18794296249009000593567185 14095722186756750445175389)
        ·
          refine ⟨5285895820033781416940771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14095722186756750445175389 5285895820033781416940771)
          ·
            refine ⟨7928843730050672125411157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285895820033781416940771 7928843730050672125411157)
            ·
              refine ⟨46458068730765656984831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7928843730050672125411157 46458068730765656984831)
              ·
                rfl

theorem cell22_3664309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 9].length) (baseStart_3664309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664309 prefixEnd_3664309 := by exact prefixLift 3664309
  have htrace : WordTrace (prefixWord ++ tailWord_3664309) baseStart_3664309 baseEnd_3664309 := by
    simpa [prefixWord, tailWord_3664309, baseEnd_3664309] using wordTrace_append hprefix tailTrace_3664309
  have hstable : (prefixWord ++ tailWord_3664309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664309).length < 2 ^ (prefixWord ++ tailWord_3664309).sum := by decide
  have hdescent : baseEnd_3664309 < baseStart_3664309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664313 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 2, 3]
def baseStart_3664313 : Nat := 118140960795 + 3664313 * 2 ^ 59
def prefixEnd_3664313 : Nat := 4983230072969 + 3 ^ 40 * 3664313 * 2
def baseEnd_3664313 : Nat := 1254369225012418061490425

theorem tailTrace_3664313 : CollatzResearch.WordTrace tailWord_3664313 prefixEnd_3664313 1254369225012418061490425 := by
  unfold tailWord_3664313
  simp only [CollatzResearch.WordTrace]
  refine ⟨133648474773827290681845593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89098983182551527121230395 133648474773827290681845593)
  ·
    refine ⟨100236356080370468011384195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133648474773827290681845593 100236356080370468011384195)
    ·
      refine ⟨150354534120555702017076293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100236356080370468011384195 150354534120555702017076293)
      ·
        refine ⟨28191475147604194128201805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150354534120555702017076293 28191475147604194128201805)
        ·
          refine ⟨10571803180351572798075677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28191475147604194128201805 10571803180351572798075677)
          ·
            refine ⟨3964426192631839799278379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10571803180351572798075677 3964426192631839799278379)
            ·
              refine ⟨5946639288947759698917569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964426192631839799278379 5946639288947759698917569)
              ·
                refine ⟨4459979466710819774188177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5946639288947759698917569 4459979466710819774188177)
                ·
                  refine ⟨3344984600033114830641133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4459979466710819774188177 3344984600033114830641133)
                  ·
                    refine ⟨1254369225012418061490425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344984600033114830641133 1254369225012418061490425)
                    ·
                      rfl

theorem cell22_3664313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 3].length) (baseStart_3664313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664313 prefixEnd_3664313 := by exact prefixLift 3664313
  have htrace : WordTrace (prefixWord ++ tailWord_3664313) baseStart_3664313 baseEnd_3664313 := by
    simpa [prefixWord, tailWord_3664313, baseEnd_3664313] using wordTrace_append hprefix tailTrace_3664313
  have hstable : (prefixWord ++ tailWord_3664313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664313).length < 2 ^ (prefixWord ++ tailWord_3664313).sum := by decide
  have hdescent : baseEnd_3664313 < baseStart_3664313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664341 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 3, 3]
def baseStart_3664341 : Nat := 118140960795 + 3664341 * 2 ^ 59
def prefixEnd_3664341 : Nat := 4983230072969 + 3 ^ 40 * 3664341 * 2
def baseEnd_3664341 : Nat := 1254378809984635321790339

theorem tailTrace_3664341 : CollatzResearch.WordTrace tailWord_3664341 prefixEnd_3664341 1254378809984635321790339 := by
  unfold tailWord_3664341
  simp only [CollatzResearch.WordTrace]
  refine ⟨133649496017725851463864877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89099664011817234309243251 133649496017725851463864877)
  ·
    refine ⟨50118561006647194298949329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133649496017725851463864877 50118561006647194298949329)
    ·
      refine ⟨37588920754985395724211997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50118561006647194298949329 37588920754985395724211997)
      ·
        refine ⟨14095845283119523396579499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37588920754985395724211997 14095845283119523396579499)
        ·
          refine ⟨21143767924679285094869249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14095845283119523396579499 21143767924679285094869249)
          ·
            refine ⟨15857825943509463821151937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21143767924679285094869249 15857825943509463821151937)
            ·
              refine ⟨11893369457632097865863953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15857825943509463821151937 11893369457632097865863953)
              ·
                refine ⟨8920027093224073399397965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11893369457632097865863953 8920027093224073399397965)
                ·
                  refine ⟨3345010159959027524774237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8920027093224073399397965 3345010159959027524774237)
                  ·
                    refine ⟨1254378809984635321790339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345010159959027524774237 1254378809984635321790339)
                    ·
                      rfl

theorem cell22_3664341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_3664341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664341 prefixEnd_3664341 := by exact prefixLift 3664341
  have htrace : WordTrace (prefixWord ++ tailWord_3664341) baseStart_3664341 baseEnd_3664341 := by
    simpa [prefixWord, tailWord_3664341, baseEnd_3664341] using wordTrace_append hprefix tailTrace_3664341
  have hstable : (prefixWord ++ tailWord_3664341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664341).length < 2 ^ (prefixWord ++ tailWord_3664341).sum := by decide
  have hdescent : baseEnd_3664341 < baseStart_3664341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664388 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 5]
def baseStart_3664388 : Nat := 118140960795 + 3664388 * 2 ^ 59
def prefixEnd_3664388 : Nat := 4983230072969 + 3 ^ 40 * 3664388 * 2
def baseEnd_3664388 : Nat := 418131633015047621955065

theorem tailTrace_3664388 : CollatzResearch.WordTrace tailWord_3664388 prefixEnd_3664388 418131633015047621955065 := by
  unfold tailWord_3664388
  simp only [CollatzResearch.WordTrace]
  refine ⟨66825605124277789245412909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89100806832370385660550545 66825605124277789245412909)
  ·
    refine ⟨25059601921604170967029841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66825605124277789245412909 25059601921604170967029841)
    ·
      refine ⟨18794701441203128225272381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25059601921604170967029841 18794701441203128225272381)
      ·
        refine ⟨7048013040451173084477143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18794701441203128225272381 7048013040451173084477143)
        ·
          refine ⟨10572019560676759626715715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048013040451173084477143 10572019560676759626715715)
          ·
            refine ⟨15858029341015139440073573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572019560676759626715715 15858029341015139440073573)
            ·
              refine ⟨2973380501440338645013795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15858029341015139440073573 2973380501440338645013795)
              ·
                refine ⟨4460070752160507967520693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973380501440338645013795 4460070752160507967520693)
                ·
                  refine ⟨418131633015047621955065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4460070752160507967520693 418131633015047621955065)
                  ·
                    rfl

theorem cell22_3664388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_3664388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664388 prefixEnd_3664388 := by exact prefixLift 3664388
  have htrace : WordTrace (prefixWord ++ tailWord_3664388) baseStart_3664388 baseEnd_3664388 := by
    simpa [prefixWord, tailWord_3664388, baseEnd_3664388] using wordTrace_append hprefix tailTrace_3664388
  have hstable : (prefixWord ++ tailWord_3664388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664388).length < 2 ^ (prefixWord ++ tailWord_3664388).sum := by decide
  have hdescent : baseEnd_3664388 < baseStart_3664388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664433 : List Nat := [1, 2, 2, 3, 1, 1, 6, 2, 4]
def baseStart_3664433 : Nat := 118140960795 + 3664433 * 2 ^ 59
def prefixEnd_3664433 : Nat := 4983230072969 + 3 ^ 40 * 3664433 * 2
def baseEnd_3664433 : Nat := 418136767821592582830019

theorem tailTrace_3664433 : CollatzResearch.WordTrace tailWord_3664433 prefixEnd_3664433 418136767821592582830019 := by
  unfold tailWord_3664433
  simp only [CollatzResearch.WordTrace]
  refine ⟨133652851533392551176213953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89101901022261700784142635 133652851533392551176213953)
  ·
    refine ⟨100239638650044413382160465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133652851533392551176213953 100239638650044413382160465)
    ·
      refine ⟨75179728987533310036620349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100239638650044413382160465 75179728987533310036620349)
      ·
        refine ⟨28192398370324991263732631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75179728987533310036620349 28192398370324991263732631)
        ·
          refine ⟨42288597555487486895598947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28192398370324991263732631 42288597555487486895598947)
          ·
            refine ⟨63432896333231230343398421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42288597555487486895598947 63432896333231230343398421)
            ·
              refine ⟨2973417015620213922346801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63432896333231230343398421 2973417015620213922346801)
              ·
                refine ⟨2230062761715160441760101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973417015620213922346801 2230062761715160441760101)
                ·
                  refine ⟨418136767821592582830019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2230062761715160441760101 418136767821592582830019)
                  ·
                    rfl

theorem cell22_3664433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 4].length) (baseStart_3664433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664433 prefixEnd_3664433 := by exact prefixLift 3664433
  have htrace : WordTrace (prefixWord ++ tailWord_3664433) baseStart_3664433 baseEnd_3664433 := by
    simpa [prefixWord, tailWord_3664433, baseEnd_3664433] using wordTrace_append hprefix tailTrace_3664433
  have hstable : (prefixWord ++ tailWord_3664433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664433).length < 2 ^ (prefixWord ++ tailWord_3664433).sum := by decide
  have hdescent : baseEnd_3664433 < baseStart_3664433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664493 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_3664493 : Nat := 118140960795 + 3664493 * 2 ^ 59
def prefixEnd_3664493 : Nat := 4983230072969 + 3 ^ 40 * 3664493 * 2
def baseEnd_3664493 : Nat := 1254430842690957591989873

theorem tailTrace_3664493 : CollatzResearch.WordTrace tailWord_3664493 prefixEnd_3664493 1254430842690957591989873 := by
  unfold tailWord_3664493
  simp only [CollatzResearch.WordTrace]
  refine ⟨133655039913175181423398133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89103359942116787615598755 133655039913175181423398133)
  ·
    refine ⟨12530159991860173258443575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133655039913175181423398133 12530159991860173258443575)
    ·
      refine ⟨18795239987790259887665363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12530159991860173258443575 18795239987790259887665363)
      ·
        refine ⟨28192859981685389831498045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18795239987790259887665363 28192859981685389831498045)
        ·
          refine ⟨10572322493132021186811767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28192859981685389831498045 10572322493132021186811767)
          ·
            refine ⟨15858483739698031780217651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572322493132021186811767 15858483739698031780217651)
            ·
              refine ⟨23787725609547047670326477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15858483739698031780217651 23787725609547047670326477)
              ·
                refine ⟨8920397103580142876372429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23787725609547047670326477 8920397103580142876372429)
                ·
                  refine ⟨3345148913842553578639661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8920397103580142876372429 3345148913842553578639661)
                  ·
                    refine ⟨1254430842690957591989873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345148913842553578639661 1254430842690957591989873)
                    ·
                      rfl

theorem cell22_3664493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_3664493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664493 prefixEnd_3664493 := by exact prefixLift 3664493
  have htrace : WordTrace (prefixWord ++ tailWord_3664493) baseStart_3664493 baseEnd_3664493 := by
    simpa [prefixWord, tailWord_3664493, baseEnd_3664493] using wordTrace_append hprefix tailTrace_3664493
  have hstable : (prefixWord ++ tailWord_3664493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664493).length < 2 ^ (prefixWord ++ tailWord_3664493).sum := by decide
  have hdescent : baseEnd_3664493 < baseStart_3664493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664596 : List Nat := [2, 4, 1, 3, 12]
def baseStart_3664596 : Nat := 118140960795 + 3664596 * 2 ^ 59
def prefixEnd_3664596 : Nat := 4983230072969 + 3 ^ 40 * 3664596 * 2
def baseEnd_3664596 : Nat := 5162411941135389533599

theorem tailTrace_3664596 : CollatzResearch.WordTrace tailWord_3664596 prefixEnd_3664596 5162411941135389533599 := by
  unfold tailWord_3664596
  simp only [CollatzResearch.WordTrace]
  refine ⟨66829398315901015007198821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89105864421201353342931761 66829398315901015007198821)
  ·
    refine ⟨12530512184231440313849779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66829398315901015007198821 12530512184231440313849779)
    ·
      refine ⟨18795768276347160470774669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12530512184231440313849779 18795768276347160470774669)
      ·
        refine ⟨7048413103630185176540501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18795768276347160470774669 7048413103630185176540501)
        ·
          refine ⟨5162411941135389533599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7048413103630185176540501 5162411941135389533599)
          ·
            rfl

theorem cell22_3664596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 12].length) (baseStart_3664596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664596 prefixEnd_3664596 := by exact prefixLift 3664596
  have htrace : WordTrace (prefixWord ++ tailWord_3664596) baseStart_3664596 baseEnd_3664596 := by
    simpa [prefixWord, tailWord_3664596, baseEnd_3664596] using wordTrace_append hprefix tailTrace_3664596
  have hstable : (prefixWord ++ tailWord_3664596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664596).length < 2 ^ (prefixWord ++ tailWord_3664596).sum := by decide
  have hdescent : baseEnd_3664596 < baseStart_3664596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664600 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_3664600 : Nat := 118140960795 + 3664600 * 2 ^ 59
def prefixEnd_3664600 : Nat := 4983230072969 + 3 ^ 40 * 3664600 * 2
def baseEnd_3664600 : Nat := 1254467470977644979564545

theorem tailTrace_3664600 : CollatzResearch.WordTrace tailWord_3664600 prefixEnd_3664600 1254467470977644979564545 := by
  unfold tailWord_3664600
  simp only [CollatzResearch.WordTrace]
  refine ⟨66829471261893769348771627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89105961682525025798362169 66829471261893769348771627)
  ·
    refine ⟨100244206892840654023157441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66829471261893769348771627 100244206892840654023157441)
    ·
      refine ⟨75183155169630490517368081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100244206892840654023157441 75183155169630490517368081)
      ·
        refine ⟨56387366377222867888026061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75183155169630490517368081 56387366377222867888026061)
        ·
          refine ⟨21145262391458575458009773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56387366377222867888026061 21145262391458575458009773)
          ·
            refine ⟨7929473396796965796753665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21145262391458575458009773 7929473396796965796753665)
            ·
              refine ⟨5947105047597724347565249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929473396796965796753665 5947105047597724347565249)
              ·
                refine ⟨4460328785698293260673937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947105047597724347565249 4460328785698293260673937)
                ·
                  refine ⟨3345246589273719945505453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4460328785698293260673937 3345246589273719945505453)
                  ·
                    refine ⟨1254467470977644979564545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345246589273719945505453 1254467470977644979564545)
                    ·
                      rfl

theorem cell22_3664600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_3664600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664600 prefixEnd_3664600 := by exact prefixLift 3664600
  have htrace : WordTrace (prefixWord ++ tailWord_3664600) baseStart_3664600 baseEnd_3664600 := by
    simpa [prefixWord, tailWord_3664600, baseEnd_3664600] using wordTrace_append hprefix tailTrace_3664600
  have hstable : (prefixWord ++ tailWord_3664600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664600).length < 2 ^ (prefixWord ++ tailWord_3664600).sum := by decide
  have hdescent : baseEnd_3664600 < baseStart_3664600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664613 : List Nat := [1, 3, 1, 4, 1, 4, 1, 7]
def baseStart_3664613 : Nat := 118140960795 + 3664613 * 2 ^ 59
def prefixEnd_3664613 : Nat := 4983230072969 + 3 ^ 40 * 3664613 * 2
def baseEnd_3664613 : Nat := 139385769015924142109945

theorem tailTrace_3664613 : CollatzResearch.WordTrace tailWord_3664613 prefixEnd_3664613 139385769015924142109945 := by
  unfold tailWord_3664613
  simp only [CollatzResearch.WordTrace]
  refine ⟨133659416672740441917766493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89106277781826961278510995 133659416672740441917766493)
  ·
    refine ⟨50122281252277665719162435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133659416672740441917766493 50122281252277665719162435)
    ·
      refine ⟨75183421878416498578743653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50122281252277665719162435 75183421878416498578743653)
      ·
        refine ⟨14096891602203093483514435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75183421878416498578743653 14096891602203093483514435)
        ·
          refine ⟨21145337403304640225271653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14096891602203093483514435 21145337403304640225271653)
          ·
            refine ⟨3964750763119620042238435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21145337403304640225271653 3964750763119620042238435)
            ·
              refine ⟨5947126144679430063357653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3964750763119620042238435 5947126144679430063357653)
              ·
                refine ⟨139385769015924142109945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5947126144679430063357653 139385769015924142109945)
                ·
                  rfl

theorem cell22_3664613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 7].length) (baseStart_3664613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664613 prefixEnd_3664613 := by exact prefixLift 3664613
  have htrace : WordTrace (prefixWord ++ tailWord_3664613) baseStart_3664613 baseEnd_3664613 := by
    simpa [prefixWord, tailWord_3664613, baseEnd_3664613] using wordTrace_append hprefix tailTrace_3664613
  have hstable : (prefixWord ++ tailWord_3664613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664613).length < 2 ^ (prefixWord ++ tailWord_3664613).sum := by decide
  have hdescent : baseEnd_3664613 < baseStart_3664613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664641 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 7]
def baseStart_3664641 : Nat := 118140960795 + 3664641 * 2 ^ 59
def prefixEnd_3664641 : Nat := 4983230072969 + 3 ^ 40 * 3664641 * 2
def baseEnd_3664641 : Nat := 418160502038511513096473

theorem tailTrace_3664641 : CollatzResearch.WordTrace tailWord_3664641 prefixEnd_3664641 418160502038511513096473 := by
  unfold tailWord_3664641
  simp only [CollatzResearch.WordTrace]
  refine ⟨133660437916639002699785777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89106958611092668466523851 133660437916639002699785777)
  ·
    refine ⟨100245328437479252024839333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133660437916639002699785777 100245328437479252024839333)
    ·
      refine ⟨18795999082027359754657375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100245328437479252024839333 18795999082027359754657375)
      ·
        refine ⟨28193998623041039631986063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18795999082027359754657375 28193998623041039631986063)
        ·
          refine ⟨42290997934561559447979095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28193998623041039631986063 42290997934561559447979095)
          ·
            refine ⟨63436496901842339171968643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42290997934561559447979095 63436496901842339171968643)
            ·
              refine ⟨95154745352763508757952965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63436496901842339171968643 95154745352763508757952965)
              ·
                refine ⟨17841514753643157892116181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95154745352763508757952965 17841514753643157892116181)
                ·
                  refine ⟨418160502038511513096473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17841514753643157892116181 418160502038511513096473)
                  ·
                    rfl

theorem cell22_3664641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_3664641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664641 prefixEnd_3664641 := by exact prefixLift 3664641
  have htrace : WordTrace (prefixWord ++ tailWord_3664641) baseStart_3664641 baseEnd_3664641 := by
    simpa [prefixWord, tailWord_3664641, baseEnd_3664641] using wordTrace_append hprefix tailTrace_3664641
  have hstable : (prefixWord ++ tailWord_3664641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664641).length < 2 ^ (prefixWord ++ tailWord_3664641).sum := by decide
  have hdescent : baseEnd_3664641 < baseStart_3664641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664735 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 2, 3]
def baseStart_3664735 : Nat := 118140960795 + 3664735 * 2 ^ 59
def prefixEnd_3664735 : Nat := 4983230072969 + 3 ^ 40 * 3664735 * 2
def baseEnd_3664735 : Nat := 1254513684236549627439131

theorem tailTrace_3664735 : CollatzResearch.WordTrace tailWord_3664735 prefixEnd_3664735 1254513684236549627439131 := by
  unfold tailWord_3664735
  simp only [CollatzResearch.WordTrace]
  refine ⟨133663866378298456753707659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89109244252198971169138439 133663866378298456753707659)
  ·
    refine ⟨200495799567447685130561489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133663866378298456753707659 200495799567447685130561489)
    ·
      refine ⟨150371849675585763847921117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200495799567447685130561489 150371849675585763847921117)
      ·
        refine ⟨56389443628344661442970419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150371849675585763847921117 56389443628344661442970419)
        ·
          refine ⟨84584165442516992164455629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56389443628344661442970419 84584165442516992164455629)
          ·
            refine ⟨31719062040943872061670861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84584165442516992164455629 31719062040943872061670861)
            ·
              refine ⟨11894648265353952023126573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31719062040943872061670861 11894648265353952023126573)
              ·
                refine ⟨4460493099507732008672465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11894648265353952023126573 4460493099507732008672465)
                ·
                  refine ⟨3345369824630799006504349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4460493099507732008672465 3345369824630799006504349)
                  ·
                    refine ⟨1254513684236549627439131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345369824630799006504349 1254513684236549627439131)
                    ·
                      rfl

theorem cell22_3664735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_3664735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664735 prefixEnd_3664735 := by exact prefixLift 3664735
  have htrace : WordTrace (prefixWord ++ tailWord_3664735) baseStart_3664735 baseEnd_3664735 := by
    simpa [prefixWord, tailWord_3664735, baseEnd_3664735] using wordTrace_append hprefix tailTrace_3664735
  have hstable : (prefixWord ++ tailWord_3664735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664735).length < 2 ^ (prefixWord ++ tailWord_3664735).sum := by decide
  have hdescent : baseEnd_3664735 < baseStart_3664735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664857 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 1, 4]
def baseStart_3664857 : Nat := 118140960795 + 3664857 * 2 ^ 59
def prefixEnd_3664857 : Nat := 4983230072969 + 3 ^ 40 * 3664857 * 2
def baseEnd_3664857 : Nat := 1254555447329781975888757

theorem tailTrace_3664857 : CollatzResearch.WordTrace tailWord_3664857 prefixEnd_3664857 1254555447329781975888757 := by
  unfold tailWord_3664857
  simp only [CollatzResearch.WordTrace]
  refine ⟨133668316083856471589648825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89112210722570981059765883 133668316083856471589648825)
  ·
    refine ⟨100251237062892353692236619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133668316083856471589648825 100251237062892353692236619)
    ·
      refine ⟨150376855594338530538354929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100251237062892353692236619 150376855594338530538354929)
      ·
        refine ⟨112782641695753897903766197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150376855594338530538354929 112782641695753897903766197)
        ·
          refine ⟨10573372658976927928478081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112782641695753897903766197 10573372658976927928478081)
          ·
            refine ⟨7930029494232695946358561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573372658976927928478081 7930029494232695946358561)
            ·
              refine ⟨5947522120674521959768921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930029494232695946358561 5947522120674521959768921)
              ·
                refine ⟨4460641590505891469826691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947522120674521959768921 4460641590505891469826691)
                ·
                  refine ⟨6690962385758837204740037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460641590505891469826691 6690962385758837204740037)
                  ·
                    refine ⟨1254555447329781975888757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690962385758837204740037 1254555447329781975888757)
                    ·
                      rfl

theorem cell22_3664857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_3664857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664857 prefixEnd_3664857 := by exact prefixLift 3664857
  have htrace : WordTrace (prefixWord ++ tailWord_3664857) baseStart_3664857 baseEnd_3664857 := by
    simpa [prefixWord, tailWord_3664857, baseEnd_3664857] using wordTrace_append hprefix tailTrace_3664857
  have hstable : (prefixWord ++ tailWord_3664857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664857).length < 2 ^ (prefixWord ++ tailWord_3664857).sum := by decide
  have hdescent : baseEnd_3664857 < baseStart_3664857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664872 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 4]
def baseStart_3664872 : Nat := 118140960795 + 3664872 * 2 ^ 59
def prefixEnd_3664872 : Nat := 4983230072969 + 3 ^ 40 * 3664872 * 2
def baseEnd_3664872 : Nat := 418186860712108978921237

theorem tailTrace_3664872 : CollatzResearch.WordTrace tailWord_3664872 prefixEnd_3664872 418186860712108978921237 := by
  unfold tailWord_3664872
  simp only [CollatzResearch.WordTrace]
  refine ⟨66834431589401064575722435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89112575452534752767629913 66834431589401064575722435)
  ·
    refine ⟨100251647384101596863583653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66834431589401064575722435 100251647384101596863583653)
    ·
      refine ⟨18797183884519049411921935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100251647384101596863583653 18797183884519049411921935)
      ·
        refine ⟨28195775826778574117882903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18797183884519049411921935 28195775826778574117882903)
        ·
          refine ⟨42293663740167861176824355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28195775826778574117882903 42293663740167861176824355)
          ·
            refine ⟨63440495610251791765236533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42293663740167861176824355 63440495610251791765236533)
            ·
              refine ⟨5947546463461105477990925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63440495610251791765236533 5947546463461105477990925)
              ·
                refine ⟨2230329923797914554246597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5947546463461105477990925 2230329923797914554246597)
                ·
                  refine ⟨418186860712108978921237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2230329923797914554246597 418186860712108978921237)
                  ·
                    rfl

theorem cell22_3664872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 4].length) (baseStart_3664872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664872 prefixEnd_3664872 := by exact prefixLift 3664872
  have htrace : WordTrace (prefixWord ++ tailWord_3664872) baseStart_3664872 baseEnd_3664872 := by
    simpa [prefixWord, tailWord_3664872, baseEnd_3664872] using wordTrace_append hprefix tailTrace_3664872
  have hstable : (prefixWord ++ tailWord_3664872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664872).length < 2 ^ (prefixWord ++ tailWord_3664872).sum := by decide
  have hdescent : baseEnd_3664872 < baseStart_3664872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664904 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 2, 3]
def baseStart_3664904 : Nat := 118140960795 + 3664904 * 2 ^ 59
def prefixEnd_3664904 : Nat := 4983230072969 + 3 ^ 40 * 3664904 * 2
def baseEnd_3664904 : Nat := 1254571536390289519963613

theorem tailTrace_3664904 : CollatzResearch.WordTrace tailWord_3664904 prefixEnd_3664904 1254571536390289519963613 := by
  unfold tailWord_3664904
  simp only [CollatzResearch.WordTrace]
  refine ⟨66835015157343099308304883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89113353543124132411073177 66835015157343099308304883)
  ·
    refine ⟨100252522736014648962457325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66835015157343099308304883 100252522736014648962457325)
    ·
      refine ⟨37594696026005493360921497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100252522736014648962457325 37594696026005493360921497)
      ·
        refine ⟨28196022019504120020691123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37594696026005493360921497 28196022019504120020691123)
        ·
          refine ⟨42294033029256180031036685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28196022019504120020691123 42294033029256180031036685)
          ·
            refine ⟨15860262385971067511638757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42294033029256180031036685 15860262385971067511638757)
            ·
              refine ⟨2973799197369575158432267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15860262385971067511638757 2973799197369575158432267)
              ·
                refine ⟨4460698796054362737648401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973799197369575158432267 4460698796054362737648401)
                ·
                  refine ⟨3345524097040772053236301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4460698796054362737648401 3345524097040772053236301)
                  ·
                    refine ⟨1254571536390289519963613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345524097040772053236301 1254571536390289519963613)
                    ·
                      rfl

theorem cell22_3664904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_3664904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664904 prefixEnd_3664904 := by exact prefixLift 3664904
  have htrace : WordTrace (prefixWord ++ tailWord_3664904) baseStart_3664904 baseEnd_3664904 := by
    simpa [prefixWord, tailWord_3664904, baseEnd_3664904] using wordTrace_append hprefix tailTrace_3664904
  have hstable : (prefixWord ++ tailWord_3664904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664904).length < 2 ^ (prefixWord ++ tailWord_3664904).sum := by decide
  have hdescent : baseEnd_3664904 < baseStart_3664904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664915 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 5, 3]
def baseStart_3664915 : Nat := 118140960795 + 3664915 * 2 ^ 59
def prefixEnd_3664915 : Nat := 4983230072969 + 3 ^ 40 * 3664915 * 2
def baseEnd_3664915 : Nat := 1254575301915089157938579

theorem tailTrace_3664915 : CollatzResearch.WordTrace tailWord_3664915 prefixEnd_3664915 1254575301915089157938579 := by
  unfold tailWord_3664915
  simp only [CollatzResearch.WordTrace]
  refine ⟨133670431517646347495260199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89113621011764231663506799 133670431517646347495260199)
  ·
    refine ⟨200505647276469521242890299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133670431517646347495260199 200505647276469521242890299)
    ·
      refine ⟨300758470914704281864335449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200505647276469521242890299 300758470914704281864335449)
      ·
        refine ⟨225568853186028211398251587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300758470914704281864335449 225568853186028211398251587)
        ·
          refine ⟨338353279779042317097377381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225568853186028211398251587 338353279779042317097377381)
          ·
            refine ⟨63441239958570434455758259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338353279779042317097377381 63441239958570434455758259)
            ·
              refine ⟨95161859937855651683637389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63441239958570434455758259 95161859937855651683637389)
              ·
                refine ⟨35685697476695869381364021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95161859937855651683637389 35685697476695869381364021)
                ·
                  refine ⟨3345534138440237754502877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35685697476695869381364021 3345534138440237754502877)
                  ·
                    refine ⟨1254575301915089157938579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345534138440237754502877 1254575301915089157938579)
                    ·
                      rfl

theorem cell22_3664915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 3].length) (baseStart_3664915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664915 prefixEnd_3664915 := by exact prefixLift 3664915
  have htrace : WordTrace (prefixWord ++ tailWord_3664915) baseStart_3664915 baseEnd_3664915 := by
    simpa [prefixWord, tailWord_3664915, baseEnd_3664915] using wordTrace_append hprefix tailTrace_3664915
  have hstable : (prefixWord ++ tailWord_3664915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664915).length < 2 ^ (prefixWord ++ tailWord_3664915).sum := by decide
  have hdescent : baseEnd_3664915 < baseStart_3664915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664960 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_3664960 : Nat := 118140960795 + 3664960 * 2 ^ 59
def prefixEnd_3664960 : Nat := 4983230072969 + 3 ^ 40 * 3664960 * 2
def baseEnd_3664960 : Nat := 1254590706334724040563441

theorem tailTrace_3664960 : CollatzResearch.WordTrace tailWord_3664960 prefixEnd_3664960 1254590706334724040563441 := by
  unfold tailWord_3664960
  simp only [CollatzResearch.WordTrace]
  refine ⟨66836036401241660090324167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89114715201655546787098889 66836036401241660090324167)
  ·
    refine ⟨100254054601862490135486251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66836036401241660090324167 100254054601862490135486251)
    ·
      refine ⟨150381081902793735203229377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100254054601862490135486251 150381081902793735203229377)
      ·
        refine ⟨112785811427095301402422033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150381081902793735203229377 112785811427095301402422033)
        ·
          refine ⟨84589358570321476051816525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112785811427095301402422033 84589358570321476051816525)
          ·
            refine ⟨31721009463870553519431197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84589358570321476051816525 31721009463870553519431197)
            ·
              refine ⟨11895378548951457569786699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31721009463870553519431197 11895378548951457569786699)
              ·
                refine ⟨17843067823427186354680049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11895378548951457569786699 17843067823427186354680049)
                ·
                  refine ⟨13382300867570389766010037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17843067823427186354680049 13382300867570389766010037)
                  ·
                    refine ⟨1254590706334724040563441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13382300867570389766010037 1254590706334724040563441)
                    ·
                      rfl

theorem cell22_3664960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_3664960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664960 prefixEnd_3664960 := by exact prefixLift 3664960
  have htrace : WordTrace (prefixWord ++ tailWord_3664960) baseStart_3664960 baseEnd_3664960 := by
    simpa [prefixWord, tailWord_3664960, baseEnd_3664960] using wordTrace_append hprefix tailTrace_3664960
  have hstable : (prefixWord ++ tailWord_3664960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664960).length < 2 ^ (prefixWord ++ tailWord_3664960).sum := by decide
  have hdescent : baseEnd_3664960 < baseStart_3664960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664966 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3664966 : Nat := 118140960795 + 3664966 * 2 ^ 59
def prefixEnd_3664966 : Nat := 4983230072969 + 3 ^ 40 * 3664966 * 2
def baseEnd_3664966 : Nat := 1254592760257342024913423

theorem tailTrace_3664966 : CollatzResearch.WordTrace tailWord_3664966 prefixEnd_3664966 1254592760257342024913423 := by
  unfold tailWord_3664966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177259113764424475167711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89114861093641055470244501 4177259113764424475167711)
  ·
    refine ⟨6265888670646636712751567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4177259113764424475167711 6265888670646636712751567)
    ·
      refine ⟨9398833005969955069127351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6265888670646636712751567 9398833005969955069127351)
      ·
        refine ⟨14098249508954932603691027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9398833005969955069127351 14098249508954932603691027)
        ·
          refine ⟨21147374263432398905536541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098249508954932603691027 21147374263432398905536541)
          ·
            refine ⟨7930265348787149589576203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21147374263432398905536541 7930265348787149589576203)
            ·
              refine ⟨11895398023180724384364305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930265348787149589576203 11895398023180724384364305)
              ·
                refine ⟨8921548517385543288273229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895398023180724384364305 8921548517385543288273229)
                ·
                  refine ⟨3345580694019578733102461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8921548517385543288273229 3345580694019578733102461)
                  ·
                    refine ⟨1254592760257342024913423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345580694019578733102461 1254592760257342024913423)
                    ·
                      rfl

theorem cell22_3664966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3664966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664966 prefixEnd_3664966 := by exact prefixLift 3664966
  have htrace : WordTrace (prefixWord ++ tailWord_3664966) baseStart_3664966 baseEnd_3664966 := by
    simpa [prefixWord, tailWord_3664966, baseEnd_3664966] using wordTrace_append hprefix tailTrace_3664966
  have hstable : (prefixWord ++ tailWord_3664966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664966).length < 2 ^ (prefixWord ++ tailWord_3664966).sum := by decide
  have hdescent : baseEnd_3664966 < baseStart_3664966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3664992 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_3664992 : Nat := 118140960795 + 3664992 * 2 ^ 59
def prefixEnd_3664992 : Nat := 4983230072969 + 3 ^ 40 * 3664992 * 2
def baseEnd_3664992 : Nat := 1254601660588686623763343

theorem tailTrace_3664992 : CollatzResearch.WordTrace tailWord_3664992 prefixEnd_3664992 1254601660588686623763343 := by
  unfold tailWord_3664992
  simp only [CollatzResearch.WordTrace]
  refine ⟨66836619969183694822906615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89115493292244926430542153 66836619969183694822906615)
  ·
    refine ⟨100254929953775542234359923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66836619969183694822906615 100254929953775542234359923)
    ·
      refine ⟨150382394930663313351539885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100254929953775542234359923 150382394930663313351539885)
      ·
        refine ⟨56393398098998742506827457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150382394930663313351539885 56393398098998742506827457)
        ·
          refine ⟨42295048574249056880120593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56393398098998742506827457 42295048574249056880120593)
          ·
            refine ⟨31721286430686792660090445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42295048574249056880120593 31721286430686792660090445)
            ·
              refine ⟨11895482411507547247533917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31721286430686792660090445 11895482411507547247533917)
              ·
                refine ⟨4460805904315330217825219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11895482411507547247533917 4460805904315330217825219)
                ·
                  refine ⟨6691208856472995326737829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460805904315330217825219 6691208856472995326737829)
                  ·
                    refine ⟨1254601660588686623763343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6691208856472995326737829 1254601660588686623763343)
                    ·
                      rfl

theorem cell22_3664992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_3664992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3664992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3664992 prefixEnd_3664992 := by exact prefixLift 3664992
  have htrace : WordTrace (prefixWord ++ tailWord_3664992) baseStart_3664992 baseEnd_3664992 := by
    simpa [prefixWord, tailWord_3664992, baseEnd_3664992] using wordTrace_append hprefix tailTrace_3664992
  have hstable : (prefixWord ++ tailWord_3664992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3664992).length < 2 ^ (prefixWord ++ tailWord_3664992).sum := by decide
  have hdescent : baseEnd_3664992 < baseStart_3664992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3664992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665007 : List Nat := [1, 1, 2, 1, 3, 3, 1, 6, 4]
def baseStart_3665007 : Nat := 118140960795 + 3665007 * 2 ^ 59
def prefixEnd_3665007 : Nat := 4983230072969 + 3 ^ 40 * 3665007 * 2
def baseEnd_3665007 : Nat := 418202265131743861546099

theorem tailTrace_3665007 : CollatzResearch.WordTrace tailWord_3665007 prefixEnd_3665007 418202265131743861546099 := by
  unfold tailWord_3665007
  simp only [CollatzResearch.WordTrace]
  refine ⟨133673787033313047207609275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89115858022208698138406183 133673787033313047207609275)
  ·
    refine ⟨200510680549969570811413913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133673787033313047207609275 200510680549969570811413913)
    ·
      refine ⟨150383010412477178108560435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200510680549969570811413913 150383010412477178108560435)
      ·
        refine ⟨225574515618715767162840653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150383010412477178108560435 225574515618715767162840653)
        ·
          refine ⟨84590443357018412686065245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225574515618715767162840653 84590443357018412686065245)
          ·
            refine ⟨31721416258881904757274467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84590443357018412686065245 31721416258881904757274467)
            ·
              refine ⟨47582124388322857135911701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31721416258881904757274467 47582124388322857135911701)
              ·
                refine ⟨2230412080702633928245861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47582124388322857135911701 2230412080702633928245861)
                ·
                  refine ⟨418202265131743861546099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2230412080702633928245861 418202265131743861546099)
                  ·
                    rfl

theorem cell22_3665007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 6, 4].length) (baseStart_3665007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665007 prefixEnd_3665007 := by exact prefixLift 3665007
  have htrace : WordTrace (prefixWord ++ tailWord_3665007) baseStart_3665007 baseEnd_3665007 := by
    simpa [prefixWord, tailWord_3665007, baseEnd_3665007] using wordTrace_append hprefix tailTrace_3665007
  have hstable : (prefixWord ++ tailWord_3665007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665007).length < 2 ^ (prefixWord ++ tailWord_3665007).sum := by decide
  have hdescent : baseEnd_3665007 < baseStart_3665007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665020 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_3665020 : Nat := 118140960795 + 3665020 * 2 ^ 59
def prefixEnd_3665020 : Nat := 4983230072969 + 3 ^ 40 * 3665020 * 2
def baseEnd_3665020 : Nat := 1254611245560903884063257

theorem tailTrace_3665020 : CollatzResearch.WordTrace tailWord_3665020 prefixEnd_3665020 1254611245560903884063257 := by
  unfold tailWord_3665020
  simp only [CollatzResearch.WordTrace]
  refine ⟨66837130591132975213916257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89116174121510633618555009 66837130591132975213916257)
  ·
    refine ⟨50127847943349731410437193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66837130591132975213916257 50127847943349731410437193)
    ·
      refine ⟨37595885957512298557827895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50127847943349731410437193 37595885957512298557827895)
      ·
        refine ⟨56393828936268447836741843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37595885957512298557827895 56393828936268447836741843)
        ·
          refine ⟨84590743404402671755112765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56393828936268447836741843 84590743404402671755112765)
          ·
            refine ⟨31721528776651001908167287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84590743404402671755112765 31721528776651001908167287)
            ·
              refine ⟨47582293164976502862250931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31721528776651001908167287 47582293164976502862250931)
              ·
                refine ⟨71373439747464754293376397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47582293164976502862250931 71373439747464754293376397)
                ·
                  refine ⟨26765039905299282860016149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71373439747464754293376397 26765039905299282860016149)
                  ·
                    refine ⟨1254611245560903884063257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26765039905299282860016149 1254611245560903884063257)
                    ·
                      rfl

theorem cell22_3665020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_3665020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665020 prefixEnd_3665020 := by exact prefixLift 3665020
  have htrace : WordTrace (prefixWord ++ tailWord_3665020) baseStart_3665020 baseEnd_3665020 := by
    simpa [prefixWord, tailWord_3665020, baseEnd_3665020] using wordTrace_append hprefix tailTrace_3665020
  have hstable : (prefixWord ++ tailWord_3665020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665020).length < 2 ^ (prefixWord ++ tailWord_3665020).sum := by decide
  have hdescent : baseEnd_3665020 < baseStart_3665020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665052 : List Nat := [2, 2, 3, 2, 1, 4, 8]
def baseStart_3665052 : Nat := 118140960795 + 3665052 * 2 ^ 59
def prefixEnd_3665052 : Nat := 4983230072969 + 3 ^ 40 * 3665052 * 2
def baseEnd_3665052 : Nat := 46467488882032091380117

theorem tailTrace_3665052 : CollatzResearch.WordTrace tailWord_3665052 prefixEnd_3665052 46467488882032091380117 := by
  unfold tailWord_3665052
  simp only [CollatzResearch.WordTrace]
  refine ⟨66837714159075009946498705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89116952212100013261998273 66837714159075009946498705)
  ·
    refine ⟨50128285619306257459874029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66837714159075009946498705 50128285619306257459874029)
    ·
      refine ⟨18798107107239846547452761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50128285619306257459874029 18798107107239846547452761)
      ·
        refine ⟨14098580330429884910589571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18798107107239846547452761 14098580330429884910589571)
        ·
          refine ⟨21147870495644827365884357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098580330429884910589571 21147870495644827365884357)
          ·
            refine ⟨3965225717933405131103317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21147870495644827365884357 3965225717933405131103317)
            ·
              refine ⟨46467488882032091380117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3965225717933405131103317 46467488882032091380117)
              ·
                rfl

theorem cell22_3665052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 8].length) (baseStart_3665052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665052 prefixEnd_3665052 := by exact prefixLift 3665052
  have htrace : WordTrace (prefixWord ++ tailWord_3665052) baseStart_3665052 baseEnd_3665052 := by
    simpa [prefixWord, tailWord_3665052, baseEnd_3665052] using wordTrace_append hprefix tailTrace_3665052
  have hstable : (prefixWord ++ tailWord_3665052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665052).length < 2 ^ (prefixWord ++ tailWord_3665052).sum := by decide
  have hdescent : baseEnd_3665052 < baseStart_3665052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665054 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3665054 : Nat := 118140960795 + 3665054 * 2 ^ 59
def prefixEnd_3665054 : Nat := 4983230072969 + 3 ^ 40 * 3665054 * 2
def baseEnd_3665054 : Nat := 1254622884455739128713153

theorem tailTrace_3665054 : CollatzResearch.WordTrace tailWord_3665054 prefixEnd_3665054 1254622884455739128713153 := by
  unfold tailWord_3665054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16709437658017846779321277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89117000842761849489713477 16709437658017846779321277)
  ·
    refine ⟨6266039121756692542245479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16709437658017846779321277 6266039121756692542245479)
    ·
      refine ⟨9399058682635038813368219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6266039121756692542245479 9399058682635038813368219)
      ·
        refine ⟨14098588023952558220052329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399058682635038813368219 14098588023952558220052329)
        ·
          refine ⟨10573941017964418665039247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14098588023952558220052329 10573941017964418665039247)
          ·
            refine ⟨15860911526946627997558871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573941017964418665039247 15860911526946627997558871)
            ·
              refine ⟨23791367290419941996338307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15860911526946627997558871 23791367290419941996338307)
              ·
                refine ⟨35687050935629912994507461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23791367290419941996338307 35687050935629912994507461)
                ·
                  refine ⟨6691322050430608686470149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35687050935629912994507461 6691322050430608686470149)
                  ·
                    refine ⟨1254622884455739128713153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6691322050430608686470149 1254622884455739128713153)
                    ·
                      rfl

theorem cell22_3665054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3665054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665054 prefixEnd_3665054 := by exact prefixLift 3665054
  have htrace : WordTrace (prefixWord ++ tailWord_3665054) baseStart_3665054 baseEnd_3665054 := by
    simpa [prefixWord, tailWord_3665054, baseEnd_3665054] using wordTrace_append hprefix tailTrace_3665054
  have hstable : (prefixWord ++ tailWord_3665054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665054).length < 2 ^ (prefixWord ++ tailWord_3665054).sum := by decide
  have hdescent : baseEnd_3665054 < baseStart_3665054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665058 : List Nat := [3, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3665058 : Nat := 118140960795 + 3665058 * 2 ^ 59
def prefixEnd_3665058 : Nat := 4983230072969 + 3 ^ 40 * 3665058 * 2
def baseEnd_3665058 : Nat := 418208084579161483871047

theorem tailTrace_3665058 : CollatzResearch.WordTrace tailWord_3665058 prefixEnd_3665058 418208084579161483871047 := by
  unfold tailWord_3665058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33418911789032070729428957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89117098104085521945143885 33418911789032070729428957)
  ·
    refine ⟨12532091920887026523535859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33418911789032070729428957 12532091920887026523535859)
    ·
      refine ⟨18798137881330539785303789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12532091920887026523535859 18798137881330539785303789)
      ·
        refine ⟨7049301705498952419488921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18798137881330539785303789 7049301705498952419488921)
        ·
          refine ⟨5286976279124214314616691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7049301705498952419488921 5286976279124214314616691)
          ·
            refine ⟨7930464418686321471925037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286976279124214314616691 7930464418686321471925037)
            ·
              refine ⟨2973924157007370551971889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7930464418686321471925037 2973924157007370551971889)
              ·
                refine ⟨2230443117755527913978917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2973924157007370551971889 2230443117755527913978917)
                ·
                  refine ⟨418208084579161483871047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2230443117755527913978917 418208084579161483871047)
                  ·
                    rfl

theorem cell22_3665058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3665058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665058 prefixEnd_3665058 := by exact prefixLift 3665058
  have htrace : WordTrace (prefixWord ++ tailWord_3665058) baseStart_3665058 baseEnd_3665058 := by
    simpa [prefixWord, tailWord_3665058, baseEnd_3665058] using wordTrace_append hprefix tailTrace_3665058
  have hstable : (prefixWord ++ tailWord_3665058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665058).length < 2 ^ (prefixWord ++ tailWord_3665058).sum := by decide
  have hdescent : baseEnd_3665058 < baseStart_3665058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665069 : List Nat := [1, 5, 2, 1, 3, 1, 2, 7]
def baseStart_3665069 : Nat := 118140960795 + 3665069 * 2 ^ 59
def prefixEnd_3665069 : Nat := 4983230072969 + 3 ^ 40 * 3665069 * 2
def baseEnd_3665069 : Nat := 139403113251364898843123

theorem tailTrace_3665069 : CollatzResearch.WordTrace tailWord_3665069 prefixEnd_3665069 139403113251364898843123 := by
  unfold tailWord_3665069
  simp only [CollatzResearch.WordTrace]
  refine ⟨133676048359088431796366261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89117365572725621197577507 133676048359088431796366261)
  ·
    refine ⟨12532129533664540480909337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133676048359088431796366261 12532129533664540480909337)
    ·
      refine ⟨9399097150248405360682003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12532129533664540480909337 9399097150248405360682003)
      ·
        refine ⟨14098645725372608041023005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399097150248405360682003 14098645725372608041023005)
        ·
          refine ⟨5286992147014728015383627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14098645725372608041023005 5286992147014728015383627)
          ·
            refine ⟨7930488220522092023075441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286992147014728015383627 7930488220522092023075441)
            ·
              refine ⟨5947866165391569017306581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930488220522092023075441 5947866165391569017306581)
              ·
                refine ⟨139403113251364898843123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5947866165391569017306581 139403113251364898843123)
                ·
                  rfl

theorem cell22_3665069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 7].length) (baseStart_3665069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665069 prefixEnd_3665069 := by exact prefixLift 3665069
  have htrace : WordTrace (prefixWord ++ tailWord_3665069) baseStart_3665069 baseEnd_3665069 := by
    simpa [prefixWord, tailWord_3665069, baseEnd_3665069] using wordTrace_append hprefix tailTrace_3665069
  have hstable : (prefixWord ++ tailWord_3665069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665069).length < 2 ^ (prefixWord ++ tailWord_3665069).sum := by decide
  have hdescent : baseEnd_3665069 < baseStart_3665069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665073 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 2, 3]
def baseStart_3665073 : Nat := 118140960795 + 3665073 * 2 ^ 59
def prefixEnd_3665073 : Nat := 4983230072969 + 3 ^ 40 * 3665073 * 2
def baseEnd_3665073 : Nat := 1254629388544029412488095

theorem tailTrace_3665073 : CollatzResearch.WordTrace tailWord_3665073 prefixEnd_3665073 1254629388544029412488095 := by
  unfold tailWord_3665073
  simp only [CollatzResearch.WordTrace]
  refine ⟨133676194251073940479511873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89117462834049293653007915 133676194251073940479511873)
  ·
    refine ⟨100257145688305455359633905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133676194251073940479511873 100257145688305455359633905)
    ·
      refine ⟨75192859266229091519725429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100257145688305455359633905 75192859266229091519725429)
      ·
        refine ⟨7049330556208977329974259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75192859266229091519725429 7049330556208977329974259)
        ·
          refine ⟨10573995834313465994961389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049330556208977329974259 10573995834313465994961389)
          ·
            refine ⟨3965248437867549748110521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10573995834313465994961389 3965248437867549748110521)
            ·
              refine ⟨2973936328400662311082891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965248437867549748110521 2973936328400662311082891)
              ·
                refine ⟨4460904492600993466624337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2973936328400662311082891 4460904492600993466624337)
                ·
                  refine ⟨3345678369450745099968253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4460904492600993466624337 3345678369450745099968253)
                  ·
                    refine ⟨1254629388544029412488095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345678369450745099968253 1254629388544029412488095)
                    ·
                      rfl

theorem cell22_3665073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_3665073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665073 prefixEnd_3665073 := by exact prefixLift 3665073
  have htrace : WordTrace (prefixWord ++ tailWord_3665073) baseStart_3665073 baseEnd_3665073 := by
    simpa [prefixWord, tailWord_3665073, baseEnd_3665073] using wordTrace_append hprefix tailTrace_3665073
  have hstable : (prefixWord ++ tailWord_3665073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665073).length < 2 ^ (prefixWord ++ tailWord_3665073).sum := by decide
  have hdescent : baseEnd_3665073 < baseStart_3665073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665080 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 9]
def baseStart_3665080 : Nat := 118140960795 + 3665080 * 2 ^ 59
def prefixEnd_3665080 : Nat := 4983230072969 + 3 ^ 40 * 3665080 * 2
def baseEnd_3665080 : Nat := 418210594929027909187691

theorem tailTrace_3665080 : CollatzResearch.WordTrace tailWord_3665080 prefixEnd_3665080 418210594929027909187691 := by
  unfold tailWord_3665080
  simp only [CollatzResearch.WordTrace]
  refine ⟨66838224781024290337508347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89117633041365720450011129 66838224781024290337508347)
  ·
    refine ⟨100257337171536435506262521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66838224781024290337508347 100257337171536435506262521)
    ·
      refine ⟨75193002878652326629696891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100257337171536435506262521 75193002878652326629696891)
      ·
        refine ⟨112789504317978489944545337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75193002878652326629696891 112789504317978489944545337)
        ·
          refine ⟨84592128238483867458409003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112789504317978489944545337 84592128238483867458409003)
          ·
            refine ⟨126888192357725801187613505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84592128238483867458409003 126888192357725801187613505)
            ·
              refine ⟨95166144268294350890710129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126888192357725801187613505 95166144268294350890710129)
              ·
                refine ⟨71374608201220763168032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95166144268294350890710129 71374608201220763168032597)
                ·
                  refine ⟨418210594929027909187691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71374608201220763168032597 418210594929027909187691)
                  ·
                    rfl

theorem cell22_3665080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_3665080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665080 prefixEnd_3665080 := by exact prefixLift 3665080
  have htrace : WordTrace (prefixWord ++ tailWord_3665080) baseStart_3665080 baseEnd_3665080 := by
    simpa [prefixWord, tailWord_3665080, baseEnd_3665080] using wordTrace_append hprefix tailTrace_3665080
  have hstable : (prefixWord ++ tailWord_3665080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665080).length < 2 ^ (prefixWord ++ tailWord_3665080).sum := by decide
  have hdescent : baseEnd_3665080 < baseStart_3665080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665157 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 1, 5]
def baseStart_3665157 : Nat := 118140960795 + 3665157 * 2 ^ 59
def prefixEnd_3665157 : Nat := 4983230072969 + 3 ^ 40 * 3665157 * 2
def baseEnd_3665157 : Nat := 1254658143460681193387837

theorem tailTrace_3665157 : CollatzResearch.WordTrace tailWord_3665157 prefixEnd_3665157 1254658143460681193387837 := by
  unfold tailWord_3665157
  simp only [CollatzResearch.WordTrace]
  refine ⟨133679257982769622825569725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89119505321846415217046483 133679257982769622825569725)
  ·
    refine ⟨50129721743538608559588647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133679257982769622825569725 50129721743538608559588647)
    ·
      refine ⟨75194582615307912839382971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50129721743538608559588647 75194582615307912839382971)
      ·
        refine ⟨112791873922961869259074457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75194582615307912839382971 112791873922961869259074457)
        ·
          refine ⟨84593905442221401944305843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112791873922961869259074457 84593905442221401944305843)
          ·
            refine ⟨126890858163332102916458765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84593905442221401944305843 126890858163332102916458765)
            ·
              refine ⟨47584071811249538593672037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126890858163332102916458765 47584071811249538593672037)
              ·
                refine ⟨8922013464609288486313507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47584071811249538593672037 8922013464609288486313507)
                ·
                  refine ⟨13383020196913932729470261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8922013464609288486313507 13383020196913932729470261)
                  ·
                    refine ⟨1254658143460681193387837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13383020196913932729470261 1254658143460681193387837)
                    ·
                      rfl

theorem cell22_3665157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_3665157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665157 prefixEnd_3665157 := by exact prefixLift 3665157
  have htrace : WordTrace (prefixWord ++ tailWord_3665157) baseStart_3665157 baseEnd_3665157 := by
    simpa [prefixWord, tailWord_3665157, baseEnd_3665157] using wordTrace_append hprefix tailTrace_3665157
  have hstable : (prefixWord ++ tailWord_3665157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665157).length < 2 ^ (prefixWord ++ tailWord_3665157).sum := by decide
  have hdescent : baseEnd_3665157 < baseStart_3665157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665204 : List Nat := [2, 5, 1, 1, 1, 1, 3, 8]
def baseStart_3665204 : Nat := 118140960795 + 3665204 * 2 ^ 59
def prefixEnd_3665204 : Nat := 4983230072969 + 3 ^ 40 * 3665204 * 2
def baseEnd_3665204 : Nat := 139408248057909859718077

theorem tailTrace_3665204 : CollatzResearch.WordTrace tailWord_3665204 prefixEnd_3665204 139408248057909859718077 := by
  unfold tailWord_3665204
  simp only [CollatzResearch.WordTrace]
  refine ⟨66840486106799674926265333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89120648142399566568353777 66840486106799674926265333)
  ·
    refine ⟨6266295572512469524337375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66840486106799674926265333 6266295572512469524337375)
    ·
      refine ⟨9399443358768704286506063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6266295572512469524337375 9399443358768704286506063)
      ·
        refine ⟨14099165038153056429759095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399443358768704286506063 14099165038153056429759095)
        ·
          refine ⟨21148747557229584644638643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14099165038153056429759095 21148747557229584644638643)
          ·
            refine ⟨31723121335844376966957965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21148747557229584644638643 31723121335844376966957965)
            ·
              refine ⟨11896170500941641362609237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31723121335844376966957965 11896170500941641362609237)
              ·
                refine ⟨139408248057909859718077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11896170500941641362609237 139408248057909859718077)
                ·
                  rfl

theorem cell22_3665204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 8].length) (baseStart_3665204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665204 prefixEnd_3665204 := by exact prefixLift 3665204
  have htrace : WordTrace (prefixWord ++ tailWord_3665204) baseStart_3665204 baseEnd_3665204 := by
    simpa [prefixWord, tailWord_3665204, baseEnd_3665204] using wordTrace_append hprefix tailTrace_3665204
  have hstable : (prefixWord ++ tailWord_3665204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665204).length < 2 ^ (prefixWord ++ tailWord_3665204).sum := by decide
  have hdescent : baseEnd_3665204 < baseStart_3665204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665232 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 7]
def baseStart_3665232 : Nat := 118140960795 + 3665232 * 2 ^ 59
def prefixEnd_3665232 : Nat := 4983230072969 + 3 ^ 40 * 3665232 * 2
def baseEnd_3665232 : Nat := 418227939164468665920869

theorem tailTrace_3665232 : CollatzResearch.WordTrace tailWord_3665232 prefixEnd_3665232 418227939164468665920869 := by
  unfold tailWord_3665232
  simp only [CollatzResearch.WordTrace]
  refine ⟨66840996728748955317274975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89121328971665273756366633 66840996728748955317274975)
  ·
    refine ⟨100261495093123432975912463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66840996728748955317274975 100261495093123432975912463)
    ·
      refine ⟨150392242639685149463868695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100261495093123432975912463 150392242639685149463868695)
      ·
        refine ⟨225588363959527724195803043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150392242639685149463868695 225588363959527724195803043)
        ·
          refine ⟨338382545939291586293704565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225588363959527724195803043 338382545939291586293704565)
          ·
            refine ⟨31723363681808586215034803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338382545939291586293704565 31723363681808586215034803)
            ·
              refine ⟨47585045522712879322552205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31723363681808586215034803 47585045522712879322552205)
              ·
                refine ⟨17844392071017329745957077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47585045522712879322552205 17844392071017329745957077)
                ·
                  refine ⟨418227939164468665920869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17844392071017329745957077 418227939164468665920869)
                  ·
                    rfl

theorem cell22_3665232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_3665232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665232 prefixEnd_3665232 := by exact prefixLift 3665232
  have htrace : WordTrace (prefixWord ++ tailWord_3665232) baseStart_3665232 baseEnd_3665232 := by
    simpa [prefixWord, tailWord_3665232, baseEnd_3665232] using wordTrace_append hprefix tailTrace_3665232
  have hstable : (prefixWord ++ tailWord_3665232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665232).length < 2 ^ (prefixWord ++ tailWord_3665232).sum := by decide
  have hdescent : baseEnd_3665232 < baseStart_3665232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665247 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_3665247 : Nat := 118140960795 + 3665247 * 2 ^ 59
def prefixEnd_3665247 : Nat := 4983230072969 + 3 ^ 40 * 3665247 * 2
def baseEnd_3665247 : Nat := 1254688952299950958637561

theorem tailTrace_3665247 : CollatzResearch.WordTrace tailWord_3665247 prefixEnd_3665247 1254688952299950958637561 := by
  unfold tailWord_3665247
  simp only [CollatzResearch.WordTrace]
  refine ⟨133682540552443568196345995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89121693701629045464230663 133682540552443568196345995)
  ·
    refine ⟨200523810828665352294518993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133682540552443568196345995 200523810828665352294518993)
    ·
      refine ⟨150392858121499014220889245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200523810828665352294518993 150392858121499014220889245)
      ·
        refine ⟨56397321795562130332833467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150392858121499014220889245 56397321795562130332833467)
        ·
          refine ⟨84595982693343195499250201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56397321795562130332833467 84595982693343195499250201)
          ·
            refine ⟨63446987020007396624437651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84595982693343195499250201 63446987020007396624437651)
            ·
              refine ⟨95170480530011094936656477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63446987020007396624437651 95170480530011094936656477)
              ·
                refine ⟨35688930198754160601246179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95170480530011094936656477 35688930198754160601246179)
                ·
                  refine ⟨53533395298131240901869269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35688930198754160601246179 53533395298131240901869269)
                  ·
                    refine ⟨1254688952299950958637561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53533395298131240901869269 1254688952299950958637561)
                    ·
                      rfl

theorem cell22_3665247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_3665247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665247 prefixEnd_3665247 := by exact prefixLift 3665247
  have htrace : WordTrace (prefixWord ++ tailWord_3665247) baseStart_3665247 baseEnd_3665247 := by
    simpa [prefixWord, tailWord_3665247, baseEnd_3665247] using wordTrace_append hprefix tailTrace_3665247
  have hstable : (prefixWord ++ tailWord_3665247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665247).length < 2 ^ (prefixWord ++ tailWord_3665247).sum := by decide
  have hdescent : baseEnd_3665247 < baseStart_3665247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665298 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3665298 : Nat := 118140960795 + 3665298 * 2 ^ 59
def prefixEnd_3665298 : Nat := 4983230072969 + 3 ^ 40 * 3665298 * 2
def baseEnd_3665298 : Nat := 1254706410642203825612405

theorem tailTrace_3665298 : CollatzResearch.WordTrace tailWord_3665298 prefixEnd_3665298 1254706410642203825612405 := by
  unfold tailWord_3665298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33421100168814700976613137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89122933783505869270968365 33421100168814700976613137)
  ·
    refine ⟨25065825126611025732459853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33421100168814700976613137 25065825126611025732459853)
    ·
      refine ⟨9399684422479134649672445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25065825126611025732459853 9399684422479134649672445)
      ·
        refine ⟨3524881658429675493627167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9399684422479134649672445 3524881658429675493627167)
        ·
          refine ⟨5287322487644513240440751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3524881658429675493627167 5287322487644513240440751)
          ·
            refine ⟨7930983731466769860661127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287322487644513240440751 7930983731466769860661127)
            ·
              refine ⟨11896475597200154790991691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930983731466769860661127 11896475597200154790991691)
              ·
                refine ⟨17844713395800232186487537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11896475597200154790991691 17844713395800232186487537)
                ·
                  refine ⟨13383535046850174139865653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17844713395800232186487537 13383535046850174139865653)
                  ·
                    refine ⟨1254706410642203825612405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13383535046850174139865653 1254706410642203825612405)
                    ·
                      rfl

theorem cell22_3665298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3665298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665298 prefixEnd_3665298 := by exact prefixLift 3665298
  have htrace : WordTrace (prefixWord ++ tailWord_3665298) baseStart_3665298 baseEnd_3665298 := by
    simpa [prefixWord, tailWord_3665298, baseEnd_3665298] using wordTrace_append hprefix tailTrace_3665298
  have hstable : (prefixWord ++ tailWord_3665298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665298).length < 2 ^ (prefixWord ++ tailWord_3665298).sum := by decide
  have hdescent : baseEnd_3665298 < baseStart_3665298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665373 : List Nat := [1, 4, 3, 1, 1, 4, 2, 6]
def baseStart_3665373 : Nat := 118140960795 + 3665373 * 2 ^ 59
def prefixEnd_3665373 : Nat := 4983230072969 + 3 ^ 40 * 3665373 * 2
def baseEnd_3665373 : Nat := 139414676074992069998575

theorem tailTrace_3665373 : CollatzResearch.WordTrace tailWord_3665373 prefixEnd_3665373 139414676074992069998575 := by
  unfold tailWord_3665373
  simp only [CollatzResearch.WordTrace]
  refine ⟨133687136149987091715432773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89124757433324727810288515 133687136149987091715432773)
  ·
    refine ⟨25066338028122579696643645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133687136149987091715432773 25066338028122579696643645)
    ·
      refine ⟨9399876760545967386241367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25066338028122579696643645 9399876760545967386241367)
      ·
        refine ⟨14099815140818951079362051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399876760545967386241367 14099815140818951079362051)
        ·
          refine ⟨21149722711228426619043077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14099815140818951079362051 21149722711228426619043077)
          ·
            refine ⟨3965573008355329991070577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21149722711228426619043077 3965573008355329991070577)
            ·
              refine ⟨2974179756266497493302933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965573008355329991070577 2974179756266497493302933)
              ·
                refine ⟨139414676074992069998575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2974179756266497493302933 139414676074992069998575)
                ·
                  rfl

theorem cell22_3665373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 6].length) (baseStart_3665373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665373 prefixEnd_3665373 := by exact prefixLift 3665373
  have htrace : WordTrace (prefixWord ++ tailWord_3665373) baseStart_3665373 baseEnd_3665373 := by
    simpa [prefixWord, tailWord_3665373, baseEnd_3665373] using wordTrace_append hprefix tailTrace_3665373
  have hstable : (prefixWord ++ tailWord_3665373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665373).length < 2 ^ (prefixWord ++ tailWord_3665373).sum := by decide
  have hdescent : baseEnd_3665373 < baseStart_3665373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665384 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 9]
def baseStart_3665384 : Nat := 118140960795 + 3665384 * 2 ^ 59
def prefixEnd_3665384 : Nat := 4983230072969 + 3 ^ 40 * 3665384 * 2
def baseEnd_3665384 : Nat := 418245283399909422654047

theorem tailTrace_3665384 : CollatzResearch.WordTrace tailWord_3665384 prefixEnd_3665384 418245283399909422654047 := by
  unfold tailWord_3665384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66843768676473620297041603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89125024901964827062722137 66843768676473620297041603)
  ·
    refine ⟨100265653014710430445562405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66843768676473620297041603 100265653014710430445562405)
    ·
      refine ⟨18799809940258205708542951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100265653014710430445562405 18799809940258205708542951)
      ·
        refine ⟨28199714910387308562814427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18799809940258205708542951 28199714910387308562814427)
        ·
          refine ⟨42299572365580962844221641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28199714910387308562814427 42299572365580962844221641)
          ·
            refine ⟨31724679274185722133166231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42299572365580962844221641 31724679274185722133166231)
            ·
              refine ⟨47587018911278583199749347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31724679274185722133166231 47587018911278583199749347)
              ·
                refine ⟨71380528366917874799624021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47587018911278583199749347 71380528366917874799624021)
                ·
                  refine ⟨418245283399909422654047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71380528366917874799624021 418245283399909422654047)
                  ·
                    rfl

theorem cell22_3665384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_3665384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665384 prefixEnd_3665384 := by exact prefixLift 3665384
  have htrace : WordTrace (prefixWord ++ tailWord_3665384) baseStart_3665384 baseEnd_3665384 := by
    simpa [prefixWord, tailWord_3665384, baseEnd_3665384] using wordTrace_append hprefix tailTrace_3665384
  have hstable : (prefixWord ++ tailWord_3665384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665384).length < 2 ^ (prefixWord ++ tailWord_3665384).sum := by decide
  have hdescent : baseEnd_3665384 < baseStart_3665384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665388 : List Nat := [2, 2, 1, 1, 2, 1, 2, 7, 1, 3]
def baseStart_3665388 : Nat := 118140960795 + 3665388 * 2 ^ 59
def prefixEnd_3665388 : Nat := 4983230072969 + 3 ^ 40 * 3665388 * 2
def baseEnd_3665388 : Nat := 1254737219481473590862129

theorem tailTrace_3665388 : CollatzResearch.WordTrace tailWord_3665388 prefixEnd_3665388 1254737219481473590862129 := by
  unfold tailWord_3665388
  simp only [CollatzResearch.WordTrace]
  refine ⟨66843841622466374638614409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89125122163288499518152545 66843841622466374638614409)
  ·
    refine ⟨50132881216849780978960807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66843841622466374638614409 50132881216849780978960807)
    ·
      refine ⟨75199321825274671468441211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50132881216849780978960807 75199321825274671468441211)
      ·
        refine ⟨112798982737912007202661817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75199321825274671468441211 112798982737912007202661817)
        ·
          refine ⟨84599237053434005401996363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112798982737912007202661817 84599237053434005401996363)
          ·
            refine ⟨126898855580151008102994545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84599237053434005401996363 126898855580151008102994545)
            ·
              refine ⟨95174141685113256077245909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126898855580151008102994545 95174141685113256077245909)
              ·
                refine ⟨2230643945744841939310451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95174141685113256077245909 2230643945744841939310451)
                ·
                  refine ⟨3345965918617262908965677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230643945744841939310451 3345965918617262908965677)
                  ·
                    refine ⟨1254737219481473590862129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3345965918617262908965677 1254737219481473590862129)
                    ·
                      rfl

theorem cell22_3665388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_3665388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665388 prefixEnd_3665388 := by exact prefixLift 3665388
  have htrace : WordTrace (prefixWord ++ tailWord_3665388) baseStart_3665388 baseEnd_3665388 := by
    simpa [prefixWord, tailWord_3665388, baseEnd_3665388] using wordTrace_append hprefix tailTrace_3665388
  have hstable : (prefixWord ++ tailWord_3665388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665388).length < 2 ^ (prefixWord ++ tailWord_3665388).sum := by decide
  have hdescent : baseEnd_3665388 < baseStart_3665388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665399 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_3665399 : Nat := 118140960795 + 3665399 * 2 ^ 59
def prefixEnd_3665399 : Nat := 4983230072969 + 3 ^ 40 * 3665399 * 2
def baseEnd_3665399 : Nat := 1254740985006273228837095

theorem tailTrace_3665399 : CollatzResearch.WordTrace tailWord_3665399 prefixEnd_3665399 1254740985006273228837095 := by
  unfold tailWord_3665399
  simp only [CollatzResearch.WordTrace]
  refine ⟨133688084447892898155879251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89125389631928598770586167 133688084447892898155879251)
  ·
    refine ⟨200532126671839347233818877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133688084447892898155879251 200532126671839347233818877)
    ·
      refine ⟨75199547501939755212682079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200532126671839347233818877 75199547501939755212682079)
      ·
        refine ⟨112799321252909632819023119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75199547501939755212682079 112799321252909632819023119)
        ·
          refine ⟨169198981879364449228534679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112799321252909632819023119 169198981879364449228534679)
          ·
            refine ⟨253798472819046673842802019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169198981879364449228534679 253798472819046673842802019)
            ·
              refine ⟨380697709228570010764203029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253798472819046673842802019 380697709228570010764203029)
              ·
                refine ⟨17845205120089219254572017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 380697709228570010764203029 17845205120089219254572017)
                ·
                  refine ⟨13383903840066914440929013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17845205120089219254572017 13383903840066914440929013)
                  ·
                    refine ⟨1254740985006273228837095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13383903840066914440929013 1254740985006273228837095)
                    ·
                      rfl

theorem cell22_3665399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_3665399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665399 prefixEnd_3665399 := by exact prefixLift 3665399
  have htrace : WordTrace (prefixWord ++ tailWord_3665399) baseStart_3665399 baseEnd_3665399 := by
    simpa [prefixWord, tailWord_3665399, baseEnd_3665399] using wordTrace_append hprefix tailTrace_3665399
  have hstable : (prefixWord ++ tailWord_3665399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665399).length < 2 ^ (prefixWord ++ tailWord_3665399).sum := by decide
  have hdescent : baseEnd_3665399 < baseStart_3665399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665418 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_3665418 : Nat := 118140960795 + 3665418 * 2 ^ 59
def prefixEnd_3665418 : Nat := 4983230072969 + 3 ^ 40 * 3665418 * 2
def baseEnd_3665418 : Nat := 418249163031521170870679

theorem tailTrace_3665418 : CollatzResearch.WordTrace tailWord_3665418 prefixEnd_3665418 418249163031521170870679 := by
  unfold tailWord_3665418
  simp only [CollatzResearch.WordTrace]
  refine ⟨33422194358706016100205227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89125851623216042933880605 33422194358706016100205227)
  ·
    refine ⟨50133291538059024150307841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33422194358706016100205227 50133291538059024150307841)
    ·
      refine ⟨37599968653544268112730881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50133291538059024150307841 37599968653544268112730881)
      ·
        refine ⟨28199976490158201084548161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37599968653544268112730881 28199976490158201084548161)
        ·
          refine ⟨21149982367618650813411121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28199976490158201084548161 21149982367618650813411121)
          ·
            refine ⟨15862486775713988110058341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21149982367618650813411121 15862486775713988110058341)
            ·
              refine ⟨2974216270446372770635939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15862486775713988110058341 2974216270446372770635939)
              ·
                refine ⟨4461324405669559155953909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974216270446372770635939 4461324405669559155953909)
                ·
                  refine ⟨418249163031521170870679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4461324405669559155953909 418249163031521170870679)
                  ·
                    rfl

theorem cell22_3665418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_3665418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665418 prefixEnd_3665418 := by exact prefixLift 3665418
  have htrace : WordTrace (prefixWord ++ tailWord_3665418) baseStart_3665418 baseEnd_3665418 := by
    simpa [prefixWord, tailWord_3665418, baseEnd_3665418] using wordTrace_append hprefix tailTrace_3665418
  have hstable : (prefixWord ++ tailWord_3665418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665418).length < 2 ^ (prefixWord ++ tailWord_3665418).sum := by decide
  have hdescent : baseEnd_3665418 < baseStart_3665418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665463 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 4]
def baseStart_3665463 : Nat := 118140960795 + 3665463 * 2 ^ 59
def prefixEnd_3665463 : Nat := 4983230072969 + 3 ^ 40 * 3665463 * 2
def baseEnd_3665463 : Nat := 418254297838066131745633

theorem tailTrace_3665463 : CollatzResearch.WordTrace tailWord_3665463 prefixEnd_3665463 418254297838066131745633 := by
  unfold tailWord_3665463
  simp only [CollatzResearch.WordTrace]
  refine ⟨133690418719661037086209043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89126945813107358057472695 133690418719661037086209043)
  ·
    refine ⟨200535628079491555629313565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133690418719661037086209043 200535628079491555629313565)
    ·
      refine ⟨75200860529809333360992587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200535628079491555629313565 75200860529809333360992587)
      ·
        refine ⟨112801290794714000041488881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75200860529809333360992587 112801290794714000041488881)
        ·
          refine ⟨84600968096035500031116661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112801290794714000041488881 84600968096035500031116661)
          ·
            refine ⟨7931340759003328127917187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84600968096035500031116661 7931340759003328127917187)
            ·
              refine ⟨11897011138504992191875781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931340759003328127917187 11897011138504992191875781)
              ·
                refine ⟨2230689588469686035976709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11897011138504992191875781 2230689588469686035976709)
                ·
                  refine ⟨418254297838066131745633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2230689588469686035976709 418254297838066131745633)
                  ·
                    rfl

theorem cell22_3665463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 4].length) (baseStart_3665463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665463 prefixEnd_3665463 := by exact prefixLift 3665463
  have htrace : WordTrace (prefixWord ++ tailWord_3665463) baseStart_3665463 baseEnd_3665463 := by
    simpa [prefixWord, tailWord_3665463, baseEnd_3665463] using wordTrace_append hprefix tailTrace_3665463
  have hstable : (prefixWord ++ tailWord_3665463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665463).length < 2 ^ (prefixWord ++ tailWord_3665463).sum := by decide
  have hdescent : baseEnd_3665463 < baseStart_3665463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665512 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3665512 : Nat := 118140960795 + 3665512 * 2 ^ 59
def prefixEnd_3665512 : Nat := 4983230072969 + 3 ^ 40 * 3665512 * 2
def baseEnd_3665512 : Nat := 1254779667215578600761749

theorem tailTrace_3665512 : CollatzResearch.WordTrace tailWord_3665512 prefixEnd_3665512 1254779667215578600761749 := by
  unfold tailWord_3665512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66846102948241759227371395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89128137264322345636495193 66846102948241759227371395)
  ·
    refine ⟨100269154422362638841057093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66846102948241759227371395 100269154422362638841057093)
    ·
      refine ⟨18800466454192994782698205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100269154422362638841057093 18800466454192994782698205)
      ·
        refine ⟨7050174920322373043511827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18800466454192994782698205 7050174920322373043511827)
        ·
          refine ⟨10575262380483559565267741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7050174920322373043511827 10575262380483559565267741)
          ·
            refine ⟨3965723392681334836975403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10575262380483559565267741 3965723392681334836975403)
            ·
              refine ⟨5948585089022002255463105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965723392681334836975403 5948585089022002255463105)
              ·
                refine ⟨4461438816766501691597329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948585089022002255463105 4461438816766501691597329)
                ·
                  refine ⟨3346079112574876268697997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461438816766501691597329 3346079112574876268697997)
                  ·
                    refine ⟨1254779667215578600761749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346079112574876268697997 1254779667215578600761749)
                    ·
                      rfl

theorem cell22_3665512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3665512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665512 prefixEnd_3665512 := by exact prefixLift 3665512
  have htrace : WordTrace (prefixWord ++ tailWord_3665512) baseStart_3665512 baseEnd_3665512 := by
    simpa [prefixWord, tailWord_3665512, baseEnd_3665512] using wordTrace_append hprefix tailTrace_3665512
  have hstable : (prefixWord ++ tailWord_3665512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665512).length < 2 ^ (prefixWord ++ tailWord_3665512).sum := by decide
  have hdescent : baseEnd_3665512 < baseStart_3665512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665611 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_3665611 : Nat := 118140960795 + 3665611 * 2 ^ 59
def prefixEnd_3665611 : Nat := 4983230072969 + 3 ^ 40 * 3665611 * 2
def baseEnd_3665611 : Nat := 1254813556938775342536445

theorem tailTrace_3665611 : CollatzResearch.WordTrace tailWord_3665611 prefixEnd_3665611 1254813556938775342536445 := by
  unfold tailWord_3665611
  simp only [CollatzResearch.WordTrace]
  refine ⟨133695816723124858362596687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89130544482083238908397791 133695816723124858362596687)
  ·
    refine ⟨200543725084687287543895031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133695816723124858362596687 200543725084687287543895031)
    ·
      refine ⟨300815587627030931315842547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200543725084687287543895031 300815587627030931315842547)
      ·
        refine ⟨451223381440546396973763821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300815587627030931315842547 451223381440546396973763821)
        ·
          refine ⟨169208768040204898865161433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451223381440546396973763821 169208768040204898865161433)
          ·
            refine ⟨126906576030153674148871075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169208768040204898865161433 126906576030153674148871075)
            ·
              refine ⟨190359864045230511223306613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126906576030153674148871075 190359864045230511223306613)
              ·
                refine ⟨17846237254240360427184995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190359864045230511223306613 17846237254240360427184995)
                ·
                  refine ⟨26769355881360540640777493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17846237254240360427184995 26769355881360540640777493)
                  ·
                    refine ⟨1254813556938775342536445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26769355881360540640777493 1254813556938775342536445)
                    ·
                      rfl

theorem cell22_3665611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_3665611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665611 prefixEnd_3665611 := by exact prefixLift 3665611
  have htrace : WordTrace (prefixWord ++ tailWord_3665611) baseStart_3665611 baseEnd_3665611 := by
    simpa [prefixWord, tailWord_3665611, baseEnd_3665611] using wordTrace_append hprefix tailTrace_3665611
  have hstable : (prefixWord ++ tailWord_3665611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665611).length < 2 ^ (prefixWord ++ tailWord_3665611).sum := by decide
  have hdescent : baseEnd_3665611 < baseStart_3665611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665626 : List Nat := [3, 1, 1, 2, 2, 13]
def baseStart_3665626 : Nat := 118140960795 + 3665626 * 2 ^ 59
def prefixEnd_3665626 : Nat := 4983230072969 + 3 ^ 40 * 3665626 * 2
def baseEnd_3665626 : Nat := 15491588786979263005079

theorem tailTrace_3665626 : CollatzResearch.WordTrace tailWord_3665626 prefixEnd_3665626 15491588786979263005079 := by
  unfold tailWord_3665626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33424090954517628981098183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89130909212047010616261821 33424090954517628981098183)
  ·
    refine ⟨50136136431776443471647275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33424090954517628981098183 50136136431776443471647275)
    ·
      refine ⟨75204204647664665207470913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50136136431776443471647275 75204204647664665207470913)
      ·
        refine ⟨56403153485748498905603185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75204204647664665207470913 56403153485748498905603185)
        ·
          refine ⟨42302365114311374179202389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56403153485748498905603185 42302365114311374179202389)
          ·
            refine ⟨15491588786979263005079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42302365114311374179202389 15491588786979263005079)
            ·
              rfl

theorem cell22_3665626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 13].length) (baseStart_3665626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665626 prefixEnd_3665626 := by exact prefixLift 3665626
  have htrace : WordTrace (prefixWord ++ tailWord_3665626) baseStart_3665626 baseEnd_3665626 := by
    simpa [prefixWord, tailWord_3665626, baseEnd_3665626] using wordTrace_append hprefix tailTrace_3665626
  have hstable : (prefixWord ++ tailWord_3665626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665626).length < 2 ^ (prefixWord ++ tailWord_3665626).sum := by decide
  have hdescent : baseEnd_3665626 < baseStart_3665626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665641 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 7]
def baseStart_3665641 : Nat := 118140960795 + 3665641 * 2 ^ 59
def prefixEnd_3665641 : Nat := 4983230072969 + 3 ^ 40 * 3665641 * 2
def baseEnd_3665641 : Nat := 1254823826551865264286353

theorem tailTrace_3665641 : CollatzResearch.WordTrace tailWord_3665641 prefixEnd_3665641 1254823826551865264286353 := by
  unfold tailWord_3665641
  simp only [CollatzResearch.WordTrace]
  refine ⟨133696910913016173486188777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89131273942010782324125851 133696910913016173486188777)
  ·
    refine ⟨100272683184762130114641583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133696910913016173486188777 100272683184762130114641583)
    ·
      refine ⟨150409024777143195171962375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100272683184762130114641583 150409024777143195171962375)
      ·
        refine ⟨225613537165714792757943563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150409024777143195171962375 225613537165714792757943563)
        ·
          refine ⟨338420305748572189136915345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225613537165714792757943563 338420305748572189136915345)
          ·
            refine ⟨253815229311429141852686509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338420305748572189136915345 253815229311429141852686509)
            ·
              refine ⟨95180710991785928194757441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253815229311429141852686509 95180710991785928194757441)
              ·
                refine ⟨71385533243839446146068081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95180710991785928194757441 71385533243839446146068081)
                ·
                  refine ⟨53539149932879584609551061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71385533243839446146068081 53539149932879584609551061)
                  ·
                    refine ⟨1254823826551865264286353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53539149932879584609551061 1254823826551865264286353)
                    ·
                      rfl

theorem cell22_3665641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_3665641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665641 prefixEnd_3665641 := by exact prefixLift 3665641
  have htrace : WordTrace (prefixWord ++ tailWord_3665641) baseStart_3665641 baseEnd_3665641 := by
    simpa [prefixWord, tailWord_3665641, baseEnd_3665641] using wordTrace_append hprefix tailTrace_3665641
  have hstable : (prefixWord ++ tailWord_3665641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665641).length < 2 ^ (prefixWord ++ tailWord_3665641).sum := by decide
  have hdescent : baseEnd_3665641 < baseStart_3665641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665692 : List Nat := [2, 2, 3, 1, 1, 2, 1, 6, 1, 3]
def baseStart_3665692 : Nat := 118140960795 + 3665692 * 2 ^ 59
def prefixEnd_3665692 : Nat := 4983230072969 + 3 ^ 40 * 3665692 * 2
def baseEnd_3665692 : Nat := 1254841284894118131261197

theorem tailTrace_3665692 : CollatzResearch.WordTrace tailWord_3665692 prefixEnd_3665692 1254841284894118131261197 := by
  unfold tailWord_3665692
  simp only [CollatzResearch.WordTrace]
  refine ⟨66849385517915704598147665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89132514023887606130863553 66849385517915704598147665)
  ·
    refine ⟨50137039138436778448610749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66849385517915704598147665 50137039138436778448610749)
    ·
      refine ⟨18801389676913791918229031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50137039138436778448610749 18801389676913791918229031)
      ·
        refine ⟨28202084515370687877343547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18801389676913791918229031 28202084515370687877343547)
        ·
          refine ⟨42303126773056031816015321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28202084515370687877343547 42303126773056031816015321)
          ·
            refine ⟨31727345079792023862011491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42303126773056031816015321 31727345079792023862011491)
            ·
              refine ⟨47591017619688035793017237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31727345079792023862011491 47591017619688035793017237)
              ·
                refine ⟨2230828950922876677797683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47591017619688035793017237 2230828950922876677797683)
                ·
                  refine ⟨3346243426384315016696525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230828950922876677797683 3346243426384315016696525)
                  ·
                    refine ⟨1254841284894118131261197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346243426384315016696525 1254841284894118131261197)
                    ·
                      rfl

theorem cell22_3665692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_3665692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665692 prefixEnd_3665692 := by exact prefixLift 3665692
  have htrace : WordTrace (prefixWord ++ tailWord_3665692) baseStart_3665692 baseEnd_3665692 := by
    simpa [prefixWord, tailWord_3665692, baseEnd_3665692] using wordTrace_append hprefix tailTrace_3665692
  have hstable : (prefixWord ++ tailWord_3665692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665692).length < 2 ^ (prefixWord ++ tailWord_3665692).sum := by decide
  have hdescent : baseEnd_3665692 < baseStart_3665692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665726 : List Nat := [4, 2, 1, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3665726 : Nat := 118140960795 + 3665726 * 2 ^ 59
def prefixEnd_3665726 : Nat := 4983230072969 + 3 ^ 40 * 3665726 * 2
def baseEnd_3665726 : Nat := 1254852923788953375911093

theorem tailTrace_3665726 : CollatzResearch.WordTrace tailWord_3665726 prefixEnd_3665726 1254852923788953375911093 := by
  unfold tailWord_3665726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712501389713529125379129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89133340745138822002022021 16712501389713529125379129)
  ·
    refine ⟨12534376042285146844034347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16712501389713529125379129 12534376042285146844034347)
    ·
      refine ⟨18801564063427720266051521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12534376042285146844034347 18801564063427720266051521)
      ·
        refine ⟨14101173047570790199538641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18801564063427720266051521 14101173047570790199538641)
        ·
          refine ⟨10575879785678092649653981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14101173047570790199538641 10575879785678092649653981)
          ·
            refine ⟨3965954919629284743620243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10575879785678092649653981 3965954919629284743620243)
            ·
              refine ⟨5948932379443927115430365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965954919629284743620243 5948932379443927115430365)
              ·
                refine ⟨2230849642291472668286387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5948932379443927115430365 2230849642291472668286387)
                ·
                  refine ⟨3346274463437209002429581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2230849642291472668286387 3346274463437209002429581)
                  ·
                    refine ⟨1254852923788953375911093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346274463437209002429581 1254852923788953375911093)
                    ·
                      rfl

theorem cell22_3665726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3665726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665726 prefixEnd_3665726 := by exact prefixLift 3665726
  have htrace : WordTrace (prefixWord ++ tailWord_3665726) baseStart_3665726 baseEnd_3665726 := by
    simpa [prefixWord, tailWord_3665726, baseEnd_3665726] using wordTrace_append hprefix tailTrace_3665726
  have hstable : (prefixWord ++ tailWord_3665726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665726).length < 2 ^ (prefixWord ++ tailWord_3665726).sum := by decide
  have hdescent : baseEnd_3665726 < baseStart_3665726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665735 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3665735 : Nat := 118140960795 + 3665735 * 2 ^ 59
def prefixEnd_3665735 : Nat := 4983230072969 + 3 ^ 40 * 3665735 * 2
def baseEnd_3665735 : Nat := 1254856004672880352436065

theorem tailTrace_3665735 : CollatzResearch.WordTrace tailWord_3665735 prefixEnd_3665735 1254856004672880352436065 := by
  unfold tailWord_3665735
  simp only [CollatzResearch.WordTrace]
  refine ⟨133700339374675627540110659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89133559583117085026740439 133700339374675627540110659)
  ·
    refine ⟨200550509062013441310165989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133700339374675627540110659 200550509062013441310165989)
    ·
      refine ⟨37603220449127520245656123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200550509062013441310165989 37603220449127520245656123)
      ·
        refine ⟨56404830673691280368484185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37603220449127520245656123 56404830673691280368484185)
        ·
          refine ⟨42303623005268460276363139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56404830673691280368484185 42303623005268460276363139)
          ·
            refine ⟨63455434507902690414544709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42303623005268460276363139 63455434507902690414544709)
            ·
              refine ⟨11897893970231754452727133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63455434507902690414544709 11897893970231754452727133)
              ·
                refine ⟨4461710238836907919772675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11897893970231754452727133 4461710238836907919772675)
                ·
                  refine ⟨6692565358255361879659013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4461710238836907919772675 6692565358255361879659013)
                  ·
                    refine ⟨1254856004672880352436065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6692565358255361879659013 1254856004672880352436065)
                    ·
                      rfl

theorem cell22_3665735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3665735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665735 prefixEnd_3665735 := by exact prefixLift 3665735
  have htrace : WordTrace (prefixWord ++ tailWord_3665735) baseStart_3665735 baseEnd_3665735 := by
    simpa [prefixWord, tailWord_3665735, baseEnd_3665735] using wordTrace_append hprefix tailTrace_3665735
  have hstable : (prefixWord ++ tailWord_3665735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665735).length < 2 ^ (prefixWord ++ tailWord_3665735).sum := by decide
  have hdescent : baseEnd_3665735 < baseStart_3665735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665756 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 5]
def baseStart_3665756 : Nat := 118140960795 + 3665756 * 2 ^ 59
def prefixEnd_3665756 : Nat := 4983230072969 + 3 ^ 40 * 3665756 * 2
def baseEnd_3665756 : Nat := 418287731134014432553667

theorem tailTrace_3665756 : CollatzResearch.WordTrace tailWord_3665756 prefixEnd_3665756 418287731134014432553667 := by
  unfold tailWord_3665756
  simp only [CollatzResearch.WordTrace]
  refine ⟨66850552653799774063312561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89134070205066365417750081 66850552653799774063312561)
  ·
    refine ⟨50137914490349830547484421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66850552653799774063312561 50137914490349830547484421)
    ·
      refine ⟨9400858966940593227653329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50137914490349830547484421 9400858966940593227653329)
      ·
        refine ⟨7050644225205444920739997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9400858966940593227653329 7050644225205444920739997)
        ·
          refine ⟨2643991584452041845277499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7050644225205444920739997 2643991584452041845277499)
          ·
            refine ⟨3965987376678062767916249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643991584452041845277499 3965987376678062767916249)
            ·
              refine ⟨2974490532508547075937187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3965987376678062767916249 2974490532508547075937187)
              ·
                refine ⟨4461735798762820613905781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974490532508547075937187 4461735798762820613905781)
                ·
                  refine ⟨418287731134014432553667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4461735798762820613905781 418287731134014432553667)
                  ·
                    rfl

theorem cell22_3665756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_3665756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665756 prefixEnd_3665756 := by exact prefixLift 3665756
  have htrace : WordTrace (prefixWord ++ tailWord_3665756) baseStart_3665756 baseEnd_3665756 := by
    simpa [prefixWord, tailWord_3665756, baseEnd_3665756] using wordTrace_append hprefix tailTrace_3665756
  have hstable : (prefixWord ++ tailWord_3665756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665756).length < 2 ^ (prefixWord ++ tailWord_3665756).sum := by decide
  have hdescent : baseEnd_3665756 < baseStart_3665756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665799 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 2, 3]
def baseStart_3665799 : Nat := 118140960795 + 3665799 * 2 ^ 59
def prefixEnd_3665799 : Nat := 4983230072969 + 3 ^ 40 * 3665799 * 2
def baseEnd_3665799 : Nat := 1254877913180805518835869

theorem tailTrace_3665799 : CollatzResearch.WordTrace tailWord_3665799 prefixEnd_3665799 1254877913180805518835869 := by
  unfold tailWord_3665799
  simp only [CollatzResearch.WordTrace]
  refine ⟨133702673646443766470440451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89135115764295844313626967 133702673646443766470440451)
  ·
    refine ⟨200554010469665649705660677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133702673646443766470440451 200554010469665649705660677)
    ·
      refine ⟨37603876963062309319811377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200554010469665649705660677 37603876963062309319811377)
      ·
        refine ⟨28202907722296731989858533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37603876963062309319811377 28202907722296731989858533)
        ·
          refine ⟨5288045197930637248098475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28202907722296731989858533 5288045197930637248098475)
          ·
            refine ⟨7932067796895955872147713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288045197930637248098475 7932067796895955872147713)
            ·
              refine ⟨5949050847671966904110785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932067796895955872147713 5949050847671966904110785)
              ·
                refine ⟨4461788135753975178083089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949050847671966904110785 4461788135753975178083089)
                ·
                  refine ⟨3346341101815481383562317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461788135753975178083089 3346341101815481383562317)
                  ·
                    refine ⟨1254877913180805518835869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346341101815481383562317 1254877913180805518835869)
                    ·
                      rfl

theorem cell22_3665799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_3665799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665799 prefixEnd_3665799 := by exact prefixLift 3665799
  have htrace : WordTrace (prefixWord ++ tailWord_3665799) baseStart_3665799 baseEnd_3665799 := by
    simpa [prefixWord, tailWord_3665799, baseEnd_3665799] using wordTrace_append hprefix tailTrace_3665799
  have hstable : (prefixWord ++ tailWord_3665799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665799).length < 2 ^ (prefixWord ++ tailWord_3665799).sum := by decide
  have hdescent : baseEnd_3665799 < baseStart_3665799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665808 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_3665808 : Nat := 118140960795 + 3665808 * 2 ^ 59
def prefixEnd_3665808 : Nat := 4983230072969 + 3 ^ 40 * 3665808 * 2
def baseEnd_3665808 : Nat := 1254880994064732495360841

theorem tailTrace_3665808 : CollatzResearch.WordTrace tailWord_3665808 prefixEnd_3665808 1254880994064732495360841 := by
  unfold tailWord_3665808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66851500951705580503759039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89135334602274107338345385 66851500951705580503759039)
  ·
    refine ⟨100277251427558370755638559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66851500951705580503759039 100277251427558370755638559)
    ·
      refine ⟨150415877141337556133457839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100277251427558370755638559 150415877141337556133457839)
      ·
        refine ⟨225623815712006334200186759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150415877141337556133457839 225623815712006334200186759)
        ·
          refine ⟨338435723568009501300280139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225623815712006334200186759 338435723568009501300280139)
          ·
            refine ⟨507653585352014251950420209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338435723568009501300280139 507653585352014251950420209)
            ·
              refine ⟨380740189014010688962815157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507653585352014251950420209 380740189014010688962815157)
              ·
                refine ⟨35694392720063502090263921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380740189014010688962815157 35694392720063502090263921)
                ·
                  refine ⟨26770794540047626567697941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35694392720063502090263921 26770794540047626567697941)
                  ·
                    refine ⟨1254880994064732495360841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26770794540047626567697941 1254880994064732495360841)
                    ·
                      rfl

theorem cell22_3665808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_3665808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665808 prefixEnd_3665808 := by exact prefixLift 3665808
  have htrace : WordTrace (prefixWord ++ tailWord_3665808) baseStart_3665808 baseEnd_3665808 := by
    simpa [prefixWord, tailWord_3665808, baseEnd_3665808] using wordTrace_append hprefix tailTrace_3665808
  have hstable : (prefixWord ++ tailWord_3665808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665808).length < 2 ^ (prefixWord ++ tailWord_3665808).sum := by decide
  have hdescent : baseEnd_3665808 < baseStart_3665808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665812 : List Nat := [2, 4, 2, 1, 1, 4, 1, 7]
def baseStart_3665812 : Nat := 118140960795 + 3665812 * 2 ^ 59
def prefixEnd_3665812 : Nat := 4983230072969 + 3 ^ 40 * 3665812 * 2
def baseEnd_3665812 : Nat := 139431373705164202028981

theorem tailTrace_3665812 : CollatzResearch.WordTrace tailWord_3665812 prefixEnd_3665812 139431373705164202028981 := by
  unfold tailWord_3665812
  simp only [CollatzResearch.WordTrace]
  refine ⟨66851573897698334845331845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89135431863597779793775793 66851573897698334845331845)
  ·
    refine ⟨12534670105818437783499721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66851573897698334845331845 12534670105818437783499721)
    ·
      refine ⟨9401002579363828337624791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12534670105818437783499721 9401002579363828337624791)
      ·
        refine ⟨14101503869045742506437187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9401002579363828337624791 14101503869045742506437187)
        ·
          refine ⟨21152255803568613759655781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14101503869045742506437187 21152255803568613759655781)
          ·
            refine ⟨3966047963169115079935459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21152255803568613759655781 3966047963169115079935459)
            ·
              refine ⟨5949071944753672619903189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966047963169115079935459 5949071944753672619903189)
              ·
                refine ⟨139431373705164202028981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5949071944753672619903189 139431373705164202028981)
                ·
                  rfl

theorem cell22_3665812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 7].length) (baseStart_3665812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665812 prefixEnd_3665812 := by exact prefixLift 3665812
  have htrace : WordTrace (prefixWord ++ tailWord_3665812) baseStart_3665812 baseEnd_3665812 := by
    simpa [prefixWord, tailWord_3665812, baseEnd_3665812] using wordTrace_append hprefix tailTrace_3665812
  have hstable : (prefixWord ++ tailWord_3665812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665812).length < 2 ^ (prefixWord ++ tailWord_3665812).sum := by decide
  have hdescent : baseEnd_3665812 < baseStart_3665812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665887 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 1, 4]
def baseStart_3665887 : Nat := 118140960795 + 3665887 * 2 ^ 59
def prefixEnd_3665887 : Nat := 4983230072969 + 3 ^ 40 * 3665887 * 2
def baseEnd_3665887 : Nat := 1254908037379202622635599

theorem tailTrace_3665887 : CollatzResearch.WordTrace tailWord_3665887 prefixEnd_3665887 1254908037379202622635599 := by
  unfold tailWord_3665887
  simp only [CollatzResearch.WordTrace]
  refine ⟨133705883270124957499643915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89137255513416638333095943 133705883270124957499643915)
  ·
    refine ⟨200558824905187436249465873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133705883270124957499643915 200558824905187436249465873)
    ·
      refine ⟨150419118678890577187099405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200558824905187436249465873 150419118678890577187099405)
      ·
        refine ⟨56407169504583966445162277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150419118678890577187099405 56407169504583966445162277)
        ·
          refine ⟨10576344282109493708467927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56407169504583966445162277 10576344282109493708467927)
          ·
            refine ⟨15864516423164240562701891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10576344282109493708467927 15864516423164240562701891)
            ·
              refine ⟨23796774634746360844052837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15864516423164240562701891 23796774634746360844052837)
              ·
                refine ⟨4461895244014942658259907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23796774634746360844052837 4461895244014942658259907)
                ·
                  refine ⟨6692842866022413987389861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4461895244014942658259907 6692842866022413987389861)
                  ·
                    refine ⟨1254908037379202622635599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6692842866022413987389861 1254908037379202622635599)
                    ·
                      rfl

theorem cell22_3665887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_3665887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665887 prefixEnd_3665887 := by exact prefixLift 3665887
  have htrace : WordTrace (prefixWord ++ tailWord_3665887) baseStart_3665887 baseEnd_3665887 := by
    simpa [prefixWord, tailWord_3665887, baseEnd_3665887] using wordTrace_append hprefix tailTrace_3665887
  have hstable : (prefixWord ++ tailWord_3665887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665887).length < 2 ^ (prefixWord ++ tailWord_3665887).sum := by decide
  have hdescent : baseEnd_3665887 < baseStart_3665887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665900 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_3665900 : Nat := 118140960795 + 3665900 * 2 ^ 59
def prefixEnd_3665900 : Nat := 4983230072969 + 3 ^ 40 * 3665900 * 2
def baseEnd_3665900 : Nat := 1254912487544874922060559

theorem tailTrace_3665900 : CollatzResearch.WordTrace tailWord_3665900 prefixEnd_3665900 1254912487544874922060559 := by
  unfold tailWord_3665900
  simp only [CollatzResearch.WordTrace]
  refine ⟨66853178709538930359933577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89137571612718573813244769 66853178709538930359933577)
  ·
    refine ⟨50139884032154197769950183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66853178709538930359933577 50139884032154197769950183)
    ·
      refine ⟨75209826048231296654925275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50139884032154197769950183 75209826048231296654925275)
      ·
        refine ⟨112814739072346944982387913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75209826048231296654925275 112814739072346944982387913)
        ·
          refine ⟨84611054304260208736790935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112814739072346944982387913 84611054304260208736790935)
          ·
            refine ⟨126916581456390313105186403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84611054304260208736790935 126916581456390313105186403)
            ·
              refine ⟨190374872184585469657779605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126916581456390313105186403 190374872184585469657779605)
              ·
                refine ⟨8923822133652443890208419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190374872184585469657779605 8923822133652443890208419)
                ·
                  refine ⟨13385733200478665835312629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923822133652443890208419 13385733200478665835312629)
                  ·
                    refine ⟨1254912487544874922060559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13385733200478665835312629 1254912487544874922060559)
                    ·
                      rfl

theorem cell22_3665900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_3665900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665900 prefixEnd_3665900 := by exact prefixLift 3665900
  have htrace : WordTrace (prefixWord ++ tailWord_3665900) baseStart_3665900 baseEnd_3665900 := by
    simpa [prefixWord, tailWord_3665900, baseEnd_3665900] using wordTrace_append hprefix tailTrace_3665900
  have hstable : (prefixWord ++ tailWord_3665900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665900).length < 2 ^ (prefixWord ++ tailWord_3665900).sum := by decide
  have hdescent : baseEnd_3665900 < baseStart_3665900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665915 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 4, 4]
def baseStart_3665915 : Nat := 118140960795 + 3665915 * 2 ^ 59
def prefixEnd_3665915 : Nat := 4983230072969 + 3 ^ 40 * 3665915 * 2
def baseEnd_3665915 : Nat := 1254917622351419882935513

theorem tailTrace_3665915 : CollatzResearch.WordTrace tailWord_3665915 prefixEnd_3665915 1254917622351419882935513 := by
  unfold tailWord_3665915
  simp only [CollatzResearch.WordTrace]
  refine ⟨133706904514023518281663199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89137936342682345521108799 133706904514023518281663199)
  ·
    refine ⟨200560356771035277422494799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133706904514023518281663199 200560356771035277422494799)
    ·
      refine ⟨300840535156552916133742199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200560356771035277422494799 300840535156552916133742199)
      ·
        refine ⟨451260802734829374200613299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300840535156552916133742199 451260802734829374200613299)
        ·
          refine ⟨676891204102244061300919949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451260802734829374200613299 676891204102244061300919949)
          ·
            refine ⟨253834201538341522987844981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 676891204102244061300919949 253834201538341522987844981)
            ·
              refine ⟨23796956394219517780110467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253834201538341522987844981 23796956394219517780110467)
              ·
                refine ⟨35695434591329276670165701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23796956394219517780110467 35695434591329276670165701)
                ·
                  refine ⟨6692893985874239375656069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35695434591329276670165701 6692893985874239375656069)
                  ·
                    refine ⟨1254917622351419882935513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6692893985874239375656069 1254917622351419882935513)
                    ·
                      rfl

theorem cell22_3665915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_3665915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665915 prefixEnd_3665915 := by exact prefixLift 3665915
  have htrace : WordTrace (prefixWord ++ tailWord_3665915) baseStart_3665915 baseEnd_3665915 := by
    simpa [prefixWord, tailWord_3665915, baseEnd_3665915] using wordTrace_append hprefix tailTrace_3665915
  have hstable : (prefixWord ++ tailWord_3665915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665915).length < 2 ^ (prefixWord ++ tailWord_3665915).sum := by decide
  have hdescent : baseEnd_3665915 < baseStart_3665915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665917 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_3665917 : Nat := 118140960795 + 3665917 * 2 ^ 59
def prefixEnd_3665917 : Nat := 4983230072969 + 3 ^ 40 * 3665917 * 2
def baseEnd_3665917 : Nat := 1254918306992292544385507

theorem tailTrace_3665917 : CollatzResearch.WordTrace tailWord_3665917 prefixEnd_3665917 1254918306992292544385507 := by
  unfold tailWord_3665917
  simp only [CollatzResearch.WordTrace]
  refine ⟨133706977460016272623236005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89137984973344181748824003 133706977460016272623236005)
  ·
    refine ⟨25070058273753051116856751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133706977460016272623236005 25070058273753051116856751)
    ·
      refine ⟨37605087410629576675285127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25070058273753051116856751 37605087410629576675285127)
      ·
        refine ⟨56407631115944365012927691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37605087410629576675285127 56407631115944365012927691)
        ·
          refine ⟨84611446673916547519391537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56407631115944365012927691 84611446673916547519391537)
          ·
            refine ⟨63458585005437410639543653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84611446673916547519391537 63458585005437410639543653)
            ·
              refine ⟨11898484688519514494914435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63458585005437410639543653 11898484688519514494914435)
              ·
                refine ⟨17847727032779271742371653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11898484688519514494914435 17847727032779271742371653)
                ·
                  refine ⟨3346448818646113451694685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17847727032779271742371653 3346448818646113451694685)
                  ·
                    refine ⟨1254918306992292544385507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346448818646113451694685 1254918306992292544385507)
                    ·
                      rfl

theorem cell22_3665917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_3665917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665917 prefixEnd_3665917 := by exact prefixLift 3665917
  have htrace : WordTrace (prefixWord ++ tailWord_3665917) baseStart_3665917 baseEnd_3665917 := by
    simpa [prefixWord, tailWord_3665917, baseEnd_3665917] using wordTrace_append hprefix tailTrace_3665917
  have hstable : (prefixWord ++ tailWord_3665917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665917).length < 2 ^ (prefixWord ++ tailWord_3665917).sum := by decide
  have hdescent : baseEnd_3665917 < baseStart_3665917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665934 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_3665934 : Nat := 118140960795 + 3665934 * 2 ^ 59
def prefixEnd_3665934 : Nat := 4983230072969 + 3 ^ 40 * 3665934 * 2
def baseEnd_3665934 : Nat := 1254924126439710166710455

theorem tailTrace_3665934 : CollatzResearch.WordTrace tailWord_3665934 prefixEnd_3665934 1254924126439710166710455 := by
  unfold tailWord_3665934
  simp only [CollatzResearch.WordTrace]
  refine ⟨16713449687619335565825607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89138398333969789684403237 16713449687619335565825607)
  ·
    refine ⟨25070174531429003348738411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16713449687619335565825607 25070174531429003348738411)
    ·
      refine ⟨37605261797143505023107617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25070174531429003348738411 37605261797143505023107617)
      ·
        refine ⟨28203946347857628767330713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37605261797143505023107617 28203946347857628767330713)
        ·
          refine ⟨21152959760893221575498035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28203946347857628767330713 21152959760893221575498035)
          ·
            refine ⟨31729439641339832363247053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21152959760893221575498035 31729439641339832363247053)
            ·
              refine ⟨11898539865502437136217645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31729439641339832363247053 11898539865502437136217645)
              ·
                refine ⟨4461952449563413926081617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11898539865502437136217645 4461952449563413926081617)
                ·
                  refine ⟨3346464337172560444561213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461952449563413926081617 3346464337172560444561213)
                  ·
                    refine ⟨1254924126439710166710455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346464337172560444561213 1254924126439710166710455)
                    ·
                      rfl

theorem cell22_3665934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_3665934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665934 prefixEnd_3665934 := by exact prefixLift 3665934
  have htrace : WordTrace (prefixWord ++ tailWord_3665934) baseStart_3665934 baseEnd_3665934 := by
    simpa [prefixWord, tailWord_3665934, baseEnd_3665934] using wordTrace_append hprefix tailTrace_3665934
  have hstable : (prefixWord ++ tailWord_3665934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665934).length < 2 ^ (prefixWord ++ tailWord_3665934).sum := by decide
  have hdescent : baseEnd_3665934 < baseStart_3665934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665949 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3665949 : Nat := 118140960795 + 3665949 * 2 ^ 59
def prefixEnd_3665949 : Nat := 4983230072969 + 3 ^ 40 * 3665949 * 2
def baseEnd_3665949 : Nat := 1254929261246255127585409

theorem tailTrace_3665949 : CollatzResearch.WordTrace tailWord_3665949 prefixEnd_3665949 1254929261246255127585409 := by
  unfold tailWord_3665949
  simp only [CollatzResearch.WordTrace]
  refine ⟨133708144595900342088400901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89138763063933561392267267 133708144595900342088400901)
  ·
    refine ⟨25070277111731314141575169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133708144595900342088400901 25070277111731314141575169)
    ·
      refine ⟨18802707833798485606181377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25070277111731314141575169 18802707833798485606181377)
      ·
        refine ⟨14102030875348864204636033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18802707833798485606181377 14102030875348864204636033)
        ·
          refine ⟨10576523156511648153477025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14102030875348864204636033 10576523156511648153477025)
          ·
            refine ⟨7932392367383736115107769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10576523156511648153477025 7932392367383736115107769)
            ·
              refine ⟨5949294275537802086330827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932392367383736115107769 5949294275537802086330827)
              ·
                refine ⟨8923941413306703129496241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949294275537802086330827 8923941413306703129496241)
                ·
                  refine ⟨6692956059980027347122181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923941413306703129496241 6692956059980027347122181)
                  ·
                    refine ⟨1254929261246255127585409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6692956059980027347122181 1254929261246255127585409)
                    ·
                      rfl

theorem cell22_3665949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3665949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665949 prefixEnd_3665949 := by exact prefixLift 3665949
  have htrace : WordTrace (prefixWord ++ tailWord_3665949) baseStart_3665949 baseEnd_3665949 := by
    simpa [prefixWord, tailWord_3665949, baseEnd_3665949] using wordTrace_append hprefix tailTrace_3665949
  have hstable : (prefixWord ++ tailWord_3665949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665949).length < 2 ^ (prefixWord ++ tailWord_3665949).sum := by decide
  have hdescent : baseEnd_3665949 < baseStart_3665949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665975 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 7]
def baseStart_3665975 : Nat := 118140960795 + 3665975 * 2 ^ 59
def prefixEnd_3665975 : Nat := 4983230072969 + 3 ^ 40 * 3665975 * 2
def baseEnd_3665975 : Nat := 418312720525866575478443

theorem tailTrace_3665975 : CollatzResearch.WordTrace tailWord_3665975 prefixEnd_3665975 418312720525866575478443 := by
  unfold tailWord_3665975
  simp only [CollatzResearch.WordTrace]
  refine ⟨133709092893806148528847379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89139395262537432352564919 133709092893806148528847379)
  ·
    refine ⟨200563639340709222793271069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133709092893806148528847379 200563639340709222793271069)
    ·
      refine ⟨75211364752765958547476651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200563639340709222793271069 75211364752765958547476651)
      ·
        refine ⟨112817047129148937821214977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75211364752765958547476651 112817047129148937821214977)
        ·
          refine ⟨84612785346861703365911233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112817047129148937821214977 84612785346861703365911233)
          ·
            refine ⟨63459589010146277524433425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84612785346861703365911233 63459589010146277524433425)
            ·
              refine ⟨47594691757609708143325069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63459589010146277524433425 47594691757609708143325069)
              ·
                refine ⟨17848009409103640553746901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47594691757609708143325069 17848009409103640553746901)
                ·
                  refine ⟨418312720525866575478443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17848009409103640553746901 418312720525866575478443)
                  ·
                    rfl

theorem cell22_3665975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_3665975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665975 prefixEnd_3665975 := by exact prefixLift 3665975
  have htrace : WordTrace (prefixWord ++ tailWord_3665975) baseStart_3665975 baseEnd_3665975 := by
    simpa [prefixWord, tailWord_3665975, baseEnd_3665975] using wordTrace_append hprefix tailTrace_3665975
  have hstable : (prefixWord ++ tailWord_3665975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665975).length < 2 ^ (prefixWord ++ tailWord_3665975).sum := by decide
  have hdescent : baseEnd_3665975 < baseStart_3665975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3665979 : List Nat := [1, 1, 1, 1, 1, 2, 1, 10, 1, 3]
def baseStart_3665979 : Nat := 118140960795 + 3665979 * 2 ^ 59
def prefixEnd_3665979 : Nat := 4983230072969 + 3 ^ 40 * 3665979 * 2
def baseEnd_3665979 : Nat := 1254939530859345049335317

theorem tailTrace_3665979 : CollatzResearch.WordTrace tailWord_3665979 prefixEnd_3665979 1254939530859345049335317 := by
  unfold tailWord_3665979
  simp only [CollatzResearch.WordTrace]
  refine ⟨133709238785791657211992991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89139492523861104807995327 133709238785791657211992991)
  ·
    refine ⟨200563858178687485817989487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133709238785791657211992991 200563858178687485817989487)
    ·
      refine ⟨300845787268031228726984231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200563858178687485817989487 300845787268031228726984231)
      ·
        refine ⟨451268680902046843090476347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300845787268031228726984231 451268680902046843090476347)
        ·
          refine ⟨676903021353070264635714521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451268680902046843090476347 676903021353070264635714521)
          ·
            refine ⟨507677266014802698476785891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676903021353070264635714521 507677266014802698476785891)
            ·
              refine ⟨761515899022204047715178837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507677266014802698476785891 761515899022204047715178837)
              ·
                refine ⟨2231003610416613421040563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 761515899022204047715178837 2231003610416613421040563)
                ·
                  refine ⟨3346505415624920131560845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231003610416613421040563 3346505415624920131560845)
                  ·
                    refine ⟨1254939530859345049335317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346505415624920131560845 1254939530859345049335317)
                    ·
                      rfl

theorem cell22_3665979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 10, 1, 3].length) (baseStart_3665979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3665979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3665979 prefixEnd_3665979 := by exact prefixLift 3665979
  have htrace : WordTrace (prefixWord ++ tailWord_3665979) baseStart_3665979 baseEnd_3665979 := by
    simpa [prefixWord, tailWord_3665979, baseEnd_3665979] using wordTrace_append hprefix tailTrace_3665979
  have hstable : (prefixWord ++ tailWord_3665979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3665979).length < 2 ^ (prefixWord ++ tailWord_3665979).sum := by decide
  have hdescent : baseEnd_3665979 < baseStart_3665979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3665979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666013 : List Nat := [1, 4, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3666013 : Nat := 118140960795 + 3666013 * 2 ^ 59
def prefixEnd_3666013 : Nat := 4983230072969 + 3 ^ 40 * 3666013 * 2
def baseEnd_3666013 : Nat := 1254951169754180293985213

theorem tailTrace_3666013 : CollatzResearch.WordTrace tailWord_3666013 prefixEnd_3666013 1254951169754180293985213 := by
  unfold tailWord_3666013
  simp only [CollatzResearch.WordTrace]
  refine ⟨133710478867668481018730693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89140319245112320679153795 133710478867668481018730693)
  ·
    refine ⟨25070714787687840191012005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133710478867668481018730693 25070714787687840191012005)
    ·
      refine ⟨4700759022691470035814751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25070714787687840191012005 4700759022691470035814751)
      ·
        refine ⟨7051138534037205053722127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4700759022691470035814751 7051138534037205053722127)
        ·
          refine ⟨10576707801055807580583191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051138534037205053722127 10576707801055807580583191)
          ·
            refine ⟨15865061701583711370874787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10576707801055807580583191 15865061701583711370874787)
            ·
              refine ⟨23797592552375567056312181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15865061701583711370874787 23797592552375567056312181)
              ·
                refine ⟨2231024301785209411529267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23797592552375567056312181 2231024301785209411529267)
                ·
                  refine ⟨3346536452677814117293901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231024301785209411529267 3346536452677814117293901)
                  ·
                    refine ⟨1254951169754180293985213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346536452677814117293901 1254951169754180293985213)
                    ·
                      rfl

theorem cell22_3666013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3666013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666013 prefixEnd_3666013 := by exact prefixLift 3666013
  have htrace : WordTrace (prefixWord ++ tailWord_3666013) baseStart_3666013 baseEnd_3666013 := by
    simpa [prefixWord, tailWord_3666013, baseEnd_3666013] using wordTrace_append hprefix tailTrace_3666013
  have hstable : (prefixWord ++ tailWord_3666013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666013).length < 2 ^ (prefixWord ++ tailWord_3666013).sum := by decide
  have hdescent : baseEnd_3666013 < baseStart_3666013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666026 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_3666026 : Nat := 118140960795 + 3666026 * 2 ^ 59
def prefixEnd_3666026 : Nat := 4983230072969 + 3 ^ 40 * 3666026 * 2
def baseEnd_3666026 : Nat := 418318539973284197803391

theorem tailTrace_3666026 : CollatzResearch.WordTrace tailWord_3666026 prefixEnd_3666026 418318539973284197803391 := by
  unfold tailWord_3666026
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427738254155346059738483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89140635344414256159302621 33427738254155346059738483)
  ·
    refine ⟨50141607381233019089607725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33427738254155346059738483 50141607381233019089607725)
    ·
      refine ⟨18803102767962382158602897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50141607381233019089607725 18803102767962382158602897)
      ·
        refine ⟨14102327075971786618952173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18803102767962382158602897 14102327075971786618952173)
        ·
          refine ⟨5288372653489419982107065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14102327075971786618952173 5288372653489419982107065)
          ·
            refine ⟨3966279490117064986580299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5288372653489419982107065 3966279490117064986580299)
            ·
              refine ⟨5949419235175597479870449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966279490117064986580299 5949419235175597479870449)
              ·
                refine ⟨4462064426381698109902837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949419235175597479870449 4462064426381698109902837)
                ·
                  refine ⟨418318539973284197803391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4462064426381698109902837 418318539973284197803391)
                  ·
                    rfl

theorem cell22_3666026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_3666026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666026 prefixEnd_3666026 := by exact prefixLift 3666026
  have htrace : WordTrace (prefixWord ++ tailWord_3666026) baseStart_3666026 baseEnd_3666026 := by
    simpa [prefixWord, tailWord_3666026, baseEnd_3666026] using wordTrace_append hprefix tailTrace_3666026
  have hstable : (prefixWord ++ tailWord_3666026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666026).length < 2 ^ (prefixWord ++ tailWord_3666026).sum := by decide
  have hdescent : baseEnd_3666026 < baseStart_3666026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666035 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_3666035 : Nat := 118140960795 + 3666035 * 2 ^ 59
def prefixEnd_3666035 : Nat := 4983230072969 + 3 ^ 40 * 3666035 * 2
def baseEnd_3666035 : Nat := 1254958700803779569935145

theorem tailTrace_3666035 : CollatzResearch.WordTrace tailWord_3666035 prefixEnd_3666035 1254958700803779569935145 := by
  unfold tailWord_3666035
  simp only [CollatzResearch.WordTrace]
  refine ⟨133711281273588778776031559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89140854182392519184021039 133711281273588778776031559)
  ·
    refine ⟨200566921910383168164047339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133711281273588778776031559 200566921910383168164047339)
    ·
      refine ⟨300850382865574752246071009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200566921910383168164047339 300850382865574752246071009)
      ·
        refine ⟨225637787149181064184553257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300850382865574752246071009 225637787149181064184553257)
        ·
          refine ⟨169228340361885798138414943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225637787149181064184553257 169228340361885798138414943)
          ·
            refine ⟨253842510542828697207622415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169228340361885798138414943 253842510542828697207622415)
            ·
              refine ⟨380763765814243045811433623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253842510542828697207622415 380763765814243045811433623)
              ·
                refine ⟨571145648721364568717150435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380763765814243045811433623 571145648721364568717150435)
                ·
                  refine ⟨856718473082046853075725653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571145648721364568717150435 856718473082046853075725653)
                  ·
                    refine ⟨1254958700803779569935145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 856718473082046853075725653 1254958700803779569935145)
                    ·
                      rfl

theorem cell22_3666035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_3666035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666035 prefixEnd_3666035 := by exact prefixLift 3666035
  have htrace : WordTrace (prefixWord ++ tailWord_3666035) baseStart_3666035 baseEnd_3666035 := by
    simpa [prefixWord, tailWord_3666035, baseEnd_3666035] using wordTrace_append hprefix tailTrace_3666035
  have hstable : (prefixWord ++ tailWord_3666035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666035).length < 2 ^ (prefixWord ++ tailWord_3666035).sum := by decide
  have hdescent : baseEnd_3666035 < baseStart_3666035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666056 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_3666056 : Nat := 118140960795 + 3666056 * 2 ^ 59
def prefixEnd_3666056 : Nat := 4983230072969 + 3 ^ 40 * 3666056 * 2
def baseEnd_3666056 : Nat := 1254965889532942515160081

theorem tailTrace_3666056 : CollatzResearch.WordTrace tailWord_3666056 prefixEnd_3666056 1254965889532942515160081 := by
  unfold tailWord_3666056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66856023603256349681273011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89141364804341799575030681 66856023603256349681273011)
  ·
    refine ⟨100284035404884524521909517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66856023603256349681273011 100284035404884524521909517)
    ·
      refine ⟨37606513276831696695716069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100284035404884524521909517 37606513276831696695716069)
      ·
        refine ⟨7051221239405943130446763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37606513276831696695716069 7051221239405943130446763)
        ·
          refine ⟨10576831859108914695670145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051221239405943130446763 10576831859108914695670145)
          ·
            refine ⟨7932623894331686021752609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10576831859108914695670145 7932623894331686021752609)
            ·
              refine ⟨5949467920748764516314457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932623894331686021752609 5949467920748764516314457)
              ·
                refine ⟨4462100940561573387235843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949467920748764516314457 4462100940561573387235843)
                ·
                  refine ⟨6693151410842360080853765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462100940561573387235843 6693151410842360080853765)
                  ·
                    refine ⟨1254965889532942515160081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693151410842360080853765 1254965889532942515160081)
                    ·
                      rfl

theorem cell22_3666056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_3666056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666056 prefixEnd_3666056 := by exact prefixLift 3666056
  have htrace : WordTrace (prefixWord ++ tailWord_3666056) baseStart_3666056 baseEnd_3666056 := by
    simpa [prefixWord, tailWord_3666056, baseEnd_3666056] using wordTrace_append hprefix tailTrace_3666056
  have hstable : (prefixWord ++ tailWord_3666056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666056).length < 2 ^ (prefixWord ++ tailWord_3666056).sum := by decide
  have hdescent : baseEnd_3666056 < baseStart_3666056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666067 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 2, 4]
def baseStart_3666067 : Nat := 118140960795 + 3666067 * 2 ^ 59
def prefixEnd_3666067 : Nat := 4983230072969 + 3 ^ 40 * 3666067 * 2
def baseEnd_3666067 : Nat := 1254969655057742153135047

theorem tailTrace_3666067 : CollatzResearch.WordTrace tailWord_3666067 prefixEnd_3666067 1254969655057742153135047 := by
  unfold tailWord_3666067
  simp only [CollatzResearch.WordTrace]
  refine ⟨133712448409472848241196455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89141632272981898827464303 133712448409472848241196455)
  ·
    refine ⟨200568672614209272361794683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133712448409472848241196455 200568672614209272361794683)
    ·
      refine ⟨300853008921313908542692025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200568672614209272361794683 300853008921313908542692025)
      ·
        refine ⟨225639756690985431407019019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300853008921313908542692025 225639756690985431407019019)
        ·
          refine ⟨338459635036478147110528529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225639756690985431407019019 338459635036478147110528529)
          ·
            refine ⟨253844726277358610332896397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338459635036478147110528529 253844726277358610332896397)
            ·
              refine ⟨95191772354009478874836149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253844726277358610332896397 95191772354009478874836149)
              ·
                refine ⟨8924228658188388644515889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95191772354009478874836149 8924228658188388644515889)
                ·
                  refine ⟨6693171493641291483386917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8924228658188388644515889 6693171493641291483386917)
                  ·
                    refine ⟨1254969655057742153135047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693171493641291483386917 1254969655057742153135047)
                    ·
                      rfl

theorem cell22_3666067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_3666067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666067 prefixEnd_3666067 := by exact prefixLift 3666067
  have htrace : WordTrace (prefixWord ++ tailWord_3666067) baseStart_3666067 baseEnd_3666067 := by
    simpa [prefixWord, tailWord_3666067, baseEnd_3666067] using wordTrace_append hprefix tailTrace_3666067
  have hstable : (prefixWord ++ tailWord_3666067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666067).length < 2 ^ (prefixWord ++ tailWord_3666067).sum := by decide
  have hdescent : baseEnd_3666067 < baseStart_3666067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666103 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 2, 3]
def baseStart_3666103 : Nat := 118140960795 + 3666103 * 2 ^ 59
def prefixEnd_3666103 : Nat := 4983230072969 + 3 ^ 40 * 3666103 * 2
def baseEnd_3666103 : Nat := 1254981978593450059234937

theorem tailTrace_3666103 : CollatzResearch.WordTrace tailWord_3666103 prefixEnd_3666103 1254981978593450059234937 := by
  unfold tailWord_3666103
  simp only [CollatzResearch.WordTrace]
  refine ⟨133713761437342426389506963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89142507624894950926337975 133713761437342426389506963)
  ·
    refine ⟨200570642156013639584260445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133713761437342426389506963 200570642156013639584260445)
    ·
      refine ⟨75213990808505114844097667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200570642156013639584260445 75213990808505114844097667)
      ·
        refine ⟨112820986212757672266146501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75213990808505114844097667 112820986212757672266146501)
        ·
          refine ⟨21153934914892063549902469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112820986212757672266146501 21153934914892063549902469)
          ·
            refine ⟨3966362796542261915606713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21153934914892063549902469 3966362796542261915606713)
            ·
              refine ⟨2974772097406696436705035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3966362796542261915606713 2974772097406696436705035)
              ·
                refine ⟨4462158146110044655057553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974772097406696436705035 4462158146110044655057553)
                ·
                  refine ⟨3346618609582533491293165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462158146110044655057553 3346618609582533491293165)
                  ·
                    refine ⟨1254981978593450059234937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346618609582533491293165 1254981978593450059234937)
                    ·
                      rfl

theorem cell22_3666103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_3666103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666103 prefixEnd_3666103 := by exact prefixLift 3666103
  have htrace : WordTrace (prefixWord ++ tailWord_3666103) baseStart_3666103 baseEnd_3666103 := by
    simpa [prefixWord, tailWord_3666103, baseEnd_3666103] using wordTrace_append hprefix tailTrace_3666103
  have hstable : (prefixWord ++ tailWord_3666103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666103).length < 2 ^ (prefixWord ++ tailWord_3666103).sum := by decide
  have hdescent : baseEnd_3666103 < baseStart_3666103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666144 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 5]
def baseStart_3666144 : Nat := 118140960795 + 3666144 * 2 ^ 59
def prefixEnd_3666144 : Nat := 4983230072969 + 3 ^ 40 * 3666144 * 2
def baseEnd_3666144 : Nat := 418332004577113206319937

theorem tailTrace_3666144 : CollatzResearch.WordTrace tailWord_3666144 prefixEnd_3666144 418332004577113206319937 := by
  unfold tailWord_3666144
  simp only [CollatzResearch.WordTrace]
  refine ⟨66857628415096945195874743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89143504553462593594499657 66857628415096945195874743)
  ·
    refine ⟨100286442622645417793812115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66857628415096945195874743 100286442622645417793812115)
    ·
      refine ⟨150429663933968126690718173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100286442622645417793812115 150429663933968126690718173)
      ·
        refine ⟨56411123975238047509019315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150429663933968126690718173 56411123975238047509019315)
        ·
          refine ⟨84616685962857071263528973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56411123975238047509019315 84616685962857071263528973)
          ·
            refine ⟨31731257236071401723823365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84616685962857071263528973 31731257236071401723823365)
            ·
              refine ⟨5949610731763387823216881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31731257236071401723823365 5949610731763387823216881)
              ·
                refine ⟨4462208048822540867412661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949610731763387823216881 4462208048822540867412661)
                ·
                  refine ⟨418332004577113206319937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4462208048822540867412661 418332004577113206319937)
                  ·
                    rfl

theorem cell22_3666144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_3666144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666144 prefixEnd_3666144 := by exact prefixLift 3666144
  have htrace : WordTrace (prefixWord ++ tailWord_3666144) baseStart_3666144 baseEnd_3666144 := by
    simpa [prefixWord, tailWord_3666144, baseEnd_3666144] using wordTrace_append hprefix tailTrace_3666144
  have hstable : (prefixWord ++ tailWord_3666144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666144).length < 2 ^ (prefixWord ++ tailWord_3666144).sum := by decide
  have hdescent : baseEnd_3666144 < baseStart_3666144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666159 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 2, 5]
def baseStart_3666159 : Nat := 118140960795 + 3666159 * 2 ^ 59
def prefixEnd_3666159 : Nat := 4983230072969 + 3 ^ 40 * 3666159 * 2
def baseEnd_3666159 : Nat := 1255001148537884579834765

theorem tailTrace_3666159 : CollatzResearch.WordTrace tailWord_3666159 prefixEnd_3666159 1255001148537884579834765 := by
  unfold tailWord_3666159
  simp only [CollatzResearch.WordTrace]
  refine ⟨133715803925139547953545531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89143869283426365302363687 133715803925139547953545531)
  ·
    refine ⟨200573705887709321930318297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133715803925139547953545531 200573705887709321930318297)
    ·
      refine ⟨150430279415781991447738723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200573705887709321930318297 150430279415781991447738723)
      ·
        refine ⟨225645419123672987171608085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150430279415781991447738723 225645419123672987171608085)
        ·
          refine ⟨10577129021422171273669129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225645419123672987171608085 10577129021422171273669129)
          ·
            refine ⟨7932846766066628455251847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577129021422171273669129 7932846766066628455251847)
            ·
              refine ⟨11899270149099942682877771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932846766066628455251847 11899270149099942682877771)
              ·
                refine ⟨17848905223649914024316657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899270149099942682877771 17848905223649914024316657)
                ·
                  refine ⟨13386678917737435518237493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17848905223649914024316657 13386678917737435518237493)
                  ·
                    refine ⟨1255001148537884579834765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13386678917737435518237493 1255001148537884579834765)
                    ·
                      rfl

theorem cell22_3666159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_3666159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666159 prefixEnd_3666159 := by exact prefixLift 3666159
  have htrace : WordTrace (prefixWord ++ tailWord_3666159) baseStart_3666159 baseEnd_3666159 := by
    simpa [prefixWord, tailWord_3666159, baseEnd_3666159] using wordTrace_append hprefix tailTrace_3666159
  have hstable : (prefixWord ++ tailWord_3666159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666159).length < 2 ^ (prefixWord ++ tailWord_3666159).sum := by decide
  have hdescent : baseEnd_3666159 < baseStart_3666159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666234 : List Nat := [3, 1, 1, 1, 4, 3, 1, 8]
def baseStart_3666234 : Nat := 118140960795 + 3666234 * 2 ^ 59
def prefixEnd_3666234 : Nat := 4983230072969 + 3 ^ 40 * 3666234 * 2
def baseEnd_3666234 : Nat := 139447424730067709356615

theorem tailTrace_3666234 : CollatzResearch.WordTrace tailWord_3666234 prefixEnd_3666234 139447424730067709356615 := by
  unfold tailWord_3666234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33429634849966958940631439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89145692933245223841683837 33429634849966958940631439)
  ·
    refine ⟨50144452274950438410947159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33429634849966958940631439 50144452274950438410947159)
    ·
      refine ⟨75216678412425657616420739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50144452274950438410947159 75216678412425657616420739)
      ·
        refine ⟨112825017618638486424631109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75216678412425657616420739 112825017618638486424631109)
        ·
          refine ⟨21154690803494716204618333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112825017618638486424631109 21154690803494716204618333)
          ·
            refine ⟨7933009051310518576731875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21154690803494716204618333 7933009051310518576731875)
            ·
              refine ⟨11899513576965777865097813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7933009051310518576731875 11899513576965777865097813)
              ·
                refine ⟨139447424730067709356615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11899513576965777865097813 139447424730067709356615)
                ·
                  rfl

theorem cell22_3666234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_3666234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666234 prefixEnd_3666234 := by exact prefixLift 3666234
  have htrace : WordTrace (prefixWord ++ tailWord_3666234) baseStart_3666234 baseEnd_3666234 := by
    simpa [prefixWord, tailWord_3666234, baseEnd_3666234] using wordTrace_append hprefix tailTrace_3666234
  have hstable : (prefixWord ++ tailWord_3666234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666234).length < 2 ^ (prefixWord ++ tailWord_3666234).sum := by decide
  have hdescent : baseEnd_3666234 < baseStart_3666234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666268 : List Nat := [2, 2, 4, 3, 1, 1, 2, 7]
def baseStart_3666268 : Nat := 118140960795 + 3666268 * 2 ^ 59
def prefixEnd_3666268 : Nat := 4983230072969 + 3 ^ 40 * 3666268 * 2
def baseEnd_3666268 : Nat := 139448717940604958762159

theorem tailTrace_3666268 : CollatzResearch.WordTrace tailWord_3666268 prefixEnd_3666268 139448717940604958762159 := by
  unfold tailWord_3666268
  simp only [CollatzResearch.WordTrace]
  refine ⟨66859889740872329784631729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89146519654496439712842305 66859889740872329784631729)
  ·
    refine ⟨50144917305654247338473797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66859889740872329784631729 50144917305654247338473797)
    ·
      refine ⟨9402171994810171375963837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50144917305654247338473797 9402171994810171375963837)
      ·
        refine ⟨3525814498053814265986439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9402171994810171375963837 3525814498053814265986439)
        ·
          refine ⟨5288721747080721398979659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525814498053814265986439 5288721747080721398979659)
          ·
            refine ⟨7933082620621082098469489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288721747080721398979659 7933082620621082098469489)
            ·
              refine ⟨5949811965465811573852117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7933082620621082098469489 5949811965465811573852117)
              ·
                refine ⟨139448717940604958762159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5949811965465811573852117 139448717940604958762159)
                ·
                  rfl

theorem cell22_3666268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 7].length) (baseStart_3666268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666268 prefixEnd_3666268 := by exact prefixLift 3666268
  have htrace : WordTrace (prefixWord ++ tailWord_3666268) baseStart_3666268 baseEnd_3666268 := by
    simpa [prefixWord, tailWord_3666268, baseEnd_3666268] using wordTrace_append hprefix tailTrace_3666268
  have hstable : (prefixWord ++ tailWord_3666268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666268).length < 2 ^ (prefixWord ++ tailWord_3666268).sum := by decide
  have hdescent : baseEnd_3666268 < baseStart_3666268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666272 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 2, 3]
def baseStart_3666272 : Nat := 118140960795 + 3666272 * 2 ^ 59
def prefixEnd_3666272 : Nat := 4983230072969 + 3 ^ 40 * 3666272 * 2
def baseEnd_3666272 : Nat := 1255039830747189951759419

theorem tailTrace_3666272 : CollatzResearch.WordTrace tailWord_3666272 prefixEnd_3666272 1255039830747189951759419 := by
  unfold tailWord_3666272
  simp only [CollatzResearch.WordTrace]
  refine ⟨66859962686865084126204535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89146616915820112168272713 66859962686865084126204535)
  ·
    refine ⟨100289944030297626189306803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66859962686865084126204535 100289944030297626189306803)
    ·
      refine ⟨150434916045446439283960205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100289944030297626189306803 150434916045446439283960205)
      ·
        refine ⟨56413093517042414731485077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150434916045446439283960205 56413093517042414731485077)
        ·
          refine ⟨2644363758611363190538363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56413093517042414731485077 2644363758611363190538363)
          ·
            refine ⟨3966545637917044785807545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644363758611363190538363 3966545637917044785807545)
            ·
              refine ⟨2974909228437783589355659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3966545637917044785807545 2974909228437783589355659)
              ·
                refine ⟨4462363842656675384033489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974909228437783589355659 4462363842656675384033489)
                ·
                  refine ⟨3346772881992506538025117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462363842656675384033489 3346772881992506538025117)
                  ·
                    refine ⟨1255039830747189951759419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346772881992506538025117 1255039830747189951759419)
                    ·
                      rfl

theorem cell22_3666272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_3666272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666272 prefixEnd_3666272 := by exact prefixLift 3666272
  have htrace : WordTrace (prefixWord ++ tailWord_3666272) baseStart_3666272 baseEnd_3666272 := by
    simpa [prefixWord, tailWord_3666272, baseEnd_3666272] using wordTrace_append hprefix tailTrace_3666272
  have hstable : (prefixWord ++ tailWord_3666272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666272).length < 2 ^ (prefixWord ++ tailWord_3666272).sum := by decide
  have hdescent : baseEnd_3666272 < baseStart_3666272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666384 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_3666384 : Nat := 118140960795 + 3666384 * 2 ^ 59
def prefixEnd_3666384 : Nat := 4983230072969 + 3 ^ 40 * 3666384 * 2
def baseEnd_3666384 : Nat := 1255078170636058992959075

theorem tailTrace_3666384 : CollatzResearch.WordTrace tailWord_3666384 prefixEnd_3666384 1255078170636058992959075 := by
  unfold tailWord_3666384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66862005174662205690243103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89149340232882940920324137 66862005174662205690243103)
  ·
    refine ⟨100293007761993308535364655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66862005174662205690243103 100293007761993308535364655)
    ·
      refine ⟨150439511642989962803046983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100293007761993308535364655 150439511642989962803046983)
      ·
        refine ⟨225659267464484944204570475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150439511642989962803046983 225659267464484944204570475)
        ·
          refine ⟨338488901196727416306855713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225659267464484944204570475 338488901196727416306855713)
          ·
            refine ⟨253866675897545562230141785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338488901196727416306855713 253866675897545562230141785)
            ·
              refine ⟨190400006923159171672606339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253866675897545562230141785 190400006923159171672606339)
              ·
                refine ⟨285600010384738757508909509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190400006923159171672606339 285600010384738757508909509)
                ·
                  refine ⟨53550001947138517032920533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285600010384738757508909509 53550001947138517032920533)
                  ·
                    refine ⟨1255078170636058992959075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53550001947138517032920533 1255078170636058992959075)
                    ·
                      rfl

theorem cell22_3666384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_3666384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666384 prefixEnd_3666384 := by exact prefixLift 3666384
  have htrace : WordTrace (prefixWord ++ tailWord_3666384) baseStart_3666384 baseEnd_3666384 := by
    simpa [prefixWord, tailWord_3666384, baseEnd_3666384] using wordTrace_append hprefix tailTrace_3666384
  have hstable : (prefixWord ++ tailWord_3666384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666384).length < 2 ^ (prefixWord ++ tailWord_3666384).sum := by decide
  have hdescent : baseEnd_3666384 < baseStart_3666384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666431 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 5]
def baseStart_3666431 : Nat := 118140960795 + 3666431 * 2 ^ 59
def prefixEnd_3666431 : Nat := 4983230072969 + 3 ^ 40 * 3666431 * 2
def baseEnd_3666431 : Nat := 418364753232188845677977

theorem tailTrace_3666431 : CollatzResearch.WordTrace tailWord_3666431 prefixEnd_3666431 418364753232188845677977 := by
  unfold tailWord_3666431
  simp only [CollatzResearch.WordTrace]
  refine ⟨133725724580154138407447147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89150483053436092271631431 133725724580154138407447147)
  ·
    refine ⟨200588586870231207611170721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133725724580154138407447147 200588586870231207611170721)
    ·
      refine ⟨150441440152673405708378041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200588586870231207611170721 150441440152673405708378041)
      ·
        refine ⟨112831080114505054281283531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150441440152673405708378041 112831080114505054281283531)
        ·
          refine ⟨169246620171757581421925297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112831080114505054281283531 169246620171757581421925297)
          ·
            refine ⟨126934965128818186066443973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169246620171757581421925297 126934965128818186066443973)
            ·
              refine ⟨23800305961653409887458245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126934965128818186066443973 23800305961653409887458245)
              ·
                refine ⟨4462557367810014353898421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23800305961653409887458245 4462557367810014353898421)
                ·
                  refine ⟨418364753232188845677977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4462557367810014353898421 418364753232188845677977)
                  ·
                    rfl

theorem cell22_3666431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 5].length) (baseStart_3666431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666431 prefixEnd_3666431 := by exact prefixLift 3666431
  have htrace : WordTrace (prefixWord ++ tailWord_3666431) baseStart_3666431 baseEnd_3666431 := by
    simpa [prefixWord, tailWord_3666431, baseEnd_3666431] using wordTrace_append hprefix tailTrace_3666431
  have hstable : (prefixWord ++ tailWord_3666431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666431).length < 2 ^ (prefixWord ++ tailWord_3666431).sum := by decide
  have hdescent : baseEnd_3666431 < baseStart_3666431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666486 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3666486 : Nat := 118140960795 + 3666486 * 2 ^ 59
def prefixEnd_3666486 : Nat := 4983230072969 + 3 ^ 40 * 3666486 * 2
def baseEnd_3666486 : Nat := 1255113087320564726908763

theorem tailTrace_3666486 : CollatzResearch.WordTrace tailWord_3666486 prefixEnd_3666486 1255113087320564726908763 := by
  unfold tailWord_3666486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357983162184680175043707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89151820396636588533799541 8357983162184680175043707)
  ·
    refine ⟨12536974743277020262565561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357983162184680175043707 12536974743277020262565561)
    ·
      refine ⟨9402731057457765196924171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12536974743277020262565561 9402731057457765196924171)
      ·
        refine ⟨14104096586186647795386257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402731057457765196924171 14104096586186647795386257)
        ·
          refine ⟨10578072439639985846539693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14104096586186647795386257 10578072439639985846539693)
          ·
            refine ⟨3966777164864994692452385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10578072439639985846539693 3966777164864994692452385)
            ·
              refine ⟨2975082873648746019339289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3966777164864994692452385 2975082873648746019339289)
              ·
                refine ⟨2231312155236559514504467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975082873648746019339289 2231312155236559514504467)
                ·
                  refine ⟨3346968232854839271756701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231312155236559514504467 3346968232854839271756701)
                  ·
                    refine ⟨1255113087320564726908763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346968232854839271756701 1255113087320564726908763)
                    ·
                      rfl

theorem cell22_3666486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3666486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666486 prefixEnd_3666486 := by exact prefixLift 3666486
  have htrace : WordTrace (prefixWord ++ tailWord_3666486) baseStart_3666486 baseEnd_3666486 := by
    simpa [prefixWord, tailWord_3666486, baseEnd_3666486] using wordTrace_append hprefix tailTrace_3666486
  have hstable : (prefixWord ++ tailWord_3666486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666486).length < 2 ^ (prefixWord ++ tailWord_3666486).sum := by decide
  have hdescent : baseEnd_3666486 < baseStart_3666486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666508 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_3666508 : Nat := 118140960795 + 3666508 * 2 ^ 59
def prefixEnd_3666508 : Nat := 4983230072969 + 3 ^ 40 * 3666508 * 2
def baseEnd_3666508 : Nat := 1255120618370164002858695

theorem tailTrace_3666508 : CollatzResearch.WordTrace tailWord_3666508 prefixEnd_3666508 1255120618370164002858695 := by
  unfold tailWord_3666508
  simp only [CollatzResearch.WordTrace]
  refine ⟨66864266500437590279000089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89152355333916787038666785 66864266500437590279000089)
  ·
    refine ⟨50148199875328192709250067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66864266500437590279000089 50148199875328192709250067)
    ·
      refine ⟨75222299812992289063875101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50148199875328192709250067 75222299812992289063875101)
      ·
        refine ⟨28208362429872108398953163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75222299812992289063875101 28208362429872108398953163)
        ·
          refine ⟨42312543644808162598429745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28208362429872108398953163 42312543644808162598429745)
          ·
            refine ⟨31734407733606121948822309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42312543644808162598429745 31734407733606121948822309)
            ·
              refine ⟨5950201450051147865404183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31734407733606121948822309 5950201450051147865404183)
              ·
                refine ⟨8925302175076721798106275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950201450051147865404183 8925302175076721798106275)
                ·
                  refine ⟨13387953262615082697159413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8925302175076721798106275 13387953262615082697159413)
                  ·
                    refine ⟨1255120618370164002858695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13387953262615082697159413 1255120618370164002858695)
                    ·
                      rfl

theorem cell22_3666508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_3666508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666508 prefixEnd_3666508 := by exact prefixLift 3666508
  have htrace : WordTrace (prefixWord ++ tailWord_3666508) baseStart_3666508 baseEnd_3666508 := by
    simpa [prefixWord, tailWord_3666508, baseEnd_3666508] using wordTrace_append hprefix tailTrace_3666508
  have hstable : (prefixWord ++ tailWord_3666508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666508).length < 2 ^ (prefixWord ++ tailWord_3666508).sum := by decide
  have hdescent : baseEnd_3666508 < baseStart_3666508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666542 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3666542 : Nat := 118140960795 + 3666542 * 2 ^ 59
def prefixEnd_3666542 : Nat := 4983230072969 + 3 ^ 40 * 3666542 * 2
def baseEnd_3666542 : Nat := 1255132257264999247508591

theorem tailTrace_3666542 : CollatzResearch.WordTrace tailWord_3666542 prefixEnd_3666542 1255132257264999247508591 := by
  unfold tailWord_3666542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16716221635344000545592235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89153182055168002909825253 16716221635344000545592235)
  ·
    refine ⟨25074332453016000818388353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16716221635344000545592235 25074332453016000818388353)
    ·
      refine ⟨18805749339762000613791265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25074332453016000818388353 18805749339762000613791265)
      ·
        refine ⟨14104312004821500460343449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18805749339762000613791265 14104312004821500460343449)
        ·
          refine ⟨10578234003616125345257587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14104312004821500460343449 10578234003616125345257587)
          ·
            refine ⟨15867351005424188017886381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10578234003616125345257587 15867351005424188017886381)
            ·
              refine ⟨5950256627034070506707393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15867351005424188017886381 5950256627034070506707393)
              ·
                refine ⟨4462692470275552880030545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950256627034070506707393 4462692470275552880030545)
                ·
                  refine ⟨3347019352706664660022909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462692470275552880030545 3347019352706664660022909)
                  ·
                    refine ⟨1255132257264999247508591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347019352706664660022909 1255132257264999247508591)
                    ·
                      rfl

theorem cell22_3666542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3666542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666542 prefixEnd_3666542 := by exact prefixLift 3666542
  have htrace : WordTrace (prefixWord ++ tailWord_3666542) baseStart_3666542 baseEnd_3666542 := by
    simpa [prefixWord, tailWord_3666542, baseEnd_3666542] using wordTrace_append hprefix tailTrace_3666542
  have hstable : (prefixWord ++ tailWord_3666542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666542).length < 2 ^ (prefixWord ++ tailWord_3666542).sum := by decide
  have hdescent : baseEnd_3666542 < baseStart_3666542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666551 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_3666551 : Nat := 118140960795 + 3666551 * 2 ^ 59
def prefixEnd_3666551 : Nat := 4983230072969 + 3 ^ 40 * 3666551 * 2
def baseEnd_3666551 : Nat := 1255135338148926224033563

theorem tailTrace_3666551 : CollatzResearch.WordTrace tailWord_3666551 prefixEnd_3666551 1255135338148926224033563 := by
  unfold tailWord_3666551
  simp only [CollatzResearch.WordTrace]
  refine ⟨133730101339719398901815507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89153400893146265934543671 133730101339719398901815507)
  ·
    refine ⟨200595152009579098352723261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133730101339719398901815507 200595152009579098352723261)
    ·
      refine ⟨75223182003592161882271223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200595152009579098352723261 75223182003592161882271223)
      ·
        refine ⟨112834773005388242823406835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75223182003592161882271223 112834773005388242823406835)
        ·
          refine ⟨169252159508082364235110253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112834773005388242823406835 169252159508082364235110253)
          ·
            refine ⟨63469559815530886588166345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169252159508082364235110253 63469559815530886588166345)
            ·
              refine ⟨47602169861648164941124759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63469559815530886588166345 47602169861648164941124759)
              ·
                refine ⟨71403254792472247411687139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47602169861648164941124759 71403254792472247411687139)
                ·
                  refine ⟨107104882188708371117530709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71403254792472247411687139 107104882188708371117530709)
                  ·
                    refine ⟨1255135338148926224033563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107104882188708371117530709 1255135338148926224033563)
                    ·
                      rfl

theorem cell22_3666551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_3666551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666551 prefixEnd_3666551 := by exact prefixLift 3666551
  have htrace : WordTrace (prefixWord ++ tailWord_3666551) baseStart_3666551 baseEnd_3666551 := by
    simpa [prefixWord, tailWord_3666551, baseEnd_3666551] using wordTrace_append hprefix tailTrace_3666551
  have hstable : (prefixWord ++ tailWord_3666551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666551).length < 2 ^ (prefixWord ++ tailWord_3666551).sum := by decide
  have hdescent : baseEnd_3666551 < baseStart_3666551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666647 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 1, 4]
def baseStart_3666647 : Nat := 118140960795 + 3666647 * 2 ^ 59
def prefixEnd_3666647 : Nat := 4983230072969 + 3 ^ 40 * 3666647 * 2
def baseEnd_3666647 : Nat := 1255168200910813973633269

theorem tailTrace_3666647 : CollatzResearch.WordTrace tailWord_3666647 prefixEnd_3666647 1255168200910813973633269 := by
  unfold tailWord_3666647
  simp only [CollatzResearch.WordTrace]
  refine ⟨133733602747371607297310195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89155735164914404864873463 133733602747371607297310195)
  ·
    refine ⟨200600404121057410945965293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133733602747371607297310195 200600404121057410945965293)
    ·
      refine ⟨75225151545396529104736985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200600404121057410945965293 75225151545396529104736985)
      ·
        refine ⟨56418863659047396828552739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75225151545396529104736985 56418863659047396828552739)
        ·
          refine ⟨84628295488571095242829109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56418863659047396828552739 84628295488571095242829109)
          ·
            refine ⟨7933902702053540179015229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84628295488571095242829109 7933902702053540179015229)
            ·
              refine ⟨2975213513270077567130711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7933902702053540179015229 2975213513270077567130711)
              ·
                refine ⟨4462820269905116350696067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975213513270077567130711 4462820269905116350696067)
                ·
                  refine ⟨6694230404857674526044101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462820269905116350696067 6694230404857674526044101)
                  ·
                    refine ⟨1255168200910813973633269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694230404857674526044101 1255168200910813973633269)
                    ·
                      rfl

theorem cell22_3666647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_3666647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666647 prefixEnd_3666647 := by exact prefixLift 3666647
  have htrace : WordTrace (prefixWord ++ tailWord_3666647) baseStart_3666647 baseEnd_3666647 := by
    simpa [prefixWord, tailWord_3666647, baseEnd_3666647] using wordTrace_append hprefix tailTrace_3666647
  have hstable : (prefixWord ++ tailWord_3666647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666647).length < 2 ^ (prefixWord ++ tailWord_3666647).sum := by decide
  have hdescent : baseEnd_3666647 < baseStart_3666647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666711 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 2, 3]
def baseStart_3666711 : Nat := 118140960795 + 3666711 * 2 ^ 59
def prefixEnd_3666711 : Nat := 4983230072969 + 3 ^ 40 * 3666711 * 2
def baseEnd_3666711 : Nat := 1255190109418739140033073

theorem tailTrace_3666711 : CollatzResearch.WordTrace tailWord_3666711 prefixEnd_3666711 1255190109418739140033073 := by
  unfold tailWord_3666711
  simp only [CollatzResearch.WordTrace]
  refine ⟨133735937019139746227639987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89157291346093164151759991 133735937019139746227639987)
  ·
    refine ⟨200603905528709619341459981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133735937019139746227639987 200603905528709619341459981)
    ·
      refine ⟨75226464573266107253047493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200603905528709619341459981 75226464573266107253047493)
      ·
        refine ⟨14104962107487395109946405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75226464573266107253047493 14104962107487395109946405)
        ·
          refine ⟨2644680395153886583114951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14104962107487395109946405 2644680395153886583114951)
          ·
            refine ⟨3967020592730829874672427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644680395153886583114951 3967020592730829874672427)
            ·
              refine ⟨5950530889096244812008641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967020592730829874672427 5950530889096244812008641)
              ·
                refine ⟨4462898166822183609006481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950530889096244812008641 4462898166822183609006481)
                ·
                  refine ⟨3347173625116637706754861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4462898166822183609006481 3347173625116637706754861)
                  ·
                    refine ⟨1255190109418739140033073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347173625116637706754861 1255190109418739140033073)
                    ·
                      rfl

theorem cell22_3666711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_3666711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666711 prefixEnd_3666711 := by exact prefixLift 3666711
  have htrace : WordTrace (prefixWord ++ tailWord_3666711) baseStart_3666711 baseEnd_3666711 := by
    simpa [prefixWord, tailWord_3666711, baseEnd_3666711] using wordTrace_append hprefix tailTrace_3666711
  have hstable : (prefixWord ++ tailWord_3666711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666711).length < 2 ^ (prefixWord ++ tailWord_3666711).sum := by decide
  have hdescent : baseEnd_3666711 < baseStart_3666711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666722 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3666722 : Nat := 118140960795 + 3666722 * 2 ^ 59
def prefixEnd_3666722 : Nat := 4983230072969 + 3 ^ 40 * 3666722 * 2
def baseEnd_3666722 : Nat := 1255193874943538778008039

theorem tailTrace_3666722 : CollatzResearch.WordTrace tailWord_3666722 prefixEnd_3666722 1255193874943538778008039 := by
  unfold tailWord_3666722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33434084555524973776572605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89157558814733263404193613 33434084555524973776572605)
  ·
    refine ⟨12537781708321865166214727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33434084555524973776572605 12537781708321865166214727)
    ·
      refine ⟨18806672562482797749322091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12537781708321865166214727 18806672562482797749322091)
      ·
        refine ⟨28210008843724196623983137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18806672562482797749322091 28210008843724196623983137)
        ·
          refine ⟨21157506632793147467987353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28210008843724196623983137 21157506632793147467987353)
          ·
            refine ⟨15868129974594860600990515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21157506632793147467987353 15868129974594860600990515)
            ·
              refine ⟨23802194961892290901485773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15868129974594860600990515 23802194961892290901485773)
              ·
                refine ⟨8925823110709609088057165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23802194961892290901485773 8925823110709609088057165)
                ·
                  refine ⟨3347183666516103408021437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8925823110709609088057165 3347183666516103408021437)
                  ·
                    refine ⟨1255193874943538778008039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347183666516103408021437 1255193874943538778008039)
                    ·
                      rfl

theorem cell22_3666722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3666722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666722 prefixEnd_3666722 := by exact prefixLift 3666722
  have htrace : WordTrace (prefixWord ++ tailWord_3666722) baseStart_3666722 baseEnd_3666722 := by
    simpa [prefixWord, tailWord_3666722, baseEnd_3666722] using wordTrace_append hprefix tailTrace_3666722
  have hstable : (prefixWord ++ tailWord_3666722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666722).length < 2 ^ (prefixWord ++ tailWord_3666722).sum := by decide
  have hdescent : baseEnd_3666722 < baseStart_3666722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666786 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3666786 : Nat := 118140960795 + 3666786 * 2 ^ 59
def prefixEnd_3666786 : Nat := 4983230072969 + 3 ^ 40 * 3666786 * 2
def baseEnd_3666786 : Nat := 418405261150487981469281

theorem tailTrace_3666786 : CollatzResearch.WordTrace tailWord_3666786 prefixEnd_3666786 418405261150487981469281 := by
  unfold tailWord_3666786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33434668123467008509155053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89159114995912022691080141 33434668123467008509155053)
  ·
    refine ⟨12538000546300128190933145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33434668123467008509155053 12538000546300128190933145)
    ·
      refine ⟨9403500409725096143199859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12538000546300128190933145 9403500409725096143199859)
      ·
        refine ⟨14105250614587644214799789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9403500409725096143199859 14105250614587644214799789)
        ·
          refine ⟨5289468980470366580549921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14105250614587644214799789 5289468980470366580549921)
          ·
            refine ⟨3967101735352774935412441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5289468980470366580549921 3967101735352774935412441)
            ·
              refine ⟨2975326301514581201559331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3967101735352774935412441 2975326301514581201559331)
              ·
                refine ⟨4462989452271871802338997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975326301514581201559331 4462989452271871802338997)
                ·
                  refine ⟨418405261150487981469281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4462989452271871802338997 418405261150487981469281)
                  ·
                    rfl

theorem cell22_3666786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3666786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666786 prefixEnd_3666786 := by exact prefixLift 3666786
  have htrace : WordTrace (prefixWord ++ tailWord_3666786) baseStart_3666786 baseEnd_3666786 := by
    simpa [prefixWord, tailWord_3666786, baseEnd_3666786] using wordTrace_append hprefix tailTrace_3666786
  have hstable : (prefixWord ++ tailWord_3666786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666786).length < 2 ^ (prefixWord ++ tailWord_3666786).sum := by decide
  have hdescent : baseEnd_3666786 < baseStart_3666786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666857 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 3, 3]
def baseStart_3666857 : Nat := 118140960795 + 3666857 * 2 ^ 59
def prefixEnd_3666857 : Nat := 4983230072969 + 3 ^ 40 * 3666857 * 2
def baseEnd_3666857 : Nat := 1255240088202443425882625

theorem tailTrace_3666857 : CollatzResearch.WordTrace tailWord_3666857 prefixEnd_3666857 1255240088202443425882625 := by
  unfold tailWord_3666857
  simp only [CollatzResearch.WordTrace]
  refine ⟨133741262076610813162454825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89160841384407208774969883 133741262076610813162454825)
  ·
    refine ⟨100305946557458109871841119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133741262076610813162454825 100305946557458109871841119)
    ·
      refine ⟨150458919836187164807761679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100305946557458109871841119 150458919836187164807761679)
      ·
        refine ⟨225688379754280747211642519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150458919836187164807761679 225688379754280747211642519)
        ·
          refine ⟨338532569631421120817463779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225688379754280747211642519 338532569631421120817463779)
          ·
            refine ⟨507798854447131681226195669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338532569631421120817463779 507798854447131681226195669)
            ·
              refine ⟨11901535651104648778738961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 507798854447131681226195669 11901535651104648778738961)
              ·
                refine ⟨8926151738328486584054221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11901535651104648778738961 8926151738328486584054221)
                ·
                  refine ⟨3347306901873182469020333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8926151738328486584054221 3347306901873182469020333)
                  ·
                    refine ⟨1255240088202443425882625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347306901873182469020333 1255240088202443425882625)
                    ·
                      rfl

theorem cell22_3666857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_3666857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666857 prefixEnd_3666857 := by exact prefixLift 3666857
  have htrace : WordTrace (prefixWord ++ tailWord_3666857) baseStart_3666857 baseEnd_3666857 := by
    simpa [prefixWord, tailWord_3666857, baseEnd_3666857] using wordTrace_append hprefix tailTrace_3666857
  have hstable : (prefixWord ++ tailWord_3666857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666857).length < 2 ^ (prefixWord ++ tailWord_3666857).sum := by decide
  have hdescent : baseEnd_3666857 < baseStart_3666857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666887 : List Nat := [1, 1, 4, 1, 1, 2, 5, 2, 5]
def baseStart_3666887 : Nat := 118140960795 + 3666887 * 2 ^ 59
def prefixEnd_3666887 : Nat := 4983230072969 + 3 ^ 40 * 3666887 * 2
def baseEnd_3666887 : Nat := 418416785938511115877511

theorem tailTrace_3666887 : CollatzResearch.WordTrace tailWord_3666887 prefixEnd_3666887 418416785938511115877511 := by
  unfold tailWord_3666887
  simp only [CollatzResearch.WordTrace]
  refine ⟨133742356266502128286046915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89161570844334752190697943 133742356266502128286046915)
  ·
    refine ⟨200613534399753192429070373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133742356266502128286046915 200613534399753192429070373)
    ·
      refine ⟨37615037699953723580450695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200613534399753192429070373 37615037699953723580450695)
      ·
        refine ⟨56422556549930585370676043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37615037699953723580450695 56422556549930585370676043)
        ·
          refine ⟨84633834824895878056014065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56422556549930585370676043 84633834824895878056014065)
          ·
            refine ⟨63475376118671908542010549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84633834824895878056014065 63475376118671908542010549)
            ·
              refine ⟨5950816511125491425813489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63475376118671908542010549 5950816511125491425813489)
              ·
                refine ⟨4463112383344118569360117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950816511125491425813489 4463112383344118569360117)
                ·
                  refine ⟨418416785938511115877511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4463112383344118569360117 418416785938511115877511)
                  ·
                    rfl

theorem cell22_3666887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 2, 5].length) (baseStart_3666887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666887 prefixEnd_3666887 := by exact prefixLift 3666887
  have htrace : WordTrace (prefixWord ++ tailWord_3666887) baseStart_3666887 baseEnd_3666887 := by
    simpa [prefixWord, tailWord_3666887, baseEnd_3666887] using wordTrace_append hprefix tailTrace_3666887
  have hstable : (prefixWord ++ tailWord_3666887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666887).length < 2 ^ (prefixWord ++ tailWord_3666887).sum := by decide
  have hdescent : baseEnd_3666887 < baseStart_3666887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666904 : List Nat := [2, 1, 2, 2, 2, 4, 3, 1, 5]
def baseStart_3666904 : Nat := 118140960795 + 3666904 * 2 ^ 59
def prefixEnd_3666904 : Nat := 4983230072969 + 3 ^ 40 * 3666904 * 2
def baseEnd_3666904 : Nat := 418418725754316989985827

theorem tailTrace_3666904 : CollatzResearch.WordTrace tailWord_3666904 prefixEnd_3666904 418418725754316989985827 := by
  unfold tailWord_3666904
  simp only [CollatzResearch.WordTrace]
  refine ⟨66871488153720270094707883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89161984204960360126277177 66871488153720270094707883)
  ·
    refine ⟨100307232230580405142061825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66871488153720270094707883 100307232230580405142061825)
    ·
      refine ⟨75230424172935303856546369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100307232230580405142061825 75230424172935303856546369)
      ·
        refine ⟨56422818129701477892409777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75230424172935303856546369 56422818129701477892409777)
        ·
          refine ⟨42317113597276108419307333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56422818129701477892409777 42317113597276108419307333)
          ·
            refine ⟨7934458799489270328620125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42317113597276108419307333 7934458799489270328620125)
            ·
              refine ⟨2975422049808476373232547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7934458799489270328620125 2975422049808476373232547)
              ·
                refine ⟨4463133074712714559848821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975422049808476373232547 4463133074712714559848821)
                ·
                  refine ⟨418418725754316989985827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4463133074712714559848821 418418725754316989985827)
                  ·
                    rfl

theorem cell22_3666904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 1, 5].length) (baseStart_3666904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666904 prefixEnd_3666904 := by exact prefixLift 3666904
  have htrace : WordTrace (prefixWord ++ tailWord_3666904) baseStart_3666904 baseEnd_3666904 := by
    simpa [prefixWord, tailWord_3666904, baseEnd_3666904] using wordTrace_append hprefix tailTrace_3666904
  have hstable : (prefixWord ++ tailWord_3666904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666904).length < 2 ^ (prefixWord ++ tailWord_3666904).sum := by decide
  have hdescent : baseEnd_3666904 < baseStart_3666904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666977 : List Nat := [1, 2, 3, 2, 3, 1, 2, 8]
def baseStart_3666977 : Nat := 118140960795 + 3666977 * 2 ^ 59
def prefixEnd_3666977 : Nat := 4983230072969 + 3 ^ 40 * 3666977 * 2
def baseEnd_3666977 : Nat := 139475685183867012542473

theorem tailTrace_3666977 : CollatzResearch.WordTrace tailWord_3666977 prefixEnd_3666977 139475685183867012542473 := by
  unfold tailWord_3666977
  simp only [CollatzResearch.WordTrace]
  refine ⟨133745638836176073656823185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89163759224117382437882123 133745638836176073656823185)
  ·
    refine ⟨100309229127132055242617389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133745638836176073656823185 100309229127132055242617389)
    ·
      refine ⟨37615960922674520715981521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100309229127132055242617389 37615960922674520715981521)
      ·
        refine ⟨28211970692005890536986141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37615960922674520715981521 28211970692005890536986141)
        ·
          refine ⟨10579489009502208951369803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28211970692005890536986141 10579489009502208951369803)
          ·
            refine ⟨15869233514253313427054705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579489009502208951369803 15869233514253313427054705)
            ·
              refine ⟨11901925135689985070291029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15869233514253313427054705 11901925135689985070291029)
              ·
                refine ⟨139475685183867012542473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11901925135689985070291029 139475685183867012542473)
                ·
                  rfl

theorem cell22_3666977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 8].length) (baseStart_3666977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666977 prefixEnd_3666977 := by exact prefixLift 3666977
  have htrace : WordTrace (prefixWord ++ tailWord_3666977) baseStart_3666977 baseEnd_3666977 := by
    simpa [prefixWord, tailWord_3666977, baseEnd_3666977] using wordTrace_append hprefix tailTrace_3666977
  have hstable : (prefixWord ++ tailWord_3666977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666977).length < 2 ^ (prefixWord ++ tailWord_3666977).sum := by decide
  have hdescent : baseEnd_3666977 < baseStart_3666977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666979 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 2, 4]
def baseStart_3666979 : Nat := 118140960795 + 3666979 * 2 ^ 59
def prefixEnd_3666979 : Nat := 4983230072969 + 3 ^ 40 * 3666979 * 2
def baseEnd_3666979 : Nat := 1255281851295675774332251

theorem tailTrace_3666979 : CollatzResearch.WordTrace tailWord_3666979 prefixEnd_3666979 1255281851295675774332251 := by
  unfold tailWord_3666979
  simp only [CollatzResearch.WordTrace]
  refine ⟨133745711782168827998395991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89163807854779218665597327 133745711782168827998395991)
  ·
    refine ⟨200618567673253241997593987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133745711782168827998395991 200618567673253241997593987)
    ·
      refine ⟨300927851509879862996390981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200618567673253241997593987 300927851509879862996390981)
      ·
        refine ⟨56423972158102474311823309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300927851509879862996390981 56423972158102474311823309)
        ·
          refine ⟨21158989559288427866933741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56423972158102474311823309 21158989559288427866933741)
          ·
            refine ⟨7934621084733160450100153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21158989559288427866933741 7934621084733160450100153)
            ·
              refine ⟨5950965813549870337575115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7934621084733160450100153 5950965813549870337575115)
              ·
                refine ⟨8926448720324805506362673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950965813549870337575115 8926448720324805506362673)
                ·
                  refine ⟨6694836540243604129772005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8926448720324805506362673 6694836540243604129772005)
                  ·
                    refine ⟨1255281851295675774332251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694836540243604129772005 1255281851295675774332251)
                    ·
                      rfl

theorem cell22_3666979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].length) (baseStart_3666979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666979 prefixEnd_3666979 := by exact prefixLift 3666979
  have htrace : WordTrace (prefixWord ++ tailWord_3666979) baseStart_3666979 baseEnd_3666979 := by
    simpa [prefixWord, tailWord_3666979, baseEnd_3666979] using wordTrace_append hprefix tailTrace_3666979
  have hstable : (prefixWord ++ tailWord_3666979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666979).length < 2 ^ (prefixWord ++ tailWord_3666979).sum := by decide
  have hdescent : baseEnd_3666979 < baseStart_3666979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666996 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3666996 : Nat := 118140960795 + 3666996 * 2 ^ 59
def prefixEnd_3666996 : Nat := 4983230072969 + 3 ^ 40 * 3666996 * 2
def baseEnd_3666996 : Nat := 1255287670743093396657199

theorem tailTrace_3666996 : CollatzResearch.WordTrace tailWord_3666996 prefixEnd_3666996 1255287670743093396657199 := by
  unfold tailWord_3666996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66873165911553619950882421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89164221215404826601176561 66873165911553619950882421)
  ·
    refine ⟨6269359304208151870395227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66873165911553619950882421 6269359304208151870395227)
    ·
      refine ⟨9404038956312227805592841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269359304208151870395227 9404038956312227805592841)
      ·
        refine ⟨7053029217234170854194631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9404038956312227805592841 7053029217234170854194631)
        ·
          refine ⟨10579543825851256281291947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053029217234170854194631 10579543825851256281291947)
          ·
            refine ⟨15869315738776884421937921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579543825851256281291947 15869315738776884421937921)
            ·
              refine ⟨11901986804082663316453441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15869315738776884421937921 11901986804082663316453441)
              ·
                refine ⟨8926490103061997487340081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11901986804082663316453441 8926490103061997487340081)
                ·
                  refine ⟨6694867577296498115505061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8926490103061997487340081 6694867577296498115505061)
                  ·
                    refine ⟨1255287670743093396657199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694867577296498115505061 1255287670743093396657199)
                    ·
                      rfl

theorem cell22_3666996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3666996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666996 prefixEnd_3666996 := by exact prefixLift 3666996
  have htrace : WordTrace (prefixWord ++ tailWord_3666996) baseStart_3666996 baseEnd_3666996 := by
    simpa [prefixWord, tailWord_3666996, baseEnd_3666996] using wordTrace_append hprefix tailTrace_3666996
  have hstable : (prefixWord ++ tailWord_3666996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666996).length < 2 ^ (prefixWord ++ tailWord_3666996).sum := by decide
  have hdescent : baseEnd_3666996 < baseStart_3666996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3666998 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3666998 : Nat := 118140960795 + 3666998 * 2 ^ 59
def prefixEnd_3666998 : Nat := 4983230072969 + 3 ^ 40 * 3666998 * 2
def baseEnd_3666998 : Nat := 1255288355383966058107193

theorem tailTrace_3666998 : CollatzResearch.WordTrace tailWord_3666998 prefixEnd_3666998 1255288355383966058107193 := by
  unfold tailWord_3666998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359150298068749640208603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89164269846066662828891765 8359150298068749640208603)
  ·
    refine ⟨12538725447103124460312905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8359150298068749640208603 12538725447103124460312905)
    ·
      refine ⟨9404044085327343345234679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12538725447103124460312905 9404044085327343345234679)
      ·
        refine ⟨14106066127991015017852019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9404044085327343345234679 14106066127991015017852019)
        ·
          refine ⟨21159099191986522526778029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14106066127991015017852019 21159099191986522526778029)
          ·
            refine ⟨7934662196994945947541761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21159099191986522526778029 7934662196994945947541761)
            ·
              refine ⟨5950996647746209460656321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7934662196994945947541761 5950996647746209460656321)
              ·
                refine ⟨4463247485809657095492241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950996647746209460656321 4463247485809657095492241)
                ·
                  refine ⟨3347435614357242821619181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4463247485809657095492241 3347435614357242821619181)
                  ·
                    refine ⟨1255288355383966058107193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347435614357242821619181 1255288355383966058107193)
                    ·
                      rfl

theorem cell22_3666998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3666998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3666998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3666998 prefixEnd_3666998 := by exact prefixLift 3666998
  have htrace : WordTrace (prefixWord ++ tailWord_3666998) baseStart_3666998 baseEnd_3666998 := by
    simpa [prefixWord, tailWord_3666998, baseEnd_3666998] using wordTrace_append hprefix tailTrace_3666998
  have hstable : (prefixWord ++ tailWord_3666998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3666998).length < 2 ^ (prefixWord ++ tailWord_3666998).sum := by decide
  have hdescent : baseEnd_3666998 < baseStart_3666998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3666998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667026 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_3667026 : Nat := 118140960795 + 3667026 * 2 ^ 59
def prefixEnd_3667026 : Nat := 4983230072969 + 3 ^ 40 * 3667026 * 2
def baseEnd_3667026 : Nat := 1255297940356183318407107

theorem tailTrace_3667026 : CollatzResearch.WordTrace tailWord_3667026 prefixEnd_3667026 1255297940356183318407107 := by
  unfold tailWord_3667026
  simp only [CollatzResearch.WordTrace]
  refine ⟨33436856503249638756339233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89164950675332370016904621 33436856503249638756339233)
  ·
    refine ⟨25077642377437229067254425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33436856503249638756339233 25077642377437229067254425)
    ·
      refine ⟨18808231783077921800440819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25077642377437229067254425 18808231783077921800440819)
      ·
        refine ⟨28212347674616882700661229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18808231783077921800440819 28212347674616882700661229)
        ·
          refine ⟨10579630377981331012747961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28212347674616882700661229 10579630377981331012747961)
          ·
            refine ⟨7934722783485998259560971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10579630377981331012747961 7934722783485998259560971)
            ·
              refine ⟨11902084175228997389341457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934722783485998259560971 11902084175228997389341457)
              ·
                refine ⟨8926563131421748042006093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11902084175228997389341457 8926563131421748042006093)
                ·
                  refine ⟨3347461174283155515752285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8926563131421748042006093 3347461174283155515752285)
                  ·
                    refine ⟨1255297940356183318407107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347461174283155515752285 1255297940356183318407107)
                    ·
                      rfl

theorem cell22_3667026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_3667026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667026 prefixEnd_3667026 := by exact prefixLift 3667026
  have htrace : WordTrace (prefixWord ++ tailWord_3667026) baseStart_3667026 baseEnd_3667026 := by
    simpa [prefixWord, tailWord_3667026, baseEnd_3667026] using wordTrace_append hprefix tailTrace_3667026
  have hstable : (prefixWord ++ tailWord_3667026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667026).length < 2 ^ (prefixWord ++ tailWord_3667026).sum := by decide
  have hdescent : baseEnd_3667026 < baseStart_3667026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667030 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3667030 : Nat := 118140960795 + 3667030 * 2 ^ 59
def prefixEnd_3667030 : Nat := 4983230072969 + 3 ^ 40 * 3667030 * 2
def baseEnd_3667030 : Nat := 1255299309637928641307095

theorem tailTrace_3667030 : CollatzResearch.WordTrace tailWord_3667030 prefixEnd_3667030 1255299309637928641307095 := by
  unfold tailWord_3667030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359223244061503981781409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89165047936656042472335029 8359223244061503981781409)
  ·
    refine ⟨6269417433046127986336057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8359223244061503981781409 6269417433046127986336057)
    ·
      refine ⟨4702063074784595989752043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6269417433046127986336057 4702063074784595989752043)
      ·
        refine ⟨7053094612176893984628065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702063074784595989752043 7053094612176893984628065)
        ·
          refine ⟨5289820959132670488471049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7053094612176893984628065 5289820959132670488471049)
          ·
            refine ⟨3967365719349502866353287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5289820959132670488471049 3967365719349502866353287)
            ·
              refine ⟨5951048579024254299529931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3967365719349502866353287 5951048579024254299529931)
              ·
                refine ⟨8926572868536381449294897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951048579024254299529931 8926572868536381449294897)
                ·
                  refine ⟨6694929651402286086971173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8926572868536381449294897 6694929651402286086971173)
                  ·
                    refine ⟨1255299309637928641307095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694929651402286086971173 1255299309637928641307095)
                    ·
                      rfl

theorem cell22_3667030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3667030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667030 prefixEnd_3667030 := by exact prefixLift 3667030
  have htrace : WordTrace (prefixWord ++ tailWord_3667030) baseStart_3667030 baseEnd_3667030 := by
    simpa [prefixWord, tailWord_3667030, baseEnd_3667030] using wordTrace_append hprefix tailTrace_3667030
  have hstable : (prefixWord ++ tailWord_3667030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667030).length < 2 ^ (prefixWord ++ tailWord_3667030).sum := by decide
  have hdescent : baseEnd_3667030 < baseStart_3667030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667054 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3667054 : Nat := 118140960795 + 3667054 * 2 ^ 59
def prefixEnd_3667054 : Nat := 4983230072969 + 3 ^ 40 * 3667054 * 2
def baseEnd_3667054 : Nat := 1255307525328400578707021

theorem tailTrace_3667054 : CollatzResearch.WordTrace tailWord_3667054 prefixEnd_3667054 1255307525328400578707021 := by
  unfold tailWord_3667054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16718555907112139475922027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89165631504598077204917477 16718555907112139475922027)
  ·
    refine ⟨25077833860668209213883041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16718555907112139475922027 25077833860668209213883041)
    ·
      refine ⟨18808375395501156910412281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25077833860668209213883041 18808375395501156910412281)
      ·
        refine ⟨14106281546625867682809211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18808375395501156910412281 14106281546625867682809211)
        ·
          refine ⟨21159422319938801524213817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14106281546625867682809211 21159422319938801524213817)
          ·
            refine ⟨15869566739954101143160363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21159422319938801524213817 15869566739954101143160363)
            ·
              refine ⟨23804350109931151714740545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15869566739954101143160363 23804350109931151714740545)
              ·
                refine ⟨17853262582448363786055409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23804350109931151714740545 17853262582448363786055409)
                ·
                  refine ⟨13389946936836272839541557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17853262582448363786055409 13389946936836272839541557)
                  ·
                    refine ⟨1255307525328400578707021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13389946936836272839541557 1255307525328400578707021)
                    ·
                      rfl

theorem cell22_3667054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3667054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667054 prefixEnd_3667054 := by exact prefixLift 3667054
  have htrace : WordTrace (prefixWord ++ tailWord_3667054) baseStart_3667054 baseEnd_3667054 := by
    simpa [prefixWord, tailWord_3667054, baseEnd_3667054] using wordTrace_append hprefix tailTrace_3667054
  have hstable : (prefixWord ++ tailWord_3667054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667054).length < 2 ^ (prefixWord ++ tailWord_3667054).sum := by decide
  have hdescent : baseEnd_3667054 < baseStart_3667054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667086 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_3667086 : Nat := 118140960795 + 3667086 * 2 ^ 59
def prefixEnd_3667086 : Nat := 4983230072969 + 3 ^ 40 * 3667086 * 2
def baseEnd_3667086 : Nat := 1255318479582363161906923

theorem tailTrace_3667086 : CollatzResearch.WordTrace tailWord_3667086 prefixEnd_3667086 1255318479582363161906923 := by
  unfold tailWord_3667086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16718701799097648159067639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89166409595187456848360741 16718701799097648159067639)
  ·
    refine ⟨25078052698646472238601459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16718701799097648159067639 25078052698646472238601459)
    ·
      refine ⟨37617079047969708357902189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25078052698646472238601459 37617079047969708357902189)
      ·
        refine ⟨14106404642988640634213321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37617079047969708357902189 14106404642988640634213321)
        ·
          refine ⟨10579803482241480475659991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14106404642988640634213321 10579803482241480475659991)
          ·
            refine ⟨15869705223362220713489987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579803482241480475659991 15869705223362220713489987)
            ·
              refine ⟨23804557835043331070234981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15869705223362220713489987 23804557835043331070234981)
              ·
                refine ⟨4463354594070624575669059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23804557835043331070234981 4463354594070624575669059)
                ·
                  refine ⟨6695031891105936863503589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463354594070624575669059 6695031891105936863503589)
                  ·
                    refine ⟨1255318479582363161906923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6695031891105936863503589 1255318479582363161906923)
                    ·
                      rfl

theorem cell22_3667086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_3667086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667086 prefixEnd_3667086 := by exact prefixLift 3667086
  have htrace : WordTrace (prefixWord ++ tailWord_3667086) baseStart_3667086 baseEnd_3667086 := by
    simpa [prefixWord, tailWord_3667086, baseEnd_3667086] using wordTrace_append hprefix tailTrace_3667086
  have hstable : (prefixWord ++ tailWord_3667086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667086).length < 2 ^ (prefixWord ++ tailWord_3667086).sum := by decide
  have hdescent : baseEnd_3667086 < baseStart_3667086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667129 : List Nat := [1, 2, 1, 4, 1, 4, 2, 7]
def baseStart_3667129 : Nat := 118140960795 + 3667129 * 2 ^ 59
def prefixEnd_3667129 : Nat := 4983230072969 + 3 ^ 40 * 3667129 * 2
def baseEnd_3667129 : Nat := 139481466595680598120199

theorem tailTrace_3667129 : CollatzResearch.WordTrace tailWord_3667129 prefixEnd_3667129 139481466595680598120199 := by
  unfold tailWord_3667129
  simp only [CollatzResearch.WordTrace]
  refine ⟨133751182731625403616356441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89167455154416935744237627 133751182731625403616356441)
  ·
    refine ⟨100313387048719052712267331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133751182731625403616356441 100313387048719052712267331)
    ·
      refine ⟨150470080573078579068400997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100313387048719052712267331 150470080573078579068400997)
      ·
        refine ⟨28213140107452233575325187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150470080573078579068400997 28213140107452233575325187)
        ·
          refine ⟨42319710161178350362987781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28213140107452233575325187 42319710161178350362987781)
          ·
            refine ⟨7934945655220940693060209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42319710161178350362987781 7934945655220940693060209)
            ·
              refine ⟨5951209241415705519795157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7934945655220940693060209 5951209241415705519795157)
              ·
                refine ⟨139481466595680598120199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5951209241415705519795157 139481466595680598120199)
                ·
                  rfl

theorem cell22_3667129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 7].length) (baseStart_3667129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667129 prefixEnd_3667129 := by exact prefixLift 3667129
  have htrace : WordTrace (prefixWord ++ tailWord_3667129) baseStart_3667129 baseEnd_3667129 := by
    simpa [prefixWord, tailWord_3667129, baseEnd_3667129] using wordTrace_append hprefix tailTrace_3667129
  have hstable : (prefixWord ++ tailWord_3667129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667129).length < 2 ^ (prefixWord ++ tailWord_3667129).sum := by decide
  have hdescent : baseEnd_3667129 < baseStart_3667129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667133 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_3667133 : Nat := 118140960795 + 3667133 * 2 ^ 59
def prefixEnd_3667133 : Nat := 4983230072969 + 3 ^ 40 * 3667133 * 2
def baseEnd_3667133 : Nat := 1255334568642870705981779

theorem tailTrace_3667133 : CollatzResearch.WordTrace tailWord_3667133 prefixEnd_3667133 1255334568642870705981779 := by
  unfold tailWord_3667133
  simp only [CollatzResearch.WordTrace]
  refine ⟨133751328623610912299502053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89167552415740608199668035 133751328623610912299502053)
  ·
    refine ⟨25078374116927046056156635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133751328623610912299502053 25078374116927046056156635)
    ·
      refine ⟨37617561175390569084234953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25078374116927046056156635 37617561175390569084234953)
      ·
        refine ⟨28213170881542926813176215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37617561175390569084234953 28213170881542926813176215)
        ·
          refine ⟨42319756322314390219764323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28213170881542926813176215 42319756322314390219764323)
          ·
            refine ⟨63479634483471585329646485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42319756322314390219764323 63479634483471585329646485)
            ·
              refine ⟨2975607866412730562327179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63479634483471585329646485 2975607866412730562327179)
              ·
                refine ⟨4463411799619095843490769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975607866412730562327179 4463411799619095843490769)
                ·
                  refine ⟨3347558849714321882618077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4463411799619095843490769 3347558849714321882618077)
                  ·
                    refine ⟨1255334568642870705981779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347558849714321882618077 1255334568642870705981779)
                    ·
                      rfl

theorem cell22_3667133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_3667133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667133 prefixEnd_3667133 := by exact prefixLift 3667133
  have htrace : WordTrace (prefixWord ++ tailWord_3667133) baseStart_3667133 baseEnd_3667133 := by
    simpa [prefixWord, tailWord_3667133, baseEnd_3667133] using wordTrace_append hprefix tailTrace_3667133
  have hstable : (prefixWord ++ tailWord_3667133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667133).length < 2 ^ (prefixWord ++ tailWord_3667133).sum := by decide
  have hdescent : baseEnd_3667133 < baseStart_3667133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667236 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_3667236 : Nat := 118140960795 + 3667236 * 2 ^ 59
def prefixEnd_3667236 : Nat := 4983230072969 + 3 ^ 40 * 3667236 * 2
def baseEnd_3667236 : Nat := 418456609215937590218821

theorem tailTrace_3667236 : CollatzResearch.WordTrace tailWord_3667236 prefixEnd_3667236 418456609215937590218821 := by
  unfold tailWord_3667236
  simp only [CollatzResearch.WordTrace]
  refine ⟨66877542671118880445250781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89170056894825173927001041 66877542671118880445250781)
  ·
    refine ⟨25079078501669580166969043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66877542671118880445250781 25079078501669580166969043)
    ·
      refine ⟨37618617752504370250453565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25079078501669580166969043 37618617752504370250453565)
      ·
        refine ⟨14106981657189138843920087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37618617752504370250453565 14106981657189138843920087)
        ·
          refine ⟨21160472485783708265880131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14106981657189138843920087 21160472485783708265880131)
          ·
            refine ⟨31740708728675562398820197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21160472485783708265880131 31740708728675562398820197)
            ·
              refine ⟨5951382886626667949778787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31740708728675562398820197 5951382886626667949778787)
              ·
                refine ⟨8927074329940001924668181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951382886626667949778787 8927074329940001924668181)
                ·
                  refine ⟨418456609215937590218821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8927074329940001924668181 418456609215937590218821)
                  ·
                    rfl

theorem cell22_3667236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_3667236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667236 prefixEnd_3667236 := by exact prefixLift 3667236
  have htrace : WordTrace (prefixWord ++ tailWord_3667236) baseStart_3667236 baseEnd_3667236 := by
    simpa [prefixWord, tailWord_3667236, baseEnd_3667236] using wordTrace_append hprefix tailTrace_3667236
  have hstable : (prefixWord ++ tailWord_3667236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667236).length < 2 ^ (prefixWord ++ tailWord_3667236).sum := by decide
  have hdescent : baseEnd_3667236 < baseStart_3667236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667251 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 1, 5]
def baseStart_3667251 : Nat := 118140960795 + 3667251 * 2 ^ 59
def prefixEnd_3667251 : Nat := 4983230072969 + 3 ^ 40 * 3667251 * 2
def baseEnd_3667251 : Nat := 1255374962454357731531417

theorem tailTrace_3667251 : CollatzResearch.WordTrace tailWord_3667251 prefixEnd_3667251 1255374962454357731531417 := by
  unfold tailWord_3667251
  simp only [CollatzResearch.WordTrace]
  refine ⟨133755632437183418452297607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89170421624788945634865071 133755632437183418452297607)
  ·
    refine ⟨200633448655775127678446411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133755632437183418452297607 200633448655775127678446411)
    ·
      refine ⟨300950172983662691517669617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200633448655775127678446411 300950172983662691517669617)
      ·
        refine ⟨225712629737747018638252213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300950172983662691517669617 225712629737747018638252213)
        ·
          refine ⟨21160559037913782997336145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225712629737747018638252213 21160559037913782997336145)
          ·
            refine ⟨15870419278435337248002109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21160559037913782997336145 15870419278435337248002109)
            ·
              refine ⟨5951407229413251468000791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15870419278435337248002109 5951407229413251468000791)
              ·
                refine ⟨8927110844119877202001187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951407229413251468000791 8927110844119877202001187)
                ·
                  refine ⟨13390666266179815803001781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927110844119877202001187 13390666266179815803001781)
                  ·
                    refine ⟨1255374962454357731531417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13390666266179815803001781 1255374962454357731531417)
                    ·
                      rfl

theorem cell22_3667251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 5].length) (baseStart_3667251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667251 prefixEnd_3667251 := by exact prefixLift 3667251
  have htrace : WordTrace (prefixWord ++ tailWord_3667251) baseStart_3667251 baseEnd_3667251 := by
    simpa [prefixWord, tailWord_3667251, baseEnd_3667251] using wordTrace_append hprefix tailTrace_3667251
  have hstable : (prefixWord ++ tailWord_3667251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667251).length < 2 ^ (prefixWord ++ tailWord_3667251).sum := by decide
  have hdescent : baseEnd_3667251 < baseStart_3667251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667264 : List Nat := [2, 1, 1, 2, 2, 1, 5, 8]
def baseStart_3667264 : Nat := 118140960795 + 3667264 * 2 ^ 59
def prefixEnd_3667264 : Nat := 4983230072969 + 3 ^ 40 * 3667264 * 2
def baseEnd_3667264 : Nat := 139486601402225558995153

theorem tailTrace_3667264 : CollatzResearch.WordTrace tailWord_3667264 prefixEnd_3667264 139486601402225558995153 := by
  unfold tailWord_3667264
  simp only [CollatzResearch.WordTrace]
  refine ⟨66878053293068160836260423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89170737724090881115013897 66878053293068160836260423)
  ·
    refine ⟨100317079939602241254390635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66878053293068160836260423 100317079939602241254390635)
    ·
      refine ⟨150475619909403361881585953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100317079939602241254390635 150475619909403361881585953)
      ·
        refine ⟨112856714932052521411189465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150475619909403361881585953 112856714932052521411189465)
        ·
          refine ⟨84642536199039391058392099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112856714932052521411189465 84642536199039391058392099)
          ·
            refine ⟨126963804298559086587588149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84642536199039391058392099 126963804298559086587588149)
            ·
              refine ⟨11902856652989914367586389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126963804298559086587588149 11902856652989914367586389)
              ·
                refine ⟨139486601402225558995153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11902856652989914367586389 139486601402225558995153)
                ·
                  rfl

theorem cell22_3667264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 8].length) (baseStart_3667264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667264 prefixEnd_3667264 := by exact prefixLift 3667264
  have htrace : WordTrace (prefixWord ++ tailWord_3667264) baseStart_3667264 baseEnd_3667264 := by
    simpa [prefixWord, tailWord_3667264, baseEnd_3667264] using wordTrace_append hprefix tailTrace_3667264
  have hstable : (prefixWord ++ tailWord_3667264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667264).length < 2 ^ (prefixWord ++ tailWord_3667264).sum := by decide
  have hdescent : baseEnd_3667264 < baseStart_3667264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667394 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3667394 : Nat := 118140960795 + 3667394 * 2 ^ 59
def prefixEnd_3667394 : Nat := 4983230072969 + 3 ^ 40 * 3667394 * 2
def baseEnd_3667394 : Nat := 418474638092251008401993

theorem tailTrace_3667394 : CollatzResearch.WordTrace tailWord_3667394 prefixEnd_3667394 418474638092251008401993 := by
  unfold tailWord_3667394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33440212018916338468688309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89173898717110235916502157 33440212018916338468688309)
  ·
    refine ⟨3135019876773406731439529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33440212018916338468688309 3135019876773406731439529)
    ·
      refine ⟨2351264907580055048579647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3135019876773406731439529 2351264907580055048579647)
      ·
        refine ⟨3526897361370082572869471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351264907580055048579647 3526897361370082572869471)
        ·
          refine ⟨5290346042055123859304207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526897361370082572869471 5290346042055123859304207)
          ·
            refine ⟨7935519063082685788956311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290346042055123859304207 7935519063082685788956311)
            ·
              refine ⟨11903278594624028683434467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935519063082685788956311 11903278594624028683434467)
              ·
                refine ⟨17854917891936043025151701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903278594624028683434467 17854917891936043025151701)
                ·
                  refine ⟨418474638092251008401993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17854917891936043025151701 418474638092251008401993)
                  ·
                    rfl

theorem cell22_3667394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3667394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667394 prefixEnd_3667394 := by exact prefixLift 3667394
  have htrace : WordTrace (prefixWord ++ tailWord_3667394) baseStart_3667394 baseEnd_3667394 := by
    simpa [prefixWord, tailWord_3667394, baseEnd_3667394] using wordTrace_append hprefix tailTrace_3667394
  have hstable : (prefixWord ++ tailWord_3667394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667394).length < 2 ^ (prefixWord ++ tailWord_3667394).sum := by decide
  have hdescent : baseEnd_3667394 < baseStart_3667394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667401 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 4, 4]
def baseStart_3667401 : Nat := 118140960795 + 3667401 * 2 ^ 59
def prefixEnd_3667401 : Nat := 4983230072969 + 3 ^ 40 * 3667401 * 2
def baseEnd_3667401 : Nat := 1255426310519807340280957

theorem tailTrace_3667401 : CollatzResearch.WordTrace tailWord_3667401 prefixEnd_3667401 1255426310519807340280957 := by
  unfold tailWord_3667401
  simp only [CollatzResearch.WordTrace]
  refine ⟨133761103386639994070258057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89174068924426662713505371 133761103386639994070258057)
  ·
    refine ⟨100320827539979995552693543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133761103386639994070258057 100320827539979995552693543)
    ·
      refine ⟨150481241309969993329040315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100320827539979995552693543 150481241309969993329040315)
      ·
        refine ⟨225721861964954989993560473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150481241309969993329040315 225721861964954989993560473)
        ·
          refine ⟨169291396473716242495170355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225721861964954989993560473 169291396473716242495170355)
          ·
            refine ⟨253937094710574363742755533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169291396473716242495170355 253937094710574363742755533)
            ·
              refine ⟨95226410516465386403533325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253937094710574363742755533 95226410516465386403533325)
              ·
                refine ⟨35709903943674519901324997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95226410516465386403533325 35709903943674519901324997)
                ·
                  refine ⟨6695606989438972481498437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35709903943674519901324997 6695606989438972481498437)
                  ·
                    refine ⟨1255426310519807340280957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6695606989438972481498437 1255426310519807340280957)
                    ·
                      rfl

theorem cell22_3667401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_3667401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667401 prefixEnd_3667401 := by exact prefixLift 3667401
  have htrace : WordTrace (prefixWord ++ tailWord_3667401) baseStart_3667401 baseEnd_3667401 := by
    simpa [prefixWord, tailWord_3667401, baseEnd_3667401] using wordTrace_append hprefix tailTrace_3667401
  have hstable : (prefixWord ++ tailWord_3667401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667401).length < 2 ^ (prefixWord ++ tailWord_3667401).sum := by decide
  have hdescent : baseEnd_3667401 < baseStart_3667401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667486 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3667486 : Nat := 118140960795 + 3667486 * 2 ^ 59
def prefixEnd_3667486 : Nat := 4983230072969 + 3 ^ 40 * 3667486 * 2
def baseEnd_3667486 : Nat := 1255455407756895451905697

theorem tailTrace_3667486 : CollatzResearch.WordTrace tailWord_3667486 prefixEnd_3667486 1255455407756895451905697 := by
  unfold tailWord_3667486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720525448916506698387789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89176135727554702391401541 16720525448916506698387789)
  ·
    refine ⟨6270197043343690011895421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16720525448916506698387789 6270197043343690011895421)
    ·
      refine ⟨2351323891253883754460783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6270197043343690011895421 2351323891253883754460783)
      ·
        refine ⟨3526985836880825631691175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351323891253883754460783 3526985836880825631691175)
        ·
          refine ⟨5290478755321238447536763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526985836880825631691175 5290478755321238447536763)
          ·
            refine ⟨7935718132981857671305145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290478755321238447536763 7935718132981857671305145)
            ·
              refine ⟨5951788599736393253478859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7935718132981857671305145 5951788599736393253478859)
              ·
                refine ⟨8927682899604589880218289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951788599736393253478859 8927682899604589880218289)
                ·
                  refine ⟨6695762174703442410163717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8927682899604589880218289 6695762174703442410163717)
                  ·
                    refine ⟨1255455407756895451905697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6695762174703442410163717 1255455407756895451905697)
                    ·
                      rfl

theorem cell22_3667486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3667486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667486 prefixEnd_3667486 := by exact prefixLift 3667486
  have htrace : WordTrace (prefixWord ++ tailWord_3667486) baseStart_3667486 baseEnd_3667486 := by
    simpa [prefixWord, tailWord_3667486, baseEnd_3667486] using wordTrace_append hprefix tailTrace_3667486
  have hstable : (prefixWord ++ tailWord_3667486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667486).length < 2 ^ (prefixWord ++ tailWord_3667486).sum := by decide
  have hdescent : baseEnd_3667486 < baseStart_3667486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667516 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 1, 3]
def baseStart_3667516 : Nat := 118140960795 + 3667516 * 2 ^ 59
def prefixEnd_3667516 : Nat := 4983230072969 + 3 ^ 40 * 3667516 * 2
def baseEnd_3667516 : Nat := 1255465677369985373655605

theorem tailTrace_3667516 : CollatzResearch.WordTrace tailWord_3667516 prefixEnd_3667516 1255465677369985373655605 := by
  unfold tailWord_3667516
  simp only [CollatzResearch.WordTrace]
  refine ⟨66882648890611684355347201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89176865187482245807129601 66882648890611684355347201)
  ·
    refine ⟨50161986667958763266510401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66882648890611684355347201 50161986667958763266510401)
    ·
      refine ⟨37621490000969072449882801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50161986667958763266510401 37621490000969072449882801)
      ·
        refine ⟨28216117500726804337412101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37621490000969072449882801 28216117500726804337412101)
        ·
          refine ⟨5290522031386275813264769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28216117500726804337412101 5290522031386275813264769)
          ·
            refine ⟨3967891523539706859948577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5290522031386275813264769 3967891523539706859948577)
            ·
              refine ⟨2975918642654780144961433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3967891523539706859948577 2975918642654780144961433)
              ·
                refine ⟨2231938981991085108721075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2975918642654780144961433 2231938981991085108721075)
                ·
                  refine ⟨3347908472986627663081613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231938981991085108721075 3347908472986627663081613)
                  ·
                    refine ⟨1255465677369985373655605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3347908472986627663081613 1255465677369985373655605)
                    ·
                      rfl

theorem cell22_3667516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_3667516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667516 prefixEnd_3667516 := by exact prefixLift 3667516
  have htrace : WordTrace (prefixWord ++ tailWord_3667516) baseStart_3667516 baseEnd_3667516 := by
    simpa [prefixWord, tailWord_3667516, baseEnd_3667516] using wordTrace_append hprefix tailTrace_3667516
  have hstable : (prefixWord ++ tailWord_3667516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667516).length < 2 ^ (prefixWord ++ tailWord_3667516).sum := by decide
  have hdescent : baseEnd_3667516 < baseStart_3667516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667553 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 1, 6]
def baseStart_3667553 : Nat := 118140960795 + 3667553 * 2 ^ 59
def prefixEnd_3667553 : Nat := 4983230072969 + 3 ^ 40 * 3667553 * 2
def baseEnd_3667553 : Nat := 1255478343226129610480491

theorem tailTrace_3667553 : CollatzResearch.WordTrace tailWord_3667553 prefixEnd_3667553 1255478343226129610480491 := by
  unfold tailWord_3667553
  simp only [CollatzResearch.WordTrace]
  refine ⟨133766647282089324029791313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89177764854726216019860875 133766647282089324029791313)
  ·
    refine ⟨100324985461566993022343485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133766647282089324029791313 100324985461566993022343485)
    ·
      refine ⟨37621869548087622383378807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100324985461566993022343485 37621869548087622383378807)
      ·
        refine ⟨56432804322131433575068211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37621869548087622383378807 56432804322131433575068211)
        ·
          refine ⟨84649206483197150362602317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56432804322131433575068211 84649206483197150362602317)
          ·
            refine ⟨31743452431198931385975869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84649206483197150362602317 31743452431198931385975869)
            ·
              refine ⟨11903794661699599269740951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31743452431198931385975869 11903794661699599269740951)
              ·
                refine ⟨17855691992549398904611427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903794661699599269740951 17855691992549398904611427)
                ·
                  refine ⟨26783537988824098356917141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17855691992549398904611427 26783537988824098356917141)
                  ·
                    refine ⟨1255478343226129610480491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26783537988824098356917141 1255478343226129610480491)
                    ·
                      rfl

theorem cell22_3667553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_3667553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667553 prefixEnd_3667553 := by exact prefixLift 3667553
  have htrace : WordTrace (prefixWord ++ tailWord_3667553) baseStart_3667553 baseEnd_3667553 := by
    simpa [prefixWord, tailWord_3667553, baseEnd_3667553] using wordTrace_append hprefix tailTrace_3667553
  have hstable : (prefixWord ++ tailWord_3667553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667553).length < 2 ^ (prefixWord ++ tailWord_3667553).sum := by decide
  have hdescent : baseEnd_3667553 < baseStart_3667553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667557 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 4]
def baseStart_3667557 : Nat := 118140960795 + 3667557 * 2 ^ 59
def prefixEnd_3667557 : Nat := 4983230072969 + 3 ^ 40 * 3667557 * 2
def baseEnd_3667557 : Nat := 418493237502624977793493

theorem tailTrace_3667557 : CollatzResearch.WordTrace tailWord_3667557 prefixEnd_3667557 418493237502624977793493 := by
  unfold tailWord_3667557
  simp only [CollatzResearch.WordTrace]
  refine ⟨133766793174074832712936925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89177862116049888475291283 133766793174074832712936925)
  ·
    refine ⟨50162547440278062267351347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133766793174074832712936925 50162547440278062267351347)
    ·
      refine ⟨75243821160417093401027021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50162547440278062267351347 75243821160417093401027021)
      ·
        refine ⟨28216432935156410025385133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75243821160417093401027021 28216432935156410025385133)
        ·
          refine ⟨10581162350683653759519425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28216432935156410025385133 10581162350683653759519425)
          ·
            refine ⟨7935871763012740319639569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10581162350683653759519425 7935871763012740319639569)
            ·
              refine ⟨5951903822259555239729677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7935871763012740319639569 5951903822259555239729677)
              ·
                refine ⟨2231963933347333214898629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5951903822259555239729677 2231963933347333214898629)
                ·
                  refine ⟨418493237502624977793493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2231963933347333214898629 418493237502624977793493)
                  ·
                    rfl

theorem cell22_3667557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_3667557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667557 prefixEnd_3667557 := by exact prefixLift 3667557
  have htrace : WordTrace (prefixWord ++ tailWord_3667557) baseStart_3667557 baseEnd_3667557 := by
    simpa [prefixWord, tailWord_3667557, baseEnd_3667557] using wordTrace_append hprefix tailTrace_3667557
  have hstable : (prefixWord ++ tailWord_3667557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667557).length < 2 ^ (prefixWord ++ tailWord_3667557).sum := by decide
  have hdescent : baseEnd_3667557 < baseStart_3667557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667568 : List Nat := [2, 1, 1, 1, 6, 2, 9]
def baseStart_3667568 : Nat := 118140960795 + 3667568 * 2 ^ 59
def prefixEnd_3667568 : Nat := 4983230072969 + 3 ^ 40 * 3667568 * 2
def baseEnd_3667568 : Nat := 46499388075284243383535

theorem tailTrace_3667568 : CollatzResearch.WordTrace tailWord_3667568 prefixEnd_3667568 46499388075284243383535 := by
  unfold tailWord_3667568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66883597188517490795793679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89178129584689987727724905 66883597188517490795793679)
  ·
    refine ⟨100325395782776236193690519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66883597188517490795793679 100325395782776236193690519)
    ·
      refine ⟨150488093674164354290535779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100325395782776236193690519 150488093674164354290535779)
      ·
        refine ⟨225732140511246531435803669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150488093674164354290535779 225732140511246531435803669)
        ·
          refine ⟨10581194086464681161053297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225732140511246531435803669 10581194086464681161053297)
          ·
            refine ⟨7935895564848510870789973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10581194086464681161053297 7935895564848510870789973)
            ·
              refine ⟨46499388075284243383535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7935895564848510870789973 46499388075284243383535)
              ·
                rfl

theorem cell22_3667568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 9].length) (baseStart_3667568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667568 prefixEnd_3667568 := by exact prefixLift 3667568
  have htrace : WordTrace (prefixWord ++ tailWord_3667568) baseStart_3667568 baseEnd_3667568 := by
    simpa [prefixWord, tailWord_3667568, baseEnd_3667568] using wordTrace_append hprefix tailTrace_3667568
  have hstable : (prefixWord ++ tailWord_3667568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667568).length < 2 ^ (prefixWord ++ tailWord_3667568).sum := by decide
  have hdescent : baseEnd_3667568 < baseStart_3667568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667722 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_3667722 : Nat := 118140960795 + 3667722 * 2 ^ 59
def prefixEnd_3667722 : Nat := 4983230072969 + 3 ^ 40 * 3667722 * 2
def baseEnd_3667722 : Nat := 1255536195379869503004973

theorem tailTrace_3667722 : CollatzResearch.WordTrace tailWord_3667722 prefixEnd_3667722 1255536195379869503004973 := by
  unfold tailWord_3667722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33443202804619266473173355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89181874145651377261795613 33443202804619266473173355)
  ·
    refine ⟨50164804206928899709760033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33443202804619266473173355 50164804206928899709760033)
    ·
      refine ⟨37623603155196674782320025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50164804206928899709760033 37623603155196674782320025)
      ·
        refine ⟨28217702366397506086740019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37623603155196674782320025 28217702366397506086740019)
        ·
          refine ⟨42326553549596259130110029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28217702366397506086740019 42326553549596259130110029)
          ·
            refine ⟨15872457581098597173791261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42326553549596259130110029 15872457581098597173791261)
            ·
              refine ⟨5952171592911973940171723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15872457581098597173791261 5952171592911973940171723)
              ·
                refine ⟨8928257389367960910257585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952171592911973940171723 8928257389367960910257585)
                ·
                  refine ⟨6696193042025970682693189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928257389367960910257585 6696193042025970682693189)
                  ·
                    refine ⟨1255536195379869503004973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696193042025970682693189 1255536195379869503004973)
                    ·
                      rfl

theorem cell22_3667722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_3667722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667722 prefixEnd_3667722 := by exact prefixLift 3667722
  have htrace : WordTrace (prefixWord ++ tailWord_3667722) baseStart_3667722 baseEnd_3667722 := by
    simpa [prefixWord, tailWord_3667722, baseEnd_3667722] using wordTrace_append hprefix tailTrace_3667722
  have hstable : (prefixWord ++ tailWord_3667722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667722).length < 2 ^ (prefixWord ++ tailWord_3667722).sum := by decide
  have hdescent : baseEnd_3667722 < baseStart_3667722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667758 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3667758 : Nat := 118140960795 + 3667758 * 2 ^ 59
def prefixEnd_3667758 : Nat := 4983230072969 + 3 ^ 40 * 3667758 * 2
def baseEnd_3667758 : Nat := 1255548518915577409104863

theorem tailTrace_3667758 : CollatzResearch.WordTrace tailWord_3667758 prefixEnd_3667758 1255548518915577409104863 := by
  unfold tailWord_3667758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721765530793330505125491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89182749497564429360669285 16721765530793330505125491)
  ·
    refine ⟨25082648296189995757688237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16721765530793330505125491 25082648296189995757688237)
    ·
      refine ⟨9405993111071248409133089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25082648296189995757688237 9405993111071248409133089)
      ·
        refine ⟨7054494833303436306849817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9405993111071248409133089 7054494833303436306849817)
        ·
          refine ⟨5290871124977577230137363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7054494833303436306849817 5290871124977577230137363)
          ·
            refine ⟨7936306687466365845206045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290871124977577230137363 7936306687466365845206045)
            ·
              refine ⟨2976115007799887191952267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7936306687466365845206045 2976115007799887191952267)
              ·
                refine ⟨4464172511699830787928401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976115007799887191952267 4464172511699830787928401)
                ·
                  refine ⟨3348129383774873090946301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4464172511699830787928401 3348129383774873090946301)
                  ·
                    refine ⟨1255548518915577409104863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3348129383774873090946301 1255548518915577409104863)
                    ·
                      rfl

theorem cell22_3667758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3667758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667758 prefixEnd_3667758 := by exact prefixLift 3667758
  have htrace : WordTrace (prefixWord ++ tailWord_3667758) baseStart_3667758 baseEnd_3667758 := by
    simpa [prefixWord, tailWord_3667758, baseEnd_3667758] using wordTrace_append hprefix tailTrace_3667758
  have hstable : (prefixWord ++ tailWord_3667758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667758).length < 2 ^ (prefixWord ++ tailWord_3667758).sum := by decide
  have hdescent : baseEnd_3667758 < baseStart_3667758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667795 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 7, 4]
def baseStart_3667795 : Nat := 118140960795 + 3667795 * 2 ^ 59
def prefixEnd_3667795 : Nat := 4983230072969 + 3 ^ 40 * 3667795 * 2
def baseEnd_3667795 : Nat := 1255561184771721645929749

theorem tailTrace_3667795 : CollatzResearch.WordTrace tailWord_3667795 prefixEnd_3667795 1255561184771721645929749 := by
  unfold tailWord_3667795
  simp only [CollatzResearch.WordTrace]
  refine ⟨133775473747212599360100839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89183649164808399573400559 133775473747212599360100839)
  ·
    refine ⟨200663210620818899040151259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133775473747212599360100839 200663210620818899040151259)
    ·
      refine ⟨300994815931228348560226889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200663210620818899040151259 300994815931228348560226889)
      ·
        refine ⟨225746111948421261420170167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300994815931228348560226889 225746111948421261420170167)
        ·
          refine ⟨338619167922631892130255251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225746111948421261420170167 338619167922631892130255251)
          ·
            refine ⟨507928751883947838195382877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338619167922631892130255251 507928751883947838195382877)
            ·
              refine ⟨190473281956480439323268579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507928751883947838195382877 190473281956480439323268579)
              ·
                refine ⟨285709922934720658984902869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190473281956480439323268579 285709922934720658984902869)
                ·
                  refine ⟨6696326318782515444958661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285709922934720658984902869 6696326318782515444958661)
                  ·
                    refine ⟨1255561184771721645929749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696326318782515444958661 1255561184771721645929749)
                    ·
                      rfl

theorem cell22_3667795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 4].length) (baseStart_3667795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667795 prefixEnd_3667795 := by exact prefixLift 3667795
  have htrace : WordTrace (prefixWord ++ tailWord_3667795) baseStart_3667795 baseEnd_3667795 := by
    simpa [prefixWord, tailWord_3667795, baseEnd_3667795] using wordTrace_append hprefix tailTrace_3667795
  have hstable : (prefixWord ++ tailWord_3667795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667795).length < 2 ^ (prefixWord ++ tailWord_3667795).sum := by decide
  have hdescent : baseEnd_3667795 < baseStart_3667795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667857 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3667857 : Nat := 118140960795 + 3667857 * 2 ^ 59
def prefixEnd_3667857 : Nat := 4983230072969 + 3 ^ 40 * 3667857 * 2
def baseEnd_3667857 : Nat := 1255582408638774150879559

theorem tailTrace_3667857 : CollatzResearch.WordTrace tailWord_3667857 prefixEnd_3667857 1255582408638774150879559 := by
  unfold tailWord_3667857
  simp only [CollatzResearch.WordTrace]
  refine ⟨133777735072987983948857825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89185156715325322632571883 133777735072987983948857825)
  ·
    refine ⟨100333301304740987961643369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133777735072987983948857825 100333301304740987961643369)
    ·
      refine ⟨75249975978555740971232527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100333301304740987961643369 75249975978555740971232527)
      ·
        refine ⟨112874963967833611456848791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75249975978555740971232527 112874963967833611456848791)
        ·
          refine ⟨169312445951750417185273187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112874963967833611456848791 169312445951750417185273187)
          ·
            refine ⟨253968668927625625777909781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169312445951750417185273187 253968668927625625777909781)
            ·
              refine ⟨11904781355982451208339521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253968668927625625777909781 11904781355982451208339521)
              ·
                refine ⟨8928586016986838406254641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11904781355982451208339521 8928586016986838406254641)
                ·
                  refine ⟨6696439512740128804690981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928586016986838406254641 6696439512740128804690981)
                  ·
                    refine ⟨1255582408638774150879559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696439512740128804690981 1255582408638774150879559)
                    ·
                      rfl

theorem cell22_3667857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3667857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667857 prefixEnd_3667857 := by exact prefixLift 3667857
  have htrace : WordTrace (prefixWord ++ tailWord_3667857) baseStart_3667857 baseEnd_3667857 := by
    simpa [prefixWord, tailWord_3667857, baseEnd_3667857] using wordTrace_append hprefix tailTrace_3667857
  have hstable : (prefixWord ++ tailWord_3667857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667857).length < 2 ^ (prefixWord ++ tailWord_3667857).sum := by decide
  have hdescent : baseEnd_3667857 < baseStart_3667857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667889 : List Nat := [1, 2, 2, 4, 2, 2, 3, 6]
def baseStart_3667889 : Nat := 118140960795 + 3667889 * 2 ^ 59
def prefixEnd_3667889 : Nat := 4983230072969 + 3 ^ 40 * 3667889 * 2
def baseEnd_3667889 : Nat := 139510373654748526008829

theorem tailTrace_3667889 : CollatzResearch.WordTrace tailWord_3667889 prefixEnd_3667889 139510373654748526008829 := by
  unfold tailWord_3667889
  simp only [CollatzResearch.WordTrace]
  refine ⟨133778902208872053414022721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89185934805914702276015147 133778902208872053414022721)
  ·
    refine ⟨100334176656654040060517041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133778902208872053414022721 100334176656654040060517041)
    ·
      refine ⟨75250632492490530045387781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100334176656654040060517041 75250632492490530045387781)
      ·
        refine ⟨14109493592341974383510209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75250632492490530045387781 14109493592341974383510209)
        ·
          refine ⟨10582120194256480787632657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14109493592341974383510209 10582120194256480787632657)
          ·
            refine ⟨7936590145692360590724493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10582120194256480787632657 7936590145692360590724493)
            ·
              refine ⟨2976221304634635221521685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7936590145692360590724493 2976221304634635221521685)
              ·
                refine ⟨139510373654748526008829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2976221304634635221521685 139510373654748526008829)
                ·
                  rfl

theorem cell22_3667889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 6].length) (baseStart_3667889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667889 prefixEnd_3667889 := by exact prefixLift 3667889
  have htrace : WordTrace (prefixWord ++ tailWord_3667889) baseStart_3667889 baseEnd_3667889 := by
    simpa [prefixWord, tailWord_3667889, baseEnd_3667889] using wordTrace_append hprefix tailTrace_3667889
  have hstable : (prefixWord ++ tailWord_3667889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667889).length < 2 ^ (prefixWord ++ tailWord_3667889).sum := by decide
  have hdescent : baseEnd_3667889 < baseStart_3667889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667947 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 3, 4]
def baseStart_3667947 : Nat := 118140960795 + 3667947 * 2 ^ 59
def prefixEnd_3667947 : Nat := 4983230072969 + 3 ^ 40 * 3667947 * 2
def baseEnd_3667947 : Nat := 1255613217478043916129283

theorem tailTrace_3667947 : CollatzResearch.WordTrace tailWord_3667947 prefixEnd_3667947 1255613217478043916129283 := by
  unfold tailWord_3667947
  simp only [CollatzResearch.WordTrace]
  refine ⟨133781017642661929319634095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89187345095107952879756063 133781017642661929319634095)
  ·
    refine ⟨200671526463992893979451143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133781017642661929319634095 200671526463992893979451143)
    ·
      refine ⟨301007289695989340969176715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200671526463992893979451143 301007289695989340969176715)
      ·
        refine ⟨451510934543984011453765073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301007289695989340969176715 451510934543984011453765073)
        ·
          refine ⟨338633200907988008590323805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451510934543984011453765073 338633200907988008590323805)
          ·
            refine ⟨126987450340495503221371427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338633200907988008590323805 126987450340495503221371427)
            ·
              refine ⟨190481175510743254832057141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126987450340495503221371427 190481175510743254832057141)
              ·
                refine ⟨17857610204132180140505357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190481175510743254832057141 17857610204132180140505357)
                ·
                  refine ⟨6696603826549567552689509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17857610204132180140505357 6696603826549567552689509)
                  ·
                    refine ⟨1255613217478043916129283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696603826549567552689509 1255613217478043916129283)
                    ·
                      rfl

theorem cell22_3667947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_3667947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667947 prefixEnd_3667947 := by exact prefixLift 3667947
  have htrace : WordTrace (prefixWord ++ tailWord_3667947) baseStart_3667947 baseEnd_3667947 := by
    simpa [prefixWord, tailWord_3667947, baseEnd_3667947] using wordTrace_append hprefix tailTrace_3667947
  have hstable : (prefixWord ++ tailWord_3667947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667947).length < 2 ^ (prefixWord ++ tailWord_3667947).sum := by decide
  have hdescent : baseEnd_3667947 < baseStart_3667947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667964 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_3667964 : Nat := 118140960795 + 3667964 * 2 ^ 59
def prefixEnd_3667964 : Nat := 4983230072969 + 3 ^ 40 * 3667964 * 2
def baseEnd_3667964 : Nat := 1255619036925461538454231

theorem tailTrace_3667964 : CollatzResearch.WordTrace tailWord_3667964 prefixEnd_3667964 1255619036925461538454231 := by
  unfold tailWord_3667964
  simp only [CollatzResearch.WordTrace]
  refine ⟨66890818841800170611501473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89187758455733560815335297 66890818841800170611501473)
  ·
    refine ⟨50168114131350127958626105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66890818841800170611501473 50168114131350127958626105)
    ·
      refine ⟨37626085598512595968969579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50168114131350127958626105 37626085598512595968969579)
      ·
        refine ⟨56439128397768893953454369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37626085598512595968969579 56439128397768893953454369)
        ·
          refine ⟨42329346298326670465090777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56439128397768893953454369 42329346298326670465090777)
          ·
            refine ⟨31747009723745002848818083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42329346298326670465090777 31747009723745002848818083)
            ·
              refine ⟨47620514585617504273227125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31747009723745002848818083 47620514585617504273227125)
              ·
                refine ⟨4464423242401641025615043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47620514585617504273227125 4464423242401641025615043)
                ·
                  refine ⟨6696634863602461538422565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464423242401641025615043 6696634863602461538422565)
                  ·
                    refine ⟨1255619036925461538454231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696634863602461538422565 1255619036925461538454231)
                    ·
                      rfl

theorem cell22_3667964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_3667964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667964 prefixEnd_3667964 := by exact prefixLift 3667964
  have htrace : WordTrace (prefixWord ++ tailWord_3667964) baseStart_3667964 baseEnd_3667964 := by
    simpa [prefixWord, tailWord_3667964, baseEnd_3667964] using wordTrace_append hprefix tailTrace_3667964
  have hstable : (prefixWord ++ tailWord_3667964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667964).length < 2 ^ (prefixWord ++ tailWord_3667964).sum := by decide
  have hdescent : baseEnd_3667964 < baseStart_3667964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3667972 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3667972 : Nat := 118140960795 + 3667972 * 2 ^ 59
def prefixEnd_3667972 : Nat := 4983230072969 + 3 ^ 40 * 3667972 * 2
def baseEnd_3667972 : Nat := 1255621775488952184254207

theorem tailTrace_3667972 : CollatzResearch.WordTrace tailWord_3667972 prefixEnd_3667972 1255621775488952184254207 := by
  unfold tailWord_3667972
  simp only [CollatzResearch.WordTrace]
  refine ⟨66890964733785679294647085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89187952978380905726196113 66890964733785679294647085)
  ·
    refine ⟨25084111775169629735492657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66890964733785679294647085 25084111775169629735492657)
    ·
      refine ⟨18813083831377222301619493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25084111775169629735492657 18813083831377222301619493)
      ·
        refine ⟨3527453218383229181553655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18813083831377222301619493 3527453218383229181553655)
        ·
          refine ⟨5291179827574843772330483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3527453218383229181553655 5291179827574843772330483)
          ·
            refine ⟨7936769741362265658495725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291179827574843772330483 7936769741362265658495725)
            ·
              refine ⟨2976288653010849621935897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7936769741362265658495725 2976288653010849621935897)
              ·
                refine ⟨2232216489758137216451923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976288653010849621935897 2232216489758137216451923)
                ·
                  refine ⟨3348324734637205824677885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232216489758137216451923 3348324734637205824677885)
                  ·
                    refine ⟨1255621775488952184254207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3348324734637205824677885 1255621775488952184254207)
                    ·
                      rfl

theorem cell22_3667972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3667972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3667972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3667972 prefixEnd_3667972 := by exact prefixLift 3667972
  have htrace : WordTrace (prefixWord ++ tailWord_3667972) baseStart_3667972 baseEnd_3667972 := by
    simpa [prefixWord, tailWord_3667972, baseEnd_3667972] using wordTrace_append hprefix tailTrace_3667972
  have hstable : (prefixWord ++ tailWord_3667972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3667972).length < 2 ^ (prefixWord ++ tailWord_3667972).sum := by decide
  have hdescent : baseEnd_3667972 < baseStart_3667972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3667972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668024 : List Nat := [2, 1, 2, 1, 7, 9]
def baseStart_3668024 : Nat := 118140960795 + 3668024 * 2 ^ 59
def prefixEnd_3668024 : Nat := 4983230072969 + 3 ^ 40 * 3668024 * 2
def baseEnd_3668024 : Nat := 15501723162365942987087

theorem tailTrace_3668024 : CollatzResearch.WordTrace tailWord_3668024 prefixEnd_3668024 15501723162365942987087 := by
  unfold tailWord_3668024
  simp only [CollatzResearch.WordTrace]
  refine ⟨66891913031691485735093563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89189217375588647646791417 66891913031691485735093563)
  ·
    refine ⟨100337869547537228602640345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66891913031691485735093563 100337869547537228602640345)
    ·
      refine ⟨75253402160652921451980259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100337869547537228602640345 75253402160652921451980259)
      ·
        refine ⟨112880103240979382177970389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75253402160652921451980259 112880103240979382177970389)
        ·
          refine ⟨2645627419710454269796181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 112880103240979382177970389 2645627419710454269796181)
          ·
            refine ⟨15501723162365942987087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2645627419710454269796181 15501723162365942987087)
            ·
              rfl

theorem cell22_3668024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 9].length) (baseStart_3668024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668024 prefixEnd_3668024 := by exact prefixLift 3668024
  have htrace : WordTrace (prefixWord ++ tailWord_3668024) baseStart_3668024 baseEnd_3668024 := by
    simpa [prefixWord, tailWord_3668024, baseEnd_3668024] using wordTrace_append hprefix tailTrace_3668024
  have hstable : (prefixWord ++ tailWord_3668024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668024).length < 2 ^ (prefixWord ++ tailWord_3668024).sum := by decide
  have hdescent : baseEnd_3668024 < baseStart_3668024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668056 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 3, 3]
def baseStart_3668056 : Nat := 118140960795 + 3668056 * 2 ^ 59
def prefixEnd_3668056 : Nat := 4983230072969 + 3 ^ 40 * 3668056 * 2
def baseEnd_3668056 : Nat := 1255650530405603965153949

theorem tailTrace_3668056 : CollatzResearch.WordTrace tailWord_3668056 prefixEnd_3668056 1255650530405603965153949 := by
  unfold tailWord_3668056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66892496599633520467676011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89189995466178027290234681 66892496599633520467676011)
  ·
    refine ⟨100338744899450280701514017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66892496599633520467676011 100338744899450280701514017)
    ·
      refine ⟨75254058674587710526135513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100338744899450280701514017 75254058674587710526135513)
      ·
        refine ⟨56440544005940782894601635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75254058674587710526135513 56440544005940782894601635)
        ·
          refine ⟨84660816008911174341902453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56440544005940782894601635 84660816008911174341902453)
          ·
            refine ⟨7936951500835422594553355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84660816008911174341902453 7936951500835422594553355)
            ·
              refine ⟨11905427251253133891830033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7936951500835422594553355 11905427251253133891830033)
              ·
                refine ⟨8929070438439850418872525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11905427251253133891830033 8929070438439850418872525)
                ·
                  refine ⟨3348401414414943907077197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8929070438439850418872525 3348401414414943907077197)
                  ·
                    refine ⟨1255650530405603965153949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3348401414414943907077197 1255650530405603965153949)
                    ·
                      rfl

theorem cell22_3668056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_3668056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668056 prefixEnd_3668056 := by exact prefixLift 3668056
  have htrace : WordTrace (prefixWord ++ tailWord_3668056) baseStart_3668056 baseEnd_3668056 := by
    simpa [prefixWord, tailWord_3668056, baseEnd_3668056] using wordTrace_append hprefix tailTrace_3668056
  have hstable : (prefixWord ++ tailWord_3668056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668056).length < 2 ^ (prefixWord ++ tailWord_3668056).sum := by decide
  have hdescent : baseEnd_3668056 < baseStart_3668056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668073 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 1, 3]
def baseStart_3668073 : Nat := 118140960795 + 3668073 * 2 ^ 59
def prefixEnd_3668073 : Nat := 4983230072969 + 3 ^ 40 * 3668073 * 2
def baseEnd_3668073 : Nat := 1255656349853021587478897

theorem tailTrace_3668073 : CollatzResearch.WordTrace tailWord_3668073 prefixEnd_3668073 1255656349853021587478897 := by
  unfold tailWord_3668073
  simp only [CollatzResearch.WordTrace]
  refine ⟨133785613240205452838720873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89190408826803635225813915 133785613240205452838720873)
  ·
    refine ⟨100339209930154089629040655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133785613240205452838720873 100339209930154089629040655)
    ·
      refine ⟨150508814895231134443560983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100339209930154089629040655 150508814895231134443560983)
      ·
        refine ⟨225763222342846701665341475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150508814895231134443560983 225763222342846701665341475)
        ·
          refine ⟨338644833514270052498012213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225763222342846701665341475 338644833514270052498012213)
          ·
            refine ⟨31747953141962817421688645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338644833514270052498012213 31747953141962817421688645)
            ·
              refine ⟨5952741214118028266566621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31747953141962817421688645 5952741214118028266566621)
              ·
                refine ⟨2232277955294260599962483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5952741214118028266566621 2232277955294260599962483)
                ·
                  refine ⟨3348416932941390899943725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232277955294260599962483 3348416932941390899943725)
                  ·
                    refine ⟨1255656349853021587478897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3348416932941390899943725 1255656349853021587478897)
                    ·
                      rfl

theorem cell22_3668073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 3].length) (baseStart_3668073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668073 prefixEnd_3668073 := by exact prefixLift 3668073
  have htrace : WordTrace (prefixWord ++ tailWord_3668073) baseStart_3668073 baseEnd_3668073 := by
    simpa [prefixWord, tailWord_3668073, baseEnd_3668073] using wordTrace_append hprefix tailTrace_3668073
  have hstable : (prefixWord ++ tailWord_3668073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668073).length < 2 ^ (prefixWord ++ tailWord_3668073).sum := by decide
  have hdescent : baseEnd_3668073 < baseStart_3668073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668086 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3668086 : Nat := 118140960795 + 3668086 * 2 ^ 59
def prefixEnd_3668086 : Nat := 4983230072969 + 3 ^ 40 * 3668086 * 2
def baseEnd_3668086 : Nat := 418553600006231295634619

theorem tailTrace_3668086 : CollatzResearch.WordTrace tailWord_3668086 prefixEnd_3668086 418553600006231295634619 := by
  unfold tailWord_3668086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361630461822397253684007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89190724926105570705962741 8361630461822397253684007)
  ·
    refine ⟨12542445692733595880526011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8361630461822397253684007 12542445692733595880526011)
    ·
      refine ⟨18813668539100393820789017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12542445692733595880526011 18813668539100393820789017)
      ·
        refine ⟨14110251404325295365591763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18813668539100393820789017 14110251404325295365591763)
        ·
          refine ⟨21165377106487943048387645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14110251404325295365591763 21165377106487943048387645)
          ·
            refine ⟨7937016414932978643145367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21165377106487943048387645 7937016414932978643145367)
            ·
              refine ⟨11905524622399467964718051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7937016414932978643145367 11905524622399467964718051)
              ·
                refine ⟨17858286933599201947077077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11905524622399467964718051 17858286933599201947077077)
                ·
                  refine ⟨418553600006231295634619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17858286933599201947077077 418553600006231295634619)
                  ·
                    rfl

theorem cell22_3668086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3668086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668086 prefixEnd_3668086 := by exact prefixLift 3668086
  have htrace : WordTrace (prefixWord ++ tailWord_3668086) baseStart_3668086 baseEnd_3668086 := by
    simpa [prefixWord, tailWord_3668086, baseEnd_3668086] using wordTrace_append hprefix tailTrace_3668086
  have hstable : (prefixWord ++ tailWord_3668086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668086).length < 2 ^ (prefixWord ++ tailWord_3668086).sum := by decide
  have hdescent : baseEnd_3668086 < baseStart_3668086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668146 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_3668146 : Nat := 118140960795 + 3668146 * 2 ^ 59
def prefixEnd_3668146 : Nat := 4983230072969 + 3 ^ 40 * 3668146 * 2
def baseEnd_3668146 : Nat := 1255681339244873730403673

theorem tailTrace_3668146 : CollatzResearch.WordTrace tailWord_3668146 prefixEnd_3668146 1255681339244873730403673 := by
  unfold tailWord_3668146
  simp only [CollatzResearch.WordTrace]
  refine ⟨33447068942235246576532073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89192183845960657537418861 33447068942235246576532073)
  ·
    refine ⟨25085301706676434932399055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33447068942235246576532073 25085301706676434932399055)
    ·
      refine ⟨37627952560014652398598583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25085301706676434932399055 37627952560014652398598583)
      ·
        refine ⟨56441928840021978597897875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37627952560014652398598583 56441928840021978597897875)
        ·
          refine ⟨84662893260032967896846813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56441928840021978597897875 84662893260032967896846813)
          ·
            refine ⟨31748584972512362961317555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84662893260032967896846813 31748584972512362961317555)
            ·
              refine ⟨47622877458768544441976333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31748584972512362961317555 47622877458768544441976333)
              ·
                refine ⟨17858579047038204165741125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47622877458768544441976333 17858579047038204165741125)
                ·
                  refine ⟨3348483571319663281076461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17858579047038204165741125 3348483571319663281076461)
                  ·
                    refine ⟨1255681339244873730403673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3348483571319663281076461 1255681339244873730403673)
                    ·
                      rfl

theorem cell22_3668146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_3668146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668146 prefixEnd_3668146 := by exact prefixLift 3668146
  have htrace : WordTrace (prefixWord ++ tailWord_3668146) baseStart_3668146 baseEnd_3668146 := by
    simpa [prefixWord, tailWord_3668146, baseEnd_3668146] using wordTrace_append hprefix tailTrace_3668146
  have hstable : (prefixWord ++ tailWord_3668146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668146).length < 2 ^ (prefixWord ++ tailWord_3668146).sum := by decide
  have hdescent : baseEnd_3668146 < baseStart_3668146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668178 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_3668178 : Nat := 118140960795 + 3668178 * 2 ^ 59
def prefixEnd_3668178 : Nat := 4983230072969 + 3 ^ 40 * 3668178 * 2
def baseEnd_3668178 : Nat := 1255692293498836313603575

theorem tailTrace_3668178 : CollatzResearch.WordTrace tailWord_3668178 prefixEnd_3668178 1255692293498836313603575 := by
  unfold tailWord_3668178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33447360726206263942823297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89192961936550037180862125 33447360726206263942823297)
  ·
    refine ⟨25085520544654697957117473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33447360726206263942823297 25085520544654697957117473)
    ·
      refine ⟨18814140408491023467838105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25085520544654697957117473 18814140408491023467838105)
      ·
        refine ⟨14110605306368267600878579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18814140408491023467838105 14110605306368267600878579)
        ·
          refine ⟨21165907959552401401317869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14110605306368267600878579 21165907959552401401317869)
          ·
            refine ⟨7937215484832150525494201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21165907959552401401317869 7937215484832150525494201)
            ·
              refine ⟨5952911613624112894120651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7937215484832150525494201 5952911613624112894120651)
              ·
                refine ⟨8929367420436169341180977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952911613624112894120651 8929367420436169341180977)
                ·
                  refine ⟨6697025565327127005885733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929367420436169341180977 6697025565327127005885733)
                  ·
                    refine ⟨1255692293498836313603575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6697025565327127005885733 1255692293498836313603575)
                    ·
                      rfl

theorem cell22_3668178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_3668178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668178 prefixEnd_3668178 := by exact prefixLift 3668178
  have htrace : WordTrace (prefixWord ++ tailWord_3668178) baseStart_3668178 baseEnd_3668178 := by
    simpa [prefixWord, tailWord_3668178, baseEnd_3668178] using wordTrace_append hprefix tailTrace_3668178
  have hstable : (prefixWord ++ tailWord_3668178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668178).length < 2 ^ (prefixWord ++ tailWord_3668178).sum := by decide
  have hdescent : baseEnd_3668178 < baseStart_3668178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668296 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_3668296 : Nat := 118140960795 + 3668296 * 2 ^ 59
def prefixEnd_3668296 : Nat := 4983230072969 + 3 ^ 40 * 3668296 * 2
def baseEnd_3668296 : Nat := 1255732687310323339153213

theorem tailTrace_3668296 : CollatzResearch.WordTrace tailWord_3668296 prefixEnd_3668296 1255732687310323339153213 := by
  unfold tailWord_3668296
  simp only [CollatzResearch.WordTrace]
  refine ⟨66896873359198780962044371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89195831145598374616059161 66896873359198780962044371)
  ·
    refine ⟨100345310038798171443066557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66896873359198780962044371 100345310038798171443066557)
    ·
      refine ⟨37629491264549314291149959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100345310038798171443066557 37629491264549314291149959)
      ·
        refine ⟨56444236896823971436724939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37629491264549314291149959 56444236896823971436724939)
        ·
          refine ⟨84666355345235957155087409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56444236896823971436724939 84666355345235957155087409)
          ·
            refine ⟨63499766508926967866315557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84666355345235957155087409 63499766508926967866315557)
            ·
              refine ⟨11906206220423806474934167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63499766508926967866315557 11906206220423806474934167)
              ·
                refine ⟨17859309330635709712401251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11906206220423806474934167 17859309330635709712401251)
                ·
                  refine ⟨26788963995953564568601877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17859309330635709712401251 26788963995953564568601877)
                  ·
                    refine ⟨1255732687310323339153213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26788963995953564568601877 1255732687310323339153213)
                    ·
                      rfl

theorem cell22_3668296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_3668296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668296 prefixEnd_3668296 := by exact prefixLift 3668296
  have htrace : WordTrace (prefixWord ++ tailWord_3668296) baseStart_3668296 baseEnd_3668296 := by
    simpa [prefixWord, tailWord_3668296, baseEnd_3668296] using wordTrace_append hprefix tailTrace_3668296
  have hstable : (prefixWord ++ tailWord_3668296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668296).length < 2 ^ (prefixWord ++ tailWord_3668296).sum := by decide
  have hdescent : baseEnd_3668296 < baseStart_3668296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668328 : List Nat := [2, 1, 4, 2, 2, 2, 2, 7]
def baseStart_3668328 : Nat := 118140960795 + 3668328 * 2 ^ 59
def prefixEnd_3668328 : Nat := 4983230072969 + 3 ^ 40 * 3668328 * 2
def baseEnd_3668328 : Nat := 139527071284920658039235

theorem tailTrace_3668328 : CollatzResearch.WordTrace tailWord_3668328 prefixEnd_3668328 139527071284920658039235 := by
  unfold tailWord_3668328
  simp only [CollatzResearch.WordTrace]
  refine ⟨66897456927140815694626819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89196609236187754259502425 66897456927140815694626819)
  ·
    refine ⟨100346185390711223541940229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66897456927140815694626819 100346185390711223541940229)
    ·
      refine ⟨18814909760758354414113793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100346185390711223541940229 18814909760758354414113793)
      ·
        refine ⟨14111182320568765810585345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18814909760758354414113793 14111182320568765810585345)
        ·
          refine ⟨10583386740426574357939009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14111182320568765810585345 10583386740426574357939009)
          ·
            refine ⟨7937540055319930768454257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10583386740426574357939009 7937540055319930768454257)
            ·
              refine ⟨5953155041489948076340693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7937540055319930768454257 5953155041489948076340693)
              ·
                refine ⟨139527071284920658039235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5953155041489948076340693 139527071284920658039235)
                ·
                  rfl

theorem cell22_3668328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 7].length) (baseStart_3668328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668328 prefixEnd_3668328 := by exact prefixLift 3668328
  have htrace : WordTrace (prefixWord ++ tailWord_3668328) baseStart_3668328 baseEnd_3668328 := by
    simpa [prefixWord, tailWord_3668328, baseEnd_3668328] using wordTrace_append hprefix tailTrace_3668328
  have hstable : (prefixWord ++ tailWord_3668328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668328).length < 2 ^ (prefixWord ++ tailWord_3668328).sum := by decide
  have hdescent : baseEnd_3668328 < baseStart_3668328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668486 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3668486 : Nat := 118140960795 + 3668486 * 2 ^ 59
def prefixEnd_3668486 : Nat := 4983230072969 + 3 ^ 40 * 3668486 * 2
def baseEnd_3668486 : Nat := 418599242731075392300877

theorem tailTrace_3668486 : CollatzResearch.WordTrace tailWord_3668486 prefixEnd_3668486 418599242731075392300877 := by
  unfold tailWord_3668486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181271143365913261672041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89200451058472816249003541 4181271143365913261672041)
  ·
    refine ⟨3135953357524434946254031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4181271143365913261672041 3135953357524434946254031)
    ·
      refine ⟨4703930036286652419381047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135953357524434946254031 4703930036286652419381047)
      ·
        refine ⟨7055895054429978629071571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703930036286652419381047 7055895054429978629071571)
        ·
          refine ⟨10583842581644967943607357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055895054429978629071571 10583842581644967943607357)
          ·
            refine ⟨3968940968116862978852759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10583842581644967943607357 3968940968116862978852759)
            ·
              refine ⟨5953411452175294468279139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968940968116862978852759 5953411452175294468279139)
              ·
                refine ⟨8930117178262941702418709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953411452175294468279139 8930117178262941702418709)
                ·
                  refine ⟨418599242731075392300877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8930117178262941702418709 418599242731075392300877)
                  ·
                    rfl

theorem cell22_3668486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3668486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668486 prefixEnd_3668486 := by exact prefixLift 3668486
  have htrace : WordTrace (prefixWord ++ tailWord_3668486) baseStart_3668486 baseEnd_3668486 := by
    simpa [prefixWord, tailWord_3668486, baseEnd_3668486] using wordTrace_append hprefix tailTrace_3668486
  have hstable : (prefixWord ++ tailWord_3668486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668486).length < 2 ^ (prefixWord ++ tailWord_3668486).sum := by decide
  have hdescent : baseEnd_3668486 < baseStart_3668486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668557 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3668557 : Nat := 118140960795 + 3668557 * 2 ^ 59
def prefixEnd_3668557 : Nat := 4983230072969 + 3 ^ 40 * 3668557 * 2
def baseEnd_3668557 : Nat := 1255822032944205658377413

theorem tailTrace_3668557 : CollatzResearch.WordTrace tailWord_3668557 prefixEnd_3668557 1255822032944205658377413 := by
  unfold tailWord_3668557
  simp only [CollatzResearch.WordTrace]
  refine ⟨133803266170452003499339925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89202177446968002332893283 133803266170452003499339925)
  ·
    refine ⟨6272028101739937664031559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133803266170452003499339925 6272028101739937664031559)
    ·
      refine ⟨9408042152609906496047339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272028101739937664031559 9408042152609906496047339)
      ·
        refine ⟨14112063228914859744071009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408042152609906496047339 14112063228914859744071009)
        ·
          refine ⟨10584047421686144808053257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14112063228914859744071009 10584047421686144808053257)
          ·
            refine ⟨7938035566264608606039943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10584047421686144808053257 7938035566264608606039943)
            ·
              refine ⟨11907053349396912909059915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938035566264608606039943 11907053349396912909059915)
              ·
                refine ⟨17860580024095369363589873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11907053349396912909059915 17860580024095369363589873)
                ·
                  refine ⟨13395435018071527022692405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17860580024095369363589873 13395435018071527022692405)
                  ·
                    refine ⟨1255822032944205658377413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13395435018071527022692405 1255822032944205658377413)
                    ·
                      rfl

theorem cell22_3668557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3668557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668557 prefixEnd_3668557 := by exact prefixLift 3668557
  have htrace : WordTrace (prefixWord ++ tailWord_3668557) baseStart_3668557 baseEnd_3668557 := by
    simpa [prefixWord, tailWord_3668557, baseEnd_3668557] using wordTrace_append hprefix tailTrace_3668557
  have hstable : (prefixWord ++ tailWord_3668557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668557).length < 2 ^ (prefixWord ++ tailWord_3668557).sum := by decide
  have hdescent : baseEnd_3668557 < baseStart_3668557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668585 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_3668585 : Nat := 118140960795 + 3668585 * 2 ^ 59
def prefixEnd_3668585 : Nat := 4983230072969 + 3 ^ 40 * 3668585 * 2
def baseEnd_3668585 : Nat := 1255831617916422918677327

theorem tailTrace_3668585 : CollatzResearch.WordTrace tailWord_3668585 prefixEnd_3668585 1255831617916422918677327 := by
  unfold tailWord_3668585
  simp only [CollatzResearch.WordTrace]
  refine ⟨133804287414350564281359209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89202858276233709520906139 133804287414350564281359209)
  ·
    refine ⟨100353215560762923211019407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133804287414350564281359209 100353215560762923211019407)
    ·
      refine ⟨150529823341144384816529111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100353215560762923211019407 150529823341144384816529111)
      ·
        refine ⟨225794735011716577224793667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150529823341144384816529111 225794735011716577224793667)
        ·
          refine ⟨338692102517574865837190501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225794735011716577224793667 338692102517574865837190501)
          ·
            refine ⟨63504769222045287344473219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338692102517574865837190501 63504769222045287344473219)
            ·
              refine ⟨95257153833067931016709829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63504769222045287344473219 95257153833067931016709829)
              ·
                refine ⟨17860716343700237065633093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95257153833067931016709829 17860716343700237065633093)
                ·
                  refine ⟨3348884314443794449806205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17860716343700237065633093 3348884314443794449806205)
                  ·
                    refine ⟨1255831617916422918677327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3348884314443794449806205 1255831617916422918677327)
                    ·
                      rfl

theorem cell22_3668585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_3668585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668585 prefixEnd_3668585 := by exact prefixLift 3668585
  have htrace : WordTrace (prefixWord ++ tailWord_3668585) baseStart_3668585 baseEnd_3668585 := by
    simpa [prefixWord, tailWord_3668585, baseEnd_3668585] using wordTrace_append hprefix tailTrace_3668585
  have hstable : (prefixWord ++ tailWord_3668585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668585).length < 2 ^ (prefixWord ++ tailWord_3668585).sum := by decide
  have hdescent : baseEnd_3668585 < baseStart_3668585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668589 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_3668589 : Nat := 118140960795 + 3668589 * 2 ^ 59
def prefixEnd_3668589 : Nat := 4983230072969 + 3 ^ 40 * 3668589 * 2
def baseEnd_3668589 : Nat := 1255832987198168241577315

theorem tailTrace_3668589 : CollatzResearch.WordTrace tailWord_3668589 prefixEnd_3668589 1255832987198168241577315 := by
  unfold tailWord_3668589
  simp only [CollatzResearch.WordTrace]
  refine ⟨133804433306336072964504821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89202955537557381976336547 133804433306336072964504821)
  ·
    refine ⟨12544165622469006840422327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133804433306336072964504821 12544165622469006840422327)
    ·
      refine ⟨18816248433703510260633491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12544165622469006840422327 18816248433703510260633491)
      ·
        refine ⟨28224372650555265390950237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18816248433703510260633491 28224372650555265390950237)
        ·
          refine ⟨10584139743958224521606339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28224372650555265390950237 10584139743958224521606339)
          ·
            refine ⟨15876209615937336782409509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584139743958224521606339 15876209615937336782409509)
            ·
              refine ⟨2976789302988250646701783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15876209615937336782409509 2976789302988250646701783)
              ·
                refine ⟨4465183954482375970052675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976789302988250646701783 4465183954482375970052675)
                ·
                  refine ⟨6697775931723563955079013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465183954482375970052675 6697775931723563955079013)
                  ·
                    refine ⟨1255832987198168241577315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6697775931723563955079013 1255832987198168241577315)
                    ·
                      rfl

theorem cell22_3668589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_3668589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668589 prefixEnd_3668589 := by exact prefixLift 3668589
  have htrace : WordTrace (prefixWord ++ tailWord_3668589) baseStart_3668589 baseEnd_3668589 := by
    simpa [prefixWord, tailWord_3668589, baseEnd_3668589] using wordTrace_append hprefix tailTrace_3668589
  have hstable : (prefixWord ++ tailWord_3668589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668589).length < 2 ^ (prefixWord ++ tailWord_3668589).sum := by decide
  have hdescent : baseEnd_3668589 < baseStart_3668589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668720 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_3668720 : Nat := 118140960795 + 3668720 * 2 ^ 59
def prefixEnd_3668720 : Nat := 4983230072969 + 3 ^ 40 * 3668720 * 2
def baseEnd_3668720 : Nat := 1255877831175327566551913

theorem tailTrace_3668720 : CollatzResearch.WordTrace tailWord_3668720 prefixEnd_3668720 1255877831175327566551913 := by
  unfold tailWord_3668720
  simp only [CollatzResearch.WordTrace]
  refine ⟨66904605634430741168761807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89206140845907654891682409 66904605634430741168761807)
  ·
    refine ⟨100356908451646111753142711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66904605634430741168761807 100356908451646111753142711)
    ·
      refine ⟨150535362677469167629714067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100356908451646111753142711 150535362677469167629714067)
      ·
        refine ⟨225803044016203751444571101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150535362677469167629714067 225803044016203751444571101)
        ·
          refine ⟨84676141506076406791714163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225803044016203751444571101 84676141506076406791714163)
          ·
            refine ⟨127014212259114610187571245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84676141506076406791714163 127014212259114610187571245)
            ·
              refine ⟨47630329597167978820339217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127014212259114610187571245 47630329597167978820339217)
              ·
                refine ⟨35722747197875984115254413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47630329597167978820339217 35722747197875984115254413)
                ·
                  refine ⟨13396030199203494043220405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35722747197875984115254413 13396030199203494043220405)
                  ·
                    refine ⟨1255877831175327566551913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13396030199203494043220405 1255877831175327566551913)
                    ·
                      rfl

theorem cell22_3668720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_3668720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668720 prefixEnd_3668720 := by exact prefixLift 3668720
  have htrace : WordTrace (prefixWord ++ tailWord_3668720) baseStart_3668720 baseEnd_3668720 := by
    simpa [prefixWord, tailWord_3668720, baseEnd_3668720] using wordTrace_append hprefix tailTrace_3668720
  have hstable : (prefixWord ++ tailWord_3668720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668720).length < 2 ^ (prefixWord ++ tailWord_3668720).sum := by decide
  have hdescent : baseEnd_3668720 < baseStart_3668720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668735 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_3668735 : Nat := 118140960795 + 3668735 * 2 ^ 59
def prefixEnd_3668735 : Nat := 4983230072969 + 3 ^ 40 * 3668735 * 2
def baseEnd_3668735 : Nat := 1255882965981872527426867

theorem tailTrace_3668735 : CollatzResearch.WordTrace tailWord_3668735 prefixEnd_3668735 1255882965981872527426867 := by
  unfold tailWord_3668735
  simp only [CollatzResearch.WordTrace]
  refine ⟨133809758363807139899319659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89206505575871426599546439 133809758363807139899319659)
  ·
    refine ⟨200714637545710709848979489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133809758363807139899319659 200714637545710709848979489)
    ·
      refine ⟨150535978159283032386734617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200714637545710709848979489 150535978159283032386734617)
      ·
        refine ⟨112901983619462274290050963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150535978159283032386734617 112901983619462274290050963)
        ·
          refine ⟨169352975429193411435076445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112901983619462274290050963 169352975429193411435076445)
          ·
            refine ⟨63507365785947529288153667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169352975429193411435076445 63507365785947529288153667)
            ·
              refine ⟨95261048678921293932230501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63507365785947529288153667 95261048678921293932230501)
              ·
                refine ⟨17861446627297742612293219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95261048678921293932230501 17861446627297742612293219)
                ·
                  refine ⟨26792169940946613918439829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17861446627297742612293219 26792169940946613918439829)
                  ·
                    refine ⟨1255882965981872527426867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26792169940946613918439829 1255882965981872527426867)
                    ·
                      rfl

theorem cell22_3668735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_3668735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668735 prefixEnd_3668735 := by exact prefixLift 3668735
  have htrace : WordTrace (prefixWord ++ tailWord_3668735) baseStart_3668735 baseEnd_3668735 := by
    simpa [prefixWord, tailWord_3668735, baseEnd_3668735] using wordTrace_append hprefix tailTrace_3668735
  have hstable : (prefixWord ++ tailWord_3668735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668735).length < 2 ^ (prefixWord ++ tailWord_3668735).sum := by decide
  have hdescent : baseEnd_3668735 < baseStart_3668735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668737 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3668737 : Nat := 118140960795 + 3668737 * 2 ^ 59
def prefixEnd_3668737 : Nat := 4983230072969 + 3 ^ 40 * 3668737 * 2
def baseEnd_3668737 : Nat := 1255883650622745188876861

theorem tailTrace_3668737 : CollatzResearch.WordTrace tailWord_3668737 prefixEnd_3668737 1255883650622745188876861 := by
  unfold tailWord_3668737
  simp only [CollatzResearch.WordTrace]
  refine ⟨133809831309799894240892465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89206554206533262827261643 133809831309799894240892465)
  ·
    refine ⟨100357373482349920680669349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133809831309799894240892465 100357373482349920680669349)
    ·
      refine ⟨18817007527940610127625503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100357373482349920680669349 18817007527940610127625503)
      ·
        refine ⟨28225511291910915191438255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18817007527940610127625503 28225511291910915191438255)
        ·
          refine ⟨42338266937866372787157383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28225511291910915191438255 42338266937866372787157383)
          ·
            refine ⟨63507400406799559180736075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42338266937866372787157383 63507400406799559180736075)
            ·
              refine ⟨95261100610199338771104113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63507400406799559180736075 95261100610199338771104113)
              ·
                refine ⟨71445825457649504078328085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95261100610199338771104113 71445825457649504078328085)
                ·
                  refine ⟨3349023068327320503671629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71445825457649504078328085 3349023068327320503671629)
                  ·
                    refine ⟨1255883650622745188876861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349023068327320503671629 1255883650622745188876861)
                    ·
                      rfl

theorem cell22_3668737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3668737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668737 prefixEnd_3668737 := by exact prefixLift 3668737
  have htrace : WordTrace (prefixWord ++ tailWord_3668737) baseStart_3668737 baseEnd_3668737 := by
    simpa [prefixWord, tailWord_3668737, baseEnd_3668737] using wordTrace_append hprefix tailTrace_3668737
  have hstable : (prefixWord ++ tailWord_3668737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668737).length < 2 ^ (prefixWord ++ tailWord_3668737).sum := by decide
  have hdescent : baseEnd_3668737 < baseStart_3668737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668788 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3668788 : Nat := 118140960795 + 3668788 * 2 ^ 59
def prefixEnd_3668788 : Nat := 4983230072969 + 3 ^ 40 * 3668788 * 2
def baseEnd_3668788 : Nat := 1255901108964998055851705

theorem tailTrace_3668788 : CollatzResearch.WordTrace tailWord_3668788 prefixEnd_3668788 1255901108964998055851705 := by
  unfold tailWord_3668788
  simp only [CollatzResearch.WordTrace]
  refine ⟨66905845716307564975499509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89207794288410086633999345 66905845716307564975499509)
  ·
    refine ⟨6272423035903834216453079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66905845716307564975499509 6272423035903834216453079)
    ·
      refine ⟨9408634553855751324679619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272423035903834216453079 9408634553855751324679619)
      ·
        refine ⟨14112951830783626987019429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408634553855751324679619 14112951830783626987019429)
        ·
          refine ⟨2646178468271930060066143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14112951830783626987019429 2646178468271930060066143)
          ·
            refine ⟨3969267702407895090099215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646178468271930060066143 3969267702407895090099215)
            ·
              refine ⟨5953901553611842635148823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969267702407895090099215 5953901553611842635148823)
              ·
                refine ⟨8930852330417763952723235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953901553611842635148823 8930852330417763952723235)
                ·
                  refine ⟨13396278495626645929084853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8930852330417763952723235 13396278495626645929084853)
                  ·
                    refine ⟨1255901108964998055851705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13396278495626645929084853 1255901108964998055851705)
                    ·
                      rfl

theorem cell22_3668788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3668788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668788 prefixEnd_3668788 := by exact prefixLift 3668788
  have htrace : WordTrace (prefixWord ++ tailWord_3668788) baseStart_3668788 baseEnd_3668788 := by
    simpa [prefixWord, tailWord_3668788, baseEnd_3668788] using wordTrace_append hprefix tailTrace_3668788
  have hstable : (prefixWord ++ tailWord_3668788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668788).length < 2 ^ (prefixWord ++ tailWord_3668788).sum := by decide
  have hdescent : baseEnd_3668788 < baseStart_3668788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668799 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 3, 3]
def baseStart_3668799 : Nat := 118140960795 + 3668799 * 2 ^ 59
def prefixEnd_3668799 : Nat := 4983230072969 + 3 ^ 40 * 3668799 * 2
def baseEnd_3668799 : Nat := 1255904874489797693826671

theorem tailTrace_3668799 : CollatzResearch.WordTrace tailWord_3668799 prefixEnd_3668799 1255904874489797693826671 := by
  unfold tailWord_3668799
  simp only [CollatzResearch.WordTrace]
  refine ⟨133812092635575278829649451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89208061757050185886432967 133812092635575278829649451)
  ·
    refine ⟨200718138953362918244474177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133812092635575278829649451 200718138953362918244474177)
    ·
      refine ⟨150538604215022188683355633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200718138953362918244474177 150538604215022188683355633)
      ·
        refine ⟨112903953161266641512516725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150538604215022188683355633 112903953161266641512516725)
        ·
          refine ⟨10584745608868747641798443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112903953161266641512516725 10584745608868747641798443)
          ·
            refine ⟨15877118413303121462697665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584745608868747641798443 15877118413303121462697665)
            ·
              refine ⟨11907838809977341097023249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15877118413303121462697665 11907838809977341097023249)
              ·
                refine ⟨8930879107483005822767437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11907838809977341097023249 8930879107483005822767437)
                ·
                  refine ⟨3349079665306127183537789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8930879107483005822767437 3349079665306127183537789)
                  ·
                    refine ⟨1255904874489797693826671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349079665306127183537789 1255904874489797693826671)
                    ·
                      rfl

theorem cell22_3668799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 3].length) (baseStart_3668799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668799 prefixEnd_3668799 := by exact prefixLift 3668799
  have htrace : WordTrace (prefixWord ++ tailWord_3668799) baseStart_3668799 baseEnd_3668799 := by
    simpa [prefixWord, tailWord_3668799, baseEnd_3668799] using wordTrace_append hprefix tailTrace_3668799
  have hstable : (prefixWord ++ tailWord_3668799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668799).length < 2 ^ (prefixWord ++ tailWord_3668799).sum := by decide
  have hdescent : baseEnd_3668799 < baseStart_3668799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668812 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 7]
def baseStart_3668812 : Nat := 118140960795 + 3668812 * 2 ^ 59
def prefixEnd_3668812 : Nat := 4983230072969 + 3 ^ 40 * 3668812 * 2
def baseEnd_3668812 : Nat := 418636441551823331083877

theorem tailTrace_3668812 : CollatzResearch.WordTrace tailWord_3668812 prefixEnd_3668812 418636441551823331083877 := by
  unfold tailWord_3668812
  simp only [CollatzResearch.WordTrace]
  refine ⟨66906283392264091024936345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89208377856352121366581793 66906283392264091024936345)
  ·
    refine ⟨50179712544198068268702259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66906283392264091024936345 50179712544198068268702259)
    ·
      refine ⟨75269568816297102403053389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50179712544198068268702259 75269568816297102403053389)
      ·
        refine ⟨28226088306111413401145021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75269568816297102403053389 28226088306111413401145021)
        ·
          refine ⟨10584783114791780025429383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28226088306111413401145021 10584783114791780025429383)
          ·
            refine ⟨15877174672187670038144075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584783114791780025429383 15877174672187670038144075)
            ·
              refine ⟨23815762008281505057216113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15877174672187670038144075 23815762008281505057216113)
              ·
                refine ⟨17861821506211128792912085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23815762008281505057216113 17861821506211128792912085)
                ·
                  refine ⟨418636441551823331083877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17861821506211128792912085 418636441551823331083877)
                  ·
                    rfl

theorem cell22_3668812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_3668812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668812 prefixEnd_3668812 := by exact prefixLift 3668812
  have htrace : WordTrace (prefixWord ++ tailWord_3668812) baseStart_3668812 baseEnd_3668812 := by
    simpa [prefixWord, tailWord_3668812, baseEnd_3668812] using wordTrace_append hprefix tailTrace_3668812
  have hstable : (prefixWord ++ tailWord_3668812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668812).length < 2 ^ (prefixWord ++ tailWord_3668812).sum := by decide
  have hdescent : baseEnd_3668812 < baseStart_3668812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668816 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 1, 3]
def baseStart_3668816 : Nat := 118140960795 + 3668816 * 2 ^ 59
def prefixEnd_3668816 : Nat := 4983230072969 + 3 ^ 40 * 3668816 * 2
def baseEnd_3668816 : Nat := 1255910693937215316151619

theorem tailTrace_3668816 : CollatzResearch.WordTrace tailWord_3668816 prefixEnd_3668816 1255910693937215316151619 := by
  unfold tailWord_3668816
  simp only [CollatzResearch.WordTrace]
  refine ⟨66906356338256845366509151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89208475117675793822012201 66906356338256845366509151)
  ·
    refine ⟨100359534507385268049763727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66906356338256845366509151 100359534507385268049763727)
    ·
      refine ⟨150539301761077902074645591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100359534507385268049763727 150539301761077902074645591)
      ·
        refine ⟨225808952641616853111968387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150539301761077902074645591 225808952641616853111968387)
        ·
          refine ⟨338713428962425279667952581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225808952641616853111968387 338713428962425279667952581)
          ·
            refine ⟨63508767930454739937741109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338713428962425279667952581 63508767930454739937741109)
            ·
              refine ⟨5953946993480131869163229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63508767930454739937741109 5953946993480131869163229)
              ·
                refine ⟨2232730122555049450936211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5953946993480131869163229 2232730122555049450936211)
                ·
                  refine ⟨3349095183832574176404317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232730122555049450936211 3349095183832574176404317)
                  ·
                    refine ⟨1255910693937215316151619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349095183832574176404317 1255910693937215316151619)
                    ·
                      rfl

theorem cell22_3668816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_3668816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668816 prefixEnd_3668816 := by exact prefixLift 3668816
  have htrace : WordTrace (prefixWord ++ tailWord_3668816) baseStart_3668816 baseEnd_3668816 := by
    simpa [prefixWord, tailWord_3668816, baseEnd_3668816] using wordTrace_append hprefix tailTrace_3668816
  have hstable : (prefixWord ++ tailWord_3668816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668816).length < 2 ^ (prefixWord ++ tailWord_3668816).sum := by decide
  have hdescent : baseEnd_3668816 < baseStart_3668816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668846 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_3668846 : Nat := 118140960795 + 3668846 * 2 ^ 59
def prefixEnd_3668846 : Nat := 4983230072969 + 3 ^ 40 * 3668846 * 2
def baseEnd_3668846 : Nat := 418640321183435079300509

theorem tailTrace_3668846 : CollatzResearch.WordTrace tailWord_3668846 prefixEnd_3668846 418640321183435079300509 := by
  unfold tailWord_3668846
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726725858300625732076299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89209204577603337237740261 16726725858300625732076299)
  ·
    refine ⟨25090088787450938598114449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16726725858300625732076299 25090088787450938598114449)
    ·
      refine ⟨18817566590588203948585837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25090088787450938598114449 18817566590588203948585837)
      ·
        refine ⟨7056587471470576480719689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18817566590588203948585837 7056587471470576480719689)
        ·
          refine ⟨5292440603602932360539767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7056587471470576480719689 5292440603602932360539767)
          ·
            refine ⟨7938660905404398540809651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292440603602932360539767 7938660905404398540809651)
            ·
              refine ⟨11907991358106597811214477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938660905404398540809651 11907991358106597811214477)
              ·
                refine ⟨4465496759289974179205429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11907991358106597811214477 4465496759289974179205429)
                ·
                  refine ⟨418640321183435079300509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4465496759289974179205429 418640321183435079300509)
                  ·
                    rfl

theorem cell22_3668846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_3668846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668846 prefixEnd_3668846 := by exact prefixLift 3668846
  have htrace : WordTrace (prefixWord ++ tailWord_3668846) baseStart_3668846 baseEnd_3668846 := by
    simpa [prefixWord, tailWord_3668846, baseEnd_3668846] using wordTrace_append hprefix tailTrace_3668846
  have hstable : (prefixWord ++ tailWord_3668846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668846).length < 2 ^ (prefixWord ++ tailWord_3668846).sum := by decide
  have hdescent : baseEnd_3668846 < baseStart_3668846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668859 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 1, 4]
def baseStart_3668859 : Nat := 118140960795 + 3668859 * 2 ^ 59
def prefixEnd_3668859 : Nat := 4983230072969 + 3 ^ 40 * 3668859 * 2
def baseEnd_3668859 : Nat := 1255925413715977537326487

theorem tailTrace_3668859 : CollatzResearch.WordTrace tailWord_3668859 prefixEnd_3668859 1255925413715977537326487 := by
  unfold tailWord_3668859
  simp only [CollatzResearch.WordTrace]
  refine ⟨133814281015357909076833631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89209520676905272717889087 133814281015357909076833631)
  ·
    refine ⟨200721421523036863615250447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133814281015357909076833631 200721421523036863615250447)
    ·
      refine ⟨301082132284555295422875671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200721421523036863615250447 301082132284555295422875671)
      ·
        refine ⟨451623198426832943134313507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301082132284555295422875671 451623198426832943134313507)
        ·
          refine ⟨677434797640249414701470261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451623198426832943134313507 677434797640249414701470261)
          ·
            refine ⟨63509512278773382628262837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 677434797640249414701470261 63509512278773382628262837)
            ·
              refine ⟨5954016776135004621399641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63509512278773382628262837 5954016776135004621399641)
              ·
                refine ⟨4465512582101253466049731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954016776135004621399641 4465512582101253466049731)
                ·
                  refine ⟨6698268873151880199074597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465512582101253466049731 6698268873151880199074597)
                  ·
                    refine ⟨1255925413715977537326487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698268873151880199074597 1255925413715977537326487)
                    ·
                      rfl

theorem cell22_3668859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 4].length) (baseStart_3668859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668859 prefixEnd_3668859 := by exact prefixLift 3668859
  have htrace : WordTrace (prefixWord ++ tailWord_3668859) baseStart_3668859 baseEnd_3668859 := by
    simpa [prefixWord, tailWord_3668859, baseEnd_3668859] using wordTrace_append hprefix tailTrace_3668859
  have hstable : (prefixWord ++ tailWord_3668859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668859).length < 2 ^ (prefixWord ++ tailWord_3668859).sum := by decide
  have hdescent : baseEnd_3668859 < baseStart_3668859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3668921 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_3668921 : Nat := 118140960795 + 3668921 * 2 ^ 59
def prefixEnd_3668921 : Nat := 4983230072969 + 3 ^ 40 * 3668921 * 2
def baseEnd_3668921 : Nat := 1255946637583030042276297

theorem tailTrace_3668921 : CollatzResearch.WordTrace tailWord_3668921 prefixEnd_3668921 1255946637583030042276297 := by
  unfold tailWord_3668921
  simp only [CollatzResearch.WordTrace]
  refine ⟨133816542341133293665590617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89211028227422195777060411 133816542341133293665590617)
  ·
    refine ⟨100362406755849970249192963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133816542341133293665590617 100362406755849970249192963)
    ·
      refine ⟨150543610133774955373789445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100362406755849970249192963 150543610133774955373789445)
      ·
        refine ⟨28226926900082804132585521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150543610133774955373789445 28226926900082804132585521)
        ·
          refine ⟨21170195175062103099439141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28226926900082804132585521 21170195175062103099439141)
          ·
            refine ⟨3969411595324144331144839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21170195175062103099439141 3969411595324144331144839)
            ·
              refine ⟨5954117392986216496717259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969411595324144331144839 5954117392986216496717259)
              ·
                refine ⟨8931176089479324745075889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954117392986216496717259 8931176089479324745075889)
                ·
                  refine ⟨6698382067109493558806917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931176089479324745075889 6698382067109493558806917)
                  ·
                    refine ⟨1255946637583030042276297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698382067109493558806917 1255946637583030042276297)
                    ·
                      rfl

theorem cell22_3668921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_3668921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3668921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3668921 prefixEnd_3668921 := by exact prefixLift 3668921
  have htrace : WordTrace (prefixWord ++ tailWord_3668921) baseStart_3668921 baseEnd_3668921 := by
    simpa [prefixWord, tailWord_3668921, baseEnd_3668921] using wordTrace_append hprefix tailTrace_3668921
  have hstable : (prefixWord ++ tailWord_3668921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3668921).length < 2 ^ (prefixWord ++ tailWord_3668921).sum := by decide
  have hdescent : baseEnd_3668921 < baseStart_3668921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3668921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669028 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_3669028 : Nat := 118140960795 + 3669028 * 2 ^ 59
def prefixEnd_3669028 : Nat := 4983230072969 + 3 ^ 40 * 3669028 * 2
def baseEnd_3669028 : Nat := 1255983265869717429850969

theorem tailTrace_3669028 : CollatzResearch.WordTrace tailWord_3669028 prefixEnd_3669028 1255983265869717429850969 := by
  unfold tailWord_3669028
  simp only [CollatzResearch.WordTrace]
  refine ⟨66910222475872825469867869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89213629967830433959823825 66910222475872825469867869)
  ·
    refine ⟨25091333428452309551200451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66910222475872825469867869 25091333428452309551200451)
    ·
      refine ⟨37637000142678464326800677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25091333428452309551200451 37637000142678464326800677)
      ·
        refine ⟨7056937526752212061275127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37637000142678464326800677 7056937526752212061275127)
        ·
          refine ⟨10585406290128318091912691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056937526752212061275127 10585406290128318091912691)
          ·
            refine ⟨15878109435192477137869037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10585406290128318091912691 15878109435192477137869037)
            ·
              refine ⟨5954291038197178926700889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15878109435192477137869037 5954291038197178926700889)
              ·
                refine ⟨4465718278647884195025667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954291038197178926700889 4465718278647884195025667)
                ·
                  refine ⟨6698577417971826292538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465718278647884195025667 6698577417971826292538501)
                  ·
                    refine ⟨1255983265869717429850969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698577417971826292538501 1255983265869717429850969)
                    ·
                      rfl

theorem cell22_3669028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_3669028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669028 prefixEnd_3669028 := by exact prefixLift 3669028
  have htrace : WordTrace (prefixWord ++ tailWord_3669028) baseStart_3669028 baseEnd_3669028 := by
    simpa [prefixWord, tailWord_3669028, baseEnd_3669028] using wordTrace_append hprefix tailTrace_3669028
  have hstable : (prefixWord ++ tailWord_3669028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669028).length < 2 ^ (prefixWord ++ tailWord_3669028).sum := by decide
  have hdescent : baseEnd_3669028 < baseStart_3669028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669090 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3669090 : Nat := 118140960795 + 3669090 * 2 ^ 59
def prefixEnd_3669090 : Nat := 4983230072969 + 3 ^ 40 * 3669090 * 2
def baseEnd_3669090 : Nat := 1256004489736769934800779

theorem tailTrace_3669090 : CollatzResearch.WordTrace tailWord_3669090 prefixEnd_3669090 1256004489736769934800779 := by
  unfold tailWord_3669090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33455676569380258882123181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89215137518347357018995149 33455676569380258882123181)
  ·
    refine ⟨12545878713517597080796193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33455676569380258882123181 12545878713517597080796193)
    ·
      refine ⟨9409409035138197810597145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12545878713517597080796193 9409409035138197810597145)
      ·
        refine ⟨7057056776353648357947859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9409409035138197810597145 7057056776353648357947859)
        ·
          refine ⟨10585585164530472536921789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057056776353648357947859 10585585164530472536921789)
          ·
            refine ⟨3969594436698927201345671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10585585164530472536921789 3969594436698927201345671)
            ·
              refine ⟨5954391655048390802018507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969594436698927201345671 5954391655048390802018507)
              ·
                refine ⟨8931587482572586203027761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954391655048390802018507 8931587482572586203027761)
                ·
                  refine ⟨6698690611929439652270821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931587482572586203027761 6698690611929439652270821)
                  ·
                    refine ⟨1256004489736769934800779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698690611929439652270821 1256004489736769934800779)
                    ·
                      rfl

theorem cell22_3669090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3669090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669090 prefixEnd_3669090 := by exact prefixLift 3669090
  have htrace : WordTrace (prefixWord ++ tailWord_3669090) baseStart_3669090 baseEnd_3669090 := by
    simpa [prefixWord, tailWord_3669090, baseEnd_3669090] using wordTrace_append hprefix tailTrace_3669090
  have hstable : (prefixWord ++ tailWord_3669090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669090).length < 2 ^ (prefixWord ++ tailWord_3669090).sum := by decide
  have hdescent : baseEnd_3669090 < baseStart_3669090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669109 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3669109 : Nat := 118140960795 + 3669109 * 2 ^ 59
def prefixEnd_3669109 : Nat := 4983230072969 + 3 ^ 40 * 3669109 * 2
def baseEnd_3669109 : Nat := 1256010993825060218575721

theorem tailTrace_3669109 : CollatzResearch.WordTrace tailWord_3669109 prefixEnd_3669109 1256010993825060218575721 := by
  unfold tailWord_3669109
  simp only [CollatzResearch.WordTrace]
  refine ⟨133823399264452201773434381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89215599509634801182289587 133823399264452201773434381)
  ·
    refine ⟨50183774724169575665037893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133823399264452201773434381 50183774724169575665037893)
    ·
      refine ⟨9409457760781795437194605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50183774724169575665037893 9409457760781795437194605)
      ·
        refine ⟨3528546660293173288947977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9409457760781795437194605 3528546660293173288947977)
        ·
          refine ⟨2646409995219879966710983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3528546660293173288947977 2646409995219879966710983)
          ·
            refine ⟨3969614992829819950066475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646409995219879966710983 3969614992829819950066475)
            ·
              refine ⟨5954422489244729925099713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969614992829819950066475 5954422489244729925099713)
              ·
                refine ⟨4465816866933547443824785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954422489244729925099713 4465816866933547443824785)
                ·
                  refine ⟨3349362650200160582868589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465816866933547443824785 3349362650200160582868589)
                  ·
                    refine ⟨1256010993825060218575721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349362650200160582868589 1256010993825060218575721)
                    ·
                      rfl

theorem cell22_3669109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3669109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669109 prefixEnd_3669109 := by exact prefixLift 3669109
  have htrace : WordTrace (prefixWord ++ tailWord_3669109) baseStart_3669109 baseEnd_3669109 := by
    simpa [prefixWord, tailWord_3669109, baseEnd_3669109] using wordTrace_append hprefix tailTrace_3669109
  have hstable : (prefixWord ++ tailWord_3669109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669109).length < 2 ^ (prefixWord ++ tailWord_3669109).sum := by decide
  have hdescent : baseEnd_3669109 < baseStart_3669109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669154 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3669154 : Nat := 118140960795 + 3669154 * 2 ^ 59
def prefixEnd_3669154 : Nat := 4983230072969 + 3 ^ 40 * 3669154 * 2
def baseEnd_3669154 : Nat := 1256026398244695101200583

theorem tailTrace_3669154 : CollatzResearch.WordTrace tailWord_3669154 prefixEnd_3669154 1256026398244695101200583 := by
  unfold tailWord_3669154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33456260137322293614705629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89216693699526116305881677 33456260137322293614705629)
  ·
    refine ⟨12546097551495860105514611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33456260137322293614705629 12546097551495860105514611)
    ·
      refine ⟨18819146327243790158271917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12546097551495860105514611 18819146327243790158271917)
      ·
        refine ⟨7057179872716421309351969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18819146327243790158271917 7057179872716421309351969)
        ·
          refine ⟨5292884904537315982013977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057179872716421309351969 5292884904537315982013977)
          ·
            refine ⟨3969663678402986986510483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5292884904537315982013977 3969663678402986986510483)
            ·
              refine ⟨5954495517604480479765725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969663678402986986510483 5954495517604480479765725)
              ·
                refine ⟨2232935819101680179912147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5954495517604480479765725 2232935819101680179912147)
                ·
                  refine ⟨3349403728652520269868221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232935819101680179912147 3349403728652520269868221)
                  ·
                    refine ⟨1256026398244695101200583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349403728652520269868221 1256026398244695101200583)
                    ·
                      rfl

theorem cell22_3669154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3669154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669154 prefixEnd_3669154 := by exact prefixLift 3669154
  have htrace : WordTrace (prefixWord ++ tailWord_3669154) baseStart_3669154 baseEnd_3669154 := by
    simpa [prefixWord, tailWord_3669154, baseEnd_3669154] using wordTrace_append hprefix tailTrace_3669154
  have hstable : (prefixWord ++ tailWord_3669154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669154).length < 2 ^ (prefixWord ++ tailWord_3669154).sum := by decide
  have hdescent : baseEnd_3669154 < baseStart_3669154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669197 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3669197 : Nat := 118140960795 + 3669197 * 2 ^ 59
def prefixEnd_3669197 : Nat := 4983230072969 + 3 ^ 40 * 3669197 * 2
def baseEnd_3669197 : Nat := 1256041118023457322375451

theorem tailTrace_3669197 : CollatzResearch.WordTrace tailWord_3669197 prefixEnd_3669197 1256041118023457322375451 := by
  unfold tailWord_3669197
  simp only [CollatzResearch.WordTrace]
  refine ⟨133826608888133392802637845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89217739258755595201758563 133826608888133392802637845)
  ·
    refine ⟨6273122291631252787623649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133826608888133392802637845 6273122291631252787623649)
    ·
      refine ⟨4704841718723439590717737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6273122291631252787623649 4704841718723439590717737)
      ·
        refine ⟨3528631289042579693038303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4704841718723439590717737 3528631289042579693038303)
        ·
          refine ⟨5292946933563869539557455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528631289042579693038303 5292946933563869539557455)
          ·
            refine ⟨7939420400345804309336183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292946933563869539557455 7939420400345804309336183)
            ·
              refine ⟨11909130600518706464004275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939420400345804309336183 11909130600518706464004275)
              ·
                refine ⟨17863695900778059696006413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11909130600518706464004275 17863695900778059696006413)
                ·
                  refine ⟨6698885962791772386002405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17863695900778059696006413 6698885962791772386002405)
                  ·
                    refine ⟨1256041118023457322375451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698885962791772386002405 1256041118023457322375451)
                    ·
                      rfl

theorem cell22_3669197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3669197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669197 prefixEnd_3669197 := by exact prefixLift 3669197
  have htrace : WordTrace (prefixWord ++ tailWord_3669197) baseStart_3669197 baseEnd_3669197 := by
    simpa [prefixWord, tailWord_3669197, baseEnd_3669197] using wordTrace_append hprefix tailTrace_3669197
  have hstable : (prefixWord ++ tailWord_3669197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669197).length < 2 ^ (prefixWord ++ tailWord_3669197).sum := by decide
  have hdescent : baseEnd_3669197 < baseStart_3669197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669223 : List Nat := [1, 1, 5, 3, 3, 9]
def baseStart_3669223 : Nat := 118140960795 + 3669223 * 2 ^ 59
def prefixEnd_3669223 : Nat := 4983230072969 + 3 ^ 40 * 3669223 * 2
def baseEnd_3669223 : Nat := 15506790350059282978091

theorem tailTrace_3669223 : CollatzResearch.WordTrace tailWord_3669223 prefixEnd_3669223 15506790350059282978091 := by
  unfold tailWord_3669223
  simp only [CollatzResearch.WordTrace]
  refine ⟨133827557186039199243084323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89218371457359466162056215 133827557186039199243084323)
  ·
    refine ⟨200741335779058798864626485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133827557186039199243084323 200741335779058798864626485)
    ·
      refine ⟨18819500229286762393558733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200741335779058798864626485 18819500229286762393558733)
      ·
        refine ⟨7057312585982535897584525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18819500229286762393558733 7057312585982535897584525)
        ·
          refine ⟨2646492219743450961594197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7057312585982535897584525 2646492219743450961594197)
          ·
            refine ⟨15506790350059282978091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2646492219743450961594197 15506790350059282978091)
            ·
              rfl

theorem cell22_3669223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 9].length) (baseStart_3669223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669223 prefixEnd_3669223 := by exact prefixLift 3669223
  have htrace : WordTrace (prefixWord ++ tailWord_3669223) baseStart_3669223 baseEnd_3669223 := by
    simpa [prefixWord, tailWord_3669223, baseEnd_3669223] using wordTrace_append hprefix tailTrace_3669223
  have hstable : (prefixWord ++ tailWord_3669223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669223).length < 2 ^ (prefixWord ++ tailWord_3669223).sum := by decide
  have hdescent : baseEnd_3669223 < baseStart_3669223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669272 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 1, 3]
def baseStart_3669272 : Nat := 118140960795 + 3669272 * 2 ^ 59
def prefixEnd_3669272 : Nat := 4983230072969 + 3 ^ 40 * 3669272 * 2
def baseEnd_3669272 : Nat := 1256066792056182126750221

theorem tailTrace_3669272 : CollatzResearch.WordTrace tailWord_3669272 prefixEnd_3669272 1256066792056182126750221 := by
  unfold tailWord_3669272
  simp only [CollatzResearch.WordTrace]
  refine ⟨66914672181430840305809035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89219562908574453741078713 66914672181430840305809035)
  ·
    refine ⟨100372008272146260458713553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66914672181430840305809035 100372008272146260458713553)
    ·
      refine ⟨75279006204109695344035165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100372008272146260458713553 75279006204109695344035165)
      ·
        refine ⟨28229627326541135754013187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75279006204109695344035165 28229627326541135754013187)
        ·
          refine ⟨42344440989811703631019781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28229627326541135754013187 42344440989811703631019781)
          ·
            refine ⟨7939582685589694430816209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42344440989811703631019781 7939582685589694430816209)
            ·
              refine ⟨5954687014192270823112157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939582685589694430816209 5954687014192270823112157)
              ·
                refine ⟨2233007630322101558667059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5954687014192270823112157 2233007630322101558667059)
                ·
                  refine ⟨3349511445483152338000589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233007630322101558667059 3349511445483152338000589)
                  ·
                    refine ⟨1256066792056182126750221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349511445483152338000589 1256066792056182126750221)
                    ·
                      rfl

theorem cell22_3669272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_3669272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669272 prefixEnd_3669272 := by exact prefixLift 3669272
  have htrace : WordTrace (prefixWord ++ tailWord_3669272) baseStart_3669272 baseEnd_3669272 := by
    simpa [prefixWord, tailWord_3669272, baseEnd_3669272] using wordTrace_append hprefix tailTrace_3669272
  have hstable : (prefixWord ++ tailWord_3669272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669272).length < 2 ^ (prefixWord ++ tailWord_3669272).sum := by decide
  have hdescent : baseEnd_3669272 < baseStart_3669272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669285 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 5]
def baseStart_3669285 : Nat := 118140960795 + 3669285 * 2 ^ 59
def prefixEnd_3669285 : Nat := 4983230072969 + 3 ^ 40 * 3669285 * 2
def baseEnd_3669285 : Nat := 418690414073951475391727

theorem tailTrace_3669285 : CollatzResearch.WordTrace tailWord_3669285 prefixEnd_3669285 418690414073951475391727 := by
  unfold tailWord_3669285
  simp only [CollatzResearch.WordTrace]
  refine ⟨133829818511814583831841309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89219879007876389221227539 133829818511814583831841309)
  ·
    refine ⟨50186181941930468936940491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133829818511814583831841309 50186181941930468936940491)
    ·
      refine ⟨75279272912895703405410737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50186181941930468936940491 75279272912895703405410737)
      ·
        refine ⟨56459454684671777554058053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75279272912895703405410737 56459454684671777554058053)
        ·
          refine ⟨10586147753375958291385885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56459454684671777554058053 10586147753375958291385885)
          ·
            refine ⟨3969805407515984359269707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10586147753375958291385885 3969805407515984359269707)
            ·
              refine ⟨5954708111273976538904561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969805407515984359269707 5954708111273976538904561)
              ·
                refine ⟨4466031083455482404178421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954708111273976538904561 4466031083455482404178421)
                ·
                  refine ⟨418690414073951475391727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4466031083455482404178421 418690414073951475391727)
                  ·
                    rfl

theorem cell22_3669285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_3669285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669285 prefixEnd_3669285 := by exact prefixLift 3669285
  have htrace : WordTrace (prefixWord ++ tailWord_3669285) baseStart_3669285 baseEnd_3669285 := by
    simpa [prefixWord, tailWord_3669285, baseEnd_3669285] using wordTrace_append hprefix tailTrace_3669285
  have hstable : (prefixWord ++ tailWord_3669285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669285).length < 2 ^ (prefixWord ++ tailWord_3669285).sum := by decide
  have hdescent : baseEnd_3669285 < baseStart_3669285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669328 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 6, 3]
def baseStart_3669328 : Nat := 118140960795 + 3669328 * 2 ^ 59
def prefixEnd_3669328 : Nat := 4983230072969 + 3 ^ 40 * 3669328 * 2
def baseEnd_3669328 : Nat := 1256085962000616647350049

theorem tailTrace_3669328 : CollatzResearch.WordTrace tailWord_3669328 prefixEnd_3669328 1256085962000616647350049 := by
  unfold tailWord_3669328
  simp only [CollatzResearch.WordTrace]
  refine ⟨66915693425329401087828319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89220924567105868117104425 66915693425329401087828319)
  ·
    refine ⟨100373540137994101631742479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66915693425329401087828319 100373540137994101631742479)
    ·
      refine ⟨150560310206991152447613719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100373540137994101631742479 150560310206991152447613719)
      ·
        refine ⟨225840465310486728671420579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150560310206991152447613719 225840465310486728671420579)
        ·
          refine ⟨338760697965730093007130869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225840465310486728671420579 338760697965730093007130869)
          ·
            refine ⟨31758815434287196219418519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338760697965730093007130869 31758815434287196219418519)
            ·
              refine ⟨47638223151430794329127779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31758815434287196219418519 47638223151430794329127779)
              ·
                refine ⟨71457334727146191493691669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47638223151430794329127779 71457334727146191493691669)
                ·
                  refine ⟨3349562565334977726266797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71457334727146191493691669 3349562565334977726266797)
                  ·
                    refine ⟨1256085962000616647350049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349562565334977726266797 1256085962000616647350049)
                    ·
                      rfl

theorem cell22_3669328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_3669328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669328 prefixEnd_3669328 := by exact prefixLift 3669328
  have htrace : WordTrace (prefixWord ++ tailWord_3669328) baseStart_3669328 baseEnd_3669328 := by
    simpa [prefixWord, tailWord_3669328, baseEnd_3669328] using wordTrace_append hprefix tailTrace_3669328
  have hstable : (prefixWord ++ tailWord_3669328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669328).length < 2 ^ (prefixWord ++ tailWord_3669328).sum := by decide
  have hdescent : baseEnd_3669328 < baseStart_3669328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669347 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 4]
def baseStart_3669347 : Nat := 118140960795 + 3669347 * 2 ^ 59
def prefixEnd_3669347 : Nat := 4983230072969 + 3 ^ 40 * 3669347 * 2
def baseEnd_3669347 : Nat := 418697488696302310374997

theorem tailTrace_3669347 : CollatzResearch.WordTrace tailWord_3669347 prefixEnd_3669347 418697488696302310374997 := by
  unfold tailWord_3669347
  simp only [CollatzResearch.WordTrace]
  refine ⟨133832079837589968420598295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89221386558393312280398863 133832079837589968420598295)
  ·
    refine ⟨200748119756384952630897443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133832079837589968420598295 200748119756384952630897443)
    ·
      refine ⟨301122179634577428946346165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200748119756384952630897443 301122179634577428946346165)
      ·
        refine ⟨28230204340741633963719953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301122179634577428946346165 28230204340741633963719953)
        ·
          refine ⟨21172653255556225472789965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28230204340741633963719953 21172653255556225472789965)
          ·
            refine ⟨7939744970833584552296237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21172653255556225472789965 7939744970833584552296237)
            ·
              refine ⟨2977404364062594207111089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7939744970833584552296237 2977404364062594207111089)
              ·
                refine ⟨2233053273046945655333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977404364062594207111089 2233053273046945655333317)
                ·
                  refine ⟨418697488696302310374997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233053273046945655333317 418697488696302310374997)
                  ·
                    rfl

theorem cell22_3669347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 4].length) (baseStart_3669347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669347 prefixEnd_3669347 := by exact prefixLift 3669347
  have htrace : WordTrace (prefixWord ++ tailWord_3669347) baseStart_3669347 baseEnd_3669347 := by
    simpa [prefixWord, tailWord_3669347, baseEnd_3669347] using wordTrace_append hprefix tailTrace_3669347
  have hstable : (prefixWord ++ tailWord_3669347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669347).length < 2 ^ (prefixWord ++ tailWord_3669347).sum := by decide
  have hdescent : baseEnd_3669347 < baseStart_3669347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669377 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3669377 : Nat := 118140960795 + 3669377 * 2 ^ 59
def prefixEnd_3669377 : Nat := 4983230072969 + 3 ^ 40 * 3669377 * 2
def baseEnd_3669377 : Nat := 1256102735701996852874899

theorem tailTrace_3669377 : CollatzResearch.WordTrace tailWord_3669377 prefixEnd_3669377 1256102735701996852874899 := by
  unfold tailWord_3669377
  simp only [CollatzResearch.WordTrace]
  refine ⟨133833174027481283544190385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89222116018320855696126923 133833174027481283544190385)
  ·
    refine ⟨100374880520610962658142789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133833174027481283544190385 100374880520610962658142789)
    ·
      refine ⟨18820290097614555498401773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100374880520610962658142789 18820290097614555498401773)
      ·
        refine ⟨7057608786605458311900665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18820290097614555498401773 7057608786605458311900665)
        ·
          refine ⟨5293206589954093733925499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057608786605458311900665 5293206589954093733925499)
          ·
            refine ⟨7939809884931140600888249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5293206589954093733925499 7939809884931140600888249)
            ·
              refine ⟨5954857413698355450666187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939809884931140600888249 5954857413698355450666187)
              ·
                refine ⟨8932286120547533175999281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954857413698355450666187 8932286120547533175999281)
                ·
                  refine ⟨6699214590410649881999461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8932286120547533175999281 6699214590410649881999461)
                  ·
                    refine ⟨1256102735701996852874899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6699214590410649881999461 1256102735701996852874899)
                    ·
                      rfl

theorem cell22_3669377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3669377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669377 prefixEnd_3669377 := by exact prefixLift 3669377
  have htrace : WordTrace (prefixWord ++ tailWord_3669377) baseStart_3669377 baseEnd_3669377 := by
    simpa [prefixWord, tailWord_3669377, baseEnd_3669377] using wordTrace_append hprefix tailTrace_3669377
  have hstable : (prefixWord ++ tailWord_3669377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669377).length < 2 ^ (prefixWord ++ tailWord_3669377).sum := by decide
  have hdescent : baseEnd_3669377 < baseStart_3669377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669448 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_3669448 : Nat := 118140960795 + 3669448 * 2 ^ 59
def prefixEnd_3669448 : Nat := 4983230072969 + 3 ^ 40 * 3669448 * 2
def baseEnd_3669448 : Nat := 418709013484325444783227

theorem tailTrace_3669448 : CollatzResearch.WordTrace tailWord_3669448 prefixEnd_3669448 418709013484325444783227 := by
  unfold tailWord_3669448
  simp only [CollatzResearch.WordTrace]
  refine ⟨66917881805112031335012499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89223842406816041780016665 66917881805112031335012499)
  ·
    refine ⟨100376822707668047002518749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66917881805112031335012499 100376822707668047002518749)
    ·
      refine ⟨37641308515375517625944531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100376822707668047002518749 37641308515375517625944531)
      ·
        refine ⟨56461962773063276438916797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37641308515375517625944531 56461962773063276438916797)
        ·
          refine ⟨21173236039898728664593799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56461962773063276438916797 21173236039898728664593799)
          ·
            refine ⟨31759854059848092996890699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21173236039898728664593799 31759854059848092996890699)
            ·
              refine ⟨47639781089772139495336049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31759854059848092996890699 47639781089772139495336049)
              ·
                refine ⟨35729835817329104621502037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47639781089772139495336049 35729835817329104621502037)
                ·
                  refine ⟨418709013484325444783227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35729835817329104621502037 418709013484325444783227)
                  ·
                    rfl

theorem cell22_3669448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_3669448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669448 prefixEnd_3669448 := by exact prefixLift 3669448
  have htrace : WordTrace (prefixWord ++ tailWord_3669448) baseStart_3669448 baseEnd_3669448 := by
    simpa [prefixWord, tailWord_3669448, baseEnd_3669448] using wordTrace_append hprefix tailTrace_3669448
  have hstable : (prefixWord ++ tailWord_3669448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669448).length < 2 ^ (prefixWord ++ tailWord_3669448).sum := by decide
  have hdescent : baseEnd_3669448 < baseStart_3669448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669463 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3669463 : Nat := 118140960795 + 3669463 * 2 ^ 59
def prefixEnd_3669463 : Nat := 4983230072969 + 3 ^ 40 * 3669463 * 2
def baseEnd_3669463 : Nat := 1256132175259521295224635

theorem tailTrace_3669463 : CollatzResearch.WordTrace tailWord_3669463 prefixEnd_3669463 1256132175259521295224635 := by
  unfold tailWord_3669463
  simp only [CollatzResearch.WordTrace]
  refine ⟨133836310705169720231821043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89224207136779813487880695 133836310705169720231821043)
  ·
    refine ⟨200754466057754580347731565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133836310705169720231821043 200754466057754580347731565)
    ·
      refine ⟨75282924771657967630399337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200754466057754580347731565 75282924771657967630399337)
      ·
        refine ⟨56462193578743475722799503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75282924771657967630399337 56462193578743475722799503)
        ·
          refine ⟨84693290368115213584199255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56462193578743475722799503 84693290368115213584199255)
          ·
            refine ⟨127039935552172820376298883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84693290368115213584199255 127039935552172820376298883)
            ·
              refine ⟨190559903328259230564448325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127039935552172820376298883 190559903328259230564448325)
              ·
                refine ⟨35729981874048605730834061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190559903328259230564448325 35729981874048605730834061)
                ·
                  refine ⟨13398743202768227149062773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35729981874048605730834061 13398743202768227149062773)
                  ·
                    refine ⟨1256132175259521295224635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13398743202768227149062773 1256132175259521295224635)
                    ·
                      rfl

theorem cell22_3669463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3669463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669463 prefixEnd_3669463 := by exact prefixLift 3669463
  have htrace : WordTrace (prefixWord ++ tailWord_3669463) baseStart_3669463 baseEnd_3669463 := by
    simpa [prefixWord, tailWord_3669463, baseEnd_3669463] using wordTrace_append hprefix tailTrace_3669463
  have hstable : (prefixWord ++ tailWord_3669463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669463).length < 2 ^ (prefixWord ++ tailWord_3669463).sum := by decide
  have hdescent : baseEnd_3669463 < baseStart_3669463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669465 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 6]
def baseStart_3669465 : Nat := 118140960795 + 3669465 * 2 ^ 59
def prefixEnd_3669465 : Nat := 4983230072969 + 3 ^ 40 * 3669465 * 2
def baseEnd_3669465 : Nat := 418710953300131318891543

theorem tailTrace_3669465 : CollatzResearch.WordTrace tailWord_3669465 prefixEnd_3669465 418710953300131318891543 := by
  unfold tailWord_3669465
  simp only [CollatzResearch.WordTrace]
  refine ⟨133836383651162474573393849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89224255767441649715595899 133836383651162474573393849)
  ·
    refine ⟨100377287738371855930045387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133836383651162474573393849 100377287738371855930045387)
    ·
      refine ⟨150565931607557783895068081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100377287738371855930045387 150565931607557783895068081)
      ·
        refine ⟨112924448705668337921301061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150565931607557783895068081 112924448705668337921301061)
        ·
          refine ⟨21173334132312813360243949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112924448705668337921301061 21173334132312813360243949)
          ·
            refine ⟨7940000299617305010091481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21173334132312813360243949 7940000299617305010091481)
            ·
              refine ⟨5955000224712978757568611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940000299617305010091481 5955000224712978757568611)
              ·
                refine ⟨8932500337069468136352917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955000224712978757568611 8932500337069468136352917)
                ·
                  refine ⟨418710953300131318891543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8932500337069468136352917 418710953300131318891543)
                  ·
                    rfl

theorem cell22_3669465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_3669465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669465 prefixEnd_3669465 := by exact prefixLift 3669465
  have htrace : WordTrace (prefixWord ++ tailWord_3669465) baseStart_3669465 baseEnd_3669465 := by
    simpa [prefixWord, tailWord_3669465, baseEnd_3669465] using wordTrace_append hprefix tailTrace_3669465
  have hstable : (prefixWord ++ tailWord_3669465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669465).length < 2 ^ (prefixWord ++ tailWord_3669465).sum := by decide
  have hdescent : baseEnd_3669465 < baseStart_3669465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669585 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3669585 : Nat := 118140960795 + 3669585 * 2 ^ 59
def prefixEnd_3669585 : Nat := 4983230072969 + 3 ^ 40 * 3669585 * 2
def baseEnd_3669585 : Nat := 1256173938352753643674261

theorem tailTrace_3669585 : CollatzResearch.WordTrace tailWord_3669585 prefixEnd_3669585 1256173938352753643674261 := by
  unfold tailWord_3669585
  simp only [CollatzResearch.WordTrace]
  refine ⟨133840760410727735067762209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89227173607151823378508139 133840760410727735067762209)
  ·
    refine ⟨100380570308045801300821657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133840760410727735067762209 100380570308045801300821657)
    ·
      refine ⟨75285427731034350975616243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100380570308045801300821657 75285427731034350975616243)
      ·
        refine ⟨112928141596551526463424365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75285427731034350975616243 112928141596551526463424365)
        ·
          refine ⟨42348053098706822423784137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112928141596551526463424365 42348053098706822423784137)
          ·
            refine ⟨31761039824030116817838103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42348053098706822423784137 31761039824030116817838103)
            ·
              refine ⟨47641559736045175226757155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31761039824030116817838103 47641559736045175226757155)
              ·
                refine ⟨71462339604067762840135733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47641559736045175226757155 71462339604067762840135733)
                ·
                  refine ⟨6699594337881352766262725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71462339604067762840135733 6699594337881352766262725)
                  ·
                    refine ⟨1256173938352753643674261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6699594337881352766262725 1256173938352753643674261)
                    ·
                      rfl

theorem cell22_3669585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3669585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669585 prefixEnd_3669585 := by exact prefixLift 3669585
  have htrace : WordTrace (prefixWord ++ tailWord_3669585) baseStart_3669585 baseEnd_3669585 := by
    simpa [prefixWord, tailWord_3669585, baseEnd_3669585] using wordTrace_append hprefix tailTrace_3669585
  have hstable : (prefixWord ++ tailWord_3669585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669585).length < 2 ^ (prefixWord ++ tailWord_3669585).sum := by decide
  have hdescent : baseEnd_3669585 < baseStart_3669585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669632 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_3669632 : Nat := 118140960795 + 3669632 * 2 ^ 59
def prefixEnd_3669632 : Nat := 4983230072969 + 3 ^ 40 * 3669632 * 2
def baseEnd_3669632 : Nat := 1256190027413261187749117

theorem tailTrace_3669632 : CollatzResearch.WordTrace tailWord_3669632 prefixEnd_3669632 1256190027413261187749117 := by
  unfold tailWord_3669632
  simp only [CollatzResearch.WordTrace]
  refine ⟨66921237320778731047361575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89228316427704974729815433 66921237320778731047361575)
  ·
    refine ⟨100381855981168096571042363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66921237320778731047361575 100381855981168096571042363)
    ·
      refine ⟨150572783971752144856563545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100381855981168096571042363 150572783971752144856563545)
      ·
        refine ⟨112929587978814108642422659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150572783971752144856563545 112929587978814108642422659)
        ·
          refine ⟨169394381968221162963633989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112929587978814108642422659 169394381968221162963633989)
          ·
            refine ⟨31761446619041468055681373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169394381968221162963633989 31761446619041468055681373)
            ·
              refine ⟨11910542482140550520880515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31761446619041468055681373 11910542482140550520880515)
              ·
                refine ⟨17865813723210825781320773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11910542482140550520880515 17865813723210825781320773)
                ·
                  refine ⟨3349840073102029833997645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17865813723210825781320773 3349840073102029833997645)
                  ·
                    refine ⟨1256190027413261187749117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349840073102029833997645 1256190027413261187749117)
                    ·
                      rfl

theorem cell22_3669632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_3669632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669632 prefixEnd_3669632 := by exact prefixLift 3669632
  have htrace : WordTrace (prefixWord ++ tailWord_3669632) baseStart_3669632 baseEnd_3669632 := by
    simpa [prefixWord, tailWord_3669632, baseEnd_3669632] using wordTrace_append hprefix tailTrace_3669632
  have hstable : (prefixWord ++ tailWord_3669632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669632).length < 2 ^ (prefixWord ++ tailWord_3669632).sum := by decide
  have hdescent : baseEnd_3669632 < baseStart_3669632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669786 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_3669786 : Nat := 118140960795 + 3669786 * 2 ^ 59
def prefixEnd_3669786 : Nat := 4983230072969 + 3 ^ 40 * 3669786 * 2
def baseEnd_3669786 : Nat := 418747581586818706466215

theorem tailTrace_3669786 : CollatzResearch.WordTrace tailWord_3669786 prefixEnd_3669786 418747581586818706466215 := by
  unfold tailWord_3669786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462022870749886598957303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89232060988666364263886141 33462022870749886598957303)
  ·
    refine ⟨50193034306124829898435955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462022870749886598957303 50193034306124829898435955)
    ·
      refine ⟨75289551459187244847653933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193034306124829898435955 75289551459187244847653933)
      ·
        refine ⟨28233581797195216817870225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75289551459187244847653933 28233581797195216817870225)
        ·
          refine ⟨21175186347896412613402669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28233581797195216817870225 21175186347896412613402669)
          ·
            refine ⟨7940694880461154730026001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21175186347896412613402669 7940694880461154730026001)
            ·
              refine ⟨5955521160345866047519501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940694880461154730026001 5955521160345866047519501)
              ·
                refine ⟨2233320435129699767819813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5955521160345866047519501 2233320435129699767819813)
                ·
                  refine ⟨418747581586818706466215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233320435129699767819813 418747581586818706466215)
                  ·
                    rfl

theorem cell22_3669786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_3669786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669786 prefixEnd_3669786 := by exact prefixLift 3669786
  have htrace : WordTrace (prefixWord ++ tailWord_3669786) baseStart_3669786 baseEnd_3669786 := by
    simpa [prefixWord, tailWord_3669786, baseEnd_3669786] using wordTrace_append hprefix tailTrace_3669786
  have hstable : (prefixWord ++ tailWord_3669786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669786).length < 2 ^ (prefixWord ++ tailWord_3669786).sum := by decide
  have hdescent : baseEnd_3669786 < baseStart_3669786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669797 : List Nat := [1, 3, 1, 2, 3, 3, 9]
def baseStart_3669797 : Nat := 118140960795 + 3669797 * 2 ^ 59
def prefixEnd_3669797 : Nat := 4983230072969 + 3 ^ 40 * 3669797 * 2
def baseEnd_3669797 : Nat := 46527648529083546569393

theorem tailTrace_3669797 : CollatzResearch.WordTrace tailWord_3669797 prefixEnd_3669797 46527648529083546569393 := by
  unfold tailWord_3669797
  simp only [CollatzResearch.WordTrace]
  refine ⟨133848492685959695274479645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89232328457306463516319763 133848492685959695274479645)
  ·
    refine ⟨50193184757234885727929867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133848492685959695274479645 50193184757234885727929867)
    ·
      refine ⟨75289777135852328591894801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193184757234885727929867 75289777135852328591894801)
      ·
        refine ⟨56467332851889246443921101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75289777135852328591894801 56467332851889246443921101)
        ·
          refine ⟨21175249819458467416470413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56467332851889246443921101 21175249819458467416470413)
          ·
            refine ⟨7940718682296925281176405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21175249819458467416470413 7940718682296925281176405)
            ·
              refine ⟨46527648529083546569393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7940718682296925281176405 46527648529083546569393)
              ·
                rfl

theorem cell22_3669797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 9].length) (baseStart_3669797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669797 prefixEnd_3669797 := by exact prefixLift 3669797
  have htrace : WordTrace (prefixWord ++ tailWord_3669797) baseStart_3669797 baseEnd_3669797 := by
    simpa [prefixWord, tailWord_3669797, baseEnd_3669797] using wordTrace_append hprefix tailTrace_3669797
  have hstable : (prefixWord ++ tailWord_3669797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669797).length < 2 ^ (prefixWord ++ tailWord_3669797).sum := by decide
  have hdescent : baseEnd_3669797 < baseStart_3669797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669818 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_3669818 : Nat := 118140960795 + 3669818 * 2 ^ 59
def prefixEnd_3669818 : Nat := 4983230072969 + 3 ^ 40 * 3669818 * 2
def baseEnd_3669818 : Nat := 1256253699014418702598547

theorem tailTrace_3669818 : CollatzResearch.WordTrace tailWord_3669818 prefixEnd_3669818 1256253699014418702598547 := by
  unfold tailWord_3669818
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462314654720903965248527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89232839079255743907329405 33462314654720903965248527)
  ·
    refine ⟨50193471982081355947872791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462314654720903965248527 50193471982081355947872791)
    ·
      refine ⟨75290207973122033921809187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193471982081355947872791 75290207973122033921809187)
      ·
        refine ⟨112935311959683050882713781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75290207973122033921809187 112935311959683050882713781)
        ·
          refine ⟨10587685496220286020254417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112935311959683050882713781 10587685496220286020254417)
          ·
            refine ⟨7940764122165214515190813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10587685496220286020254417 7940764122165214515190813)
            ·
              refine ⟨2977786545811955443196555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7940764122165214515190813 2977786545811955443196555)
              ·
                refine ⟨4466679818717933164794833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977786545811955443196555 4466679818717933164794833)
                ·
                  refine ⟨3350009864038449873596125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466679818717933164794833 3350009864038449873596125)
                  ·
                    refine ⟨1256253699014418702598547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3350009864038449873596125 1256253699014418702598547)
                    ·
                      rfl

theorem cell22_3669818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_3669818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669818 prefixEnd_3669818 := by exact prefixLift 3669818
  have htrace : WordTrace (prefixWord ++ tailWord_3669818) baseStart_3669818 baseEnd_3669818 := by
    simpa [prefixWord, tailWord_3669818, baseEnd_3669818] using wordTrace_append hprefix tailTrace_3669818
  have hstable : (prefixWord ++ tailWord_3669818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669818).length < 2 ^ (prefixWord ++ tailWord_3669818).sum := by decide
  have hdescent : baseEnd_3669818 < baseStart_3669818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669829 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_3669829 : Nat := 118140960795 + 3669829 * 2 ^ 59
def prefixEnd_3669829 : Nat := 4983230072969 + 3 ^ 40 * 3669829 * 2
def baseEnd_3669829 : Nat := 1256257464539218340573513

theorem tailTrace_3669829 : CollatzResearch.WordTrace tailWord_3669829 prefixEnd_3669829 1256257464539218340573513 := by
  unfold tailWord_3669829
  simp only [CollatzResearch.WordTrace]
  refine ⟨133849659821843764739644541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89233106547895843159763027 133849659821843764739644541)
  ·
    refine ⟨50193622433191411777366703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133849659821843764739644541 50193622433191411777366703)
    ·
      refine ⟨75290433649787117666050055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193622433191411777366703 75290433649787117666050055)
      ·
        refine ⟨112935650474680676499075083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75290433649787117666050055 112935650474680676499075083)
        ·
          refine ⟨169403475712021014748612625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112935650474680676499075083 169403475712021014748612625)
          ·
            refine ⟨127052606784015761061459469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169403475712021014748612625 127052606784015761061459469)
            ·
              refine ⟨47644727544005910398047301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127052606784015761061459469 47644727544005910398047301)
              ·
                refine ⟨8933386414501108199633869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47644727544005910398047301 8933386414501108199633869)
                ·
                  refine ⟨3350019905437915574862701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8933386414501108199633869 3350019905437915574862701)
                  ·
                    refine ⟨1256257464539218340573513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3350019905437915574862701 1256257464539218340573513)
                    ·
                      rfl

theorem cell22_3669829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_3669829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669829 prefixEnd_3669829 := by exact prefixLift 3669829
  have htrace : WordTrace (prefixWord ++ tailWord_3669829) baseStart_3669829 baseEnd_3669829 := by
    simpa [prefixWord, tailWord_3669829, baseEnd_3669829] using wordTrace_append hprefix tailTrace_3669829
  have hstable : (prefixWord ++ tailWord_3669829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669829).length < 2 ^ (prefixWord ++ tailWord_3669829).sum := by decide
  have hdescent : baseEnd_3669829 < baseStart_3669829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669872 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_3669872 : Nat := 118140960795 + 3669872 * 2 ^ 59
def prefixEnd_3669872 : Nat := 4983230072969 + 3 ^ 40 * 3669872 * 2
def baseEnd_3669872 : Nat := 1256272184317980561748381

theorem tailTrace_3669872 : CollatzResearch.WordTrace tailWord_3669872 prefixEnd_3669872 1256272184317980561748381 := by
  unfold tailWord_3669872
  simp only [CollatzResearch.WordTrace]
  refine ⟨66925614080343991541729935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89234152107125322055639913 66925614080343991541729935)
  ·
    refine ⟨100388421120515987312594903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66925614080343991541729935 100388421120515987312594903)
    ·
      refine ⟨150582631680773980968892355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100388421120515987312594903 150582631680773980968892355)
      ·
        refine ⟨225873947521160971453338533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150582631680773980968892355 225873947521160971453338533)
        ·
          refine ⟨42351365160217682147500975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225873947521160971453338533 42351365160217682147500975)
          ·
            refine ⟨63527047740326523221251463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42351365160217682147500975 63527047740326523221251463)
            ·
              refine ⟨95290571610489784831877195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63527047740326523221251463 95290571610489784831877195)
              ·
                refine ⟨142935857415734677247815793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95290571610489784831877195 142935857415734677247815793)
                ·
                  refine ⟨107201893061801007935861845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142935857415734677247815793 107201893061801007935861845)
                  ·
                    refine ⟨1256272184317980561748381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107201893061801007935861845 1256272184317980561748381)
                    ·
                      rfl

theorem cell22_3669872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_3669872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669872 prefixEnd_3669872 := by exact prefixLift 3669872
  have htrace : WordTrace (prefixWord ++ tailWord_3669872) baseStart_3669872 baseEnd_3669872 := by
    simpa [prefixWord, tailWord_3669872, baseEnd_3669872] using wordTrace_append hprefix tailTrace_3669872
  have hstable : (prefixWord ++ tailWord_3669872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669872).length < 2 ^ (prefixWord ++ tailWord_3669872).sum := by decide
  have hdescent : baseEnd_3669872 < baseStart_3669872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669887 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 8]
def baseStart_3669887 : Nat := 118140960795 + 3669887 * 2 ^ 59
def prefixEnd_3669887 : Nat := 4983230072969 + 3 ^ 40 * 3669887 * 2
def baseEnd_3669887 : Nat := 418759106374841840874445

theorem tailTrace_3669887 : CollatzResearch.WordTrace tailWord_3669887 prefixEnd_3669887 418759106374841840874445 := by
  unfold tailWord_3669887
  simp only [CollatzResearch.WordTrace]
  refine ⟨133851775255633640645255915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89234516837089093763503943 133851775255633640645255915)
  ·
    refine ⟨200777662883450460967883873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133851775255633640645255915 200777662883450460967883873)
    ·
      refine ⟨150583247162587845725912905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200777662883450460967883873 150583247162587845725912905)
      ·
        refine ⟨112937435371940884294434679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150583247162587845725912905 112937435371940884294434679)
        ·
          refine ⟨169406153057911326441652019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112937435371940884294434679 169406153057911326441652019)
          ·
            refine ⟨254109229586866989662478029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169406153057911326441652019 254109229586866989662478029)
            ·
              refine ⟨95290961095075121123429261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254109229586866989662478029 95290961095075121123429261)
              ·
                refine ⟨35734110410653170421285973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95290961095075121123429261 35734110410653170421285973)
                ·
                  refine ⟨418759106374841840874445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35734110410653170421285973 418759106374841840874445)
                  ·
                    rfl

theorem cell22_3669887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_3669887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669887 prefixEnd_3669887 := by exact prefixLift 3669887
  have htrace : WordTrace (prefixWord ++ tailWord_3669887) baseStart_3669887 baseEnd_3669887 := by
    simpa [prefixWord, tailWord_3669887, baseEnd_3669887] using wordTrace_append hprefix tailTrace_3669887
  have hstable : (prefixWord ++ tailWord_3669887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669887).length < 2 ^ (prefixWord ++ tailWord_3669887).sum := by decide
  have hdescent : baseEnd_3669887 < baseStart_3669887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3669998 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3669998 : Nat := 118140960795 + 3669998 * 2 ^ 59
def prefixEnd_3669998 : Nat := 4983230072969 + 3 ^ 40 * 3669998 * 2
def baseEnd_3669998 : Nat := 1256315316692958233097995

theorem tailTrace_3669998 : CollatzResearch.WordTrace tailWord_3669998 prefixEnd_3669998 1256315316692958233097995 := by
  unfold tailWord_3669998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16731977969778938325318331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89237215838821004401697765 16731977969778938325318331)
  ·
    refine ⟨25097966954668407487977497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16731977969778938325318331 25097966954668407487977497)
    ·
      refine ⟨18823475216001305615983123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25097966954668407487977497 18823475216001305615983123)
      ·
        refine ⟨28235212824001958423974685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18823475216001305615983123 28235212824001958423974685)
        ·
          refine ⟨10588204809000734408990507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28235212824001958423974685 10588204809000734408990507)
          ·
            refine ⟨15882307213501101613485761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588204809000734408990507 15882307213501101613485761)
            ·
              refine ⟨11911730410125826210114321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15882307213501101613485761 11911730410125826210114321)
              ·
                refine ⟨8933797807594369657585741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11911730410125826210114321 8933797807594369657585741)
                ·
                  refine ⟨3350174177847888621594653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8933797807594369657585741 3350174177847888621594653)
                  ·
                    refine ⟨1256315316692958233097995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3350174177847888621594653 1256315316692958233097995)
                    ·
                      rfl

theorem cell22_3669998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3669998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3669998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3669998 prefixEnd_3669998 := by exact prefixLift 3669998
  have htrace : WordTrace (prefixWord ++ tailWord_3669998) baseStart_3669998 baseEnd_3669998 := by
    simpa [prefixWord, tailWord_3669998, baseEnd_3669998] using wordTrace_append hprefix tailTrace_3669998
  have hstable : (prefixWord ++ tailWord_3669998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3669998).length < 2 ^ (prefixWord ++ tailWord_3669998).sum := by decide
  have hdescent : baseEnd_3669998 < baseStart_3669998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3669998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670045 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 5]
def baseStart_3670045 : Nat := 118140960795 + 3670045 * 2 ^ 59
def prefixEnd_3670045 : Nat := 4983230072969 + 3 ^ 40 * 3670045 * 2
def baseEnd_3670045 : Nat := 418777135251155259057617

theorem tailTrace_3670045 : CollatzResearch.WordTrace tailWord_3670045 prefixEnd_3670045 418777135251155259057617 := by
  unfold tailWord_3670045
  simp only [CollatzResearch.WordTrace]
  refine ⟨133857537989061233629507589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89238358659374155753005059 133857537989061233629507589)
  ·
    refine ⟨25098288372948981305532673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133857537989061233629507589 25098288372948981305532673)
    ·
      refine ⟨18823716279711735979149505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25098288372948981305532673 18823716279711735979149505)
      ·
        refine ⟨14117787209783801984362129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18823716279711735979149505 14117787209783801984362129)
        ·
          refine ⟨10588340407337851488271597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14117787209783801984362129 10588340407337851488271597)
          ·
            refine ⟨3970627652751694308101849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10588340407337851488271597 3970627652751694308101849)
            ·
              refine ⟨2977970739563770731076387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970627652751694308101849 2977970739563770731076387)
              ·
                refine ⟨4466956109345656096614581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977970739563770731076387 4466956109345656096614581)
                ·
                  refine ⟨418777135251155259057617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4466956109345656096614581 418777135251155259057617)
                  ·
                    rfl

theorem cell22_3670045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_3670045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670045 prefixEnd_3670045 := by exact prefixLift 3670045
  have htrace : WordTrace (prefixWord ++ tailWord_3670045) baseStart_3670045 baseEnd_3670045 := by
    simpa [prefixWord, tailWord_3670045, baseEnd_3670045] using wordTrace_append hprefix tailTrace_3670045
  have hstable : (prefixWord ++ tailWord_3670045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670045).length < 2 ^ (prefixWord ++ tailWord_3670045).sum := by decide
  have hdescent : baseEnd_3670045 < baseStart_3670045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670058 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3670058 : Nat := 118140960795 + 3670058 * 2 ^ 59
def prefixEnd_3670058 : Nat := 4983230072969 + 3 ^ 40 * 3670058 * 2
def baseEnd_3670058 : Nat := 1256335855919138076597811

theorem tailTrace_3670058 : CollatzResearch.WordTrace tailWord_3670058 prefixEnd_3670058 1256335855919138076597811 := by
  unfold tailWord_3670058
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464503034503534212432707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89238674758676091233153885 33464503034503534212432707)
  ·
    refine ⟨50196754551755301318649061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33464503034503534212432707 50196754551755301318649061)
    ·
      refine ⟨9411891478454118997246699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50196754551755301318649061 9411891478454118997246699)
      ·
        refine ⟨14117837217681178495870049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411891478454118997246699 14117837217681178495870049)
        ·
          refine ⟨10588377913260883871902537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14117837217681178495870049 10588377913260883871902537)
          ·
            refine ⟨7941283434945662903926903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10588377913260883871902537 7941283434945662903926903)
            ·
              refine ⟨11911925152418494355890355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941283434945662903926903 11911925152418494355890355)
              ·
                refine ⟨17867887728627741533835533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11911925152418494355890355 17867887728627741533835533)
                ·
                  refine ⟨6700457898235403075188325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17867887728627741533835533 6700457898235403075188325)
                  ·
                    refine ⟨1256335855919138076597811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6700457898235403075188325 1256335855919138076597811)
                    ·
                      rfl

theorem cell22_3670058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3670058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670058 prefixEnd_3670058 := by exact prefixLift 3670058
  have htrace : WordTrace (prefixWord ++ tailWord_3670058) baseStart_3670058 baseEnd_3670058 := by
    simpa [prefixWord, tailWord_3670058, baseEnd_3670058] using wordTrace_append hprefix tailTrace_3670058
  have hstable : (prefixWord ++ tailWord_3670058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670058).length < 2 ^ (prefixWord ++ tailWord_3670058).sum := by decide
  have hdescent : baseEnd_3670058 < baseStart_3670058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670071 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 6, 3]
def baseStart_3670071 : Nat := 118140960795 + 3670071 * 2 ^ 59
def prefixEnd_3670071 : Nat := 4983230072969 + 3 ^ 40 * 3670071 * 2
def baseEnd_3670071 : Nat := 1256340306084810376022771

theorem tailTrace_3670071 : CollatzResearch.WordTrace tailWord_3670071 prefixEnd_3670071 1256340306084810376022771 := by
  unfold tailWord_3670071
  simp only [CollatzResearch.WordTrace]
  refine ⟨133858486286967040069954067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89238990857978026713302711 133858486286967040069954067)
  ·
    refine ⟨200787729430450560104931101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133858486286967040069954067 200787729430450560104931101)
    ·
      refine ⟨75295398536418960039349163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200787729430450560104931101 75295398536418960039349163)
      ·
        refine ⟨112943097804628440059023745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75295398536418960039349163 112943097804628440059023745)
        ·
          refine ⟨84707323353471330044267809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112943097804628440059023745 84707323353471330044267809)
          ·
            refine ⟨63530492515103497533200857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84707323353471330044267809 63530492515103497533200857)
            ·
              refine ⟨47647869386327623149900643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63530492515103497533200857 47647869386327623149900643)
              ·
                refine ⟨71471804079491434724850965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47647869386327623149900643 71471804079491434724850965)
                ·
                  refine ⟨3350240816226161002727389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71471804079491434724850965 3350240816226161002727389)
                  ·
                    refine ⟨1256340306084810376022771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3350240816226161002727389 1256340306084810376022771)
                    ·
                      rfl

theorem cell22_3670071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_3670071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670071 prefixEnd_3670071 := by exact prefixLift 3670071
  have htrace : WordTrace (prefixWord ++ tailWord_3670071) baseStart_3670071 baseEnd_3670071 := by
    simpa [prefixWord, tailWord_3670071, baseEnd_3670071] using wordTrace_append hprefix tailTrace_3670071
  have hstable : (prefixWord ++ tailWord_3670071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670071).length < 2 ^ (prefixWord ++ tailWord_3670071).sum := by decide
  have hdescent : baseEnd_3670071 < baseStart_3670071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670084 : List Nat := [2, 3, 17]
def baseStart_3670084 : Nat := 118140960795 + 3670084 * 2 ^ 59
def prefixEnd_3670084 : Nat := 4983230072969 + 3 ^ 40 * 3670084 * 2
def baseEnd_3670084 : Nat := 574460336648597473913

theorem tailTrace_3670084 : CollatzResearch.WordTrace tailWord_3670084 prefixEnd_3670084 574460336648597473913 := by
  unfold tailWord_3670084
  simp only [CollatzResearch.WordTrace]
  refine ⟨66929480217959971645088653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89239306957279962193451537 66929480217959971645088653)
  ·
    refine ⟨25098555081734989366908245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66929480217959971645088653 25098555081734989366908245)
    ·
      refine ⟨574460336648597473913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 25098555081734989366908245 574460336648597473913)
      ·
        rfl

theorem cell22_3670084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 17].length) (baseStart_3670084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670084 prefixEnd_3670084 := by exact prefixLift 3670084
  have htrace : WordTrace (prefixWord ++ tailWord_3670084) baseStart_3670084 baseEnd_3670084 := by
    simpa [prefixWord, tailWord_3670084, baseEnd_3670084] using wordTrace_append hprefix tailTrace_3670084
  have hstable : (prefixWord ++ tailWord_3670084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670084).length < 2 ^ (prefixWord ++ tailWord_3670084).sum := by decide
  have hdescent : baseEnd_3670084 < baseStart_3670084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670101 : List Nat := [1, 3, 2, 2, 1, 3, 3, 7]
def baseStart_3670101 : Nat := 118140960795 + 3670101 * 2 ^ 59
def prefixEnd_3670101 : Nat := 4983230072969 + 3 ^ 40 * 3670101 * 2
def baseEnd_3670101 : Nat := 139594508410877810863631

theorem tailTrace_3670101 : CollatzResearch.WordTrace tailWord_3670101 prefixEnd_3670101 139594508410877810863631 := by
  unfold tailWord_3670101
  simp only [CollatzResearch.WordTrace]
  refine ⟨133859580476858355193546157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89239720317905570129030771 133859580476858355193546157)
  ·
    refine ⟨50197342678821883197579809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133859580476858355193546157 50197342678821883197579809)
    ·
      refine ⟨37648007009116412398184857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50197342678821883197579809 37648007009116412398184857)
      ·
        refine ⟨28236005256837309298638643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37648007009116412398184857 28236005256837309298638643)
        ·
          refine ⟨42354007885255963947957965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28236005256837309298638643 42354007885255963947957965)
          ·
            refine ⟨15882752956970986480484237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42354007885255963947957965 15882752956970986480484237)
            ·
              refine ⟨5956032358864119930181589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15882752956970986480484237 5956032358864119930181589)
              ·
                refine ⟨139594508410877810863631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5956032358864119930181589 139594508410877810863631)
                ·
                  rfl

theorem cell22_3670101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 7].length) (baseStart_3670101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670101 prefixEnd_3670101 := by exact prefixLift 3670101
  have htrace : WordTrace (prefixWord ++ tailWord_3670101) baseStart_3670101 baseEnd_3670101 := by
    simpa [prefixWord, tailWord_3670101, baseEnd_3670101] using wordTrace_append hprefix tailTrace_3670101
  have hstable : (prefixWord ++ tailWord_3670101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670101).length < 2 ^ (prefixWord ++ tailWord_3670101).sum := by decide
  have hdescent : baseEnd_3670101 < baseStart_3670101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670208 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_3670208 : Nat := 118140960795 + 3670208 * 2 ^ 59
def prefixEnd_3670208 : Nat := 4983230072969 + 3 ^ 40 * 3670208 * 2
def baseEnd_3670208 : Nat := 418795734661529228449117

theorem tailTrace_3670208 : CollatzResearch.WordTrace tailWord_3670208 prefixEnd_3670208 418795734661529228449117 := by
  unfold tailWord_3670208
  simp only [CollatzResearch.WordTrace]
  refine ⟨66931741543735356233845639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89242322058313808311794185 66931741543735356233845639)
  ·
    refine ⟨100397612315603034350768459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66931741543735356233845639 100397612315603034350768459)
    ·
      refine ⟨150596418473404551526152689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100397612315603034350768459 150596418473404551526152689)
      ·
        refine ⟨112947313855053413644614517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150596418473404551526152689 112947313855053413644614517)
        ·
          refine ⟨10588810673911257529182611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112947313855053413644614517 10588810673911257529182611)
          ·
            refine ⟨15883216010866886293773917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588810673911257529182611 15883216010866886293773917)
            ·
              refine ⟨5956206004075082360165219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15883216010866886293773917 5956206004075082360165219)
              ·
                refine ⟨8934309006112623540247829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956206004075082360165219 8934309006112623540247829)
                ·
                  refine ⟨418795734661529228449117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8934309006112623540247829 418795734661529228449117)
                  ·
                    rfl

theorem cell22_3670208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_3670208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670208 prefixEnd_3670208 := by exact prefixLift 3670208
  have htrace : WordTrace (prefixWord ++ tailWord_3670208) baseStart_3670208 baseEnd_3670208 := by
    simpa [prefixWord, tailWord_3670208, baseEnd_3670208] using wordTrace_append hprefix tailTrace_3670208
  have hstable : (prefixWord ++ tailWord_3670208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670208).length < 2 ^ (prefixWord ++ tailWord_3670208).sum := by decide
  have hdescent : baseEnd_3670208 < baseStart_3670208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670253 : List Nat := [1, 5, 1, 2, 3, 10]
def baseStart_3670253 : Nat := 118140960795 + 3670253 * 2 ^ 59
def prefixEnd_3670253 : Nat := 4983230072969 + 3 ^ 40 * 3670253 * 2
def baseEnd_3670253 : Nat := 15511143313632377382373

theorem tailTrace_3670253 : CollatzResearch.WordTrace tailWord_3670253 prefixEnd_3670253 15511143313632377382373 := by
  unfold tailWord_3670253
  simp only [CollatzResearch.WordTrace]
  refine ⟨133865124372307685153079413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89243416248205123435386275 133865124372307685153079413)
  ·
    refine ⟨12549855409903845483101195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133865124372307685153079413 12549855409903845483101195)
    ·
      refine ⟨18824783114855768224651793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12549855409903845483101195 18824783114855768224651793)
      ·
        refine ⟨14118587336141826168488845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18824783114855768224651793 14118587336141826168488845)
        ·
          refine ⟨5294470251053184813183317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14118587336141826168488845 5294470251053184813183317)
          ·
            refine ⟨15511143313632377382373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5294470251053184813183317 15511143313632377382373)
            ·
              rfl

theorem cell22_3670253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 10].length) (baseStart_3670253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670253 prefixEnd_3670253 := by exact prefixLift 3670253
  have htrace : WordTrace (prefixWord ++ tailWord_3670253) baseStart_3670253 baseEnd_3670253 := by
    simpa [prefixWord, tailWord_3670253, baseEnd_3670253] using wordTrace_append hprefix tailTrace_3670253
  have hstable : (prefixWord ++ tailWord_3670253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670253).length < 2 ^ (prefixWord ++ tailWord_3670253).sum := by decide
  have hdescent : baseEnd_3670253 < baseStart_3670253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670328 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_3670328 : Nat := 118140960795 + 3670328 * 2 ^ 59
def prefixEnd_3670328 : Nat := 4983230072969 + 3 ^ 40 * 3670328 * 2
def baseEnd_3670328 : Nat := 1256428282436947372346983

theorem tailTrace_3670328 : CollatzResearch.WordTrace tailWord_3670328 prefixEnd_3670328 1256428282436947372346983 := by
  unfold tailWord_3670328
  simp only [CollatzResearch.WordTrace]
  refine ⟨66933929923517986481029819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89245239898023981974706425 66933929923517986481029819)
  ·
    refine ⟨100400894885276979721544729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66933929923517986481029819 100400894885276979721544729)
    ·
      refine ⟨75300671163957734791158547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100400894885276979721544729 75300671163957734791158547)
      ·
        refine ⟨112951006745936602186737821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75300671163957734791158547 112951006745936602186737821)
        ·
          refine ⟨42356627529726225820026683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112951006745936602186737821 42356627529726225820026683)
          ·
            refine ⟨63534941294589338730040025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42356627529726225820026683 63534941294589338730040025)
            ·
              refine ⟨47651205970942004047530019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63534941294589338730040025 47651205970942004047530019)
              ·
                refine ⟨71476808956413006071295029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47651205970942004047530019 71476808956413006071295029)
                ·
                  refine ⟨6700950839663719319183909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71476808956413006071295029 6700950839663719319183909)
                  ·
                    refine ⟨1256428282436947372346983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6700950839663719319183909 1256428282436947372346983)
                    ·
                      rfl

theorem cell22_3670328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_3670328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670328 prefixEnd_3670328 := by exact prefixLift 3670328
  have htrace : WordTrace (prefixWord ++ tailWord_3670328) baseStart_3670328 baseEnd_3670328 := by
    simpa [prefixWord, tailWord_3670328, baseEnd_3670328] using wordTrace_append hprefix tailTrace_3670328
  have hstable : (prefixWord ++ tailWord_3670328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670328).length < 2 ^ (prefixWord ++ tailWord_3670328).sum := by decide
  have hdescent : baseEnd_3670328 < baseStart_3670328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670343 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 6]
def baseStart_3670343 : Nat := 118140960795 + 3670343 * 2 ^ 59
def prefixEnd_3670343 : Nat := 4983230072969 + 3 ^ 40 * 3670343 * 2
def baseEnd_3670343 : Nat := 418811139081164111073979

theorem tailTrace_3670343 : CollatzResearch.WordTrace tailWord_3670343 prefixEnd_3670343 418811139081164111073979 := by
  unfold tailWord_3670343
  simp only [CollatzResearch.WordTrace]
  refine ⟨133868406941981630523855683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89245604627987753682570455 133868406941981630523855683)
  ·
    refine ⟨200802610412972445785783525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133868406941981630523855683 200802610412972445785783525)
    ·
      refine ⟨37650489452432333584834411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200802610412972445785783525 37650489452432333584834411)
      ·
        refine ⟨56475734178648500377251617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37650489452432333584834411 56475734178648500377251617)
        ·
          refine ⟨42356800633986375282938713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56475734178648500377251617 42356800633986375282938713)
          ·
            refine ⟨31767600475489781462204035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42356800633986375282938713 31767600475489781462204035)
            ·
              refine ⟨47651400713234672193306053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31767600475489781462204035 47651400713234672193306053)
              ·
                refine ⟨8934637633731501036244885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47651400713234672193306053 8934637633731501036244885)
                ·
                  refine ⟨418811139081164111073979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8934637633731501036244885 418811139081164111073979)
                  ·
                    rfl

theorem cell22_3670343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 6].length) (baseStart_3670343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670343 prefixEnd_3670343 := by exact prefixLift 3670343
  have htrace : WordTrace (prefixWord ++ tailWord_3670343) baseStart_3670343 baseEnd_3670343 := by
    simpa [prefixWord, tailWord_3670343, baseEnd_3670343] using wordTrace_append hprefix tailTrace_3670343
  have hstable : (prefixWord ++ tailWord_3670343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670343).length < 2 ^ (prefixWord ++ tailWord_3670343).sum := by decide
  have hdescent : baseEnd_3670343 < baseStart_3670343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670360 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 4]
def baseStart_3670360 : Nat := 118140960795 + 3670360 * 2 ^ 59
def prefixEnd_3670360 : Nat := 4983230072969 + 3 ^ 40 * 3670360 * 2
def baseEnd_3670360 : Nat := 418813078896969985182295

theorem tailTrace_3670360 : CollatzResearch.WordTrace tailWord_3670360 prefixEnd_3670360 418813078896969985182295 := by
  unfold tailWord_3670360
  simp only [CollatzResearch.WordTrace]
  refine ⟨66934513491460021213612267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89246017988613361618149689 66934513491460021213612267)
  ·
    refine ⟨100401770237190031820418401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66934513491460021213612267 100401770237190031820418401)
    ·
      refine ⟨75301327677892523865313801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100401770237190031820418401 75301327677892523865313801)
      ·
        refine ⟨56475995758419392898985351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75301327677892523865313801 56475995758419392898985351)
        ·
          refine ⟨84713993637629089348478027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56475995758419392898985351 84713993637629089348478027)
          ·
            refine ⟨127070990456443634022717041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84713993637629089348478027 127070990456443634022717041)
            ·
              refine ⟨95303242842332725517037781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127070990456443634022717041 95303242842332725517037781)
              ·
                refine ⟨2233669754117173254305573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95303242842332725517037781 2233669754117173254305573)
                ·
                  refine ⟨418813078896969985182295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233669754117173254305573 418813078896969985182295)
                  ·
                    rfl

theorem cell22_3670360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_3670360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670360 prefixEnd_3670360 := by exact prefixLift 3670360
  have htrace : WordTrace (prefixWord ++ tailWord_3670360) baseStart_3670360 baseEnd_3670360 := by
    simpa [prefixWord, tailWord_3670360, baseEnd_3670360] using wordTrace_append hprefix tailTrace_3670360
  have hstable : (prefixWord ++ tailWord_3670360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670360).length < 2 ^ (prefixWord ++ tailWord_3670360).sum := by decide
  have hdescent : baseEnd_3670360 < baseStart_3670360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670377 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 4]
def baseStart_3670377 : Nat := 118140960795 + 3670377 * 2 ^ 59
def prefixEnd_3670377 : Nat := 4983230072969 + 3 ^ 40 * 3670377 * 2
def baseEnd_3670377 : Nat := 418815018712775859290611

theorem tailTrace_3670377 : CollatzResearch.WordTrace tailWord_3670377 prefixEnd_3670377 418815018712775859290611 := by
  unfold tailWord_3670377
  simp only [CollatzResearch.WordTrace]
  refine ⟨133869647023858454330593385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89246431349238969553728923 133869647023858454330593385)
  ·
    refine ⟨100402235267893840747945039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133869647023858454330593385 100402235267893840747945039)
    ·
      refine ⟨150603352901840761121917559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100402235267893840747945039 150603352901840761121917559)
      ·
        refine ⟨225905029352761141682876339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150603352901840761121917559 225905029352761141682876339)
        ·
          refine ⟨338857544029141712524314509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225905029352761141682876339 338857544029141712524314509)
          ·
            refine ⟨127071579010928142196617941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338857544029141712524314509 127071579010928142196617941)
            ·
              refine ⟨2978240133068628332733233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127071579010928142196617941 2978240133068628332733233)
              ·
                refine ⟨2233680099801471249549925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978240133068628332733233 2233680099801471249549925)
                ·
                  refine ⟨418815018712775859290611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233680099801471249549925 418815018712775859290611)
                  ·
                    rfl

theorem cell22_3670377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_3670377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670377 prefixEnd_3670377 := by exact prefixLift 3670377
  have htrace : WordTrace (prefixWord ++ tailWord_3670377) baseStart_3670377 baseEnd_3670377 := by
    simpa [prefixWord, tailWord_3670377, baseEnd_3670377] using wordTrace_append hprefix tailTrace_3670377
  have hstable : (prefixWord ++ tailWord_3670377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670377).length < 2 ^ (prefixWord ++ tailWord_3670377).sum := by decide
  have hdescent : baseEnd_3670377 < baseStart_3670377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670450 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3670450 : Nat := 118140960795 + 3670450 * 2 ^ 59
def prefixEnd_3670450 : Nat := 4983230072969 + 3 ^ 40 * 3670450 * 2
def baseEnd_3670450 : Nat := 418823348510059906932203

theorem tailTrace_3670450 : CollatzResearch.WordTrace tailWord_3670450 prefixEnd_3670450 418823348510059906932203 := by
  unfold tailWord_3670450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33468077388148496949500201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89248206368395991865333869 33468077388148496949500201)
  ·
    refine ⟨25101058041111372712125151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33468077388148496949500201 25101058041111372712125151)
    ·
      refine ⟨37651587061667059068187727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25101058041111372712125151 37651587061667059068187727)
      ·
        refine ⟨56477380592500588602281591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37651587061667059068187727 56477380592500588602281591)
        ·
          refine ⟨84716070888750882903422387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56477380592500588602281591 84716070888750882903422387)
          ·
            refine ⟨127074106333126324355133581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84716070888750882903422387 127074106333126324355133581)
            ·
              refine ⟨47652789874922371633175093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127074106333126324355133581 47652789874922371633175093)
              ·
                refine ⟨4467449050773972340610165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47652789874922371633175093 4467449050773972340610165)
                ·
                  refine ⟨418823348510059906932203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4467449050773972340610165 418823348510059906932203)
                  ·
                    rfl

theorem cell22_3670450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3670450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670450 prefixEnd_3670450 := by exact prefixLift 3670450
  have htrace : WordTrace (prefixWord ++ tailWord_3670450) baseStart_3670450 baseEnd_3670450 := by
    simpa [prefixWord, tailWord_3670450, baseEnd_3670450] using wordTrace_append hprefix tailTrace_3670450
  have hstable : (prefixWord ++ tailWord_3670450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670450).length < 2 ^ (prefixWord ++ tailWord_3670450).sum := by decide
  have hdescent : baseEnd_3670450 < baseStart_3670450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670484 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 5]
def baseStart_3670484 : Nat := 118140960795 + 3670484 * 2 ^ 59
def prefixEnd_3670484 : Nat := 4983230072969 + 3 ^ 40 * 3670484 * 2
def baseEnd_3670484 : Nat := 418827228141671655148835

theorem tailTrace_3670484 : CollatzResearch.WordTrace tailWord_3670484 prefixEnd_3670484 418827228141671655148835 := by
  unfold tailWord_3670484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66936774817235405802369253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89249033089647207736492337 66936774817235405802369253)
  ·
    refine ⟨12550645278231638587944235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66936774817235405802369253 12550645278231638587944235)
    ·
      refine ⟨18825967917347457881916353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12550645278231638587944235 18825967917347457881916353)
      ·
        refine ⟨14119475938010593411437265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18825967917347457881916353 14119475938010593411437265)
        ·
          refine ⟨10589606953507945058577949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14119475938010593411437265 10589606953507945058577949)
          ·
            refine ⟨3971102607565479396966731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10589606953507945058577949 3971102607565479396966731)
            ·
              refine ⟨5956653911348219095450097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971102607565479396966731 5956653911348219095450097)
              ·
                refine ⟨4467490433511164321587573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5956653911348219095450097 4467490433511164321587573)
                ·
                  refine ⟨418827228141671655148835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4467490433511164321587573 418827228141671655148835)
                  ·
                    rfl

theorem cell22_3670484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_3670484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670484 prefixEnd_3670484 := by exact prefixLift 3670484
  have htrace : WordTrace (prefixWord ++ tailWord_3670484) baseStart_3670484 baseEnd_3670484 := by
    simpa [prefixWord, tailWord_3670484, baseEnd_3670484] using wordTrace_append hprefix tailTrace_3670484
  have hstable : (prefixWord ++ tailWord_3670484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670484).length < 2 ^ (prefixWord ++ tailWord_3670484).sum := by decide
  have hdescent : baseEnd_3670484 < baseStart_3670484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670495 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 6]
def baseStart_3670495 : Nat := 118140960795 + 3670495 * 2 ^ 59
def prefixEnd_3670495 : Nat := 4983230072969 + 3 ^ 40 * 3670495 * 2
def baseEnd_3670495 : Nat := 418828483316604867807157

theorem tailTrace_3670495 : CollatzResearch.WordTrace tailWord_3670495 prefixEnd_3670495 418828483316604867807157 := by
  unfold tailWord_3670495
  simp only [CollatzResearch.WordTrace]
  refine ⟨133873950837430960483388939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89249300558287306988925959 133873950837430960483388939)
  ·
    refine ⟨200810926256146440725083409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133873950837430960483388939 200810926256146440725083409)
    ·
      refine ⟨150608194692109830543812557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200810926256146440725083409 150608194692109830543812557)
      ·
        refine ⟨56478073009541186453929709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150608194692109830543812557 56478073009541186453929709)
        ·
          refine ⟨21179277378577944920223641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56478073009541186453929709 21179277378577944920223641)
          ·
            refine ⟨15884458033933458690167731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21179277378577944920223641 15884458033933458690167731)
            ·
              refine ⟨23826687050900188035251597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884458033933458690167731 23826687050900188035251597)
              ·
                refine ⟨8935007644087570513219349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23826687050900188035251597 8935007644087570513219349)
                ·
                  refine ⟨418828483316604867807157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8935007644087570513219349 418828483316604867807157)
                  ·
                    rfl

theorem cell22_3670495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 6].length) (baseStart_3670495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670495 prefixEnd_3670495 := by exact prefixLift 3670495
  have htrace : WordTrace (prefixWord ++ tailWord_3670495) baseStart_3670495 baseEnd_3670495 := by
    simpa [prefixWord, tailWord_3670495, baseEnd_3670495] using wordTrace_append hprefix tailTrace_3670495
  have hstable : (prefixWord ++ tailWord_3670495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670495).length < 2 ^ (prefixWord ++ tailWord_3670495).sum := by decide
  have hdescent : baseEnd_3670495 < baseStart_3670495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670525 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3670525 : Nat := 118140960795 + 3670525 * 2 ^ 59
def prefixEnd_3670525 : Nat := 4983230072969 + 3 ^ 40 * 3670525 * 2
def baseEnd_3670525 : Nat := 1256495719562904525171379

theorem tailTrace_3670525 : CollatzResearch.WordTrace tailWord_3670525 prefixEnd_3670525 1256495719562904525171379 := by
  unfold tailWord_3670525
  simp only [CollatzResearch.WordTrace]
  refine ⟨133875045027322275606981029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89250030018214850404654019 133875045027322275606981029)
  ·
    refine ⟨25101570942622926676308943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133875045027322275606981029 25101570942622926676308943)
    ·
      refine ⟨37652356413934390014463415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25101570942622926676308943 37652356413934390014463415)
      ·
        refine ⟨56478534620901585021695123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37652356413934390014463415 56478534620901585021695123)
        ·
          refine ⟨84717801931352377532542685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56478534620901585021695123 84717801931352377532542685)
          ·
            refine ⟨31769175724257141574703507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84717801931352377532542685 31769175724257141574703507)
            ·
              refine ⟨47653763586385712362055261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31769175724257141574703507 47653763586385712362055261)
              ·
                refine ⟨17870161344894642135770723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47653763586385712362055261 17870161344894642135770723)
                ·
                  refine ⟨26805242017341963203656085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17870161344894642135770723 26805242017341963203656085)
                  ·
                    refine ⟨1256495719562904525171379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26805242017341963203656085 1256495719562904525171379)
                    ·
                      rfl

theorem cell22_3670525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3670525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670525 prefixEnd_3670525 := by exact prefixLift 3670525
  have htrace : WordTrace (prefixWord ++ tailWord_3670525) baseStart_3670525 baseEnd_3670525 := by
    simpa [prefixWord, tailWord_3670525, baseEnd_3670525] using wordTrace_append hprefix tailTrace_3670525
  have hstable : (prefixWord ++ tailWord_3670525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670525).length < 2 ^ (prefixWord ++ tailWord_3670525).sum := by decide
  have hdescent : baseEnd_3670525 < baseStart_3670525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670529 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 4]
def baseStart_3670529 : Nat := 118140960795 + 3670529 * 2 ^ 59
def prefixEnd_3670529 : Nat := 4983230072969 + 3 ^ 40 * 3670529 * 2
def baseEnd_3670529 : Nat := 418832362948216616023789

theorem tailTrace_3670529 : CollatzResearch.WordTrace tailWord_3670529 prefixEnd_3670529 418832362948216616023789 := by
  unfold tailWord_3670529
  simp only [CollatzResearch.WordTrace]
  refine ⟨133875190919307784290126641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89250127279538522860084427 133875190919307784290126641)
  ·
    refine ⟨100406393189480838217594981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133875190919307784290126641 100406393189480838217594981)
    ·
      refine ⟨18826198723027657165799059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100406393189480838217594981 18826198723027657165799059)
      ·
        refine ⟨28239298084541485748698589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18826198723027657165799059 28239298084541485748698589)
        ·
          refine ⟨10589736781703057155761971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28239298084541485748698589 10589736781703057155761971)
          ·
            refine ⟨15884605172554585733642957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589736781703057155761971 15884605172554585733642957)
            ·
              refine ⟨5956726939707969650116109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15884605172554585733642957 5956726939707969650116109)
              ·
                refine ⟨2233772602390488618793541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5956726939707969650116109 2233772602390488618793541)
                ·
                  refine ⟨418832362948216616023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233772602390488618793541 418832362948216616023789)
                  ·
                    rfl

theorem cell22_3670529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_3670529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670529 prefixEnd_3670529 := by exact prefixLift 3670529
  have htrace : WordTrace (prefixWord ++ tailWord_3670529) baseStart_3670529 baseEnd_3670529 := by
    simpa [prefixWord, tailWord_3670529, baseEnd_3670529] using wordTrace_append hprefix tailTrace_3670529
  have hstable : (prefixWord ++ tailWord_3670529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670529).length < 2 ^ (prefixWord ++ tailWord_3670529).sum := by decide
  have hdescent : baseEnd_3670529 < baseStart_3670529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670540 : List Nat := [2, 2, 1, 2, 4, 1, 10]
def baseStart_3670540 : Nat := 118140960795 + 3670540 * 2 ^ 59
def prefixEnd_3670540 : Nat := 4983230072969 + 3 ^ 40 * 3670540 * 2
def baseEnd_3670540 : Nat := 46537068680349980964679

theorem tailTrace_3670540 : CollatzResearch.WordTrace tailWord_3670540 prefixEnd_3670540 46537068680349980964679 := by
  unfold tailWord_3670540
  simp only [CollatzResearch.WordTrace]
  refine ⟨66937796061133966584388537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89250394748178622112518049 66937796061133966584388537)
  ·
    refine ⟨50203347045850474938291403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66937796061133966584388537 50203347045850474938291403)
    ·
      refine ⟨75305020568775712407437105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50203347045850474938291403 75305020568775712407437105)
      ·
        refine ⟨56478765426581784305577829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75305020568775712407437105 56478765426581784305577829)
        ·
          refine ⟨10589768517484084557295843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56478765426581784305577829 10589768517484084557295843)
          ·
            refine ⟨15884652776226126835943765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589768517484084557295843 15884652776226126835943765)
            ·
              refine ⟨46537068680349980964679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15884652776226126835943765 46537068680349980964679)
              ·
                rfl

theorem cell22_3670540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 10].length) (baseStart_3670540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670540 prefixEnd_3670540 := by exact prefixLift 3670540
  have htrace : WordTrace (prefixWord ++ tailWord_3670540) baseStart_3670540 baseEnd_3670540 := by
    simpa [prefixWord, tailWord_3670540, baseEnd_3670540] using wordTrace_append hprefix tailTrace_3670540
  have hstable : (prefixWord ++ tailWord_3670540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670540).length < 2 ^ (prefixWord ++ tailWord_3670540).sum := by decide
  have hdescent : baseEnd_3670540 < baseStart_3670540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670542 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_3670542 : Nat := 118140960795 + 3670542 * 2 ^ 59
def prefixEnd_3670542 : Nat := 4983230072969 + 3 ^ 40 * 3670542 * 2
def baseEnd_3670542 : Nat := 1256501539010322147496327

theorem tailTrace_3670542 : CollatzResearch.WordTrace tailWord_3670542 prefixEnd_3670542 1256501539010322147496327 := by
  unfold tailWord_3670542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734458133532585938793735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89250443378840458340233253 16734458133532585938793735)
  ·
    refine ⟨25101687200298878908190603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16734458133532585938793735 25101687200298878908190603)
    ·
      refine ⟨37652530800448318362285905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25101687200298878908190603 37652530800448318362285905)
      ·
        refine ⟨28239398100336238771714429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37652530800448318362285905 28239398100336238771714429)
        ·
          refine ⟨10589774287626089539392911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28239398100336238771714429 10589774287626089539392911)
          ·
            refine ⟨15884661431439134309089367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10589774287626089539392911 15884661431439134309089367)
            ·
              refine ⟨23826992147158701463634051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884661431439134309089367 23826992147158701463634051)
              ·
                refine ⟨35740488220738052195451077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23826992147158701463634051 35740488220738052195451077)
                ·
                  refine ⟨6701341541388384786647077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35740488220738052195451077 6701341541388384786647077)
                  ·
                    refine ⟨1256501539010322147496327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701341541388384786647077 1256501539010322147496327)
                    ·
                      rfl

theorem cell22_3670542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_3670542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670542 prefixEnd_3670542 := by exact prefixLift 3670542
  have htrace : WordTrace (prefixWord ++ tailWord_3670542) baseStart_3670542 baseEnd_3670542 := by
    simpa [prefixWord, tailWord_3670542, baseEnd_3670542] using wordTrace_append hprefix tailTrace_3670542
  have hstable : (prefixWord ++ tailWord_3670542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670542).length < 2 ^ (prefixWord ++ tailWord_3670542).sum := by decide
  have hdescent : baseEnd_3670542 < baseStart_3670542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670557 : List Nat := [1, 4, 2, 2, 1, 3, 2, 7]
def baseStart_3670557 : Nat := 118140960795 + 3670557 * 2 ^ 59
def prefixEnd_3670557 : Nat := 4983230072969 + 3 ^ 40 * 3670557 * 2
def baseEnd_3670557 : Nat := 139611852646318567596809

theorem tailTrace_3670557 : CollatzResearch.WordTrace tailWord_3670557 prefixEnd_3670557 139611852646318567596809 := by
  unfold tailWord_3670557
  simp only [CollatzResearch.WordTrace]
  refine ⟨133876212163206345072145925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89250808108804230048097283 133876212163206345072145925)
  ·
    refine ⟨25101789780601189701027361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133876212163206345072145925 25101789780601189701027361)
    ·
      refine ⟨18826342335450892275770521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25101789780601189701027361 18826342335450892275770521)
      ·
        refine ⟨14119756751588169206827891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18826342335450892275770521 14119756751588169206827891)
        ·
          refine ⟨21179635127382253810241837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14119756751588169206827891 21179635127382253810241837)
          ·
            refine ⟨7942363172768345178840689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21179635127382253810241837 7942363172768345178840689)
            ·
              refine ⟨5956772379576258884130517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7942363172768345178840689 5956772379576258884130517)
              ·
                refine ⟨139611852646318567596809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5956772379576258884130517 139611852646318567596809)
                ·
                  rfl

theorem cell22_3670557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 7].length) (baseStart_3670557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670557 prefixEnd_3670557 := by exact prefixLift 3670557
  have htrace : WordTrace (prefixWord ++ tailWord_3670557) baseStart_3670557 baseEnd_3670557 := by
    simpa [prefixWord, tailWord_3670557, baseEnd_3670557] using wordTrace_append hprefix tailTrace_3670557
  have hstable : (prefixWord ++ tailWord_3670557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670557).length < 2 ^ (prefixWord ++ tailWord_3670557).sum := by decide
  have hdescent : baseEnd_3670557 < baseStart_3670557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670572 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_3670572 : Nat := 118140960795 + 3670572 * 2 ^ 59
def prefixEnd_3670572 : Nat := 4983230072969 + 3 ^ 40 * 3670572 * 2
def baseEnd_3670572 : Nat := 1256511808623412069246235

theorem tailTrace_3670572 : CollatzResearch.WordTrace tailWord_3670572 prefixEnd_3670572 1256511808623412069246235 := by
  unfold tailWord_3670572
  simp only [CollatzResearch.WordTrace]
  refine ⟨66938379629076001316970985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89251172838768001755961313 66938379629076001316970985)
  ·
    refine ⟨50203784721807000987728239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66938379629076001316970985 50203784721807000987728239)
    ·
      refine ⟨75305677082710501481592359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50203784721807000987728239 75305677082710501481592359)
      ·
        refine ⟨112958515624065752222388539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75305677082710501481592359 112958515624065752222388539)
        ·
          refine ⟨169437773436098628333582809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112958515624065752222388539 169437773436098628333582809)
          ·
            refine ⟨127078330077073971250187107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169437773436098628333582809 127078330077073971250187107)
            ·
              refine ⟨190617495115610956875280661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127078330077073971250187107 190617495115610956875280661)
              ·
                refine ⟨8935195083544263603528781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190617495115610956875280661 8935195083544263603528781)
                ·
                  refine ⟨3350698156329098851323293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8935195083544263603528781 3350698156329098851323293)
                  ·
                    refine ⟨1256511808623412069246235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3350698156329098851323293 1256511808623412069246235)
                    ·
                      rfl

theorem cell22_3670572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_3670572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670572 prefixEnd_3670572 := by exact prefixLift 3670572
  have htrace : WordTrace (prefixWord ++ tailWord_3670572) baseStart_3670572 baseEnd_3670572 := by
    simpa [prefixWord, tailWord_3670572, baseEnd_3670572] using wordTrace_append hprefix tailTrace_3670572
  have hstable : (prefixWord ++ tailWord_3670572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670572).length < 2 ^ (prefixWord ++ tailWord_3670572).sum := by decide
  have hdescent : baseEnd_3670572 < baseStart_3670572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670600 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_3670600 : Nat := 118140960795 + 3670600 * 2 ^ 59
def prefixEnd_3670600 : Nat := 4983230072969 + 3 ^ 40 * 3670600 * 2
def baseEnd_3670600 : Nat := 1256521393595629329546149

theorem tailTrace_3670600 : CollatzResearch.WordTrace tailWord_3670600 prefixEnd_3670600 1256521393595629329546149 := by
  unfold tailWord_3670600
  simp only [CollatzResearch.WordTrace]
  refine ⟨66938890251025281707980627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89251853668033708943974169 66938890251025281707980627)
  ·
    refine ⟨100408335376537922561970941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66938890251025281707980627 100408335376537922561970941)
    ·
      refine ⟨37653125766201720960739103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100408335376537922561970941 37653125766201720960739103)
      ·
        refine ⟨56479688649302581441108655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37653125766201720960739103 56479688649302581441108655)
        ·
          refine ⟨84719532973953872161662983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56479688649302581441108655 84719532973953872161662983)
          ·
            refine ⟨127079299460930808242494475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84719532973953872161662983 127079299460930808242494475)
            ·
              refine ⟨190618949191396212363741713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127079299460930808242494475 190618949191396212363741713)
              ·
                refine ⟨142964211893547159272806285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190618949191396212363741713 142964211893547159272806285)
                ·
                  refine ⟨53611579460080184727302357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142964211893547159272806285 53611579460080184727302357)
                  ·
                    refine ⟨1256521393595629329546149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53611579460080184727302357 1256521393595629329546149)
                    ·
                      rfl

theorem cell22_3670600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_3670600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670600 prefixEnd_3670600 := by exact prefixLift 3670600
  have htrace : WordTrace (prefixWord ++ tailWord_3670600) baseStart_3670600 baseEnd_3670600 := by
    simpa [prefixWord, tailWord_3670600, baseEnd_3670600] using wordTrace_append hprefix tailTrace_3670600
  have hstable : (prefixWord ++ tailWord_3670600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670600).length < 2 ^ (prefixWord ++ tailWord_3670600).sum := by decide
  have hdescent : baseEnd_3670600 < baseStart_3670600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670602 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_3670602 : Nat := 118140960795 + 3670602 * 2 ^ 59
def prefixEnd_3670602 : Nat := 4983230072969 + 3 ^ 40 * 3670602 * 2
def baseEnd_3670602 : Nat := 418840692745500663665381

theorem tailTrace_3670602 : CollatzResearch.WordTrace tailWord_3670602 prefixEnd_3670602 418840692745500663665381 := by
  unfold tailWord_3670602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33469463362010829439383515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89251902298695545171689373 33469463362010829439383515)
  ·
    refine ⟨50204195043016244159075273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33469463362010829439383515 50204195043016244159075273)
    ·
      refine ⟨37653146282262183119306455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50204195043016244159075273 37653146282262183119306455)
      ·
        refine ⟨56479719423393274678959683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37653146282262183119306455 56479719423393274678959683)
        ·
          refine ⟨84719579135089912018439525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56479719423393274678959683 84719579135089912018439525)
          ·
            refine ⟨15884921087829358503457411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84719579135089912018439525 15884921087829358503457411)
            ·
              refine ⟨23827381631744037755186117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884921087829358503457411 23827381631744037755186117)
              ·
                refine ⟨4467634055952007079097397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23827381631744037755186117 4467634055952007079097397)
                ·
                  refine ⟨418840692745500663665381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4467634055952007079097397 418840692745500663665381)
                  ·
                    rfl

theorem cell22_3670602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_3670602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670602 prefixEnd_3670602 := by exact prefixLift 3670602
  have htrace : WordTrace (prefixWord ++ tailWord_3670602) baseStart_3670602 baseEnd_3670602 := by
    simpa [prefixWord, tailWord_3670602, baseEnd_3670602] using wordTrace_append hprefix tailTrace_3670602
  have hstable : (prefixWord ++ tailWord_3670602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670602).length < 2 ^ (prefixWord ++ tailWord_3670602).sum := by decide
  have hdescent : baseEnd_3670602 < baseStart_3670602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670649 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_3670649 : Nat := 118140960795 + 3670649 * 2 ^ 59
def prefixEnd_3670649 : Nat := 4983230072969 + 3 ^ 40 * 3670649 * 2
def baseEnd_3670649 : Nat := 1256538167297009535070999

theorem tailTrace_3670649 : CollatzResearch.WordTrace tailWord_3670649 prefixEnd_3670649 1256538167297009535070999 := by
  unfold tailWord_3670649
  simp only [CollatzResearch.WordTrace]
  refine ⟨133879567678873044784495001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89253045119248696522996667 133879567678873044784495001)
  ·
    refine ⟨100409675759154783588371251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133879567678873044784495001 100409675759154783588371251)
    ·
      refine ⟨150614513638732175382556877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100409675759154783588371251 150614513638732175382556877)
      ·
        refine ⟨56480442614524565768458829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150614513638732175382556877 56480442614524565768458829)
        ·
          refine ⟨21180165980446712163172061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56480442614524565768458829 21180165980446712163172061)
          ·
            refine ⟨7942562242667517061189523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21180165980446712163172061 7942562242667517061189523)
            ·
              refine ⟨11913843364001275591784285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942562242667517061189523 11913843364001275591784285)
              ·
                refine ⟨4467691261500478346919107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11913843364001275591784285 4467691261500478346919107)
                ·
                  refine ⟨6701536892250717520378661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467691261500478346919107 6701536892250717520378661)
                  ·
                    refine ⟨1256538167297009535070999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701536892250717520378661 1256538167297009535070999)
                    ·
                      rfl

theorem cell22_3670649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_3670649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670649 prefixEnd_3670649 := by exact prefixLift 3670649
  have htrace : WordTrace (prefixWord ++ tailWord_3670649) baseStart_3670649 baseEnd_3670649 := by
    simpa [prefixWord, tailWord_3670649, baseEnd_3670649] using wordTrace_append hprefix tailTrace_3670649
  have hstable : (prefixWord ++ tailWord_3670649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670649).length < 2 ^ (prefixWord ++ tailWord_3670649).sum := by decide
  have hdescent : baseEnd_3670649 < baseStart_3670649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670692 : List Nat := [2, 3, 1, 2, 2, 1, 3, 8]
def baseStart_3670692 : Nat := 118140960795 + 3670692 * 2 ^ 59
def prefixEnd_3670692 : Nat := 4983230072969 + 3 ^ 40 * 3670692 * 2
def baseEnd_3670692 : Nat := 139616987452863528471763

theorem tailTrace_3670692 : CollatzResearch.WordTrace tailWord_3670692 prefixEnd_3670692 139616987452863528471763 := by
  unfold tailWord_3670692
  simp only [CollatzResearch.WordTrace]
  refine ⟨66940568008858631564155165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89254090678478175418873553 66940568008858631564155165)
  ·
    refine ⟨25102713003321986836558187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66940568008858631564155165 25102713003321986836558187)
    ·
      refine ⟨37654069504982980254837281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25102713003321986836558187 37654069504982980254837281)
      ·
        refine ⟨28240552128737235191127961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37654069504982980254837281 28240552128737235191127961)
        ·
          refine ⟨21180414096552926393345971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28240552128737235191127961 21180414096552926393345971)
          ·
            refine ⟨31770621144829389590018957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21180414096552926393345971 31770621144829389590018957)
            ·
              refine ⟨11913982929311021096257109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31770621144829389590018957 11913982929311021096257109)
              ·
                refine ⟨139616987452863528471763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11913982929311021096257109 139616987452863528471763)
                ·
                  rfl

theorem cell22_3670692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_3670692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670692 prefixEnd_3670692 := by exact prefixLift 3670692
  have htrace : WordTrace (prefixWord ++ tailWord_3670692) baseStart_3670692 baseEnd_3670692 := by
    simpa [prefixWord, tailWord_3670692, baseEnd_3670692] using wordTrace_append hprefix tailTrace_3670692
  have hstable : (prefixWord ++ tailWord_3670692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670692).length < 2 ^ (prefixWord ++ tailWord_3670692).sum := by decide
  have hdescent : baseEnd_3670692 < baseStart_3670692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670709 : List Nat := [1, 3, 3, 3, 1, 3, 8]
def baseStart_3670709 : Nat := 118140960795 + 3670709 * 2 ^ 59
def prefixEnd_3670709 : Nat := 4983230072969 + 3 ^ 40 * 3670709 * 2
def baseEnd_3670709 : Nat := 46539211352710717724845

theorem tailTrace_3670709 : CollatzResearch.WordTrace tailWord_3670709 prefixEnd_3670709 46539211352710717724845 := by
  unfold tailWord_3670709
  simp only [CollatzResearch.WordTrace]
  refine ⟨133881756058655675031679181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89254504039103783354452787 133881756058655675031679181)
  ·
    refine ⟨50205658521995878136879693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133881756058655675031679181 50205658521995878136879693)
    ·
      refine ⟨18827121945748454301329885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50205658521995878136879693 18827121945748454301329885)
      ·
        refine ⟨7060170729655670362998707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18827121945748454301329885 7060170729655670362998707)
        ·
          refine ⟨10590256094483505544498061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060170729655670362998707 10590256094483505544498061)
          ·
            refine ⟨3971346035431314579186773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10590256094483505544498061 3971346035431314579186773)
            ·
              refine ⟨46539211352710717724845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3971346035431314579186773 46539211352710717724845)
              ·
                rfl

theorem cell22_3670709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 8].length) (baseStart_3670709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670709 prefixEnd_3670709 := by exact prefixLift 3670709
  have htrace : WordTrace (prefixWord ++ tailWord_3670709) baseStart_3670709 baseEnd_3670709 := by
    simpa [prefixWord, tailWord_3670709, baseEnd_3670709] using wordTrace_append hprefix tailTrace_3670709
  have hstable : (prefixWord ++ tailWord_3670709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670709).length < 2 ^ (prefixWord ++ tailWord_3670709).sum := by decide
  have hdescent : baseEnd_3670709 < baseStart_3670709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670752 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_3670752 : Nat := 118140960795 + 3670752 * 2 ^ 59
def prefixEnd_3670752 : Nat := 4983230072969 + 3 ^ 40 * 3670752 * 2
def baseEnd_3670752 : Nat := 1256573426301951599745683

theorem tailTrace_3670752 : CollatzResearch.WordTrace tailWord_3670752 prefixEnd_3670752 1256573426301951599745683 := by
  unfold tailWord_3670752
  simp only [CollatzResearch.WordTrace]
  refine ⟨66941662198749946687747255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89255549598333262250329673 66941662198749946687747255)
  ·
    refine ⟨100412493298124920031620883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66941662198749946687747255 100412493298124920031620883)
    ·
      refine ⟨150618739947187380047431325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100412493298124920031620883 150618739947187380047431325)
      ·
        refine ⟨56482027480195267517786747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150618739947187380047431325 56482027480195267517786747)
        ·
          refine ⟨84723041220292901276680121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56482027480195267517786747 84723041220292901276680121)
          ·
            refine ⟨63542280915219675957510091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84723041220292901276680121 63542280915219675957510091)
            ·
              refine ⟨95313421372829513936265137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63542280915219675957510091 95313421372829513936265137)
              ·
                refine ⟨71485066029622135452198853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95313421372829513936265137 71485066029622135452198853)
                ·
                  refine ⟨13403449880554150397287285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71485066029622135452198853 13403449880554150397287285)
                  ·
                    refine ⟨1256573426301951599745683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13403449880554150397287285 1256573426301951599745683)
                    ·
                      rfl

theorem cell22_3670752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_3670752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670752 prefixEnd_3670752 := by exact prefixLift 3670752
  have htrace : WordTrace (prefixWord ++ tailWord_3670752) baseStart_3670752 baseEnd_3670752 := by
    simpa [prefixWord, tailWord_3670752, baseEnd_3670752] using wordTrace_append hprefix tailTrace_3670752
  have hstable : (prefixWord ++ tailWord_3670752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670752).length < 2 ^ (prefixWord ++ tailWord_3670752).sum := by decide
  have hdescent : baseEnd_3670752 < baseStart_3670752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670786 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3670786 : Nat := 118140960795 + 3670786 * 2 ^ 59
def prefixEnd_3670786 : Nat := 4983230072969 + 3 ^ 40 * 3670786 * 2
def baseEnd_3670786 : Nat := 1256585065196786844395579

theorem tailTrace_3670786 : CollatzResearch.WordTrace tailWord_3670786 prefixEnd_3670786 1256585065196786844395579 := by
  unfold tailWord_3670786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33471141119844179295558053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89256376319584478121488141 33471141119844179295558053)
  ·
    refine ⟨6275838959970783617917135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33471141119844179295558053 6275838959970783617917135)
    ·
      refine ⟨9413758439956175426875703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6275838959970783617917135 9413758439956175426875703)
      ·
        refine ⟨14120637659934263140313555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9413758439956175426875703 14120637659934263140313555)
        ·
          refine ⟨21180956489901394710470333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14120637659934263140313555 21180956489901394710470333)
          ·
            refine ⟨7942858683713023016426375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21180956489901394710470333 7942858683713023016426375)
            ·
              refine ⟨11914288025569534524639563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942858683713023016426375 11914288025569534524639563)
              ·
                refine ⟨17871432038354301786959345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11914288025569534524639563 17871432038354301786959345)
                ·
                  refine ⟨13403574028765726340219509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17871432038354301786959345 13403574028765726340219509)
                  ·
                    refine ⟨1256585065196786844395579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13403574028765726340219509 1256585065196786844395579)
                    ·
                      rfl

theorem cell22_3670786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3670786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670786 prefixEnd_3670786 := by exact prefixLift 3670786
  have htrace : WordTrace (prefixWord ++ tailWord_3670786) baseStart_3670786 baseEnd_3670786 := by
    simpa [prefixWord, tailWord_3670786, baseEnd_3670786] using wordTrace_append hprefix tailTrace_3670786
  have hstable : (prefixWord ++ tailWord_3670786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670786).length < 2 ^ (prefixWord ++ tailWord_3670786).sum := by decide
  have hdescent : baseEnd_3670786 < baseStart_3670786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670816 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 4]
def baseStart_3670816 : Nat := 118140960795 + 3670816 * 2 ^ 59
def prefixEnd_3670816 : Nat := 4983230072969 + 3 ^ 40 * 3670816 * 2
def baseEnd_3670816 : Nat := 418865111603292255381829

theorem tailTrace_3670816 : CollatzResearch.WordTrace tailWord_3670816 prefixEnd_3670816 418865111603292255381829 := by
  unfold tailWord_3670816
  simp only [CollatzResearch.WordTrace]
  refine ⟨66942829334634016152912151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89257105779512021537216201 66942829334634016152912151)
  ·
    refine ⟨100414244001951024229368227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66942829334634016152912151 100414244001951024229368227)
    ·
      refine ⟨150621366002926536344052341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100414244001951024229368227 150621366002926536344052341)
      ·
        refine ⟨14120753062774362782254907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150621366002926536344052341 14120753062774362782254907)
        ·
          refine ⟨21181129594161544173382361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14120753062774362782254907 21181129594161544173382361)
          ·
            refine ⟨15885847195621158130036771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21181129594161544173382361 15885847195621158130036771)
            ·
              refine ⟨23828770793431737195055157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15885847195621158130036771 23828770793431737195055157)
              ·
                refine ⟨2233947261884225362036421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23828770793431737195055157 2233947261884225362036421)
                ·
                  refine ⟨418865111603292255381829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2233947261884225362036421 418865111603292255381829)
                  ·
                    rfl

theorem cell22_3670816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_3670816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670816 prefixEnd_3670816 := by exact prefixLift 3670816
  have htrace : WordTrace (prefixWord ++ tailWord_3670816) baseStart_3670816 baseEnd_3670816 := by
    simpa [prefixWord, tailWord_3670816, baseEnd_3670816] using wordTrace_append hprefix tailTrace_3670816
  have hstable : (prefixWord ++ tailWord_3670816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670816).length < 2 ^ (prefixWord ++ tailWord_3670816).sum := by decide
  have hdescent : baseEnd_3670816 < baseStart_3670816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670818 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3670818 : Nat := 118140960795 + 3670818 * 2 ^ 59
def prefixEnd_3670818 : Nat := 4983230072969 + 3 ^ 40 * 3670818 * 2
def baseEnd_3670818 : Nat := 1256596019450749427595481

theorem tailTrace_3670818 : CollatzResearch.WordTrace tailWord_3670818 prefixEnd_3670818 1256596019450749427595481 := by
  unfold tailWord_3670818
  simp only [CollatzResearch.WordTrace]
  refine ⟨33471432903815196661849277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89257154410173857764931405 33471432903815196661849277)
  ·
    refine ⟨12551787338930698748193479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33471432903815196661849277 12551787338930698748193479)
    ·
      refine ⟨18827681008396048122290219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12551787338930698748193479 18827681008396048122290219)
      ·
        refine ⟨28241521512594072183435329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18827681008396048122290219 28241521512594072183435329)
        ·
          refine ⟨21181141134445554137576497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28241521512594072183435329 21181141134445554137576497)
          ·
            refine ⟨15885855850834165603182373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21181141134445554137576497 15885855850834165603182373)
            ·
              refine ⟨2978597972031406050596695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15885855850834165603182373 2978597972031406050596695)
              ·
                refine ⟨4467896958047109075895043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978597972031406050596695 4467896958047109075895043)
                ·
                  refine ⟨6701845437070663613842565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467896958047109075895043 6701845437070663613842565)
                  ·
                    refine ⟨1256596019450749427595481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6701845437070663613842565 1256596019450749427595481)
                    ·
                      rfl

theorem cell22_3670818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3670818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670818 prefixEnd_3670818 := by exact prefixLift 3670818
  have htrace : WordTrace (prefixWord ++ tailWord_3670818) baseStart_3670818 baseEnd_3670818 := by
    simpa [prefixWord, tailWord_3670818, baseEnd_3670818] using wordTrace_append hprefix tailTrace_3670818
  have hstable : (prefixWord ++ tailWord_3670818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670818).length < 2 ^ (prefixWord ++ tailWord_3670818).sum := by decide
  have hdescent : baseEnd_3670818 < baseStart_3670818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3670996 : List Nat := [2, 4, 1, 2, 1, 3, 9]
def baseStart_3670996 : Nat := 118140960795 + 3670996 * 2 ^ 59
def prefixEnd_3670996 : Nat := 4983230072969 + 3 ^ 40 * 3670996 * 2
def baseEnd_3670996 : Nat := 46542850092163566542405

theorem tailTrace_3670996 : CollatzResearch.WordTrace tailWord_3670996 prefixEnd_3670996 46542850092163566542405 := by
  unfold tailWord_3670996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66946111904307961523688421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89261482539077282031584561 66946111904307961523688421)
  ·
    refine ⟨12552395982057742785691579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66946111904307961523688421 12552395982057742785691579)
    ·
      refine ⟨18828593973086614178537369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12552395982057742785691579 18828593973086614178537369)
      ·
        refine ⟨14121445479814960633903027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18828593973086614178537369 14121445479814960633903027)
        ·
          refine ⟨21182168219722440950854541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14121445479814960633903027 21182168219722440950854541)
          ·
            refine ⟨7943313082395915356570453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21182168219722440950854541 7943313082395915356570453)
            ·
              refine ⟨46542850092163566542405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7943313082395915356570453 46542850092163566542405)
              ·
                rfl

theorem cell22_3670996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 9].length) (baseStart_3670996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3670996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3670996 prefixEnd_3670996 := by exact prefixLift 3670996
  have htrace : WordTrace (prefixWord ++ tailWord_3670996) baseStart_3670996 baseEnd_3670996 := by
    simpa [prefixWord, tailWord_3670996, baseEnd_3670996] using wordTrace_append hprefix tailTrace_3670996
  have hstable : (prefixWord ++ tailWord_3670996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3670996).length < 2 ^ (prefixWord ++ tailWord_3670996).sum := by decide
  have hdescent : baseEnd_3670996 < baseStart_3670996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3670996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671000 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_3671000 : Nat := 118140960795 + 3671000 * 2 ^ 59
def prefixEnd_3671000 : Nat := 4983230072969 + 3 ^ 40 * 3671000 * 2
def baseEnd_3671000 : Nat := 1256658321770161619544923

theorem tailTrace_3671000 : CollatzResearch.WordTrace tailWord_3671000 prefixEnd_3671000 1256658321770161619544923 := by
  unfold tailWord_3671000
  simp only [CollatzResearch.WordTrace]
  refine ⟨66946184850300715865261227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89261579800400954487014969 66946184850300715865261227)
  ·
    refine ⟨100419277275451073797891841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66946184850300715865261227 100419277275451073797891841)
    ·
      refine ⟨75314457956588305348418881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100419277275451073797891841 75314457956588305348418881)
      ·
        refine ⟨56485843467441229011314161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75314457956588305348418881 56485843467441229011314161)
        ·
          refine ⟨42364382600580921758485621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56485843467441229011314161 42364382600580921758485621)
          ·
            refine ⟨3971660868804461414858027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42364382600580921758485621 3971660868804461414858027)
            ·
              refine ⟨5957491303206692122287041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971660868804461414858027 5957491303206692122287041)
              ·
                refine ⟨4468118477405019091715281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5957491303206692122287041 4468118477405019091715281)
                ·
                  refine ⟨3351088858053764318786461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4468118477405019091715281 3351088858053764318786461)
                  ·
                    refine ⟨1256658321770161619544923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351088858053764318786461 1256658321770161619544923)
                    ·
                      rfl

theorem cell22_3671000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_3671000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671000 prefixEnd_3671000 := by exact prefixLift 3671000
  have htrace : WordTrace (prefixWord ++ tailWord_3671000) baseStart_3671000 baseEnd_3671000 := by
    simpa [prefixWord, tailWord_3671000, baseEnd_3671000] using wordTrace_append hprefix tailTrace_3671000
  have hstable : (prefixWord ++ tailWord_3671000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671000).length < 2 ^ (prefixWord ++ tailWord_3671000).sum := by decide
  have hdescent : baseEnd_3671000 < baseStart_3671000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671030 : List Nat := [5, 1, 1, 1, 3, 3, 2, 6]
def baseStart_3671030 : Nat := 118140960795 + 3671030 * 2 ^ 59
def prefixEnd_3671030 : Nat := 4983230072969 + 3 ^ 40 * 3671030 * 2
def baseEnd_3671030 : Nat := 139629843487027949032759

theorem tailTrace_3671030 : CollatzResearch.WordTrace tailWord_3671030 prefixEnd_3671030 139629843487027949032759 := by
  unfold tailWord_3671030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8368341493155796678382159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89262309260328497902743029 8368341493155796678382159)
  ·
    refine ⟨12552512239733695017573239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8368341493155796678382159 12552512239733695017573239)
    ·
      refine ⟨18828768359600542526359859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12552512239733695017573239 18828768359600542526359859)
      ·
        refine ⟨28243152539400813789539789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18828768359600542526359859 28243152539400813789539789)
        ·
          refine ⟨10591182202275305171077421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28243152539400813789539789 10591182202275305171077421)
          ·
            refine ⟨3971693325853239439154033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10591182202275305171077421 3971693325853239439154033)
            ·
              refine ⟨2978769994389929579365525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971693325853239439154033 2978769994389929579365525)
              ·
                refine ⟨139629843487027949032759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2978769994389929579365525 139629843487027949032759)
                ·
                  rfl

theorem cell22_3671030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_3671030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671030 prefixEnd_3671030 := by exact prefixLift 3671030
  have htrace : WordTrace (prefixWord ++ tailWord_3671030) baseStart_3671030 baseEnd_3671030 := by
    simpa [prefixWord, tailWord_3671030, baseEnd_3671030] using wordTrace_append hprefix tailTrace_3671030
  have hstable : (prefixWord ++ tailWord_3671030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671030).length < 2 ^ (prefixWord ++ tailWord_3671030).sum := by decide
  have hdescent : baseEnd_3671030 < baseStart_3671030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671041 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 7]
def baseStart_3671041 : Nat := 118140960795 + 3671041 * 2 ^ 59
def prefixEnd_3671041 : Nat := 4983230072969 + 3 ^ 40 * 3671041 * 2
def baseEnd_3671041 : Nat := 418890785636017059756599

theorem tailTrace_3671041 : CollatzResearch.WordTrace tailWord_3671041 prefixEnd_3671041 418890785636017059756599 := by
  unfold tailWord_3671041
  simp only [CollatzResearch.WordTrace]
  refine ⟨133893865093452895732764977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89262576728968597155176651 133893865093452895732764977)
  ·
    refine ⟨100420398820089671799573733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133893865093452895732764977 100420398820089671799573733)
    ·
      refine ⟨18828824778766813462420075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100420398820089671799573733 18828824778766813462420075)
      ·
        refine ⟨28243237168150220193630113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18828824778766813462420075 28243237168150220193630113)
        ·
          refine ⟨21182427876112665145222585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28243237168150220193630113 21182427876112665145222585)
          ·
            refine ⟨15886820907084498858916939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21182427876112665145222585 15886820907084498858916939)
            ·
              refine ⟨23830231360626748288375409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15886820907084498858916939 23830231360626748288375409)
              ·
                refine ⟨17872673520470061216281557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23830231360626748288375409 17872673520470061216281557)
                ·
                  refine ⟨418890785636017059756599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17872673520470061216281557 418890785636017059756599)
                  ·
                    rfl

theorem cell22_3671041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_3671041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671041 prefixEnd_3671041 := by exact prefixLift 3671041
  have htrace : WordTrace (prefixWord ++ tailWord_3671041) baseStart_3671041 baseEnd_3671041 := by
    simpa [prefixWord, tailWord_3671041, baseEnd_3671041] using wordTrace_append hprefix tailTrace_3671041
  have hstable : (prefixWord ++ tailWord_3671041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671041).length < 2 ^ (prefixWord ++ tailWord_3671041).sum := by decide
  have hdescent : baseEnd_3671041 < baseStart_3671041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671075 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 5]
def baseStart_3671075 : Nat := 118140960795 + 3671075 * 2 ^ 59
def prefixEnd_3671075 : Nat := 4983230072969 + 3 ^ 40 * 3671075 * 2
def baseEnd_3671075 : Nat := 418894665267628807973231

theorem tailTrace_3671075 : CollatzResearch.WordTrace tailWord_3671075 prefixEnd_3671075 418894665267628807973231 := by
  unfold tailWord_3671075
  simp only [CollatzResearch.WordTrace]
  refine ⟨133895105175329719539502679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89263403450219813026335119 133895105175329719539502679)
  ·
    refine ⟨200842657762994579309254019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133895105175329719539502679 200842657762994579309254019)
    ·
      refine ⟨301263986644491868963881029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200842657762994579309254019 301263986644491868963881029)
      ·
        refine ⟨56486997495842225430727693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301263986644491868963881029 56486997495842225430727693)
        ·
          refine ⟨21182624060940834536522885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56486997495842225430727693 21182624060940834536522885)
          ·
            refine ⟨3971742011426406475598041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21182624060940834536522885 3971742011426406475598041)
            ·
              refine ⟨2978806508569804856698531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971742011426406475598041 2978806508569804856698531)
              ·
                refine ⟨4468209762854707285047797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978806508569804856698531 4468209762854707285047797)
                ·
                  refine ⟨418894665267628807973231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4468209762854707285047797 418894665267628807973231)
                  ·
                    rfl

theorem cell22_3671075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 5].length) (baseStart_3671075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671075 prefixEnd_3671075 := by exact prefixLift 3671075
  have htrace : WordTrace (prefixWord ++ tailWord_3671075) baseStart_3671075 baseEnd_3671075 := by
    simpa [prefixWord, tailWord_3671075, baseEnd_3671075] using wordTrace_append hprefix tailTrace_3671075
  have hstable : (prefixWord ++ tailWord_3671075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671075).length < 2 ^ (prefixWord ++ tailWord_3671075).sum := by decide
  have hdescent : baseEnd_3671075 < baseStart_3671075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671103 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 4]
def baseStart_3671103 : Nat := 118140960795 + 3671103 * 2 ^ 59
def prefixEnd_3671103 : Nat := 4983230072969 + 3 ^ 40 * 3671103 * 2
def baseEnd_3671103 : Nat := 418897860258367894739869

theorem tailTrace_3671103 : CollatzResearch.WordTrace tailWord_3671103 prefixEnd_3671103 418897860258367894739869 := by
  unfold tailWord_3671103
  simp only [CollatzResearch.WordTrace]
  refine ⟨133896126419228280321521963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89264084279485520214347975 133896126419228280321521963)
  ·
    refine ⟨200844189628842420482282945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133896126419228280321521963 200844189628842420482282945)
    ·
      refine ⟨150633142221631815361712209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200844189628842420482282945 150633142221631815361712209)
      ·
        refine ⟨112974856666223861521284157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150633142221631815361712209 112974856666223861521284157)
        ·
          refine ⟨42365571249833948070481559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112974856666223861521284157 42365571249833948070481559)
          ·
            refine ⟨63548356874750922105722339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42365571249833948070481559 63548356874750922105722339)
            ·
              refine ⟨95322535312126383158583509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63548356874750922105722339 95322535312126383158583509)
              ·
                refine ⟨2234121921377962105279301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95322535312126383158583509 2234121921377962105279301)
                ·
                  refine ⟨418897860258367894739869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234121921377962105279301 418897860258367894739869)
                  ·
                    rfl

theorem cell22_3671103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 4].length) (baseStart_3671103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671103 prefixEnd_3671103 := by exact prefixLift 3671103
  have htrace : WordTrace (prefixWord ++ tailWord_3671103) baseStart_3671103 baseEnd_3671103 := by
    simpa [prefixWord, tailWord_3671103, baseEnd_3671103] using wordTrace_append hprefix tailTrace_3671103
  have hstable : (prefixWord ++ tailWord_3671103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671103).length < 2 ^ (prefixWord ++ tailWord_3671103).sum := by decide
  have hdescent : baseEnd_3671103 < baseStart_3671103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671116 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_3671116 : Nat := 118140960795 + 3671116 * 2 ^ 59
def prefixEnd_3671116 : Nat := 4983230072969 + 3 ^ 40 * 3671116 * 2
def baseEnd_3671116 : Nat := 1256698030940775983644567

theorem tailTrace_3671116 : CollatzResearch.WordTrace tailWord_3671116 prefixEnd_3671116 1256698030940775983644567 := by
  unfold tailWord_3671116
  simp only [CollatzResearch.WordTrace]
  refine ⟨66948300284090591770872601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89264400378787455694496801 66948300284090591770872601)
  ·
    refine ⟨50211225213067943828154451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66948300284090591770872601 50211225213067943828154451)
    ·
      refine ⟨75316837819601915742231677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50211225213067943828154451 75316837819601915742231677)
      ·
        refine ⟨28243814182350718403336879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75316837819601915742231677 28243814182350718403336879)
        ·
          refine ⟨42365721273526077605005319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28243814182350718403336879 42365721273526077605005319)
          ·
            refine ⟨63548581910289116407507979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42365721273526077605005319 63548581910289116407507979)
            ·
              refine ⟨95322872865433674611261969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63548581910289116407507979 95322872865433674611261969)
              ·
                refine ⟨71492154649075255958446477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95322872865433674611261969 71492154649075255958446477)
                ·
                  refine ⟨26809557993403220984417429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71492154649075255958446477 26809557993403220984417429)
                  ·
                    refine ⟨1256698030940775983644567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26809557993403220984417429 1256698030940775983644567)
                    ·
                      rfl

theorem cell22_3671116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_3671116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671116 prefixEnd_3671116 := by exact prefixLift 3671116
  have htrace : WordTrace (prefixWord ++ tailWord_3671116) baseStart_3671116 baseEnd_3671116 := by
    simpa [prefixWord, tailWord_3671116, baseEnd_3671116] using wordTrace_append hprefix tailTrace_3671116
  have hstable : (prefixWord ++ tailWord_3671116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671116).length < 2 ^ (prefixWord ++ tailWord_3671116).sum := by decide
  have hdescent : baseEnd_3671116 < baseStart_3671116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671148 : List Nat := [2, 2, 1, 1, 3, 2, 5, 6]
def baseStart_3671148 : Nat := 118140960795 + 3671148 * 2 ^ 59
def prefixEnd_3671148 : Nat := 4983230072969 + 3 ^ 40 * 3671148 * 2
def baseEnd_3671148 : Nat := 139634331688304285204941

theorem tailTrace_3671148 : CollatzResearch.WordTrace tailWord_3671148 prefixEnd_3671148 139634331688304285204941 := by
  unfold tailWord_3671148
  simp only [CollatzResearch.WordTrace]
  refine ⟨66948883852032626503455049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89265178469376835337940065 66948883852032626503455049)
  ·
    refine ⟨50211662889024469877591287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66948883852032626503455049 50211662889024469877591287)
    ·
      refine ⟨75317494333536704816386931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50211662889024469877591287 75317494333536704816386931)
      ·
        refine ⟨112976241500305057224580397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75317494333536704816386931 112976241500305057224580397)
        ·
          refine ⟨42366090562614396459217649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112976241500305057224580397 42366090562614396459217649)
          ·
            refine ⟨31774567921960797344413237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42366090562614396459217649 31774567921960797344413237)
            ·
              refine ⟨2978865742683824751038741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31774567921960797344413237 2978865742683824751038741)
              ·
                refine ⟨139634331688304285204941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2978865742683824751038741 139634331688304285204941)
                ·
                  rfl

theorem cell22_3671148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 6].length) (baseStart_3671148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671148 prefixEnd_3671148 := by exact prefixLift 3671148
  have htrace : WordTrace (prefixWord ++ tailWord_3671148) baseStart_3671148 baseEnd_3671148 := by
    simpa [prefixWord, tailWord_3671148, baseEnd_3671148] using wordTrace_append hprefix tailTrace_3671148
  have hstable : (prefixWord ++ tailWord_3671148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671148).length < 2 ^ (prefixWord ++ tailWord_3671148).sum := by decide
  have hdescent : baseEnd_3671148 < baseStart_3671148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671150 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3671150 : Nat := 118140960795 + 3671150 * 2 ^ 59
def prefixEnd_3671150 : Nat := 4983230072969 + 3 ^ 40 * 3671150 * 2
def baseEnd_3671150 : Nat := 1256709669835611228294463

theorem tailTrace_3671150 : CollatzResearch.WordTrace tailWord_3671150 prefixEnd_3671150 1256709669835611228294463 := by
  unfold tailWord_3671150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737230081257250918560363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89265227100038671565655269 16737230081257250918560363)
  ·
    refine ⟨25105845121885876377840545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16737230081257250918560363 25105845121885876377840545)
    ·
      refine ⟨18829383841414407283380409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25105845121885876377840545 18829383841414407283380409)
      ·
        refine ⟨14122037881060805462535307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18829383841414407283380409 14122037881060805462535307)
        ·
          refine ⟨21183056821591208193802961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14122037881060805462535307 21183056821591208193802961)
          ·
            refine ⟨15887292616193406145352221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21183056821591208193802961 15887292616193406145352221)
            ·
              refine ⟨5957734731072527304507083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15887292616193406145352221 5957734731072527304507083)
              ·
                refine ⟨8936602096608790956760625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5957734731072527304507083 8936602096608790956760625)
                ·
                  refine ⟨6702451572456593217570469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8936602096608790956760625 6702451572456593217570469)
                  ·
                    refine ⟨1256709669835611228294463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702451572456593217570469 1256709669835611228294463)
                    ·
                      rfl

theorem cell22_3671150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3671150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671150 prefixEnd_3671150 := by exact prefixLift 3671150
  have htrace : WordTrace (prefixWord ++ tailWord_3671150) baseStart_3671150 baseEnd_3671150 := by
    simpa [prefixWord, tailWord_3671150, baseEnd_3671150] using wordTrace_append hprefix tailTrace_3671150
  have hstable : (prefixWord ++ tailWord_3671150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671150).length < 2 ^ (prefixWord ++ tailWord_3671150).sum := by decide
  have hdescent : baseEnd_3671150 < baseStart_3671150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671210 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_3671210 : Nat := 118140960795 + 3671210 * 2 ^ 59
def prefixEnd_3671210 : Nat := 4983230072969 + 3 ^ 40 * 3671210 * 2
def baseEnd_3671210 : Nat := 418910069687263690598093

theorem tailTrace_3671210 : CollatzResearch.WordTrace tailWord_3671210 prefixEnd_3671210 418910069687263690598093 := by
  unfold tailWord_3671210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33475007257460159398916771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89266686019893758397111389 33475007257460159398916771)
  ·
    refine ⟨50212510886190239098375157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33475007257460159398916771 50212510886190239098375157)
    ·
      refine ⟨4707422895580334915472671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50212510886190239098375157 4707422895580334915472671)
      ·
        refine ⟨7061134343370502373209007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707422895580334915472671 7061134343370502373209007)
        ·
          refine ⟨10591701515055753559813511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061134343370502373209007 10591701515055753559813511)
          ·
            refine ⟨15887552272583630339720267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591701515055753559813511 15887552272583630339720267)
            ·
              refine ⟨23831328408875445509580401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887552272583630339720267 23831328408875445509580401)
              ·
                refine ⟨17873496306656584132185301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23831328408875445509580401 17873496306656584132185301)
                ·
                  refine ⟨418910069687263690598093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17873496306656584132185301 418910069687263690598093)
                  ·
                    rfl

theorem cell22_3671210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_3671210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671210 prefixEnd_3671210 := by exact prefixLift 3671210
  have htrace : WordTrace (prefixWord ++ tailWord_3671210) baseStart_3671210 baseEnd_3671210 := by
    simpa [prefixWord, tailWord_3671210, baseEnd_3671210] using wordTrace_append hprefix tailTrace_3671210
  have hstable : (prefixWord ++ tailWord_3671210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671210).length < 2 ^ (prefixWord ++ tailWord_3671210).sum := by decide
  have hdescent : baseEnd_3671210 < baseStart_3671210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671268 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_3671268 : Nat := 118140960795 + 3671268 * 2 ^ 59
def prefixEnd_3671268 : Nat := 4983230072969 + 3 ^ 40 * 3671268 * 2
def baseEnd_3671268 : Nat := 1256750063647098253844101

theorem tailTrace_3671268 : CollatzResearch.WordTrace tailWord_3671268 prefixEnd_3671268 1256750063647098253844101 := by
  unfold tailWord_3671268
  simp only [CollatzResearch.WordTrace]
  refine ⟨66951072231815256750639229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89268096309087009000852305 66951072231815256750639229)
  ·
    refine ⟨25106652086930721281489711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66951072231815256750639229 25106652086930721281489711)
    ·
      refine ⟨37659978130396081922234567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25106652086930721281489711 37659978130396081922234567)
      ·
        refine ⟨56489967195594122883351851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37659978130396081922234567 56489967195594122883351851)
        ·
          refine ⟨84734950793391184325027777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56489967195594122883351851 84734950793391184325027777)
          ·
            refine ⟨63551213095043388243770833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84734950793391184325027777 63551213095043388243770833)
            ·
              refine ⟨47663409821282541182828125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63551213095043388243770833 47663409821282541182828125)
              ·
                refine ⟨17873778682980952943560547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47663409821282541182828125 17873778682980952943560547)
                ·
                  refine ⟨26810668024471429415340821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17873778682980952943560547 26810668024471429415340821)
                  ·
                    refine ⟨1256750063647098253844101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26810668024471429415340821 1256750063647098253844101)
                    ·
                      rfl

theorem cell22_3671268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_3671268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671268 prefixEnd_3671268 := by exact prefixLift 3671268
  have htrace : WordTrace (prefixWord ++ tailWord_3671268) baseStart_3671268 baseEnd_3671268 := by
    simpa [prefixWord, tailWord_3671268, baseEnd_3671268] using wordTrace_append hprefix tailTrace_3671268
  have hstable : (prefixWord ++ tailWord_3671268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671268).length < 2 ^ (prefixWord ++ tailWord_3671268).sum := by decide
  have hdescent : baseEnd_3671268 < baseStart_3671268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671300 : List Nat := [2, 3, 2, 2, 2, 1, 3, 7]
def baseStart_3671300 : Nat := 118140960795 + 3671300 * 2 ^ 59
def prefixEnd_3671300 : Nat := 4983230072969 + 3 ^ 40 * 3671300 * 2
def baseEnd_3671300 : Nat := 139640113100117870782667

theorem tailTrace_3671300 : CollatzResearch.WordTrace tailWord_3671300 prefixEnd_3671300 139640113100117870782667 := by
  unfold tailWord_3671300
  simp only [CollatzResearch.WordTrace]
  refine ⟨66951655799757291483221677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89268874399676388644295569 66951655799757291483221677)
  ·
    refine ⟨25106870924908984306208129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66951655799757291483221677 25106870924908984306208129)
    ·
      refine ⟨18830153193681738229656097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25106870924908984306208129 18830153193681738229656097)
      ·
        refine ⟨14122614895261303672242073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18830153193681738229656097 14122614895261303672242073)
        ·
          refine ⟨10591961171445977754181555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14122614895261303672242073 10591961171445977754181555)
          ·
            refine ⟨15887941757168966631272333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591961171445977754181555 15887941757168966631272333)
            ·
              refine ⟨5957978158938362486727125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15887941757168966631272333 5957978158938362486727125)
              ·
                refine ⟨139640113100117870782667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5957978158938362486727125 139640113100117870782667)
                ·
                  rfl

theorem cell22_3671300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_3671300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671300 prefixEnd_3671300 := by exact prefixLift 3671300
  have htrace : WordTrace (prefixWord ++ tailWord_3671300) baseStart_3671300 baseEnd_3671300 := by
    simpa [prefixWord, tailWord_3671300, baseEnd_3671300] using wordTrace_append hprefix tailTrace_3671300
  have hstable : (prefixWord ++ tailWord_3671300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671300).length < 2 ^ (prefixWord ++ tailWord_3671300).sum := by decide
  have hdescent : baseEnd_3671300 < baseStart_3671300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671313 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3671313 : Nat := 118140960795 + 3671313 * 2 ^ 59
def prefixEnd_3671313 : Nat := 4983230072969 + 3 ^ 40 * 3671313 * 2
def baseEnd_3671313 : Nat := 1256765468066733136468963

theorem tailTrace_3671313 : CollatzResearch.WordTrace tailWord_3671313 prefixEnd_3671313 1256765468066733136468963 := by
  unfold tailWord_3671313
  simp only [CollatzResearch.WordTrace]
  refine ⟨133903785748467486186666593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89269190498978324124444395 133903785748467486186666593)
  ·
    refine ⟨100427839311350614639999945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133903785748467486186666593 100427839311350614639999945)
    ·
      refine ⟨75320879483512960979999959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100427839311350614639999945 75320879483512960979999959)
      ·
        refine ⟨112981319225269441469999939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75320879483512960979999959 112981319225269441469999939)
        ·
          refine ⟨169471978837904162204999909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112981319225269441469999939 169471978837904162204999909)
          ·
            refine ⟨31775996032107030413437483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169471978837904162204999909 31775996032107030413437483)
            ·
              refine ⟨47663994048160545620156225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31775996032107030413437483 47663994048160545620156225)
              ·
                refine ⟨35747995536120409215117169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47663994048160545620156225 35747995536120409215117169)
                ·
                  refine ⟨26810996652090306911337877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35747995536120409215117169 26810996652090306911337877)
                  ·
                    refine ⟨1256765468066733136468963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26810996652090306911337877 1256765468066733136468963)
                    ·
                      rfl

theorem cell22_3671313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3671313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671313 prefixEnd_3671313 := by exact prefixLift 3671313
  have htrace : WordTrace (prefixWord ++ tailWord_3671313) baseStart_3671313 baseEnd_3671313 := by
    simpa [prefixWord, tailWord_3671313, baseEnd_3671313] using wordTrace_append hprefix tailTrace_3671313
  have hstable : (prefixWord ++ tailWord_3671313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671313).length < 2 ^ (prefixWord ++ tailWord_3671313).sum := by decide
  have hdescent : baseEnd_3671313 < baseStart_3671313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671345 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 7]
def baseStart_3671345 : Nat := 118140960795 + 3671345 * 2 ^ 59
def prefixEnd_3671345 : Nat := 4983230072969 + 3 ^ 40 * 3671345 * 2
def baseEnd_3671345 : Nat := 418925474106898573222955

theorem tailTrace_3671345 : CollatzResearch.WordTrace tailWord_3671345 prefixEnd_3671345 418925474106898573222955 := by
  unfold tailWord_3671345
  simp only [CollatzResearch.WordTrace]
  refine ⟨133904952884351555651831489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89269968589567703767887659 133904952884351555651831489)
  ·
    refine ⟨100428714663263666738873617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133904952884351555651831489 100428714663263666738873617)
    ·
      refine ⟨75321535997447750054155213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100428714663263666738873617 75321535997447750054155213)
      ·
        refine ⟨28245575999042906270308205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75321535997447750054155213 28245575999042906270308205)
        ·
          refine ⟨10592090999641089851365577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28245575999042906270308205 10592090999641089851365577)
          ·
            refine ⟨7944068249730817388524183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10592090999641089851365577 7944068249730817388524183)
            ·
              refine ⟨11916102374596226082786275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944068249730817388524183 11916102374596226082786275)
              ·
                refine ⟨17874153561894339124179413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11916102374596226082786275 17874153561894339124179413)
                ·
                  refine ⟨418925474106898573222955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17874153561894339124179413 418925474106898573222955)
                  ·
                    rfl

theorem cell22_3671345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_3671345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671345 prefixEnd_3671345 := by exact prefixLift 3671345
  have htrace : WordTrace (prefixWord ++ tailWord_3671345) baseStart_3671345 baseEnd_3671345 := by
    simpa [prefixWord, tailWord_3671345, baseEnd_3671345] using wordTrace_append hprefix tailTrace_3671345
  have hstable : (prefixWord ++ tailWord_3671345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671345).length < 2 ^ (prefixWord ++ tailWord_3671345).sum := by decide
  have hdescent : baseEnd_3671345 < baseStart_3671345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671349 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3671349 : Nat := 118140960795 + 3671349 * 2 ^ 59
def prefixEnd_3671349 : Nat := 4983230072969 + 3 ^ 40 * 3671349 * 2
def baseEnd_3671349 : Nat := 1256777791602441042568853

theorem tailTrace_3671349 : CollatzResearch.WordTrace tailWord_3671349 prefixEnd_3671349 1256777791602441042568853 := by
  unfold tailWord_3671349
  simp only [CollatzResearch.WordTrace]
  refine ⟨133905098776337064334977101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89270065850891376223318067 133905098776337064334977101)
  ·
    refine ⟨50214412041126399125616413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133905098776337064334977101 50214412041126399125616413)
    ·
      refine ⟨18830404515422399672106155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50214412041126399125616413 18830404515422399672106155)
      ·
        refine ⟨28245606773133599508159233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18830404515422399672106155 28245606773133599508159233)
        ·
          refine ⟨21184205079850199631119425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28245606773133599508159233 21184205079850199631119425)
          ·
            refine ⟨15888153809887649723339569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21184205079850199631119425 15888153809887649723339569)
            ·
              refine ⟨11916115357415737292504677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15888153809887649723339569 11916115357415737292504677)
              ·
                refine ⟨2234271629515450742344627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11916115357415737292504677 2234271629515450742344627)
                ·
                  refine ⟨3351407444273176113516941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234271629515450742344627 3351407444273176113516941)
                  ·
                    refine ⟨1256777791602441042568853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351407444273176113516941 1256777791602441042568853)
                    ·
                      rfl

theorem cell22_3671349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3671349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671349 prefixEnd_3671349 := by exact prefixLift 3671349
  have htrace : WordTrace (prefixWord ++ tailWord_3671349) baseStart_3671349 baseEnd_3671349 := by
    simpa [prefixWord, tailWord_3671349, baseEnd_3671349] using wordTrace_append hprefix tailTrace_3671349
  have hstable : (prefixWord ++ tailWord_3671349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671349).length < 2 ^ (prefixWord ++ tailWord_3671349).sum := by decide
  have hdescent : baseEnd_3671349 < baseStart_3671349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671392 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_3671392 : Nat := 118140960795 + 3671392 * 2 ^ 59
def prefixEnd_3671392 : Nat := 4983230072969 + 3 ^ 40 * 3671392 * 2
def baseEnd_3671392 : Nat := 1256792511381203263743721

theorem tailTrace_3671392 : CollatzResearch.WordTrace tailWord_3671392 prefixEnd_3671392 1256792511381203263743721 := by
  unfold tailWord_3671392
  simp only [CollatzResearch.WordTrace]
  refine ⟨66953333557590641339396215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89271111410120855119194953 66953333557590641339396215)
  ·
    refine ⟨100430000336385962009094323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66953333557590641339396215 100430000336385962009094323)
    ·
      refine ⟨150645000504578943013641485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100430000336385962009094323 150645000504578943013641485)
      ·
        refine ⟨56491875189217103630115557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150645000504578943013641485 56491875189217103630115557)
        ·
          refine ⟨10592226597978206930646667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56491875189217103630115557 10592226597978206930646667)
          ·
            refine ⟨15888339896967310395970001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10592226597978206930646667 15888339896967310395970001)
            ·
              refine ⟨11916254922725482796977501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15888339896967310395970001 11916254922725482796977501)
              ·
                refine ⟨4468595596022056048866563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11916254922725482796977501 4468595596022056048866563)
                ·
                  refine ⟨6702893394033084073299845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468595596022056048866563 6702893394033084073299845)
                  ·
                    refine ⟨1256792511381203263743721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702893394033084073299845 1256792511381203263743721)
                    ·
                      rfl

theorem cell22_3671392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_3671392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671392 prefixEnd_3671392 := by exact prefixLift 3671392
  have htrace : WordTrace (prefixWord ++ tailWord_3671392) baseStart_3671392 baseEnd_3671392 := by
    simpa [prefixWord, tailWord_3671392, baseEnd_3671392] using wordTrace_append hprefix tailTrace_3671392
  have hstable : (prefixWord ++ tailWord_3671392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671392).length < 2 ^ (prefixWord ++ tailWord_3671392).sum := by decide
  have hdescent : baseEnd_3671392 < baseStart_3671392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671420 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_3671420 : Nat := 118140960795 + 3671420 * 2 ^ 59
def prefixEnd_3671420 : Nat := 4983230072969 + 3 ^ 40 * 3671420 * 2
def baseEnd_3671420 : Nat := 1256802096353420524043635

theorem tailTrace_3671420 : CollatzResearch.WordTrace tailWord_3671420 prefixEnd_3671420 1256802096353420524043635 := by
  unfold tailWord_3671420
  simp only [CollatzResearch.WordTrace]
  refine ⟨66953844179539921730405857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89271792239386562307207809 66953844179539921730405857)
  ·
    refine ⟨50215383134654941297804393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66953844179539921730405857 50215383134654941297804393)
    ·
      refine ⟨37661537350991205973353295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50215383134654941297804393 37661537350991205973353295)
      ·
        refine ⟨56492306026486808960029943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37661537350991205973353295 56492306026486808960029943)
        ·
          refine ⟨84738459039730213440044915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56492306026486808960029943 84738459039730213440044915)
          ·
            refine ⟨127107688559595320160067373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84738459039730213440044915 127107688559595320160067373)
            ·
              refine ⟨47665383209848245060025265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127107688559595320160067373 47665383209848245060025265)
              ·
                refine ⟨35749037407386183795018949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47665383209848245060025265 35749037407386183795018949)
                ·
                  refine ⟨6702944513884909461566053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35749037407386183795018949 6702944513884909461566053)
                  ·
                    refine ⟨1256802096353420524043635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702944513884909461566053 1256802096353420524043635)
                    ·
                      rfl

theorem cell22_3671420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_3671420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671420 prefixEnd_3671420 := by exact prefixLift 3671420
  have htrace : WordTrace (prefixWord ++ tailWord_3671420) baseStart_3671420 baseEnd_3671420 := by
    simpa [prefixWord, tailWord_3671420, baseEnd_3671420] using wordTrace_append hprefix tailTrace_3671420
  have hstable : (prefixWord ++ tailWord_3671420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671420).length < 2 ^ (prefixWord ++ tailWord_3671420).sum := by decide
  have hdescent : baseEnd_3671420 < baseStart_3671420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671426 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3671426 : Nat := 118140960795 + 3671426 * 2 ^ 59
def prefixEnd_3671426 : Nat := 4983230072969 + 3 ^ 40 * 3671426 * 2
def baseEnd_3671426 : Nat := 1256804150276038508393617

theorem tailTrace_3671426 : CollatzResearch.WordTrace tailWord_3671426 prefixEnd_3671426 1256804150276038508393617 := by
  unfold tailWord_3671426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33476976799264526621382533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89271938131372070990353421 33476976799264526621382533)
  ·
    refine ⟨6276933149862098741509225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33476976799264526621382533 6276933149862098741509225)
    ·
      refine ⟨4707699862396574056131919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6276933149862098741509225 4707699862396574056131919)
      ·
        refine ⟨7061549793594861084197879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707699862396574056131919 7061549793594861084197879)
        ·
          refine ⟨10592324690392291626296819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061549793594861084197879 10592324690392291626296819)
          ·
            refine ⟨15888487035588437439445229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10592324690392291626296819 15888487035588437439445229)
            ·
              refine ⟨5958182638345664039791961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15888487035588437439445229 5958182638345664039791961)
              ·
                refine ⟨4468636978759248029843971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958182638345664039791961 4468636978759248029843971)
                ·
                  refine ⟨6702955468138872044765957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468636978759248029843971 6702955468138872044765957)
                  ·
                    refine ⟨1256804150276038508393617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702955468138872044765957 1256804150276038508393617)
                    ·
                      rfl

theorem cell22_3671426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3671426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671426 prefixEnd_3671426 := by exact prefixLift 3671426
  have htrace : WordTrace (prefixWord ++ tailWord_3671426) baseStart_3671426 baseEnd_3671426 := by
    simpa [prefixWord, tailWord_3671426, baseEnd_3671426] using wordTrace_append hprefix tailTrace_3671426
  have hstable : (prefixWord ++ tailWord_3671426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671426).length < 2 ^ (prefixWord ++ tailWord_3671426).sum := by decide
  have hdescent : baseEnd_3671426 < baseStart_3671426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671452 : List Nat := [2, 2, 3, 4, 1, 10]
def baseStart_3671452 : Nat := 118140960795 + 3671452 * 2 ^ 59
def prefixEnd_3671452 : Nat := 4983230072969 + 3 ^ 40 * 3671452 * 2
def baseEnd_3671452 : Nat := 15516210501325717373377

theorem tailTrace_3671452 : CollatzResearch.WordTrace tailWord_3671452 prefixEnd_3671452 15516210501325717373377 := by
  unfold tailWord_3671452
  simp only [CollatzResearch.WordTrace]
  refine ⟨66954427747481956462988305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89272570329975941950651073 66954427747481956462988305)
  ·
    refine ⟨50215820810611467347241229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66954427747481956462988305 50215820810611467347241229)
    ·
      refine ⟨18830932803979300255215461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50215820810611467347241229 18830932803979300255215461)
      ·
        refine ⟨3530799900746118797852899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18830932803979300255215461 3530799900746118797852899)
        ·
          refine ⟨5296199851119178196779349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530799900746118797852899 5296199851119178196779349)
          ·
            refine ⟨15516210501325717373377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5296199851119178196779349 15516210501325717373377)
            ·
              rfl

theorem cell22_3671452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 10].length) (baseStart_3671452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671452 prefixEnd_3671452 := by exact prefixLift 3671452
  have htrace : WordTrace (prefixWord ++ tailWord_3671452) baseStart_3671452 baseEnd_3671452 := by
    simpa [prefixWord, tailWord_3671452, baseEnd_3671452] using wordTrace_append hprefix tailTrace_3671452
  have hstable : (prefixWord ++ tailWord_3671452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671452).length < 2 ^ (prefixWord ++ tailWord_3671452).sum := by decide
  have hdescent : baseEnd_3671452 < baseStart_3671452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671469 : List Nat := [1, 5, 2, 2, 1, 3, 1, 7]
def baseStart_3671469 : Nat := 118140960795 + 3671469 * 2 ^ 59
def prefixEnd_3671469 : Nat := 4983230072969 + 3 ^ 40 * 3671469 * 2
def baseEnd_3671469 : Nat := 139646541117200081063165

theorem tailTrace_3671469 : CollatzResearch.WordTrace tailWord_3671469 prefixEnd_3671469 139646541117200081063165 := by
  unfold tailWord_3671469
  simp only [CollatzResearch.WordTrace]
  refine ⟨133909475535902324829345461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89272983690601549886230307 133909475535902324829345461)
  ·
    refine ⟨12554013331490842952751137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133909475535902324829345461 12554013331490842952751137)
    ·
      refine ⟨9415509998618132214563353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12554013331490842952751137 9415509998618132214563353)
      ·
        refine ⟨7061632498963599160922515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9415509998618132214563353 7061632498963599160922515)
        ·
          refine ⟨10592448748445398741383773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061632498963599160922515 10592448748445398741383773)
          ·
            refine ⟨3972168280667024528018915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10592448748445398741383773 3972168280667024528018915)
            ·
              refine ⟨5958252421000536792028373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972168280667024528018915 5958252421000536792028373)
              ·
                refine ⟨139646541117200081063165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5958252421000536792028373 139646541117200081063165)
                ·
                  rfl

theorem cell22_3671469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 7].length) (baseStart_3671469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671469 prefixEnd_3671469 := by exact prefixLift 3671469
  have htrace : WordTrace (prefixWord ++ tailWord_3671469) baseStart_3671469 baseEnd_3671469 := by
    simpa [prefixWord, tailWord_3671469, baseEnd_3671469] using wordTrace_append hprefix tailTrace_3671469
  have hstable : (prefixWord ++ tailWord_3671469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671469).length < 2 ^ (prefixWord ++ tailWord_3671469).sum := by decide
  have hdescent : baseEnd_3671469 < baseStart_3671469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671495 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3671495 : Nat := 118140960795 + 3671495 * 2 ^ 59
def prefixEnd_3671495 : Nat := 4983230072969 + 3 ^ 40 * 3671495 * 2
def baseEnd_3671495 : Nat := 1256827770386145328418405

theorem tailTrace_3671495 : CollatzResearch.WordTrace tailWord_3671495 prefixEnd_3671495 1256827770386145328418405 := by
  unfold tailWord_3671495
  simp only [CollatzResearch.WordTrace]
  refine ⟨133910423833808131269791939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89273615889205420846527959 133910423833808131269791939)
  ·
    refine ⟨200865635750712196904687909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133910423833808131269791939 200865635750712196904687909)
    ·
      refine ⟨37662306703258536919628983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200865635750712196904687909 37662306703258536919628983)
      ·
        refine ⟨56493460054887805379443475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37662306703258536919628983 56493460054887805379443475)
        ·
          refine ⟨84740190082331708069165213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56493460054887805379443475 84740190082331708069165213)
          ·
            refine ⟨31777571280874390525936955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84740190082331708069165213 31777571280874390525936955)
            ·
              refine ⟨47666356921311585788905433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31777571280874390525936955 47666356921311585788905433)
              ·
                refine ⟨35749767690983689341679075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47666356921311585788905433 35749767690983689341679075)
                ·
                  refine ⟨53624651536475534012518613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35749767690983689341679075 53624651536475534012518613)
                  ·
                    refine ⟨1256827770386145328418405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53624651536475534012518613 1256827770386145328418405)
                    ·
                      rfl

theorem cell22_3671495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3671495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671495 prefixEnd_3671495 := by exact prefixLift 3671495
  have htrace : WordTrace (prefixWord ++ tailWord_3671495) baseStart_3671495 baseEnd_3671495 := by
    simpa [prefixWord, tailWord_3671495, baseEnd_3671495] using wordTrace_append hprefix tailTrace_3671495
  have hstable : (prefixWord ++ tailWord_3671495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671495).length < 2 ^ (prefixWord ++ tailWord_3671495).sum := by decide
  have hdescent : baseEnd_3671495 < baseStart_3671495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671514 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_3671514 : Nat := 118140960795 + 3671514 * 2 ^ 59
def prefixEnd_3671514 : Nat := 4983230072969 + 3 ^ 40 * 3671514 * 2
def baseEnd_3671514 : Nat := 418944758158145204064449

theorem tailTrace_3671514 : CollatzResearch.WordTrace tailWord_3671514 prefixEnd_3671514 418944758158145204064449 := by
  unfold tailWord_3671514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477779205184824378683399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89274077880492865009822397 33477779205184824378683399)
  ·
    refine ⟨50216668807777236568025099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33477779205184824378683399 50216668807777236568025099)
    ·
      refine ⟨75325003211665854852037649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50216668807777236568025099 75325003211665854852037649)
      ·
        refine ⟨56493752408749391139028237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75325003211665854852037649 56493752408749391139028237)
        ·
          refine ⟨21185157153281021677135589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56493752408749391139028237 21185157153281021677135589)
          ·
            refine ⟨3972216966240191564462923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21185157153281021677135589 3972216966240191564462923)
            ·
              refine ⟨5958325449360287346694385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972216966240191564462923 5958325449360287346694385)
              ·
                refine ⟨4468744087020215510020789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958325449360287346694385 4468744087020215510020789)
                ·
                  refine ⟨418944758158145204064449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4468744087020215510020789 418944758158145204064449)
                  ·
                    rfl

theorem cell22_3671514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_3671514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671514 prefixEnd_3671514 := by exact prefixLift 3671514
  have htrace : WordTrace (prefixWord ++ tailWord_3671514) baseStart_3671514 baseEnd_3671514 := by
    simpa [prefixWord, tailWord_3671514, baseEnd_3671514] using wordTrace_append hprefix tailTrace_3671514
  have hstable : (prefixWord ++ tailWord_3671514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671514).length < 2 ^ (prefixWord ++ tailWord_3671514).sum := by decide
  have hdescent : baseEnd_3671514 < baseStart_3671514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671544 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_3671544 : Nat := 118140960795 + 3671544 * 2 ^ 59
def prefixEnd_3671544 : Nat := 4983230072969 + 3 ^ 40 * 3671544 * 2
def baseEnd_3671544 : Nat := 1256844544087525533943255

theorem tailTrace_3671544 : CollatzResearch.WordTrace tailWord_3671544 prefixEnd_3671544 1256844544087525533943255 := by
  unfold tailWord_3671544
  simp only [CollatzResearch.WordTrace]
  refine ⟨66956105505315306319162843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89274807340420408425550457 66956105505315306319162843)
  ·
    refine ⟨100434158257972959478744265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66956105505315306319162843 100434158257972959478744265)
    ·
      refine ⟨75325618693479719609058199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100434158257972959478744265 75325618693479719609058199)
      ·
        refine ⟨112988428040219579413587299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75325618693479719609058199 112988428040219579413587299)
        ·
          refine ⟨169482642060329369120380949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112988428040219579413587299 169482642060329369120380949)
          ·
            refine ⟨7944498846577939177517857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169482642060329369120380949 7944498846577939177517857)
            ·
              refine ⟨5958374134933454383138393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944498846577939177517857 5958374134933454383138393)
              ·
                refine ⟨4468780601200090787353795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5958374134933454383138393 4468780601200090787353795)
                ·
                  refine ⟨6703170901800136181030693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468780601200090787353795 6703170901800136181030693)
                  ·
                    refine ⟨1256844544087525533943255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703170901800136181030693 1256844544087525533943255)
                    ·
                      rfl

theorem cell22_3671544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_3671544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671544 prefixEnd_3671544 := by exact prefixLift 3671544
  have htrace : WordTrace (prefixWord ++ tailWord_3671544) baseStart_3671544 baseEnd_3671544 := by
    simpa [prefixWord, tailWord_3671544, baseEnd_3671544] using wordTrace_append hprefix tailTrace_3671544
  have hstable : (prefixWord ++ tailWord_3671544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671544).length < 2 ^ (prefixWord ++ tailWord_3671544).sum := by decide
  have hdescent : baseEnd_3671544 < baseStart_3671544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671576 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 6]
def baseStart_3671576 : Nat := 118140960795 + 3671576 * 2 ^ 59
def prefixEnd_3671576 : Nat := 4983230072969 + 3 ^ 40 * 3671576 * 2
def baseEnd_3671576 : Nat := 418951832780496039047719

theorem tailTrace_3671576 : CollatzResearch.WordTrace tailWord_3671576 prefixEnd_3671576 418951832780496039047719 := by
  unfold tailWord_3671576
  simp only [CollatzResearch.WordTrace]
  refine ⟨66956689073257341051745291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89275585431009788068993721 66956689073257341051745291)
  ·
    refine ⟨100435033609886011577617937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66956689073257341051745291 100435033609886011577617937)
    ·
      refine ⟨75326275207414508683213453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100435033609886011577617937 75326275207414508683213453)
      ·
        refine ⟨28247353202780440756205045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75326275207414508683213453 28247353202780440756205045)
        ·
          refine ⟨2648189362760666320894223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28247353202780440756205045 2648189362760666320894223)
          ·
            refine ⟨3972284044140999481341335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648189362760666320894223 3972284044140999481341335)
            ·
              refine ⟨5958426066211499222012003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972284044140999481341335 5958426066211499222012003)
              ·
                refine ⟨8937639099317248833018005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5958426066211499222012003 8937639099317248833018005)
                ·
                  refine ⟨418951832780496039047719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8937639099317248833018005 418951832780496039047719)
                  ·
                    rfl

theorem cell22_3671576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_3671576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671576 prefixEnd_3671576 := by exact prefixLift 3671576
  have htrace : WordTrace (prefixWord ++ tailWord_3671576) baseStart_3671576 baseEnd_3671576 := by
    simpa [prefixWord, tailWord_3671576, baseEnd_3671576] using wordTrace_append hprefix tailTrace_3671576
  have hstable : (prefixWord ++ tailWord_3671576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671576).length < 2 ^ (prefixWord ++ tailWord_3671576).sum := by decide
  have hdescent : baseEnd_3671576 < baseStart_3671576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671582 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3671582 : Nat := 118140960795 + 3671582 * 2 ^ 59
def prefixEnd_3671582 : Nat := 4983230072969 + 3 ^ 40 * 3671582 * 2
def baseEnd_3671582 : Nat := 418952517421368700497713

theorem tailTrace_3671582 : CollatzResearch.WordTrace tailWord_3671582 prefixEnd_3671582 418952517421368700497713 := by
  unfold tailWord_3671582
  simp only [CollatzResearch.WordTrace]
  refine ⟨16739199623061618141026125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89275731322995296752139333 16739199623061618141026125)
  ·
    refine ⟨6277199858648106802884797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16739199623061618141026125 6277199858648106802884797)
    ·
      refine ⟨2353949946993040051081799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6277199858648106802884797 2353949946993040051081799)
      ·
        refine ⟨3530924920489560076622699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353949946993040051081799 3530924920489560076622699)
        ·
          refine ⟨5296387380734340114934049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530924920489560076622699 5296387380734340114934049)
          ·
            refine ⟨3972290535550755086200537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5296387380734340114934049 3972290535550755086200537)
            ·
              refine ⟨2979217901663066314650403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3972290535550755086200537 2979217901663066314650403)
              ·
                refine ⟨4468826852494599471975605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979217901663066314650403 4468826852494599471975605)
                ·
                  refine ⟨418952517421368700497713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4468826852494599471975605 418952517421368700497713)
                  ·
                    rfl

theorem cell22_3671582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3671582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671582 prefixEnd_3671582 := by exact prefixLift 3671582
  have htrace : WordTrace (prefixWord ++ tailWord_3671582) baseStart_3671582 baseEnd_3671582 := by
    simpa [prefixWord, tailWord_3671582, baseEnd_3671582] using wordTrace_append hprefix tailTrace_3671582
  have hstable : (prefixWord ++ tailWord_3671582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671582).length < 2 ^ (prefixWord ++ tailWord_3671582).sum := by decide
  have hdescent : baseEnd_3671582 < baseStart_3671582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671670 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_3671670 : Nat := 118140960795 + 3671670 * 2 ^ 59
def prefixEnd_3671670 : Nat := 4983230072969 + 3 ^ 40 * 3671670 * 2
def baseEnd_3671670 : Nat := 1256887676462503205292869

theorem tailTrace_3671670 : CollatzResearch.WordTrace tailWord_3671670 prefixEnd_3671670 1256887676462503205292869 := by
  unfold tailWord_3671670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8369800413010883509838279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89277871072116090771608309 8369800413010883509838279)
  ·
    refine ⟨12554700619516325264757419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8369800413010883509838279 12554700619516325264757419)
    ·
      refine ⟨18832050929274487897136129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12554700619516325264757419 18832050929274487897136129)
      ·
        refine ⟨14124038196955865922852097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18832050929274487897136129 14124038196955865922852097)
        ·
          refine ⟨10593028647716899442139073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14124038196955865922852097 10593028647716899442139073)
          ·
            refine ⟨7944771485787674581604305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10593028647716899442139073 7944771485787674581604305)
            ·
              refine ⟨5958578614340755936203229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944771485787674581604305 5958578614340755936203229)
              ·
                refine ⟨2234466980377783476076211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5958578614340755936203229 2234466980377783476076211)
                ·
                  refine ⟨3351700470566675214114317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234466980377783476076211 3351700470566675214114317)
                  ·
                    refine ⟨1256887676462503205292869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351700470566675214114317 1256887676462503205292869)
                    ·
                      rfl

theorem cell22_3671670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_3671670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671670 prefixEnd_3671670 := by exact prefixLift 3671670
  have htrace : WordTrace (prefixWord ++ tailWord_3671670) baseStart_3671670 baseEnd_3671670 := by
    simpa [prefixWord, tailWord_3671670, baseEnd_3671670] using wordTrace_append hprefix tailTrace_3671670
  have hstable : (prefixWord ++ tailWord_3671670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671670).length < 2 ^ (prefixWord ++ tailWord_3671670).sum := by decide
  have hdescent : baseEnd_3671670 < baseStart_3671670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671694 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_3671694 : Nat := 118140960795 + 3671694 * 2 ^ 59
def prefixEnd_3671694 : Nat := 4983230072969 + 3 ^ 40 * 3671694 * 2
def baseEnd_3671694 : Nat := 418965297384325047564265

theorem tailTrace_3671694 : CollatzResearch.WordTrace tailWord_3671694 prefixEnd_3671694 418965297384325047564265 := by
  unfold tailWord_3671694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16739710245010898532035767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89278454640058125504190757 16739710245010898532035767)
  ·
    refine ⟨25109565367516347798053651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16739710245010898532035767 25109565367516347798053651)
    ·
      refine ⟨37664348051274521697080477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25109565367516347798053651 37664348051274521697080477)
      ·
        refine ⟨14124130519227945636405179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37664348051274521697080477 14124130519227945636405179)
        ·
          refine ⟨21186195778841918454607769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14124130519227945636405179 21186195778841918454607769)
          ·
            refine ⟨15889646834131438840955827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21186195778841918454607769 15889646834131438840955827)
            ·
              refine ⟨23834470251197158261433741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15889646834131438840955827 23834470251197158261433741)
              ·
                refine ⟨8937926344198934348037653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23834470251197158261433741 8937926344198934348037653)
                ·
                  refine ⟨418965297384325047564265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8937926344198934348037653 418965297384325047564265)
                  ·
                    rfl

theorem cell22_3671694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_3671694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671694 prefixEnd_3671694 := by exact prefixLift 3671694
  have htrace : WordTrace (prefixWord ++ tailWord_3671694) baseStart_3671694 baseEnd_3671694 := by
    simpa [prefixWord, tailWord_3671694, baseEnd_3671694] using wordTrace_append hprefix tailTrace_3671694
  have hstable : (prefixWord ++ tailWord_3671694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671694).length < 2 ^ (prefixWord ++ tailWord_3671694).sum := by decide
  have hdescent : baseEnd_3671694 < baseStart_3671694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671756 : List Nat := [2, 2, 1, 5, 2, 1, 2, 7]
def baseStart_3671756 : Nat := 118140960795 + 3671756 * 2 ^ 59
def prefixEnd_3671756 : Nat := 4983230072969 + 3 ^ 40 * 3671756 * 2
def baseEnd_3671756 : Nat := 139657457335558627515845

theorem tailTrace_3671756 : CollatzResearch.WordTrace tailWord_3671756 prefixEnd_3671756 139657457335558627515845 := by
  unfold tailWord_3671756
  simp only [CollatzResearch.WordTrace]
  refine ⟨66959971642931286422521561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89279962190575048563362081 66959971642931286422521561)
  ·
    refine ⟨50219978732198464816891171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66959971642931286422521561 50219978732198464816891171)
    ·
      refine ⟨75329968098297697225336757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50219978732198464816891171 75329968098297697225336757)
      ·
        refine ⟨7062184509215409114875321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75329968098297697225336757 7062184509215409114875321)
        ·
          refine ⟨5296638381911556836156491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7062184509215409114875321 5296638381911556836156491)
          ·
            refine ⟨7944957572867335254234737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296638381911556836156491 7944957572867335254234737)
            ·
              refine ⟨5958718179650501440676053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944957572867335254234737 5958718179650501440676053)
              ·
                refine ⟨139657457335558627515845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5958718179650501440676053 139657457335558627515845)
                ·
                  rfl

theorem cell22_3671756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_3671756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671756 prefixEnd_3671756 := by exact prefixLift 3671756
  have htrace : WordTrace (prefixWord ++ tailWord_3671756) baseStart_3671756 baseEnd_3671756 := by
    simpa [prefixWord, tailWord_3671756, baseEnd_3671756] using wordTrace_append hprefix tailTrace_3671756
  have hstable : (prefixWord ++ tailWord_3671756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671756).length < 2 ^ (prefixWord ++ tailWord_3671756).sum := by decide
  have hdescent : baseEnd_3671756 < baseStart_3671756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671829 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3671829 : Nat := 118140960795 + 3671829 * 2 ^ 59
def prefixEnd_3671829 : Nat := 4983230072969 + 3 ^ 40 * 3671829 * 2
def baseEnd_3671829 : Nat := 418980701803959930189127

theorem tailTrace_3671829 : CollatzResearch.WordTrace tailWord_3671829 prefixEnd_3671829 418980701803959930189127 := by
  unfold tailWord_3671829
  simp only [CollatzResearch.WordTrace]
  refine ⟨133922605814598106312450541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89281737209732070874967027 133922605814598106312450541)
  ·
    refine ⟨50220977180474289867168953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133922605814598106312450541 50220977180474289867168953)
    ·
      refine ⟨37665732885355717400376715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50220977180474289867168953 37665732885355717400376715)
      ·
        refine ⟨56498599328033576100565073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37665732885355717400376715 56498599328033576100565073)
        ·
          refine ⟨42373949496025182075423805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56498599328033576100565073 42373949496025182075423805)
          ·
            refine ⟨15890231061009443278283927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42373949496025182075423805 15890231061009443278283927)
            ·
              refine ⟨23835346591514164917425891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15890231061009443278283927 23835346591514164917425891)
              ·
                refine ⟨35753019887271247376138837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23835346591514164917425891 35753019887271247376138837)
                ·
                  refine ⟨418980701803959930189127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35753019887271247376138837 418980701803959930189127)
                  ·
                    rfl

theorem cell22_3671829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3671829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671829 prefixEnd_3671829 := by exact prefixLift 3671829
  have htrace : WordTrace (prefixWord ++ tailWord_3671829) baseStart_3671829 baseEnd_3671829 := by
    simpa [prefixWord, tailWord_3671829, baseEnd_3671829] using wordTrace_append hprefix tailTrace_3671829
  have hstable : (prefixWord ++ tailWord_3671829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671829).length < 2 ^ (prefixWord ++ tailWord_3671829).sum := by decide
  have hdescent : baseEnd_3671829 < baseStart_3671829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671831 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 3, 4]
def baseStart_3671831 : Nat := 118140960795 + 3671831 * 2 ^ 59
def prefixEnd_3671831 : Nat := 4983230072969 + 3 ^ 40 * 3671831 * 2
def baseEnd_3671831 : Nat := 1256942790052752452017375

theorem tailTrace_3671831 : CollatzResearch.WordTrace tailWord_3671831 prefixEnd_3671831 1256942790052752452017375 := by
  unfold tailWord_3671831
  simp only [CollatzResearch.WordTrace]
  refine ⟨133922678760590860654023347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89281785840393907102682231 133922678760590860654023347)
  ·
    refine ⟨200884018140886290981035021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133922678760590860654023347 200884018140886290981035021)
    ·
      refine ⟨75331506802832359117888133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200884018140886290981035021 75331506802832359117888133)
      ·
        refine ⟨14124657525531067334604025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75331506802832359117888133 14124657525531067334604025)
        ·
          refine ⟨10593493144148300500953019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14124657525531067334604025 10593493144148300500953019)
          ·
            refine ⟨15890239716222450751429529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10593493144148300500953019 15890239716222450751429529)
            ·
              refine ⟨11917679787166838063572147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15890239716222450751429529 11917679787166838063572147)
              ·
                refine ⟨17876519680750257095358221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11917679787166838063572147 17876519680750257095358221)
                ·
                  refine ⟨6703694880281346410759333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17876519680750257095358221 6703694880281346410759333)
                  ·
                    refine ⟨1256942790052752452017375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703694880281346410759333 1256942790052752452017375)
                    ·
                      rfl

theorem cell22_3671831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_3671831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671831 prefixEnd_3671831 := by exact prefixLift 3671831
  have htrace : WordTrace (prefixWord ++ tailWord_3671831) baseStart_3671831 baseEnd_3671831 := by
    simpa [prefixWord, tailWord_3671831, baseEnd_3671831] using wordTrace_append hprefix tailTrace_3671831
  have hstable : (prefixWord ++ tailWord_3671831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671831).length < 2 ^ (prefixWord ++ tailWord_3671831).sum := by decide
  have hdescent : baseEnd_3671831 < baseStart_3671831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671848 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3671848 : Nat := 118140960795 + 3671848 * 2 ^ 59
def prefixEnd_3671848 : Nat := 4983230072969 + 3 ^ 40 * 3671848 * 2
def baseEnd_3671848 : Nat := 1256948609500170074342323

theorem tailTrace_3671848 : CollatzResearch.WordTrace tailWord_3671848 prefixEnd_3671848 1256948609500170074342323 := by
  unfold tailWord_3671848
  simp only [CollatzResearch.WordTrace]
  refine ⟨66961649400764636278696099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89282199201019515038261465 66961649400764636278696099)
  ·
    refine ⟨100442474101146954418044149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66961649400764636278696099 100442474101146954418044149)
    ·
      refine ⟨9416481946982526976691639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100442474101146954418044149 9416481946982526976691639)
      ·
        refine ⟨14124722920473790465037459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9416481946982526976691639 14124722920473790465037459)
        ·
          refine ⟨21187084380710685697556189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14124722920473790465037459 21187084380710685697556189)
          ·
            refine ⟨7945156642766507136583571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21187084380710685697556189 7945156642766507136583571)
            ·
              refine ⟨11917734964149760704875357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945156642766507136583571 11917734964149760704875357)
              ·
                refine ⟨4469150611556160264328259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11917734964149760704875357 4469150611556160264328259)
                ·
                  refine ⟨6703725917334240396492389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469150611556160264328259 6703725917334240396492389)
                  ·
                    refine ⟨1256948609500170074342323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6703725917334240396492389 1256948609500170074342323)
                    ·
                      rfl

theorem cell22_3671848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3671848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671848 prefixEnd_3671848 := by exact prefixLift 3671848
  have htrace : WordTrace (prefixWord ++ tailWord_3671848) baseStart_3671848 baseEnd_3671848 := by
    simpa [prefixWord, tailWord_3671848, baseEnd_3671848] using wordTrace_append hprefix tailTrace_3671848
  have hstable : (prefixWord ++ tailWord_3671848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671848).length < 2 ^ (prefixWord ++ tailWord_3671848).sum := by decide
  have hdescent : baseEnd_3671848 < baseStart_3671848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671908 : List Nat := [2, 3, 1, 1, 6, 1, 8]
def baseStart_3671908 : Nat := 118140960795 + 3671908 * 2 ^ 59
def prefixEnd_3671908 : Nat := 4983230072969 + 3 ^ 40 * 3671908 * 2
def baseEnd_3671908 : Nat := 46554412915790737697857

theorem tailTrace_3671908 : CollatzResearch.WordTrace tailWord_3671908 prefixEnd_3671908 46554412915790737697857 := by
  unfold tailWord_3671908
  simp only [CollatzResearch.WordTrace]
  refine ⟨66962743590655951402288189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89283658120874601869717585 66962743590655951402288189)
  ·
    refine ⟨25111028846495981775858071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66962743590655951402288189 25111028846495981775858071)
    ·
      refine ⟨37666543269743972663787107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25111028846495981775858071 37666543269743972663787107)
      ·
        refine ⟨56499814904615958995680661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37666543269743972663787107 56499814904615958995680661)
        ·
          refine ⟨2648428823653873077922531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56499814904615958995680661 2648428823653873077922531)
          ·
            refine ⟨3972643235480809616883797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648428823653873077922531 3972643235480809616883797)
            ·
              refine ⟨46554412915790737697857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3972643235480809616883797 46554412915790737697857)
              ·
                rfl

theorem cell22_3671908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 8].length) (baseStart_3671908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671908 prefixEnd_3671908 := by exact prefixLift 3671908
  have htrace : WordTrace (prefixWord ++ tailWord_3671908) baseStart_3671908 baseEnd_3671908 := by
    simpa [prefixWord, tailWord_3671908, baseEnd_3671908] using wordTrace_append hprefix tailTrace_3671908
  have hstable : (prefixWord ++ tailWord_3671908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671908).length < 2 ^ (prefixWord ++ tailWord_3671908).sum := by decide
  have hdescent : baseEnd_3671908 < baseStart_3671908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671936 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_3671936 : Nat := 118140960795 + 3671936 * 2 ^ 59
def prefixEnd_3671936 : Nat := 4983230072969 + 3 ^ 40 * 3671936 * 2
def baseEnd_3671936 : Nat := 418992911232855726047351

theorem tailTrace_3671936 : CollatzResearch.WordTrace tailWord_3671936 prefixEnd_3671936 418992911232855726047351 := by
  unfold tailWord_3671936
  simp only [CollatzResearch.WordTrace]
  refine ⟨66963254212605231793297831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89284338950140309057730441 66963254212605231793297831)
  ·
    refine ⟨100444881318907847689946747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66963254212605231793297831 100444881318907847689946747)
    ·
      refine ⟨150667321978361771534920121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100444881318907847689946747 150667321978361771534920121)
      ·
        refine ⟨113000491483771328651190091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150667321978361771534920121 113000491483771328651190091)
        ·
          refine ⟨169500737225656992976785137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113000491483771328651190091 169500737225656992976785137)
          ·
            refine ⟨127125552919242744732588853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169500737225656992976785137 127125552919242744732588853)
            ·
              refine ⟨11918020586179007318680205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127125552919242744732588853 11918020586179007318680205)
              ·
                refine ⟨4469257719817127744505077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11918020586179007318680205 4469257719817127744505077)
                ·
                  refine ⟨418992911232855726047351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469257719817127744505077 418992911232855726047351)
                  ·
                    rfl

theorem cell22_3671936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_3671936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671936 prefixEnd_3671936 := by exact prefixLift 3671936
  have htrace : WordTrace (prefixWord ++ tailWord_3671936) baseStart_3671936 baseEnd_3671936 := by
    simpa [prefixWord, tailWord_3671936, baseEnd_3671936] using wordTrace_append hprefix tailTrace_3671936
  have hstable : (prefixWord ++ tailWord_3671936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671936).length < 2 ^ (prefixWord ++ tailWord_3671936).sum := by decide
  have hdescent : baseEnd_3671936 < baseStart_3671936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671970 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3671970 : Nat := 118140960795 + 3671970 * 2 ^ 59
def prefixEnd_3671970 : Nat := 4983230072969 + 3 ^ 40 * 3671970 * 2
def baseEnd_3671970 : Nat := 418996790864467474263983

theorem tailTrace_3671970 : CollatzResearch.WordTrace tailWord_3671970 prefixEnd_3671970 418996790864467474263983 := by
  unfold tailWord_3671970
  simp only [CollatzResearch.WordTrace]
  refine ⟨33481937126771821848333341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89285165671391524928888909 33481937126771821848333341)
  ·
    refine ⟨12555726422539433193125003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33481937126771821848333341 12555726422539433193125003)
    ·
      refine ⟨18833589633809149789687505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12555726422539433193125003 18833589633809149789687505)
      ·
        refine ⟨14125192225356862342265629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18833589633809149789687505 14125192225356862342265629)
        ·
          refine ⟨5296947084508823378349611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14125192225356862342265629 5296947084508823378349611)
          ·
            refine ⟨7945420626763235067524417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296947084508823378349611 7945420626763235067524417)
            ·
              refine ⟨5959065470072426300643313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7945420626763235067524417 5959065470072426300643313)
              ·
                refine ⟨4469299102554319725482485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959065470072426300643313 4469299102554319725482485)
                ·
                  refine ⟨418996790864467474263983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469299102554319725482485 418996790864467474263983)
                  ·
                    rfl

theorem cell22_3671970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3671970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671970 prefixEnd_3671970 := by exact prefixLift 3671970
  have htrace : WordTrace (prefixWord ++ tailWord_3671970) baseStart_3671970 baseEnd_3671970 := by
    simpa [prefixWord, tailWord_3671970, baseEnd_3671970] using wordTrace_append hprefix tailTrace_3671970
  have hstable : (prefixWord ++ tailWord_3671970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671970).length < 2 ^ (prefixWord ++ tailWord_3671970).sum := by decide
  have hdescent : baseEnd_3671970 < baseStart_3671970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3671998 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3671998 : Nat := 118140960795 + 3671998 * 2 ^ 59
def prefixEnd_3671998 : Nat := 4983230072969 + 3 ^ 40 * 3671998 * 2
def baseEnd_3671998 : Nat := 418999985855206561030621

theorem tailTrace_3671998 : CollatzResearch.WordTrace tailWord_3671998 prefixEnd_3671998 418999985855206561030621 := by
  unfold tailWord_3671998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16741096218873231021919081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89285846500657232116901765 16741096218873231021919081)
  ·
    refine ⟨12555822164154923266439311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16741096218873231021919081 12555822164154923266439311)
    ·
      refine ⟨18833733246232384899658967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12555822164154923266439311 18833733246232384899658967)
      ·
        refine ⟨28250599869348577349488451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18833733246232384899658967 28250599869348577349488451)
        ·
          refine ⟨42375899804022866024232677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28250599869348577349488451 42375899804022866024232677)
          ·
            refine ⟨7945481213254287379543627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42375899804022866024232677 7945481213254287379543627)
            ·
              refine ⟨11918221819881431069315441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945481213254287379543627 11918221819881431069315441)
              ·
                refine ⟨8938666364911073301986581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11918221819881431069315441 8938666364911073301986581)
                ·
                  refine ⟨418999985855206561030621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8938666364911073301986581 418999985855206561030621)
                  ·
                    rfl

theorem cell22_3671998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3671998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3671998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3671998 prefixEnd_3671998 := by exact prefixLift 3671998
  have htrace : WordTrace (prefixWord ++ tailWord_3671998) baseStart_3671998 baseEnd_3671998 := by
    simpa [prefixWord, tailWord_3671998, baseEnd_3671998] using wordTrace_append hprefix tailTrace_3671998
  have hstable : (prefixWord ++ tailWord_3671998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3671998).length < 2 ^ (prefixWord ++ tailWord_3671998).sum := by decide
  have hdescent : baseEnd_3671998 < baseStart_3671998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3671998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672011 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 1, 6]
def baseStart_3672011 : Nat := 118140960795 + 3672011 * 2 ^ 59
def prefixEnd_3672011 : Nat := 4983230072969 + 3 ^ 40 * 3672011 * 2
def baseEnd_3672011 : Nat := 1257004407731291982516823

theorem tailTrace_3672011 : CollatzResearch.WordTrace tailWord_3672011 prefixEnd_3672011 1257004407731291982516823 := by
  unfold tailWord_3672011
  simp only [CollatzResearch.WordTrace]
  refine ⟨133929243899938751395575887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89286162599959167597050591 133929243899938751395575887)
  ·
    refine ⟨200893865849908127093363831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133929243899938751395575887 200893865849908127093363831)
    ·
      refine ⟨301340798774862190640045747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200893865849908127093363831 301340798774862190640045747)
      ·
        refine ⟨452011198162293285960068621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301340798774862190640045747 452011198162293285960068621)
        ·
          refine ⟨169504199310859982235025733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452011198162293285960068621 169504199310859982235025733)
          ·
            refine ⟨31782037370786246669067325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169504199310859982235025733 31782037370786246669067325)
            ·
              refine ⟨11918264014044842500900247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31782037370786246669067325 11918264014044842500900247)
              ·
                refine ⟨17877396021067263751350371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11918264014044842500900247 17877396021067263751350371)
                ·
                  refine ⟨26816094031600895627025557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17877396021067263751350371 26816094031600895627025557)
                  ·
                    refine ⟨1257004407731291982516823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26816094031600895627025557 1257004407731291982516823)
                    ·
                      rfl

theorem cell22_3672011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_3672011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672011 prefixEnd_3672011 := by exact prefixLift 3672011
  have htrace : WordTrace (prefixWord ++ tailWord_3672011) baseStart_3672011 baseEnd_3672011 := by
    simpa [prefixWord, tailWord_3672011, baseEnd_3672011] using wordTrace_append hprefix tailTrace_3672011
  have hstable : (prefixWord ++ tailWord_3672011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672011).length < 2 ^ (prefixWord ++ tailWord_3672011).sum := by decide
  have hdescent : baseEnd_3672011 < baseStart_3672011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672056 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_3672056 : Nat := 118140960795 + 3672056 * 2 ^ 59
def prefixEnd_3672056 : Nat := 4983230072969 + 3 ^ 40 * 3672056 * 2
def baseEnd_3672056 : Nat := 1257019812150926865141685

theorem tailTrace_3672056 : CollatzResearch.WordTrace tailWord_3672056 prefixEnd_3672056 1257019812150926865141685 := by
  unfold tailWord_3672056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66965442592387862040482011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89287256789850482720642681 66965442592387862040482011)
  ·
    refine ⟨100448163888581793060723017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66965442592387862040482011 100448163888581793060723017)
    ·
      refine ⟨75336122916436344795542263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100448163888581793060723017 75336122916436344795542263)
      ·
        refine ⟨113004184374654517193313395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75336122916436344795542263 113004184374654517193313395)
        ·
          refine ⟨169506276561981775789970093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113004184374654517193313395 169506276561981775789970093)
          ·
            refine ⟨63564853710743165921238785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169506276561981775789970093 63564853710743165921238785)
            ·
              refine ⟨47673640283057374440929089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63564853710743165921238785 47673640283057374440929089)
              ·
                refine ⟨35755230212293030830696817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47673640283057374440929089 35755230212293030830696817)
                ·
                  refine ⟨26816422659219773123022613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35755230212293030830696817 26816422659219773123022613)
                  ·
                    refine ⟨1257019812150926865141685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26816422659219773123022613 1257019812150926865141685)
                    ·
                      rfl

theorem cell22_3672056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_3672056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672056 prefixEnd_3672056 := by exact prefixLift 3672056
  have htrace : WordTrace (prefixWord ++ tailWord_3672056) baseStart_3672056 baseEnd_3672056 := by
    simpa [prefixWord, tailWord_3672056, baseEnd_3672056] using wordTrace_append hprefix tailTrace_3672056
  have hstable : (prefixWord ++ tailWord_3672056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672056).length < 2 ^ (prefixWord ++ tailWord_3672056).sum := by decide
  have hdescent : baseEnd_3672056 < baseStart_3672056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672088 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_3672088 : Nat := 118140960795 + 3672088 * 2 ^ 59
def prefixEnd_3672088 : Nat := 4983230072969 + 3 ^ 40 * 3672088 * 2
def baseEnd_3672088 : Nat := 419010255468296482780529

theorem tailTrace_3672088 : CollatzResearch.WordTrace tailWord_3672088 prefixEnd_3672088 419010255468296482780529 := by
  unfold tailWord_3672088
  simp only [CollatzResearch.WordTrace]
  refine ⟨66966026160329896773064459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89288034880439862364085945 66966026160329896773064459)
  ·
    refine ⟨100449039240494845159596689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66966026160329896773064459 100449039240494845159596689)
    ·
      refine ⟨75336779430371133869697517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100449039240494845159596689 75336779430371133869697517)
      ·
        refine ⟨28251292286389175201136569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75336779430371133869697517 28251292286389175201136569)
        ·
          refine ⟨21188469214791881400852427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28251292286389175201136569 21188469214791881400852427)
          ·
            refine ⟨31782703822187822101278641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21188469214791881400852427 31782703822187822101278641)
            ·
              refine ⟨23837027866640866575958981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31782703822187822101278641 23837027866640866575958981)
              ·
                refine ⟨4469442724995162482992309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23837027866640866575958981 4469442724995162482992309)
                ·
                  refine ⟨419010255468296482780529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469442724995162482992309 419010255468296482780529)
                  ·
                    rfl

theorem cell22_3672088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_3672088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672088 prefixEnd_3672088 := by exact prefixLift 3672088
  have htrace : WordTrace (prefixWord ++ tailWord_3672088) baseStart_3672088 baseEnd_3672088 := by
    simpa [prefixWord, tailWord_3672088, baseEnd_3672088] using wordTrace_append hprefix tailTrace_3672088
  have hstable : (prefixWord ++ tailWord_3672088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672088).length < 2 ^ (prefixWord ++ tailWord_3672088).sum := by decide
  have hdescent : baseEnd_3672088 < baseStart_3672088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672092 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_3672092 : Nat := 118140960795 + 3672092 * 2 ^ 59
def prefixEnd_3672092 : Nat := 4983230072969 + 3 ^ 40 * 3672092 * 2
def baseEnd_3672092 : Nat := 1257032135686634771241575

theorem tailTrace_3672092 : CollatzResearch.WordTrace tailWord_3672092 prefixEnd_3672092 1257032135686634771241575 := by
  unfold tailWord_3672092
  simp only [CollatzResearch.WordTrace]
  refine ⟨66966099106322651114637265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89288132141763534819516353 66966099106322651114637265)
  ·
    refine ⟨50224574329741988335977949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66966099106322651114637265 50224574329741988335977949)
    ·
      refine ⟨18834215373653245625991731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50224574329741988335977949 18834215373653245625991731)
      ·
        refine ⟨28251323060479868438987597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18834215373653245625991731 28251323060479868438987597)
        ·
          refine ⟨10594246147679950664620349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28251323060479868438987597 10594246147679950664620349)
          ·
            refine ⟨3972842305379981499232631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10594246147679950664620349 3972842305379981499232631)
            ·
              refine ⟨5959263458069972248848947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972842305379981499232631 5959263458069972248848947)
              ·
                refine ⟨8938895187104958373273421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959263458069972248848947 8938895187104958373273421)
                ·
                  refine ⟨3352085695164359389977533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8938895187104958373273421 3352085695164359389977533)
                  ·
                    refine ⟨1257032135686634771241575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3352085695164359389977533 1257032135686634771241575)
                    ·
                      rfl

theorem cell22_3672092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_3672092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672092 prefixEnd_3672092 := by exact prefixLift 3672092
  have htrace : WordTrace (prefixWord ++ tailWord_3672092) baseStart_3672092 baseEnd_3672092 := by
    simpa [prefixWord, tailWord_3672092, baseEnd_3672092] using wordTrace_append hprefix tailTrace_3672092
  have hstable : (prefixWord ++ tailWord_3672092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672092).length < 2 ^ (prefixWord ++ tailWord_3672092).sum := by decide
  have hdescent : baseEnd_3672092 < baseStart_3672092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672148 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3672148 : Nat := 118140960795 + 3672148 * 2 ^ 59
def prefixEnd_3672148 : Nat := 4983230072969 + 3 ^ 40 * 3672148 * 2
def baseEnd_3672148 : Nat := 1257051305631069291841403

theorem tailTrace_3672148 : CollatzResearch.WordTrace tailWord_3672148 prefixEnd_3672148 1257051305631069291841403 := by
  unfold tailWord_3672148
  simp only [CollatzResearch.WordTrace]
  refine ⟨66967120350221211896656549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89289493800294949195542065 66967120350221211896656549)
  ·
    refine ⟨12556335065666477230623103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66967120350221211896656549 12556335065666477230623103)
    ·
      refine ⟨18834502598499715845934655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12556335065666477230623103 18834502598499715845934655)
      ·
        refine ⟨28251753897749573768901983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18834502598499715845934655 28251753897749573768901983)
        ·
          refine ⟨42377630846624360653352975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28251753897749573768901983 42377630846624360653352975)
          ·
            refine ⟨63566446269936540980029463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42377630846624360653352975 63566446269936540980029463)
            ·
              refine ⟨95349669404904811470044195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63566446269936540980029463 95349669404904811470044195)
              ·
                refine ⟨143024504107357217205066293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95349669404904811470044195 143024504107357217205066293)
                ·
                  refine ⟨13408547260064739112974965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143024504107357217205066293 13408547260064739112974965)
                  ·
                    refine ⟨1257051305631069291841403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13408547260064739112974965 1257051305631069291841403)
                    ·
                      rfl

theorem cell22_3672148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3672148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672148 prefixEnd_3672148 := by exact prefixLift 3672148
  have htrace : WordTrace (prefixWord ++ tailWord_3672148) baseStart_3672148 baseEnd_3672148 := by
    simpa [prefixWord, tailWord_3672148, baseEnd_3672148] using wordTrace_append hprefix tailTrace_3672148
  have hstable : (prefixWord ++ tailWord_3672148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672148).length < 2 ^ (prefixWord ++ tailWord_3672148).sum := by decide
  have hdescent : baseEnd_3672148 < baseStart_3672148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672163 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 4, 4]
def baseStart_3672163 : Nat := 118140960795 + 3672163 * 2 ^ 59
def prefixEnd_3672163 : Nat := 4983230072969 + 3 ^ 40 * 3672163 * 2
def baseEnd_3672163 : Nat := 1257056440437614252716357

theorem tailTrace_3672163 : CollatzResearch.WordTrace tailWord_3672163 prefixEnd_3672163 1257056440437614252716357 := by
  unfold tailWord_3672163
  simp only [CollatzResearch.WordTrace]
  refine ⟨133934787795388081355109143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89289858530258720903406095 133934787795388081355109143)
  ·
    refine ⟨200902181693082122032663715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133934787795388081355109143 200902181693082122032663715)
    ·
      refine ⟨301353272539623183048995573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200902181693082122032663715 301353272539623183048995573)
      ·
        refine ⟨28251869300589673410843335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301353272539623183048995573 28251869300589673410843335)
        ·
          refine ⟨42377803950884510116265003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28251869300589673410843335 42377803950884510116265003)
          ·
            refine ⟨63566705926326765174397505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42377803950884510116265003 63566705926326765174397505)
            ·
              refine ⟨47675029444745073880798129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63566705926326765174397505 47675029444745073880798129)
              ·
                refine ⟨35756272083558805410598597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47675029444745073880798129 35756272083558805410598597)
                ·
                  refine ⟨6704301015667276014487237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35756272083558805410598597 6704301015667276014487237)
                  ·
                    refine ⟨1257056440437614252716357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6704301015667276014487237 1257056440437614252716357)
                    ·
                      rfl

theorem cell22_3672163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_3672163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672163 prefixEnd_3672163 := by exact prefixLift 3672163
  have htrace : WordTrace (prefixWord ++ tailWord_3672163) baseStart_3672163 baseEnd_3672163 := by
    simpa [prefixWord, tailWord_3672163, baseEnd_3672163] using wordTrace_append hprefix tailTrace_3672163
  have hstable : (prefixWord ++ tailWord_3672163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672163).length < 2 ^ (prefixWord ++ tailWord_3672163).sum := by decide
  have hdescent : baseEnd_3672163 < baseStart_3672163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672165 : List Nat := [1, 3, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3672165 : Nat := 118140960795 + 3672165 * 2 ^ 59
def prefixEnd_3672165 : Nat := 4983230072969 + 3 ^ 40 * 3672165 * 2
def baseEnd_3672165 : Nat := 1257057125078486914166351

theorem tailTrace_3672165 : CollatzResearch.WordTrace tailWord_3672165 prefixEnd_3672165 1257057125078486914166351 := by
  unfold tailWord_3672165
  simp only [CollatzResearch.WordTrace]
  refine ⟨133934860741380835696681949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89289907160920557131121299 133934860741380835696681949)
  ·
    refine ⟨50225572778017813386255731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133934860741380835696681949 50225572778017813386255731)
    ·
      refine ⟨75338359167026720079383597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50225572778017813386255731 75338359167026720079383597)
      ·
        refine ⟨28251884687635020029768849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75338359167026720079383597 28251884687635020029768849)
        ·
          refine ⟨21188913515726265022326637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28251884687635020029768849 21188913515726265022326637)
          ·
            refine ⟨7945842568397349383372489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21188913515726265022326637 7945842568397349383372489)
            ·
              refine ⟨5959381926298012037529367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7945842568397349383372489 5959381926298012037529367)
              ·
                refine ⟨8939072889447018056294051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959381926298012037529367 8939072889447018056294051)
                ·
                  refine ⟨13408609334170527084441077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939072889447018056294051 13408609334170527084441077)
                  ·
                    refine ⟨1257057125078486914166351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13408609334170527084441077 1257057125078486914166351)
                    ·
                      rfl

theorem cell22_3672165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3672165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672165 prefixEnd_3672165 := by exact prefixLift 3672165
  have htrace : WordTrace (prefixWord ++ tailWord_3672165) baseStart_3672165 baseEnd_3672165 := by
    simpa [prefixWord, tailWord_3672165, baseEnd_3672165] using wordTrace_append hprefix tailTrace_3672165
  have hstable : (prefixWord ++ tailWord_3672165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672165).length < 2 ^ (prefixWord ++ tailWord_3672165).sum := by decide
  have hdescent : baseEnd_3672165 < baseStart_3672165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672274 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_3672274 : Nat := 118140960795 + 3672274 * 2 ^ 59
def prefixEnd_3672274 : Nat := 4983230072969 + 3 ^ 40 * 3672274 * 2
def baseEnd_3672274 : Nat := 419031479335348987730339

theorem tailTrace_3672274 : CollatzResearch.WordTrace tailWord_3672274 prefixEnd_3672274 419031479335348987730339 := by
  unfold tailWord_3672274
  simp only [CollatzResearch.WordTrace]
  refine ⟨33484709074496486828099969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89292557531990631541599917 33484709074496486828099969)
  ·
    refine ⟨25113531805872365121074977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33484709074496486828099969 25113531805872365121074977)
    ·
      refine ⟨18835148854404273840806233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25113531805872365121074977 18835148854404273840806233)
      ·
        refine ⟨14126361640803205380604675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18835148854404273840806233 14126361640803205380604675)
        ·
          refine ⟨21189542461204808070907013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126361640803205380604675 21189542461204808070907013)
          ·
            refine ⟨3973039211475901513295065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21189542461204808070907013 3973039211475901513295065)
            ·
              refine ⟨2979779408606926134971299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3973039211475901513295065 2979779408606926134971299)
              ·
                refine ⟨4469669112910389202456949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979779408606926134971299 4469669112910389202456949)
                ·
                  refine ⟨419031479335348987730339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4469669112910389202456949 419031479335348987730339)
                  ·
                    rfl

theorem cell22_3672274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_3672274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672274 prefixEnd_3672274 := by exact prefixLift 3672274
  have htrace : WordTrace (prefixWord ++ tailWord_3672274) baseStart_3672274 baseEnd_3672274 := by
    simpa [prefixWord, tailWord_3672274, baseEnd_3672274] using wordTrace_append hprefix tailTrace_3672274
  have hstable : (prefixWord ++ tailWord_3672274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672274).length < 2 ^ (prefixWord ++ tailWord_3672274).sum := by decide
  have hdescent : baseEnd_3672274 < baseStart_3672274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672300 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_3672300 : Nat := 118140960795 + 3672300 * 2 ^ 59
def prefixEnd_3672300 : Nat := 4983230072969 + 3 ^ 40 * 3672300 * 2
def baseEnd_3672300 : Nat := 1257103338337391562040937

theorem tailTrace_3672300 : CollatzResearch.WordTrace tailWord_3672300 prefixEnd_3672300 1257103338337391562040937 := by
  unfold tailWord_3672300
  simp only [CollatzResearch.WordTrace]
  refine ⟨66969892297945876876423177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89293189730594502501897569 66969892297945876876423177)
  ·
    refine ⟨50227419223459407657317383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66969892297945876876423177 50227419223459407657317383)
    ·
      refine ⟨75341128835189111485976075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50227419223459407657317383 75341128835189111485976075)
      ·
        refine ⟨113011693252783667228964113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75341128835189111485976075 113011693252783667228964113)
        ·
          refine ⟨84758769939587750421723085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113011693252783667228964113 84758769939587750421723085)
          ·
            refine ⟨31784538727345406408146157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84758769939587750421723085 31784538727345406408146157)
            ·
              refine ⟨11919202022754527403054809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31784538727345406408146157 11919202022754527403054809)
              ·
                refine ⟨8939401517065895552291107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11919202022754527403054809 8939401517065895552291107)
                ·
                  refine ⟨13409102275598843328436661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939401517065895552291107 13409102275598843328436661)
                  ·
                    refine ⟨1257103338337391562040937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13409102275598843328436661 1257103338337391562040937)
                    ·
                      rfl

theorem cell22_3672300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_3672300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672300 prefixEnd_3672300 := by exact prefixLift 3672300
  have htrace : WordTrace (prefixWord ++ tailWord_3672300) baseStart_3672300 baseEnd_3672300 := by
    simpa [prefixWord, tailWord_3672300, baseEnd_3672300] using wordTrace_append hprefix tailTrace_3672300
  have hstable : (prefixWord ++ tailWord_3672300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672300).length < 2 ^ (prefixWord ++ tailWord_3672300).sum := by decide
  have hdescent : baseEnd_3672300 < baseStart_3672300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672302 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_3672302 : Nat := 118140960795 + 3672302 * 2 ^ 59
def prefixEnd_3672302 : Nat := 4983230072969 + 3 ^ 40 * 3672302 * 2
def baseEnd_3672302 : Nat := 419034674326088074496977

theorem tailTrace_3672302 : CollatzResearch.WordTrace tailWord_3672302 prefixEnd_3672302 419034674326088074496977 := by
  unfold tailWord_3672302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742482192735563511802395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89293238361256338729612773 16742482192735563511802395)
  ·
    refine ⟨25113723289103345267703593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16742482192735563511802395 25113723289103345267703593)
    ·
      refine ⟨18835292466827508950777695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25113723289103345267703593 18835292466827508950777695)
      ·
        refine ⟨28252938700241263426166543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18835292466827508950777695 28252938700241263426166543)
        ·
          refine ⟨42379408050361895139249815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28252938700241263426166543 42379408050361895139249815)
          ·
            refine ⟨63569112075542842708874723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42379408050361895139249815 63569112075542842708874723)
            ·
              refine ⟨95353668113314264063312085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63569112075542842708874723 95353668113314264063312085)
              ·
                refine ⟨2234851596405803063983877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95353668113314264063312085 2234851596405803063983877)
                ·
                  refine ⟨419034674326088074496977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234851596405803063983877 419034674326088074496977)
                  ·
                    rfl

theorem cell22_3672302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_3672302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672302 prefixEnd_3672302 := by exact prefixLift 3672302
  have htrace : WordTrace (prefixWord ++ tailWord_3672302) baseStart_3672302 baseEnd_3672302 := by
    simpa [prefixWord, tailWord_3672302, baseEnd_3672302] using wordTrace_append hprefix tailTrace_3672302
  have hstable : (prefixWord ++ tailWord_3672302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672302).length < 2 ^ (prefixWord ++ tailWord_3672302).sum := by decide
  have hdescent : baseEnd_3672302 < baseStart_3672302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672330 : List Nat := [3, 1, 2, 2, 1, 1, 5, 7]
def baseStart_3672330 : Nat := 118140960795 + 3672330 * 2 ^ 59
def prefixEnd_3672330 : Nat := 4983230072969 + 3 ^ 40 * 3672330 * 2
def baseEnd_3672330 : Nat := 139679289772275720421205

theorem tailTrace_3672330 : CollatzResearch.WordTrace tailWord_3672330 prefixEnd_3672330 139679289772275720421205 := by
  unfold tailWord_3672330
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485219696445767219109611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89293919190522045917625629 33485219696445767219109611)
  ·
    refine ⟨50227829544668650828664417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33485219696445767219109611 50227829544668650828664417)
    ·
      refine ⟨37670872158501488121498313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50227829544668650828664417 37670872158501488121498313)
      ·
        refine ⟨28253154118876116091123735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37670872158501488121498313 28253154118876116091123735)
        ·
          refine ⟨42379731178314174136685603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28253154118876116091123735 42379731178314174136685603)
          ·
            refine ⟨63569596767471261205028405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42379731178314174136685603 63569596767471261205028405)
            ·
              refine ⟨5959649696950430737971413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63569596767471261205028405 5959649696950430737971413)
              ·
                refine ⟨139679289772275720421205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5959649696950430737971413 139679289772275720421205)
                ·
                  rfl

theorem cell22_3672330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_3672330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672330 prefixEnd_3672330 := by exact prefixLift 3672330
  have htrace : WordTrace (prefixWord ++ tailWord_3672330) baseStart_3672330 baseEnd_3672330 := by
    simpa [prefixWord, tailWord_3672330, baseEnd_3672330] using wordTrace_append hprefix tailTrace_3672330
  have hstable : (prefixWord ++ tailWord_3672330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672330).length < 2 ^ (prefixWord ++ tailWord_3672330).sum := by decide
  have hdescent : baseEnd_3672330 < baseStart_3672330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672435 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_3672435 : Nat := 118140960795 + 3672435 * 2 ^ 59
def prefixEnd_3672435 : Nat := 4983230072969 + 3 ^ 40 * 3672435 * 2
def baseEnd_3672435 : Nat := 1257149551596296209915523

theorem tailTrace_3672435 : CollatzResearch.WordTrace tailWord_3672435 prefixEnd_3672435 1257149551596296209915523 := by
  unfold tailWord_3672435
  simp only [CollatzResearch.WordTrace]
  refine ⟨133944708450402671809010759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89296472300268447872673839 133944708450402671809010759)
  ·
    refine ⟨200917062675604007713516139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133944708450402671809010759 200917062675604007713516139)
    ·
      refine ⟨301375594013406011570274209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200917062675604007713516139 301375594013406011570274209)
      ·
        refine ⟨226031695510054508677705657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301375594013406011570274209 226031695510054508677705657)
        ·
          refine ⟨169523771632540881508279243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226031695510054508677705657 169523771632540881508279243)
          ·
            refine ⟨254285657448811322262418865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169523771632540881508279243 254285657448811322262418865)
            ·
              refine ⟨190714243086608491696814149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254285657448811322262418865 190714243086608491696814149)
              ·
                refine ⟨35758920578739092193152653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190714243086608491696814149 35758920578739092193152653)
                ·
                  refine ⟨13409595217027159572432245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35758920578739092193152653 13409595217027159572432245)
                  ·
                    refine ⟨1257149551596296209915523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13409595217027159572432245 1257149551596296209915523)
                    ·
                      rfl

theorem cell22_3672435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_3672435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672435 prefixEnd_3672435 := by exact prefixLift 3672435
  have htrace : WordTrace (prefixWord ++ tailWord_3672435) baseStart_3672435 baseEnd_3672435 := by
    simpa [prefixWord, tailWord_3672435, baseEnd_3672435] using wordTrace_append hprefix tailTrace_3672435
  have hstable : (prefixWord ++ tailWord_3672435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672435).length < 2 ^ (prefixWord ++ tailWord_3672435).sum := by decide
  have hdescent : baseEnd_3672435 < baseStart_3672435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672452 : List Nat := [2, 3, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3672452 : Nat := 118140960795 + 3672452 * 2 ^ 59
def prefixEnd_3672452 : Nat := 4983230072969 + 3 ^ 40 * 3672452 * 2
def baseEnd_3672452 : Nat := 1257155371043713832240471

theorem tailTrace_3672452 : CollatzResearch.WordTrace tailWord_3672452 prefixEnd_3672452 1257155371043713832240471 := by
  unfold tailWord_3672452
  simp only [CollatzResearch.WordTrace]
  refine ⟨66972664245670541856189805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89296885660894055808253073 66972664245670541856189805)
  ·
    refine ⟨25114749092126453196071177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66972664245670541856189805 25114749092126453196071177)
    ·
      refine ⟨18836061819094839897053383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25114749092126453196071177 18836061819094839897053383)
      ·
        refine ⟨28254092728642259845580075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18836061819094839897053383 28254092728642259845580075)
        ·
          refine ⟨42381139092963389768370113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28254092728642259845580075 42381139092963389768370113)
          ·
            refine ⟨31785854319722542326277585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42381139092963389768370113 31785854319722542326277585)
            ·
              refine ⟨23839390739791906744708189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31785854319722542326277585 23839390739791906744708189)
              ·
                refine ⟨8939771527421965029265571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23839390739791906744708189 8939771527421965029265571)
                ·
                  refine ⟨13409657291132947543898357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939771527421965029265571 13409657291132947543898357)
                  ·
                    refine ⟨1257155371043713832240471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13409657291132947543898357 1257155371043713832240471)
                    ·
                      rfl

theorem cell22_3672452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3672452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672452 prefixEnd_3672452 := by exact prefixLift 3672452
  have htrace : WordTrace (prefixWord ++ tailWord_3672452) baseStart_3672452 baseEnd_3672452 := by
    simpa [prefixWord, tailWord_3672452, baseEnd_3672452] using wordTrace_append hprefix tailTrace_3672452
  have hstable : (prefixWord ++ tailWord_3672452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672452).length < 2 ^ (prefixWord ++ tailWord_3672452).sum := by decide
  have hdescent : baseEnd_3672452 < baseStart_3672452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672488 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 4]
def baseStart_3672488 : Nat := 118140960795 + 3672488 * 2 ^ 59
def prefixEnd_3672488 : Nat := 4983230072969 + 3 ^ 40 * 3672488 * 2
def baseEnd_3672488 : Nat := 419055898193140579446787

theorem tailTrace_3672488 : CollatzResearch.WordTrace tailWord_3672488 prefixEnd_3672488 419055898193140579446787 := by
  unfold tailWord_3672488
  simp only [CollatzResearch.WordTrace]
  refine ⟨66973320759605330930345059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89297761012807107907126745 66973320759605330930345059)
  ·
    refine ⟨100459981139407996395517589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66973320759605330930345059 100459981139407996395517589)
    ·
      refine ⟨4709061615909749831039887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100459981139407996395517589 4709061615909749831039887)
      ·
        refine ⟨7063592423864624746559831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709061615909749831039887 7063592423864624746559831)
        ·
          refine ⟨10595388635796937119839747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063592423864624746559831 10595388635796937119839747)
          ·
            refine ⟨15893082953695405679759621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10595388635796937119839747 15893082953695405679759621)
            ·
              refine ⟨2979953053817888564954929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15893082953695405679759621 2979953053817888564954929)
              ·
                refine ⟨2234964790363416423716197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979953053817888564954929 2234964790363416423716197)
                ·
                  refine ⟨419055898193140579446787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2234964790363416423716197 419055898193140579446787)
                  ·
                    rfl

theorem cell22_3672488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_3672488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672488 prefixEnd_3672488 := by exact prefixLift 3672488
  have htrace : WordTrace (prefixWord ++ tailWord_3672488) baseStart_3672488 baseEnd_3672488 := by
    simpa [prefixWord, tailWord_3672488, baseEnd_3672488] using wordTrace_append hprefix tailTrace_3672488
  have hstable : (prefixWord ++ tailWord_3672488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672488).length < 2 ^ (prefixWord ++ tailWord_3672488).sum := by decide
  have hdescent : baseEnd_3672488 < baseStart_3672488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672516 : List Nat := [2, 3, 3, 2, 2, 1, 3, 6]
def baseStart_3672516 : Nat := 118140960795 + 3672516 * 2 ^ 59
def prefixEnd_3672516 : Nat := 4983230072969 + 3 ^ 40 * 3672516 * 2
def baseEnd_3672516 : Nat := 139686364394626555404475

theorem tailTrace_3672516 : CollatzResearch.WordTrace tailWord_3672516 prefixEnd_3672516 139686364394626555404475 := by
  unfold tailWord_3672516
  simp only [CollatzResearch.WordTrace]
  refine ⟨66973831381554611321354701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89298441842072815095139601 66973831381554611321354701)
  ·
    refine ⟨25115186768082979245508013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66973831381554611321354701 25115186768082979245508013)
    ·
      refine ⟨9418195038031117217065505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25115186768082979245508013 9418195038031117217065505)
      ·
        refine ⟨7063646278523337912799129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9418195038031117217065505 7063646278523337912799129)
        ·
          refine ⟨5297734708892503434599347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7063646278523337912799129 5297734708892503434599347)
          ·
            refine ⟨7946602063338755151899021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297734708892503434599347 7946602063338755151899021)
            ·
              refine ⟨2979975773752033181962133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7946602063338755151899021 2979975773752033181962133)
              ·
                refine ⟨139686364394626555404475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2979975773752033181962133 139686364394626555404475)
                ·
                  rfl

theorem cell22_3672516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 6].length) (baseStart_3672516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672516 prefixEnd_3672516 := by exact prefixLift 3672516
  have htrace : WordTrace (prefixWord ++ tailWord_3672516) baseStart_3672516 baseEnd_3672516 := by
    simpa [prefixWord, tailWord_3672516, baseEnd_3672516] using wordTrace_append hprefix tailTrace_3672516
  have hstable : (prefixWord ++ tailWord_3672516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672516).length < 2 ^ (prefixWord ++ tailWord_3672516).sum := by decide
  have hdescent : baseEnd_3672516 < baseStart_3672516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672636 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_3672636 : Nat := 118140960795 + 3672636 * 2 ^ 59
def prefixEnd_3672636 : Nat := 4983230072969 + 3 ^ 40 * 3672636 * 2
def baseEnd_3672636 : Nat := 1257218358003998685639907

theorem tailTrace_3672636 : CollatzResearch.WordTrace tailWord_3672636 prefixEnd_3672636 1257218358003998685639907 := by
  unfold tailWord_3672636
  simp only [CollatzResearch.WordTrace]
  refine ⟨66976019761337241568538881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89301359681782988758051841 66976019761337241568538881)
  ·
    refine ⟨50232014821002931176404161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66976019761337241568538881 50232014821002931176404161)
    ·
      refine ⟨37674011115752198382303121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50232014821002931176404161 37674011115752198382303121)
      ·
        refine ⟨28255508336814148786727341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37674011115752198382303121 28255508336814148786727341)
        ·
          refine ⟨10595815626305305795022753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28255508336814148786727341 10595815626305305795022753)
          ·
            refine ⟨7946861719728979346267065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595815626305305795022753 7946861719728979346267065)
            ·
              refine ⟨5960146289796734509700299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946861719728979346267065 5960146289796734509700299)
              ·
                refine ⟨8940219434695101764550449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960146289796734509700299 8940219434695101764550449)
                ·
                  refine ⟨6705164576021326323412837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8940219434695101764550449 6705164576021326323412837)
                  ·
                    refine ⟨1257218358003998685639907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6705164576021326323412837 1257218358003998685639907)
                    ·
                      rfl

theorem cell22_3672636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_3672636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672636 prefixEnd_3672636 := by exact prefixLift 3672636
  have htrace : WordTrace (prefixWord ++ tailWord_3672636) baseStart_3672636 baseEnd_3672636 := by
    simpa [prefixWord, tailWord_3672636, baseEnd_3672636] using wordTrace_append hprefix tailTrace_3672636
  have hstable : (prefixWord ++ tailWord_3672636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672636).length < 2 ^ (prefixWord ++ tailWord_3672636).sum := by decide
  have hdescent : baseEnd_3672636 < baseStart_3672636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672638 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3672638 : Nat := 118140960795 + 3672638 * 2 ^ 59
def prefixEnd_3672638 : Nat := 4983230072969 + 3 ^ 40 * 3672638 * 2
def baseEnd_3672638 : Nat := 1257219042644871347089901

theorem tailTrace_3672638 : CollatzResearch.WordTrace tailWord_3672638 prefixEnd_3672638 1257219042644871347089901 := by
  unfold tailWord_3672638
  simp only [CollatzResearch.WordTrace]
  refine ⟨16744014058583404684831321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89301408312444824985767045 16744014058583404684831321)
  ·
    refine ⟨12558010543937553513623491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16744014058583404684831321 12558010543937553513623491)
    ·
      refine ⟨18837015815906330270435237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12558010543937553513623491 18837015815906330270435237)
      ·
        refine ⟨3531940465482436925706607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18837015815906330270435237 3531940465482436925706607)
        ·
          refine ⟨5297910698223655388559911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531940465482436925706607 5297910698223655388559911)
          ·
            refine ⟨7946866047335483082839867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297910698223655388559911 7946866047335483082839867)
            ·
              refine ⟨11920299071003224624259801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946866047335483082839867 11920299071003224624259801)
              ·
                refine ⟨8940224303252418468194851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11920299071003224624259801 8940224303252418468194851)
                ·
                  refine ⟨13410336454878627702292277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940224303252418468194851 13410336454878627702292277)
                  ·
                    refine ⟨1257219042644871347089901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13410336454878627702292277 1257219042644871347089901)
                    ·
                      rfl

theorem cell22_3672638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3672638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672638 prefixEnd_3672638 := by exact prefixLift 3672638
  have htrace : WordTrace (prefixWord ++ tailWord_3672638) baseStart_3672638 baseEnd_3672638 := by
    simpa [prefixWord, tailWord_3672638, baseEnd_3672638] using wordTrace_append hprefix tailTrace_3672638
  have hstable : (prefixWord ++ tailWord_3672638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672638).length < 2 ^ (prefixWord ++ tailWord_3672638).sum := by decide
  have hdescent : baseEnd_3672638 < baseStart_3672638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672668 : List Nat := [2, 2, 4, 1, 4, 1, 1, 7]
def baseStart_3672668 : Nat := 118140960795 + 3672668 * 2 ^ 59
def prefixEnd_3672668 : Nat := 4983230072969 + 3 ^ 40 * 3672668 * 2
def baseEnd_3672668 : Nat := 139692145806440140982201

theorem tailTrace_3672668 : CollatzResearch.WordTrace tailWord_3672668 prefixEnd_3672668 139692145806440140982201 := by
  unfold tailWord_3672668
  simp only [CollatzResearch.WordTrace]
  refine ⟨66976603329279276301121329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89302137772372368401495105 66976603329279276301121329)
  ·
    refine ⟨50232452496959457225840997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66976603329279276301121329 50232452496959457225840997)
    ·
      refine ⟨9418584843179898229845187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50232452496959457225840997 9418584843179898229845187)
      ·
        refine ⟨14127877264769847344767781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9418584843179898229845187 14127877264769847344767781)
        ·
          refine ⟨2648976987144346377143959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14127877264769847344767781 2648976987144346377143959)
          ·
            refine ⟨3973465480716519565715939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648976987144346377143959 3973465480716519565715939)
            ·
              refine ⟨5960198221074779348573909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973465480716519565715939 5960198221074779348573909)
              ·
                refine ⟨139692145806440140982201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5960198221074779348573909 139692145806440140982201)
                ·
                  rfl

theorem cell22_3672668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 7].length) (baseStart_3672668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672668 prefixEnd_3672668 := by exact prefixLift 3672668
  have htrace : WordTrace (prefixWord ++ tailWord_3672668) baseStart_3672668 baseEnd_3672668 := by
    simpa [prefixWord, tailWord_3672668, baseEnd_3672668] using wordTrace_append hprefix tailTrace_3672668
  have hstable : (prefixWord ++ tailWord_3672668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672668).length < 2 ^ (prefixWord ++ tailWord_3672668).sum := by decide
  have hdescent : baseEnd_3672668 < baseStart_3672668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672706 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3672706 : Nat := 118140960795 + 3672706 * 2 ^ 59
def prefixEnd_3672706 : Nat := 4983230072969 + 3 ^ 40 * 3672706 * 2
def baseEnd_3672706 : Nat := 1257242320434541836389693

theorem tailTrace_3672706 : CollatzResearch.WordTrace tailWord_3672706 prefixEnd_3672706 1257242320434541836389693 := by
  unfold tailWord_3672706
  simp only [CollatzResearch.WordTrace]
  refine ⟨33488648158105221273031493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89303061754947256728083981 33488648158105221273031493)
  ·
    refine ⟨6279121529644728988693405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33488648158105221273031493 6279121529644728988693405)
    ·
      refine ⟨2354670573616773370760027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6279121529644728988693405 2354670573616773370760027)
      ·
        refine ⟨3532005860425160056140041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354670573616773370760027 3532005860425160056140041)
        ·
          refine ⟨2649004395318870042105031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3532005860425160056140041 2649004395318870042105031)
          ·
            refine ⟨3973506592978305063157547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649004395318870042105031 3973506592978305063157547)
            ·
              refine ⟨5960259889467457594736321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973506592978305063157547 5960259889467457594736321)
              ·
                refine ⟨4470194917100593196052241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5960259889467457594736321 4470194917100593196052241)
                ·
                  refine ⟨3352646187825444897039181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470194917100593196052241 3352646187825444897039181)
                  ·
                    refine ⟨1257242320434541836389693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3352646187825444897039181 1257242320434541836389693)
                    ·
                      rfl

theorem cell22_3672706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3672706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672706 prefixEnd_3672706 := by exact prefixLift 3672706
  have htrace : WordTrace (prefixWord ++ tailWord_3672706) baseStart_3672706 baseEnd_3672706 := by
    simpa [prefixWord, tailWord_3672706, baseEnd_3672706] using wordTrace_append hprefix tailTrace_3672706
  have hstable : (prefixWord ++ tailWord_3672706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672706).length < 2 ^ (prefixWord ++ tailWord_3672706).sum := by decide
  have hdescent : baseEnd_3672706 < baseStart_3672706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672730 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_3672730 : Nat := 118140960795 + 3672730 * 2 ^ 59
def prefixEnd_3672730 : Nat := 4983230072969 + 3 ^ 40 * 3672730 * 2
def baseEnd_3672730 : Nat := 419083512041671257929873

theorem tailTrace_3672730 : CollatzResearch.WordTrace tailWord_3672730 prefixEnd_3672730 419083512041671257929873 := by
  unfold tailWord_3672730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33488866996083484297749911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89303645322889291460666429 33488866996083484297749911)
  ·
    refine ⟨50233300494125226446624867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33488866996083484297749911 50233300494125226446624867)
    ·
      refine ⟨75349950741187839669937301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50233300494125226446624867 75349950741187839669937301)
      ·
        refine ⟨3532028940993179984528311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75349950741187839669937301 3532028940993179984528311)
        ·
          refine ⟨5298043411489769976792467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532028940993179984528311 5298043411489769976792467)
          ·
            refine ⟨7947065117234654965188701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298043411489769976792467 7947065117234654965188701)
            ·
              refine ⟨2980149418962995611945763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7947065117234654965188701 2980149418962995611945763)
              ·
                refine ⟨4470224128444493417918645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980149418962995611945763 4470224128444493417918645)
                ·
                  refine ⟨419083512041671257929873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470224128444493417918645 419083512041671257929873)
                  ·
                    rfl

theorem cell22_3672730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_3672730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672730 prefixEnd_3672730 := by exact prefixLift 3672730
  have htrace : WordTrace (prefixWord ++ tailWord_3672730) baseStart_3672730 baseEnd_3672730 := by
    simpa [prefixWord, tailWord_3672730, baseEnd_3672730] using wordTrace_append hprefix tailTrace_3672730
  have hstable : (prefixWord ++ tailWord_3672730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672730).length < 2 ^ (prefixWord ++ tailWord_3672730).sum := by decide
  have hdescent : baseEnd_3672730 < baseStart_3672730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672739 : List Nat := [1, 1, 1, 4, 1, 1, 2, 5, 1, 5]
def baseStart_3672739 : Nat := 118140960795 + 3672739 * 2 ^ 59
def prefixEnd_3672739 : Nat := 4983230072969 + 3 ^ 40 * 3672739 * 2
def baseEnd_3672739 : Nat := 1257253617008940750314591

theorem tailTrace_3672739 : CollatzResearch.WordTrace tailWord_3672739 prefixEnd_3672739 1257253617008940750314591 := by
  unfold tailWord_3672739
  simp only [CollatzResearch.WordTrace]
  refine ⟨133955796241301331728077271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89303864160867554485384847 133955796241301331728077271)
  ·
    refine ⟨200933694361951997592115907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133955796241301331728077271 200933694361951997592115907)
    ·
      refine ⟨301400541542927996388173861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200933694361951997592115907 301400541542927996388173861)
      ·
        refine ⟨56512601539298999322782599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301400541542927996388173861 56512601539298999322782599)
        ·
          refine ⟨84768902308948498984173899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56512601539298999322782599 84768902308948498984173899)
          ·
            refine ⟨127153353463422748476260849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84768902308948498984173899 127153353463422748476260849)
            ·
              refine ⟨95365015097567061357195637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127153353463422748476260849 95365015097567061357195637)
              ·
                refine ⟨8940470165396912002237091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95365015097567061357195637 8940470165396912002237091)
                ·
                  refine ⟨13410705248095368003355637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940470165396912002237091 13410705248095368003355637)
                  ·
                    refine ⟨1257253617008940750314591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13410705248095368003355637 1257253617008940750314591)
                    ·
                      rfl

theorem cell22_3672739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_3672739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672739 prefixEnd_3672739 := by exact prefixLift 3672739
  have htrace : WordTrace (prefixWord ++ tailWord_3672739) baseStart_3672739 baseEnd_3672739 := by
    simpa [prefixWord, tailWord_3672739, baseEnd_3672739] using wordTrace_append hprefix tailTrace_3672739
  have hstable : (prefixWord ++ tailWord_3672739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672739).length < 2 ^ (prefixWord ++ tailWord_3672739).sum := by decide
  have hdescent : baseEnd_3672739 < baseStart_3672739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672820 : List Nat := [2, 6, 1, 1, 3, 9]
def baseStart_3672820 : Nat := 118140960795 + 3672820 * 2 ^ 59
def prefixEnd_3672820 : Nat := 4983230072969 + 3 ^ 40 * 3672820 * 2
def baseEnd_3672820 : Nat := 15521991913139302951103

theorem tailTrace_3672820 : CollatzResearch.WordTrace tailWord_3672820 prefixEnd_3672820 15521991913139302951103 := by
  unfold tailWord_3672820
  simp only [CollatzResearch.WordTrace]
  refine ⟨66979375277003941280887957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89305833702671921707850609 66979375277003941280887957)
  ·
    refine ⟨3139658216109559747541623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66979375277003941280887957 3139658216109559747541623)
    ·
      refine ⟨4709487324164339621312435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139658216109559747541623 4709487324164339621312435)
      ·
        refine ⟨7064230986246509431968653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709487324164339621312435 7064230986246509431968653)
        ·
          refine ⟨2649086619842441036988245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7064230986246509431968653 2649086619842441036988245)
          ·
            refine ⟨15521991913139302951103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2649086619842441036988245 15521991913139302951103)
            ·
              rfl

theorem cell22_3672820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 9].length) (baseStart_3672820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672820 prefixEnd_3672820 := by exact prefixLift 3672820
  have htrace : WordTrace (prefixWord ++ tailWord_3672820) baseStart_3672820 baseEnd_3672820 := by
    simpa [prefixWord, tailWord_3672820, baseEnd_3672820] using wordTrace_append hprefix tailTrace_3672820
  have hstable : (prefixWord ++ tailWord_3672820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672820).length < 2 ^ (prefixWord ++ tailWord_3672820).sum := by decide
  have hdescent : baseEnd_3672820 < baseStart_3672820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672906 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_3672906 : Nat := 118140960795 + 3672906 * 2 ^ 59
def prefixEnd_3672906 : Nat := 4983230072969 + 3 ^ 40 * 3672906 * 2
def baseEnd_3672906 : Nat := 1257310784521807981389079

theorem tailTrace_3672906 : CollatzResearch.WordTrace tailWord_3672906 prefixEnd_3672906 1257310784521807981389079 := by
  unfold tailWord_3672906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33490471807924079812351643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89307924821130879499604381 33490471807924079812351643)
  ·
    refine ⟨50235707711886119718527465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33490471807924079812351643 50235707711886119718527465)
    ·
      refine ⟨37676780783914589788895599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50235707711886119718527465 37676780783914589788895599)
      ·
        refine ⟨56515171175871884683343399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37676780783914589788895599 56515171175871884683343399)
        ·
          refine ⟨84772756763807827025015099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56515171175871884683343399 84772756763807827025015099)
          ·
            refine ⟨127159135145711740537522649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84772756763807827025015099 127159135145711740537522649)
            ·
              refine ⟨95369351359283805403141987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127159135145711740537522649 95369351359283805403141987)
              ·
                refine ⟨143054027038925708104712981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95369351359283805403141987 143054027038925708104712981)
                ·
                  refine ⟨6705657517449642567408421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143054027038925708104712981 6705657517449642567408421)
                  ·
                    refine ⟨1257310784521807981389079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6705657517449642567408421 1257310784521807981389079)
                    ·
                      rfl

theorem cell22_3672906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_3672906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672906 prefixEnd_3672906 := by exact prefixLift 3672906
  have htrace : WordTrace (prefixWord ++ tailWord_3672906) baseStart_3672906 baseEnd_3672906 := by
    simpa [prefixWord, tailWord_3672906, baseEnd_3672906] using wordTrace_append hprefix tailTrace_3672906
  have hstable : (prefixWord ++ tailWord_3672906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672906).length < 2 ^ (prefixWord ++ tailWord_3672906).sum := by decide
  have hdescent : baseEnd_3672906 < baseStart_3672906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672908 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_3672908 : Nat := 118140960795 + 3672908 * 2 ^ 59
def prefixEnd_3672908 : Nat := 4983230072969 + 3 ^ 40 * 3672908 * 2
def baseEnd_3672908 : Nat := 1257311469162680642839073

theorem tailTrace_3672908 : CollatzResearch.WordTrace tailWord_3672908 prefixEnd_3672908 1257311469162680642839073 := by
  unfold tailWord_3672908
  simp only [CollatzResearch.WordTrace]
  refine ⟨66980980088844536795489689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89307973451792715727319585 66980980088844536795489689)
  ·
    refine ⟨50235735066633402596617267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66980980088844536795489689 50235735066633402596617267)
    ·
      refine ⟨75353602599950103894925901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50235735066633402596617267 75353602599950103894925901)
      ·
        refine ⟨28257600974981288960597213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75353602599950103894925901 28257600974981288960597213)
        ·
          refine ⟨10596600365617983360223955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28257600974981288960597213 10596600365617983360223955)
          ·
            refine ⟨15894900548426975040335933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10596600365617983360223955 15894900548426975040335933)
            ·
              refine ⟨5960587705660115640125975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15894900548426975040335933 5960587705660115640125975)
              ·
                refine ⟨8940881558490173460188963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960587705660115640125975 8940881558490173460188963)
                ·
                  refine ⟨13411322337735260190283445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940881558490173460188963 13411322337735260190283445)
                  ·
                    refine ⟨1257311469162680642839073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13411322337735260190283445 1257311469162680642839073)
                    ·
                      rfl

theorem cell22_3672908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_3672908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672908 prefixEnd_3672908 := by exact prefixLift 3672908
  have htrace : WordTrace (prefixWord ++ tailWord_3672908) baseStart_3672908 baseEnd_3672908 := by
    simpa [prefixWord, tailWord_3672908, baseEnd_3672908] using wordTrace_append hprefix tailTrace_3672908
  have hstable : (prefixWord ++ tailWord_3672908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672908).length < 2 ^ (prefixWord ++ tailWord_3672908).sum := by decide
  have hdescent : baseEnd_3672908 < baseStart_3672908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672921 : List Nat := [1, 2, 1, 2, 2, 5, 1, 8]
def baseStart_3672921 : Nat := 118140960795 + 3672921 * 2 ^ 59
def prefixEnd_3672921 : Nat := 4983230072969 + 3 ^ 40 * 3672921 * 2
def baseEnd_3672921 : Nat := 139701768814261438029337

theorem tailTrace_3672921 : CollatzResearch.WordTrace tailWord_3672921 prefixEnd_3672921 139701768814261438029337 := by
  unfold tailWord_3672921
  simp only [CollatzResearch.WordTrace]
  refine ⟨133962434326641976811202617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89308289551094651207468411 133962434326641976811202617)
  ·
    refine ⟨100471825744981482608401963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133962434326641976811202617 100471825744981482608401963)
    ·
      refine ⟨150707738617472223912602945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100471825744981482608401963 150707738617472223912602945)
      ·
        refine ⟨113030803963104167934452209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150707738617472223912602945 113030803963104167934452209)
        ·
          refine ⟨84773102972328125950839157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113030803963104167934452209 84773102972328125950839157)
          ·
            refine ⟨7947478403655761807891171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84773102972328125950839157 7947478403655761807891171)
            ·
              refine ⟨11921217605483642711836757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947478403655761807891171 11921217605483642711836757)
              ·
                refine ⟨139701768814261438029337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11921217605483642711836757 139701768814261438029337)
                ·
                  rfl

theorem cell22_3672921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 8].length) (baseStart_3672921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3672921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3672921 prefixEnd_3672921 := by exact prefixLift 3672921
  have htrace : WordTrace (prefixWord ++ tailWord_3672921) baseStart_3672921 baseEnd_3672921 := by
    simpa [prefixWord, tailWord_3672921, baseEnd_3672921] using wordTrace_append hprefix tailTrace_3672921
  have hstable : (prefixWord ++ tailWord_3672921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672921).length < 2 ^ (prefixWord ++ tailWord_3672921).sum := by decide
  have hdescent : baseEnd_3672921 < baseStart_3672921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673013 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_3673013 : Nat := 118140960795 + 3673013 * 2 ^ 59
def prefixEnd_3673013 : Nat := 4983230072969 + 3 ^ 40 * 3673013 * 2
def baseEnd_3673013 : Nat := 1257347412808495368963751

theorem tailTrace_3673013 : CollatzResearch.WordTrace tailWord_3673013 prefixEnd_3673013 1257347412808495368963751 := by
  unfold tailWord_3673013
  simp only [CollatzResearch.WordTrace]
  refine ⟨133965789842308676523551693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89310526561539117682367795 133965789842308676523551693)
  ·
    refine ⟨50237171190865753696331885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133965789842308676523551693 50237171190865753696331885)
    ·
      refine ⟨18838939196574657636124457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50237171190865753696331885 18838939196574657636124457)
      ·
        refine ⟨14129204397430993227093343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18838939196574657636124457 14129204397430993227093343)
        ·
          refine ⟨21193806596146489840640015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14129204397430993227093343 21193806596146489840640015)
          ·
            refine ⟨31790709894219734760960023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21193806596146489840640015 31790709894219734760960023)
            ·
              refine ⟨47686064841329602141440035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31790709894219734760960023 47686064841329602141440035)
              ·
                refine ⟨71529097261994403212160053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47686064841329602141440035 71529097261994403212160053)
                ·
                  refine ⟨6705852868311975301140005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71529097261994403212160053 6705852868311975301140005)
                  ·
                    refine ⟨1257347412808495368963751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6705852868311975301140005 1257347412808495368963751)
                    ·
                      rfl

theorem cell22_3673013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_3673013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3673013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3673013 prefixEnd_3673013 := by exact prefixLift 3673013
  have htrace : WordTrace (prefixWord ++ tailWord_3673013) baseStart_3673013 baseEnd_3673013 := by
    simpa [prefixWord, tailWord_3673013, baseEnd_3673013] using wordTrace_append hprefix tailTrace_3673013
  have hstable : (prefixWord ++ tailWord_3673013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673013).length < 2 ^ (prefixWord ++ tailWord_3673013).sum := by decide
  have hdescent : baseEnd_3673013 < baseStart_3673013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
