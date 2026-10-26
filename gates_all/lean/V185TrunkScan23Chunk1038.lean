import V185TrunkScan23Chunk1037

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6145526 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_6145526 : Nat := 118140960795 + 6145526 * 2 ^ 59
def prefixEnd_6145526 : Nat := 4983230072969 + 3 ^ 40 * 6145526 * 2
def baseEnd_6145526 : Nat := 3155608712702827834962247

theorem tailTrace_6145526 : CollatzResearch.WordTrace tailWord_6145526 prefixEnd_6145526 3155608712702827834962247 := by
  unfold tailWord_6145526
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009109220863521820324527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149430498355877566083461621 14009109220863521820324527)
  ·
    refine ⟨21013663831295282730486791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14009109220863521820324527 21013663831295282730486791)
    ·
      refine ⟨31520495746942924095730187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21013663831295282730486791 31520495746942924095730187)
      ·
        refine ⟨47280743620414386143595281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31520495746942924095730187 47280743620414386143595281)
        ·
          refine ⟨35460557715310789607696461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47280743620414386143595281 35460557715310789607696461)
          ·
            refine ⟨13297709143241546102886173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35460557715310789607696461 13297709143241546102886173)
            ·
              refine ⟨4986640928715579788582315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13297709143241546102886173 4986640928715579788582315)
              ·
                refine ⟨7479961393073369682873473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986640928715579788582315 7479961393073369682873473)
                ·
                  refine ⟨5609971044805027262155105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7479961393073369682873473 5609971044805027262155105)
                  ·
                    refine ⟨4207478283603770446616329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609971044805027262155105 4207478283603770446616329)
                    ·
                      refine ⟨3155608712702827834962247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207478283603770446616329 3155608712702827834962247)
                      ·
                        rfl

theorem cell23_6145526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_6145526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145526 prefixEnd_6145526 := by exact prefixLift 6145526
  have htrace : WordTrace (prefixWord ++ tailWord_6145526) baseStart_6145526 baseEnd_6145526 := by
    simpa [prefixWord, tailWord_6145526, baseEnd_6145526] using wordTrace_append hprefix tailTrace_6145526
  have hstable : (prefixWord ++ tailWord_6145526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145526).length < 2 ^ (prefixWord ++ tailWord_6145526).sum := by decide
  have hdescent : baseEnd_6145526 < baseStart_6145526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145541 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_6145541 : Nat := 118140960795 + 6145541 * 2 ^ 59
def prefixEnd_6145541 : Nat := 4983230072969 + 3 ^ 40 * 6145541 * 2
def baseEnd_6145541 : Nat := 1051872138304215092091559

theorem tailTrace_6145541 : CollatzResearch.WordTrace tailWord_6145541 prefixEnd_6145541 1051872138304215092091559 := by
  unfold tailWord_6145541
  simp only [CollatzResearch.WordTrace]
  refine ⟨224146294628762006686988477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149430863085841337791325651 224146294628762006686988477)
  ·
    refine ⟨84054860485785752507620679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224146294628762006686988477 84054860485785752507620679)
    ·
      refine ⟨126082290728678628761431019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84054860485785752507620679 126082290728678628761431019)
      ·
        refine ⟨189123436093017943142146529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126082290728678628761431019 189123436093017943142146529)
        ·
          refine ⟨141842577069763457356609897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189123436093017943142146529 141842577069763457356609897)
          ·
            refine ⟨106381932802322593017457423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141842577069763457356609897 106381932802322593017457423)
            ·
              refine ⟨159572899203483889526186135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106381932802322593017457423 159572899203483889526186135)
              ·
                refine ⟨239359348805225834289279203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159572899203483889526186135 239359348805225834289279203)
                ·
                  refine ⟨359039023207838751433918805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239359348805225834289279203 359039023207838751433918805)
                  ·
                    refine ⟨1051872138304215092091559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 359039023207838751433918805 1051872138304215092091559)
                    ·
                      rfl

theorem cell23_6145541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_6145541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145541 prefixEnd_6145541 := by exact prefixLift 6145541
  have htrace : WordTrace (prefixWord ++ tailWord_6145541) baseStart_6145541 baseEnd_6145541 := by
    simpa [prefixWord, tailWord_6145541, baseEnd_6145541] using wordTrace_append hprefix tailTrace_6145541
  have hstable : (prefixWord ++ tailWord_6145541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145541).length < 2 ^ (prefixWord ++ tailWord_6145541).sum := by decide
  have hdescent : baseEnd_6145541 < baseStart_6145541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145565 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_6145565 : Nat := 118140960795 + 6145565 * 2 ^ 59
def prefixEnd_6145565 : Nat := 4983230072969 + 3 ^ 40 * 6145565 * 2
def baseEnd_6145565 : Nat := 3155628738448353182374567

theorem tailTrace_6145565 : CollatzResearch.WordTrace tailWord_6145565 prefixEnd_6145565 3155628738448353182374567 := by
  unfold tailWord_6145565
  simp only [CollatzResearch.WordTrace]
  refine ⟨224147169980675058785862149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149431446653783372523908099 224147169980675058785862149)
  ·
    refine ⟨42027594371376573522349153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224147169980675058785862149 42027594371376573522349153)
    ·
      refine ⟨31520695778532430141761865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42027594371376573522349153 31520695778532430141761865)
      ·
        refine ⟨23640521833899322606321399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31520695778532430141761865 23640521833899322606321399)
        ·
          refine ⟨35460782750848983909482099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23640521833899322606321399 35460782750848983909482099)
          ·
            refine ⟨53191174126273475864223149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35460782750848983909482099 53191174126273475864223149)
            ·
              refine ⟨19946690297352553449083681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53191174126273475864223149 19946690297352553449083681)
              ·
                refine ⟨14960017723014415086812761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19946690297352553449083681 14960017723014415086812761)
                ·
                  refine ⟨11220013292260811315109571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14960017723014415086812761 11220013292260811315109571)
                  ·
                    refine ⟨16830019938391216972664357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11220013292260811315109571 16830019938391216972664357)
                    ·
                      refine ⟨3155628738448353182374567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16830019938391216972664357 3155628738448353182374567)
                      ·
                        rfl

theorem cell23_6145565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_6145565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145565 prefixEnd_6145565 := by exact prefixLift 6145565
  have htrace : WordTrace (prefixWord ++ tailWord_6145565) baseStart_6145565 baseEnd_6145565 := by
    simpa [prefixWord, tailWord_6145565, baseEnd_6145565] using wordTrace_append hprefix tailTrace_6145565
  have hstable : (prefixWord ++ tailWord_6145565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145565).length < 2 ^ (prefixWord ++ tailWord_6145565).sum := by decide
  have hdescent : baseEnd_6145565 < baseStart_6145565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145566 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 7]
def baseStart_6145566 : Nat := 118140960795 + 6145566 * 2 ^ 59
def prefixEnd_6145566 : Nat := 4983230072969 + 3 ^ 40 * 6145566 * 2
def baseEnd_6145566 : Nat := 350625472436556408718007

theorem tailTrace_6145566 : CollatzResearch.WordTrace tailWord_6145566 prefixEnd_6145566 350625472436556408718007 := by
  unfold tailWord_6145566
  simp only [CollatzResearch.WordTrace]
  refine ⟨28018400806708929494581069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149431470969114290637765701 28018400806708929494581069)
  ·
    refine ⟨10506900302515848560467901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28018400806708929494581069 10506900302515848560467901)
    ·
      refine ⟨3940087613443443210175463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10506900302515848560467901 3940087613443443210175463)
      ·
        refine ⟨5910131420165164815263195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940087613443443210175463 5910131420165164815263195)
        ·
          refine ⟨8865197130247747222894793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910131420165164815263195 8865197130247747222894793)
          ·
            refine ⟨6648897847685810417171095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8865197130247747222894793 6648897847685810417171095)
            ·
              refine ⟨9973346771528715625756643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648897847685810417171095 9973346771528715625756643)
              ·
                refine ⟨14960020157293073438634965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9973346771528715625756643 14960020157293073438634965)
                ·
                  refine ⟨350625472436556408718007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14960020157293073438634965 350625472436556408718007)
                  ·
                    rfl

theorem cell23_6145566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_6145566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145566 prefixEnd_6145566 := by exact prefixLift 6145566
  have htrace : WordTrace (prefixWord ++ tailWord_6145566) baseStart_6145566 baseEnd_6145566 := by
    simpa [prefixWord, tailWord_6145566, baseEnd_6145566] using wordTrace_append hprefix tailTrace_6145566
  have hstable : (prefixWord ++ tailWord_6145566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145566).length < 2 ^ (prefixWord ++ tailWord_6145566).sum := by decide
  have hdescent : baseEnd_6145566 < baseStart_6145566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145655 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 4]
def baseStart_6145655 : Nat := 118140960795 + 6145655 * 2 ^ 59
def prefixEnd_6145655 : Nat := 4983230072969 + 3 ^ 40 * 6145655 * 2
def baseEnd_6145655 : Nat := 3155674951707257830249153

theorem tailTrace_6145655 : CollatzResearch.WordTrace tailWord_6145655 prefixEnd_6145655 3155674951707257830249153 := by
  unfold tailWord_6145655
  simp only [CollatzResearch.WordTrace]
  refine ⟨224150452550349004156638419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149433635033566002771092279 224150452550349004156638419)
  ·
    refine ⟨336225678825523506234957629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224150452550349004156638419 336225678825523506234957629)
    ·
      refine ⟨126084629559571314838109111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336225678825523506234957629 126084629559571314838109111)
      ·
        refine ⟨189126944339356972257163667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126084629559571314838109111 189126944339356972257163667)
        ·
          refine ⟨283690416509035458385745501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189126944339356972257163667 283690416509035458385745501)
          ·
            refine ⟨106383906190888296894654563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283690416509035458385745501 106383906190888296894654563)
            ·
              refine ⟨159575859286332445341981845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106383906190888296894654563 159575859286332445341981845)
              ·
                refine ⟨7480118404046833375405399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159575859286332445341981845 7480118404046833375405399)
                ·
                  refine ⟨11220177606070250063108099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480118404046833375405399 11220177606070250063108099)
                  ·
                    refine ⟨16830266409105375094662149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11220177606070250063108099 16830266409105375094662149)
                    ·
                      refine ⟨3155674951707257830249153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16830266409105375094662149 3155674951707257830249153)
                      ·
                        rfl

theorem cell23_6145655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_6145655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145655 prefixEnd_6145655 := by exact prefixLift 6145655
  have htrace : WordTrace (prefixWord ++ tailWord_6145655) baseStart_6145655 baseEnd_6145655 := by
    simpa [prefixWord, tailWord_6145655, baseEnd_6145655] using wordTrace_append hprefix tailTrace_6145655
  have hstable : (prefixWord ++ tailWord_6145655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145655).length < 2 ^ (prefixWord ++ tailWord_6145655).sum := by decide
  have hdescent : baseEnd_6145655 < baseStart_6145655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145658 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_6145658 : Nat := 118140960795 + 6145658 * 2 ^ 59
def prefixEnd_6145658 : Nat := 4983230072969 + 3 ^ 40 * 6145658 * 2
def baseEnd_6145658 : Nat := 3155676492149221318511639

theorem tailTrace_6145658 : CollatzResearch.WordTrace tailWord_6145658 prefixEnd_6145658 3155676492149221318511639 := by
  unfold tailWord_6145658
  simp only [CollatzResearch.WordTrace]
  refine ⟨56037640492334533917249407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149433707979558757112665085 56037640492334533917249407)
  ·
    refine ⟨84056460738501800875874111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56037640492334533917249407 84056460738501800875874111)
    ·
      refine ⟨126084691107752701313811167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84056460738501800875874111 126084691107752701313811167)
      ·
        refine ⟨189127036661629051970716751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126084691107752701313811167 189127036661629051970716751)
        ·
          refine ⟨283690554992443577956075127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189127036661629051970716751 283690554992443577956075127)
          ·
            refine ⟨425535832488665366934112691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283690554992443577956075127 425535832488665366934112691)
            ·
              refine ⟨638303748732998050401169037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425535832488665366934112691 638303748732998050401169037)
              ·
                refine ⟨239363905774874268900438389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 638303748732998050401169037 239363905774874268900438389)
                ·
                  refine ⟨22440366166394462709416099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239363905774874268900438389 22440366166394462709416099)
                  ·
                    refine ⟨33660549249591694064124149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22440366166394462709416099 33660549249591694064124149)
                    ·
                      refine ⟨3155676492149221318511639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33660549249591694064124149 3155676492149221318511639)
                      ·
                        rfl

theorem cell23_6145658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_6145658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145658 prefixEnd_6145658 := by exact prefixLift 6145658
  have htrace : WordTrace (prefixWord ++ tailWord_6145658) baseStart_6145658 baseEnd_6145658 := by
    simpa [prefixWord, tailWord_6145658, baseEnd_6145658] using wordTrace_append hprefix tailTrace_6145658
  have hstable : (prefixWord ++ tailWord_6145658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145658).length < 2 ^ (prefixWord ++ tailWord_6145658).sum := by decide
  have hdescent : baseEnd_6145658 < baseStart_6145658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145665 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_6145665 : Nat := 118140960795 + 6145665 * 2 ^ 59
def prefixEnd_6145665 : Nat := 4983230072969 + 3 ^ 40 * 6145665 * 2
def baseEnd_6145665 : Nat := 1051893362171267597041369

theorem tailTrace_6145665 : CollatzResearch.WordTrace tailWord_6145665 prefixEnd_6145665 1051893362171267597041369 := by
  unfold tailWord_6145665
  simp only [CollatzResearch.WordTrace]
  refine ⟨224150817280312775864502449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149433878186875183909668299 224150817280312775864502449)
  ·
    refine ⟨168113112960234581898376837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224150817280312775864502449 168113112960234581898376837)
    ·
      refine ⟨31521208680043984105945657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168113112960234581898376837 31521208680043984105945657)
      ·
        refine ⟨23640906510032988079459243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31521208680043984105945657 23640906510032988079459243)
        ·
          refine ⟨35461359765049482119188865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23640906510032988079459243 35461359765049482119188865)
          ·
            refine ⟨26596019823787111589391649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35461359765049482119188865 26596019823787111589391649)
            ·
              refine ⟨19947014867840333692043737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26596019823787111589391649 19947014867840333692043737)
              ·
                refine ⟨14960261150880250269032803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19947014867840333692043737 14960261150880250269032803)
                ·
                  refine ⟨22440391726320375403549205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14960261150880250269032803 22440391726320375403549205)
                  ·
                    refine ⟨1051893362171267597041369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22440391726320375403549205 1051893362171267597041369)
                    ·
                      rfl

theorem cell23_6145665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_6145665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145665 prefixEnd_6145665 := by exact prefixLift 6145665
  have htrace : WordTrace (prefixWord ++ tailWord_6145665) baseStart_6145665 baseEnd_6145665 := by
    simpa [prefixWord, tailWord_6145665, baseEnd_6145665] using wordTrace_append hprefix tailTrace_6145665
  have hstable : (prefixWord ++ tailWord_6145665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145665).length < 2 ^ (prefixWord ++ tailWord_6145665).sum := by decide
  have hdescent : baseEnd_6145665 < baseStart_6145665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145692 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_6145692 : Nat := 118140960795 + 6145692 * 2 ^ 59
def prefixEnd_6145692 : Nat := 4983230072969 + 3 ^ 40 * 6145692 * 2
def baseEnd_6145692 : Nat := 3155693950491474185486483

theorem tailTrace_6145692 : CollatzResearch.WordTrace tailWord_6145692 prefixEnd_6145692 3155693950491474185486483 := by
  unfold tailWord_6145692
  simp only [CollatzResearch.WordTrace]
  refine ⟨112075901025607479737867665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149434534700809972983823553 112075901025607479737867665)
  ·
    refine ⟨84056925769205609803400749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112075901025607479737867665 84056925769205609803400749)
    ·
      refine ⟨31521347163452103676275281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84056925769205609803400749 31521347163452103676275281)
      ·
        refine ⟨23641010372589077757206461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31521347163452103676275281 23641010372589077757206461)
        ·
          refine ⟨8865378889720904158952423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23641010372589077757206461 8865378889720904158952423)
          ·
            refine ⟨13298068334581356238428635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8865378889720904158952423 13298068334581356238428635)
            ·
              refine ⟨19947102501872034357642953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13298068334581356238428635 19947102501872034357642953)
              ·
                refine ⟨14960326876404025768232215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19947102501872034357642953 14960326876404025768232215)
                ·
                  refine ⟨22440490314606038652348323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14960326876404025768232215 22440490314606038652348323)
                  ·
                    refine ⟨33660735471909057978522485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22440490314606038652348323 33660735471909057978522485)
                    ·
                      refine ⟨3155693950491474185486483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33660735471909057978522485 3155693950491474185486483)
                      ·
                        rfl

theorem cell23_6145692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_6145692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145692 prefixEnd_6145692 := by exact prefixLift 6145692
  have htrace : WordTrace (prefixWord ++ tailWord_6145692) baseStart_6145692 baseEnd_6145692 := by
    simpa [prefixWord, tailWord_6145692, baseEnd_6145692] using wordTrace_append hprefix tailTrace_6145692
  have hstable : (prefixWord ++ tailWord_6145692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145692).length < 2 ^ (prefixWord ++ tailWord_6145692).sum := by decide
  have hdescent : baseEnd_6145692 < baseStart_6145692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145709 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6145709 : Nat := 118140960795 + 6145709 * 2 ^ 59
def prefixEnd_6145709 : Nat := 4983230072969 + 3 ^ 40 * 6145709 * 2
def baseEnd_6145709 : Nat := 3155702679662600618973905

theorem tailTrace_6145709 : CollatzResearch.WordTrace tailWord_6145709 prefixEnd_6145709 3155702679662600618973905 := by
  unfold tailWord_6145709
  simp only [CollatzResearch.WordTrace]
  refine ⟨224152422092153371379104181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149434948061435580919402787 224152422092153371379104181)
  ·
    refine ⟨21014289571139378566791017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224152422092153371379104181 21014289571139378566791017)
    ·
      refine ⟨15760717178354533925093263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21014289571139378566791017 15760717178354533925093263)
      ·
        refine ⟨23641075767531800887639895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15760717178354533925093263 23641075767531800887639895)
        ·
          refine ⟨35461613651297701331459843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23641075767531800887639895 35461613651297701331459843)
          ·
            refine ⟨53192420476946551997189765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35461613651297701331459843 53192420476946551997189765)
            ·
              refine ⟨9973578839427478499473081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53192420476946551997189765 9973578839427478499473081)
              ·
                refine ⟨7480184129570608874604811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9973578839427478499473081 7480184129570608874604811)
                ·
                  refine ⟨11220276194355913311907217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480184129570608874604811 11220276194355913311907217)
                  ·
                    refine ⟨8415207145766934983930413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11220276194355913311907217 8415207145766934983930413)
                    ·
                      refine ⟨3155702679662600618973905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8415207145766934983930413 3155702679662600618973905)
                      ·
                        rfl

theorem cell23_6145709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6145709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145709 prefixEnd_6145709 := by exact prefixLift 6145709
  have htrace : WordTrace (prefixWord ++ tailWord_6145709) baseStart_6145709 baseEnd_6145709 := by
    simpa [prefixWord, tailWord_6145709, baseEnd_6145709] using wordTrace_append hprefix tailTrace_6145709
  have hstable : (prefixWord ++ tailWord_6145709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145709).length < 2 ^ (prefixWord ++ tailWord_6145709).sum := by decide
  have hdescent : baseEnd_6145709 < baseStart_6145709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145722 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_6145722 : Nat := 118140960795 + 6145722 * 2 ^ 59
def prefixEnd_6145722 : Nat := 4983230072969 + 3 ^ 40 * 6145722 * 2
def baseEnd_6145722 : Nat := 3155709354911109068111345

theorem tailTrace_6145722 : CollatzResearch.WordTrace tailWord_6145722 prefixEnd_6145722 3155709354911109068111345 := by
  unfold tailWord_6145722
  simp only [CollatzResearch.WordTrace]
  refine ⟨56038224060276568649831855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149435264160737516399551613 56038224060276568649831855)
  ·
    refine ⟨84057336090414852974747783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56038224060276568649831855 84057336090414852974747783)
    ·
      refine ⟨126086004135622279462121675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84057336090414852974747783 126086004135622279462121675)
      ·
        refine ⟨189129006203433419193182513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126086004135622279462121675 189129006203433419193182513)
        ·
          refine ⟨141846754652575064394886885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189129006203433419193182513 141846754652575064394886885)
          ·
            refine ⟨26596266497357824574041291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141846754652575064394886885 26596266497357824574041291)
            ·
              refine ⟨39894399746036736861061937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26596266497357824574041291 39894399746036736861061937)
              ·
                refine ⟨29920799809527552645796453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39894399746036736861061937 29920799809527552645796453)
                ·
                  refine ⟨5610149964286416121086835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29920799809527552645796453 5610149964286416121086835)
                  ·
                    refine ⟨8415224946429624181630253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5610149964286416121086835 8415224946429624181630253)
                    ·
                      refine ⟨3155709354911109068111345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8415224946429624181630253 3155709354911109068111345)
                      ·
                        rfl

theorem cell23_6145722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_6145722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145722 prefixEnd_6145722 := by exact prefixLift 6145722
  have htrace : WordTrace (prefixWord ++ tailWord_6145722) baseStart_6145722 baseEnd_6145722 := by
    simpa [prefixWord, tailWord_6145722, baseEnd_6145722] using wordTrace_append hprefix tailTrace_6145722
  have hstable : (prefixWord ++ tailWord_6145722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145722).length < 2 ^ (prefixWord ++ tailWord_6145722).sum := by decide
  have hdescent : baseEnd_6145722 < baseStart_6145722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145740 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 1, 2, 2]
def baseStart_6145740 : Nat := 118140960795 + 6145740 * 2 ^ 59
def prefixEnd_6145740 : Nat := 4983230072969 + 3 ^ 40 * 6145740 * 2
def baseEnd_6145740 : Nat := 3155718597562889997686263

theorem tailTrace_6145740 : CollatzResearch.WordTrace tailWord_6145740 prefixEnd_6145740 3155718597562889997686263 := by
  unfold tailWord_6145740
  simp only [CollatzResearch.WordTrace]
  refine ⟨112076776377520531836741337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149435701836694042448988449 112076776377520531836741337)
  ·
    refine ⟨84057582283140398877556003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112076776377520531836741337 84057582283140398877556003)
    ·
      refine ⟨126086373424710598316334005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84057582283140398877556003 126086373424710598316334005)
      ·
        refine ⟨11820597508566618592156313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126086373424710598316334005 11820597508566618592156313)
        ·
          refine ⟨8865448131424963944117235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11820597508566618592156313 8865448131424963944117235)
          ·
            refine ⟨13298172197137445916175853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8865448131424963944117235 13298172197137445916175853)
            ·
              refine ⟨4986814573926542218565945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13298172197137445916175853 4986814573926542218565945)
              ·
                refine ⟨3740110930444906663924459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4986814573926542218565945 3740110930444906663924459)
                ·
                  refine ⟨5610166395667359995886689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740110930444906663924459 5610166395667359995886689)
                  ·
                    refine ⟨4207624796750519996915017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610166395667359995886689 4207624796750519996915017)
                    ·
                      refine ⟨3155718597562889997686263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207624796750519996915017 3155718597562889997686263)
                      ·
                        rfl

theorem cell23_6145740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_6145740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145740 prefixEnd_6145740 := by exact prefixLift 6145740
  have htrace : WordTrace (prefixWord ++ tailWord_6145740) baseStart_6145740 baseEnd_6145740 := by
    simpa [prefixWord, tailWord_6145740, baseEnd_6145740] using wordTrace_append hprefix tailTrace_6145740
  have hstable : (prefixWord ++ tailWord_6145740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145740).length < 2 ^ (prefixWord ++ tailWord_6145740).sum := by decide
  have hdescent : baseEnd_6145740 < baseStart_6145740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145750 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_6145750 : Nat := 118140960795 + 6145750 * 2 ^ 59
def prefixEnd_6145750 : Nat := 4983230072969 + 3 ^ 40 * 6145750 * 2
def baseEnd_6145750 : Nat := 1051907910789811652853739

theorem tailTrace_6145750 : CollatzResearch.WordTrace tailWord_6145750 prefixEnd_6145750 1051907910789811652853739 := by
  unfold tailWord_6145750
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009619842812802211334169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149435944990003223587564469 14009619842812802211334169)
  ·
    refine ⟨10507214882109601658500627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14009619842812802211334169 10507214882109601658500627)
    ·
      refine ⟨15760822323164402487750941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10507214882109601658500627 15760822323164402487750941)
      ·
        refine ⟨5910308371186650932906603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15760822323164402487750941 5910308371186650932906603)
        ·
          refine ⟨8865462556779976399359905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5910308371186650932906603 8865462556779976399359905)
          ·
            refine ⟨6649096917584982299519929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8865462556779976399359905 6649096917584982299519929)
            ·
              refine ⟨4986822688188736724639947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6649096917584982299519929 4986822688188736724639947)
              ·
                refine ⟨7480234032283105086959921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986822688188736724639947 7480234032283105086959921)
                ·
                  refine ⟨5610175524212328815219941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7480234032283105086959921 5610175524212328815219941)
                  ·
                    refine ⟨1051907910789811652853739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610175524212328815219941 1051907910789811652853739)
                    ·
                      rfl

theorem cell23_6145750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_6145750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145750 prefixEnd_6145750 := by exact prefixLift 6145750
  have htrace : WordTrace (prefixWord ++ tailWord_6145750) baseStart_6145750 baseEnd_6145750 := by
    simpa [prefixWord, tailWord_6145750, baseEnd_6145750] using wordTrace_append hprefix tailTrace_6145750
  have hstable : (prefixWord ++ tailWord_6145750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145750).length < 2 ^ (prefixWord ++ tailWord_6145750).sum := by decide
  have hdescent : baseEnd_6145750 < baseStart_6145750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145765 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6145765 : Nat := 118140960795 + 6145765 * 2 ^ 59
def prefixEnd_6145765 : Nat := 4983230072969 + 3 ^ 40 * 6145765 * 2
def baseEnd_6145765 : Nat := 3155731434579252399873647

theorem tailTrace_6145765 : CollatzResearch.WordTrace tailWord_6145765 prefixEnd_6145765 3155731434579252399873647 := by
  unfold tailWord_6145765
  simp only [CollatzResearch.WordTrace]
  refine ⟨224154464579950492943142749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149436309719966995295428499 224154464579950492943142749)
  ·
    refine ⟨84057924217481434853678531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224154464579950492943142749 84057924217481434853678531)
    ·
      refine ⟨126086886326222152280517797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84057924217481434853678531 126086886326222152280517797)
      ·
        refine ⟨23641291186166653552597087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126086886326222152280517797 23641291186166653552597087)
        ·
          refine ⟨35461936779249980328895631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23641291186166653552597087 35461936779249980328895631)
          ·
            refine ⟨53192905168874970493343447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35461936779249980328895631 53192905168874970493343447)
            ·
              refine ⟨79789357753312455740015171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53192905168874970493343447 79789357753312455740015171)
              ·
                refine ⟨119684036629968683610022757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79789357753312455740015171 119684036629968683610022757)
                ·
                  refine ⟨22440756868119128176879267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119684036629968683610022757 22440756868119128176879267)
                  ·
                    refine ⟨33661135302178692265318901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22440756868119128176879267 33661135302178692265318901)
                    ·
                      refine ⟨3155731434579252399873647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33661135302178692265318901 3155731434579252399873647)
                      ·
                        rfl

theorem cell23_6145765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6145765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145765 prefixEnd_6145765 := by exact prefixLift 6145765
  have htrace : WordTrace (prefixWord ++ tailWord_6145765) baseStart_6145765 baseEnd_6145765 := by
    simpa [prefixWord, tailWord_6145765, baseEnd_6145765] using wordTrace_append hprefix tailTrace_6145765
  have hstable : (prefixWord ++ tailWord_6145765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145765).length < 2 ^ (prefixWord ++ tailWord_6145765).sum := by decide
  have hdescent : baseEnd_6145765 < baseStart_6145765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145782 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6145782 : Nat := 118140960795 + 6145782 * 2 ^ 59
def prefixEnd_6145782 : Nat := 4983230072969 + 3 ^ 40 * 6145782 * 2
def baseEnd_6145782 : Nat := 3155740163750378833361069

theorem tailTrace_6145782 : CollatzResearch.WordTrace tailWord_6145782 prefixEnd_6145782 3155740163750378833361069 := by
  unfold tailWord_6145782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009692788805556552906975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149436723080592603231007733 14009692788805556552906975)
  ·
    refine ⟨21014539183208334829360463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14009692788805556552906975 21014539183208334829360463)
    ·
      refine ⟨31521808774812502244040695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21014539183208334829360463 31521808774812502244040695)
      ·
        refine ⟨47282713162218753366061043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31521808774812502244040695 47282713162218753366061043)
        ·
          refine ⟨70924069743328130049091565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47282713162218753366061043 70924069743328130049091565)
          ·
            refine ⟨26596526153748048768409337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70924069743328130049091565 26596526153748048768409337)
            ·
              refine ⟨19947394615311036576307003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26596526153748048768409337 19947394615311036576307003)
              ·
                refine ⟨29921091922966554864460505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19947394615311036576307003 29921091922966554864460505)
                ·
                  refine ⟨22440818942224916148345379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29921091922966554864460505 22440818942224916148345379)
                  ·
                    refine ⟨33661228413337374222518069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22440818942224916148345379 33661228413337374222518069)
                    ·
                      refine ⟨3155740163750378833361069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33661228413337374222518069 3155740163750378833361069)
                      ·
                        rfl

theorem cell23_6145782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6145782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145782 prefixEnd_6145782 := by exact prefixLift 6145782
  have htrace : WordTrace (prefixWord ++ tailWord_6145782) baseStart_6145782 baseEnd_6145782 := by
    simpa [prefixWord, tailWord_6145782, baseEnd_6145782] using wordTrace_append hprefix tailTrace_6145782
  have hstable : (prefixWord ++ tailWord_6145782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145782).length < 2 ^ (prefixWord ++ tailWord_6145782).sum := by decide
  have hdescent : baseEnd_6145782 < baseStart_6145782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145796 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_6145796 : Nat := 118140960795 + 6145796 * 2 ^ 59
def prefixEnd_6145796 : Nat := 4983230072969 + 3 ^ 40 * 6145796 * 2
def baseEnd_6145796 : Nat := 3155747352479541778586005

theorem tailTrace_6145796 : CollatzResearch.WordTrace tailWord_6145796 prefixEnd_6145796 3155747352479541778586005 := by
  unfold tailWord_6145796
  simp only [CollatzResearch.WordTrace]
  refine ⟨112077797621419092618760621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149437063495225456825014161 112077797621419092618760621)
  ·
    refine ⟨42029174108032159732035233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112077797621419092618760621 42029174108032159732035233)
    ·
      refine ⟨31521880581024119799026425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42029174108032159732035233 31521880581024119799026425)
      ·
        refine ⟨23641410435768089849269819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31521880581024119799026425 23641410435768089849269819)
        ·
          refine ⟨35462115653652134773904729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23641410435768089849269819 35462115653652134773904729)
          ·
            refine ⟨26596586740239101080428547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35462115653652134773904729 26596586740239101080428547)
            ·
              refine ⟨39894880110358651620642821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26596586740239101080428547 39894880110358651620642821)
              ·
                refine ⟨7480290020692247178870529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39894880110358651620642821 7480290020692247178870529)
                ·
                  refine ⟨5610217515519185384152897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7480290020692247178870529 5610217515519185384152897)
                  ·
                    refine ⟨4207663136639389038114673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610217515519185384152897 4207663136639389038114673)
                    ·
                      refine ⟨3155747352479541778586005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207663136639389038114673 3155747352479541778586005)
                      ·
                        rfl

theorem cell23_6145796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_6145796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145796 prefixEnd_6145796 := by exact prefixLift 6145796
  have htrace : WordTrace (prefixWord ++ tailWord_6145796) baseStart_6145796 baseEnd_6145796 := by
    simpa [prefixWord, tailWord_6145796, baseEnd_6145796] using wordTrace_append hprefix tailTrace_6145796
  have hstable : (prefixWord ++ tailWord_6145796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145796).length < 2 ^ (prefixWord ++ tailWord_6145796).sum := by decide
  have hdescent : baseEnd_6145796 < baseStart_6145796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145832 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6145832 : Nat := 118140960795 + 6145832 * 2 ^ 59
def prefixEnd_6145832 : Nat := 4983230072969 + 3 ^ 40 * 6145832 * 2
def baseEnd_6145832 : Nat := 1051921945927701212578613

theorem tailTrace_6145832 : CollatzResearch.WordTrace tailWord_6145832 prefixEnd_6145832 1051921945927701212578613 := by
  unfold tailWord_6145832
  simp only [CollatzResearch.WordTrace]
  refine ⟨112078454135353881692915875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149437938847138508923887833 112078454135353881692915875)
  ·
    refine ⟨168117681203030822539373813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112078454135353881692915875 168117681203030822539373813)
    ·
      refine ⟨15761032612784139613066295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168117681203030822539373813 15761032612784139613066295)
      ·
        refine ⟨23641548919176209419599443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15761032612784139613066295 23641548919176209419599443)
        ·
          refine ⟨35462323378764314129399165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23641548919176209419599443 35462323378764314129399165)
          ·
            refine ⟨13298371267036617798524687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35462323378764314129399165 13298371267036617798524687)
            ·
              refine ⟨19947556900554926697787031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13298371267036617798524687 19947556900554926697787031)
              ·
                refine ⟨29921335350832390046680547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19947556900554926697787031 29921335350832390046680547)
                ·
                  refine ⟨44882003026248585070020821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29921335350832390046680547 44882003026248585070020821)
                  ·
                    refine ⟨1051921945927701212578613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44882003026248585070020821 1051921945927701212578613)
                    ·
                      rfl

theorem cell23_6145832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6145832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145832 prefixEnd_6145832 := by exact prefixLift 6145832
  have htrace : WordTrace (prefixWord ++ tailWord_6145832) baseStart_6145832 baseEnd_6145832 := by
    simpa [prefixWord, tailWord_6145832, baseEnd_6145832] using wordTrace_append hprefix tailTrace_6145832
  have hstable : (prefixWord ++ tailWord_6145832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145832).length < 2 ^ (prefixWord ++ tailWord_6145832).sum := by decide
  have hdescent : baseEnd_6145832 < baseStart_6145832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145852 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_6145852 : Nat := 118140960795 + 6145852 * 2 ^ 59
def prefixEnd_6145852 : Nat := 4983230072969 + 3 ^ 40 * 6145852 * 2
def baseEnd_6145852 : Nat := 3155776107396193559485747

theorem tailTrace_6145852 : CollatzResearch.WordTrace tailWord_6145852 prefixEnd_6145852 3155776107396193559485747 := by
  unfold tailWord_6145852
  simp only [CollatzResearch.WordTrace]
  refine ⟨112078818865317653400779905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149438425153756871201039873 112078818865317653400779905)
  ·
    refine ⟨84059114148988240050584929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112078818865317653400779905 84059114148988240050584929)
    ·
      refine ⟨63044335611741180037938697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84059114148988240050584929 63044335611741180037938697)
      ·
        refine ⟨47283251708805885028454023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63044335611741180037938697 47283251708805885028454023)
        ·
          refine ⟨70924877563208827542681035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47283251708805885028454023 70924877563208827542681035)
          ·
            refine ⟨106387316344813241314021553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70924877563208827542681035 106387316344813241314021553)
            ·
              refine ⟨79790487258609930985516165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106387316344813241314021553 79790487258609930985516165)
              ·
                refine ⟨14960716360989362059784281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79790487258609930985516165 14960716360989362059784281)
                ·
                  refine ⟨11220537270742021544838211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14960716360989362059784281 11220537270742021544838211)
                  ·
                    refine ⟨16830805906113032317257317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11220537270742021544838211 16830805906113032317257317)
                    ·
                      refine ⟨3155776107396193559485747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16830805906113032317257317 3155776107396193559485747)
                      ·
                        rfl

theorem cell23_6145852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_6145852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145852 prefixEnd_6145852 := by exact prefixLift 6145852
  have htrace : WordTrace (prefixWord ++ tailWord_6145852) baseStart_6145852 baseEnd_6145852 := by
    simpa [prefixWord, tailWord_6145852, baseEnd_6145852] using wordTrace_append hprefix tailTrace_6145852
  have hstable : (prefixWord ++ tailWord_6145852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145852).length < 2 ^ (prefixWord ++ tailWord_6145852).sum := by decide
  have hdescent : baseEnd_6145852 < baseStart_6145852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145865 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_6145865 : Nat := 118140960795 + 6145865 * 2 ^ 59
def prefixEnd_6145865 : Nat := 4983230072969 + 3 ^ 40 * 6145865 * 2
def baseEnd_6145865 : Nat := 3155782782644702008623187

theorem tailTrace_6145865 : CollatzResearch.WordTrace tailWord_6145865 prefixEnd_6145865 3155782782644702008623187 := by
  unfold tailWord_6145865
  simp only [CollatzResearch.WordTrace]
  refine ⟨224158111879588210021783049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149438741253058806681188699 224158111879588210021783049)
  ·
    refine ⟨168118583909691157516337287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224158111879588210021783049 168118583909691157516337287)
    ·
      refine ⟨252177875864536736274505931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168118583909691157516337287 252177875864536736274505931)
      ·
        refine ⟨378266813796805104411758897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252177875864536736274505931 378266813796805104411758897)
        ·
          refine ⟨283700110347603828308819173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378266813796805104411758897 283700110347603828308819173)
          ·
            refine ⟨53193770690175717807903595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283700110347603828308819173 53193770690175717807903595)
            ·
              refine ⟨79790656035263576711855393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53193770690175717807903595 79790656035263576711855393)
              ·
                refine ⟨59842992026447682533891545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79790656035263576711855393 59842992026447682533891545)
                ·
                  refine ⟨44882244019835761900418659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59842992026447682533891545 44882244019835761900418659)
                  ·
                    refine ⟨67323366029753642850627989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44882244019835761900418659 67323366029753642850627989)
                    ·
                      refine ⟨3155782782644702008623187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67323366029753642850627989 3155782782644702008623187)
                      ·
                        rfl

theorem cell23_6145865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_6145865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145865 prefixEnd_6145865 := by exact prefixLift 6145865
  have htrace : WordTrace (prefixWord ++ tailWord_6145865) baseStart_6145865 baseEnd_6145865 := by
    simpa [prefixWord, tailWord_6145865, baseEnd_6145865] using wordTrace_append hprefix tailTrace_6145865
  have hstable : (prefixWord ++ tailWord_6145865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145865).length < 2 ^ (prefixWord ++ tailWord_6145865).sum := by decide
  have hdescent : baseEnd_6145865 < baseStart_6145865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145869 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6145869 : Nat := 118140960795 + 6145869 * 2 ^ 59
def prefixEnd_6145869 : Nat := 4983230072969 + 3 ^ 40 * 6145869 * 2
def baseEnd_6145869 : Nat := 3155784836567319992973169

theorem tailTrace_6145869 : CollatzResearch.WordTrace tailWord_6145869 prefixEnd_6145869 3155784836567319992973169 := by
  unfold tailWord_6145869
  simp only [CollatzResearch.WordTrace]
  refine ⟨224158257771573718704928661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149438838514382479136619107 224158257771573718704928661)
  ·
    refine ⟨10507418333042518064293531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 224158257771573718704928661 10507418333042518064293531)
    ·
      refine ⟨15761127499563777096440297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10507418333042518064293531 15761127499563777096440297)
      ·
        refine ⟨11820845624672832822330223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15761127499563777096440297 11820845624672832822330223)
        ·
          refine ⟨17731268437009249233495335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11820845624672832822330223 17731268437009249233495335)
          ·
            refine ⟨26596902655513873850243003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17731268437009249233495335 26596902655513873850243003)
            ·
              refine ⟨39895353983270810775364505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26596902655513873850243003 39895353983270810775364505)
              ·
                refine ⟨29921515487453108081523379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39895353983270810775364505 29921515487453108081523379)
                ·
                  refine ⟨44882273231179662122285069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29921515487453108081523379 44882273231179662122285069)
                  ·
                    refine ⟨16830852461692373295856901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44882273231179662122285069 16830852461692373295856901)
                    ·
                      refine ⟨3155784836567319992973169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16830852461692373295856901 3155784836567319992973169)
                      ·
                        rfl

theorem cell23_6145869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6145869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145869 prefixEnd_6145869 := by exact prefixLift 6145869
  have htrace : WordTrace (prefixWord ++ tailWord_6145869) baseStart_6145869 baseEnd_6145869 := by
    simpa [prefixWord, tailWord_6145869, baseEnd_6145869] using wordTrace_append hprefix tailTrace_6145869
  have hstable : (prefixWord ++ tailWord_6145869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145869).length < 2 ^ (prefixWord ++ tailWord_6145869).sum := by decide
  have hdescent : baseEnd_6145869 < baseStart_6145869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145915 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_6145915 : Nat := 118140960795 + 6145915 * 2 ^ 59
def prefixEnd_6145915 : Nat := 4983230072969 + 3 ^ 40 * 6145915 * 2
def baseEnd_6145915 : Nat := 3155808456677426812997957

theorem tailTrace_6145915 : CollatzResearch.WordTrace tailWord_6145915 prefixEnd_6145915 3155808456677426812997957 := by
  unfold tailWord_6145915
  simp only [CollatzResearch.WordTrace]
  refine ⟨224159935529407068561103199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149439957019604712374068799 224159935529407068561103199)
  ·
    refine ⟨336239903294110602841654799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224159935529407068561103199 336239903294110602841654799)
    ·
      refine ⟨504359854941165904262482199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336239903294110602841654799 504359854941165904262482199)
      ·
        refine ⟨756539782411748856393723299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504359854941165904262482199 756539782411748856393723299)
        ·
          refine ⟨1134809673617623284590584949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756539782411748856393723299 1134809673617623284590584949)
          ·
            refine ⟨106388406901652182930367339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1134809673617623284590584949 106388406901652182930367339)
            ·
              refine ⟨159582610352478274395551009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106388406901652182930367339 159582610352478274395551009)
              ·
                refine ⟨119686957764358705796663257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159582610352478274395551009 119686957764358705796663257)
                ·
                  refine ⟨89765218323269029347497443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119686957764358705796663257 89765218323269029347497443)
                  ·
                    refine ⟨134647827484903544021246165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89765218323269029347497443 134647827484903544021246165)
                    ·
                      refine ⟨3155808456677426812997957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134647827484903544021246165 3155808456677426812997957)
                      ·
                        rfl

theorem cell23_6145915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_6145915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145915 prefixEnd_6145915 := by exact prefixLift 6145915
  have htrace : WordTrace (prefixWord ++ tailWord_6145915) baseStart_6145915 baseEnd_6145915 := by
    simpa [prefixWord, tailWord_6145915, baseEnd_6145915] using wordTrace_append hprefix tailTrace_6145915
  have hstable : (prefixWord ++ tailWord_6145915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145915).length < 2 ^ (prefixWord ++ tailWord_6145915).sum := by decide
  have hdescent : baseEnd_6145915 < baseStart_6145915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145929 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 4, 3, 2]
def baseStart_6145929 : Nat := 118140960795 + 6145929 * 2 ^ 59
def prefixEnd_6145929 : Nat := 4983230072969 + 3 ^ 40 * 6145929 * 2
def baseEnd_6145929 : Nat := 3155815645406589758222893

theorem tailTrace_6145929 : CollatzResearch.WordTrace tailWord_6145929 prefixEnd_6145929 3155815645406589758222893 := by
  unfold tailWord_6145929
  simp only [CollatzResearch.WordTrace]
  refine ⟨224160446151356348952112841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149440297434237565968075227 224160446151356348952112841)
  ·
    refine ⟨168120334613517261714084631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224160446151356348952112841 168120334613517261714084631)
    ·
      refine ⟨252180501920275892571126947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168120334613517261714084631 252180501920275892571126947)
      ·
        refine ⟨378270752880413838856690421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252180501920275892571126947 378270752880413838856690421)
        ·
          refine ⟨35462883082538797392814727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 378270752880413838856690421 35462883082538797392814727)
          ·
            refine ⟨53194324623808196089222091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35462883082538797392814727 53194324623808196089222091)
            ·
              refine ⟨79791486935712294133833137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53194324623808196089222091 79791486935712294133833137)
              ·
                refine ⟨59843615201784220600374853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79791486935712294133833137 59843615201784220600374853)
                ·
                  refine ⟨11220677850334541362570285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59843615201784220600374853 11220677850334541362570285)
                  ·
                    refine ⟨4207754193875453010963857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11220677850334541362570285 4207754193875453010963857)
                    ·
                      refine ⟨3155815645406589758222893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207754193875453010963857 3155815645406589758222893)
                      ·
                        rfl

theorem cell23_6145929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 3, 2].length) (baseStart_6145929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145929 prefixEnd_6145929 := by exact prefixLift 6145929
  have htrace : WordTrace (prefixWord ++ tailWord_6145929) baseStart_6145929 baseEnd_6145929 := by
    simpa [prefixWord, tailWord_6145929, baseEnd_6145929] using wordTrace_append hprefix tailTrace_6145929
  have hstable : (prefixWord ++ tailWord_6145929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145929).length < 2 ^ (prefixWord ++ tailWord_6145929).sum := by decide
  have hdescent : baseEnd_6145929 < baseStart_6145929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145946 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2]
def baseStart_6145946 : Nat := 118140960795 + 6145946 * 2 ^ 59
def prefixEnd_6145946 : Nat := 4983230072969 + 3 ^ 40 * 6145946 * 2
def baseEnd_6145946 : Nat := 3155824374577716191710315

theorem tailTrace_6145946 : CollatzResearch.WordTrace tailWord_6145946 prefixEnd_6145946 3155824374577716191710315 := by
  unfold tailWord_6145946
  simp only [CollatzResearch.WordTrace]
  refine ⟨56040266548073690213870423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149440710794863173903654461 56040266548073690213870423)
  ·
    refine ⟨84060399822110535320805635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56040266548073690213870423 84060399822110535320805635)
    ·
      refine ⟨126090599733165802981208453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84060399822110535320805635 126090599733165802981208453)
      ·
        refine ⟨23641987449968588058976585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126090599733165802981208453 23641987449968588058976585)
        ·
          refine ⟨17731490587476441044232439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23641987449968588058976585 17731490587476441044232439)
          ·
            refine ⟨26597235881214661566348659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17731490587476441044232439 26597235881214661566348659)
            ·
              refine ⟨39895853821821992349522989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26597235881214661566348659 39895853821821992349522989)
              ·
                refine ⟨14960945183183247131071121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39895853821821992349522989 14960945183183247131071121)
                ·
                  refine ⟨11220708887387435348303341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14960945183183247131071121 11220708887387435348303341)
                  ·
                    refine ⟨4207765832770288255613753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11220708887387435348303341 4207765832770288255613753)
                    ·
                      refine ⟨3155824374577716191710315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207765832770288255613753 3155824374577716191710315)
                      ·
                        rfl

theorem cell23_6145946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_6145946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145946 prefixEnd_6145946 := by exact prefixLift 6145946
  have htrace : WordTrace (prefixWord ++ tailWord_6145946) baseStart_6145946 baseEnd_6145946 := by
    simpa [prefixWord, tailWord_6145946, baseEnd_6145946] using wordTrace_append hprefix tailTrace_6145946
  have hstable : (prefixWord ++ tailWord_6145946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145946).length < 2 ^ (prefixWord ++ tailWord_6145946).sum := by decide
  have hdescent : baseEnd_6145946 < baseStart_6145946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145956 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 1, 5]
def baseStart_6145956 : Nat := 118140960795 + 6145956 * 2 ^ 59
def prefixEnd_6145956 : Nat := 4983230072969 + 3 ^ 40 * 6145956 * 2
def baseEnd_6145956 : Nat := 1051943169794753717528423

theorem tailTrace_6145956 : CollatzResearch.WordTrace tailWord_6145956 prefixEnd_6145956 1051943169794753717528423 := by
  unfold tailWord_6145956
  simp only [CollatzResearch.WordTrace]
  refine ⟨112080715461129266281672861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149440953948172355042230481 112080715461129266281672861)
  ·
    refine ⟨42030268297923474855627323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112080715461129266281672861 42030268297923474855627323)
    ·
      refine ⟨63045402446885212283440985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42030268297923474855627323 63045402446885212283440985)
      ·
        refine ⟨47284051835163909212580739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63045402446885212283440985 47284051835163909212580739)
        ·
          refine ⟨70926077752745863818871109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47284051835163909212580739 70926077752745863818871109)
          ·
            refine ⟨13298639578639849466038333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70926077752745863818871109 13298639578639849466038333)
            ·
              refine ⟨4986989841989943549764375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13298639578639849466038333 4986989841989943549764375)
              ·
                refine ⟨7480484762984915324646563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986989841989943549764375 7480484762984915324646563)
                ·
                  refine ⟨11220727144477372986969845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480484762984915324646563 11220727144477372986969845)
                  ·
                    refine ⟨1051943169794753717528423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11220727144477372986969845 1051943169794753717528423)
                    ·
                      rfl

theorem cell23_6145956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_6145956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145956 prefixEnd_6145956 := by exact prefixLift 6145956
  have htrace : WordTrace (prefixWord ++ tailWord_6145956) baseStart_6145956 baseEnd_6145956 := by
    simpa [prefixWord, tailWord_6145956, baseEnd_6145956] using wordTrace_append hprefix tailTrace_6145956
  have hstable : (prefixWord ++ tailWord_6145956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145956).length < 2 ^ (prefixWord ++ tailWord_6145956).sum := by decide
  have hdescent : baseEnd_6145956 < baseStart_6145956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145976 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 3, 2, 2]
def baseStart_6145976 : Nat := 118140960795 + 6145976 * 2 ^ 59
def prefixEnd_6145976 : Nat := 4983230072969 + 3 ^ 40 * 6145976 * 2
def baseEnd_6145976 : Nat := 3155839778997351074335177

theorem tailTrace_6145976 : CollatzResearch.WordTrace tailWord_6145976 prefixEnd_6145976 3155839778997351074335177 := by
  unfold tailWord_6145976
  simp only [CollatzResearch.WordTrace]
  refine ⟨112081080191093037989536891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149441440254790717319382521 112081080191093037989536891)
  ·
    refine ⟨168121620286639556984305337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112081080191093037989536891 168121620286639556984305337)
    ·
      refine ⟨126091215214979667738229003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168121620286639556984305337 126091215214979667738229003)
      ·
        refine ⟨189136822822469501607343505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126091215214979667738229003 189136822822469501607343505)
        ·
          refine ⟨141852617116852126205507629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189136822822469501607343505 141852617116852126205507629)
          ·
            refine ⟨53194731418819547327065361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141852617116852126205507629 53194731418819547327065361)
            ·
              refine ⟨39896048564114660495299021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53194731418819547327065361 39896048564114660495299021)
              ·
                refine ⟨14961018211542997685737133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39896048564114660495299021 14961018211542997685737133)
                ·
                  refine ⟨5610381829328624132151425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14961018211542997685737133 5610381829328624132151425)
                  ·
                    refine ⟨4207786371996468099113569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610381829328624132151425 4207786371996468099113569)
                    ·
                      refine ⟨3155839778997351074335177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207786371996468099113569 3155839778997351074335177)
                      ·
                        rfl

theorem cell23_6145976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_6145976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145976 prefixEnd_6145976 := by exact prefixLift 6145976
  have htrace : WordTrace (prefixWord ++ tailWord_6145976) baseStart_6145976 baseEnd_6145976 := by
    simpa [prefixWord, tailWord_6145976, baseEnd_6145976] using wordTrace_append hprefix tailTrace_6145976
  have hstable : (prefixWord ++ tailWord_6145976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145976).length < 2 ^ (prefixWord ++ tailWord_6145976).sum := by decide
  have hdescent : baseEnd_6145976 < baseStart_6145976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146010 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4]
def baseStart_6146010 : Nat := 118140960795 + 6146010 * 2 ^ 59
def prefixEnd_6146010 : Nat := 4983230072969 + 3 ^ 40 * 6146010 * 2
def baseEnd_6146010 : Nat := 3155857237339603941310021

theorem tailTrace_6146010 : CollatzResearch.WordTrace tailWord_6146010 prefixEnd_6146010 3155857237339603941310021 := by
  unfold tailWord_6146010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56040850116015724946452871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149442266976041933190540989 56040850116015724946452871)
  ·
    refine ⟨84061275174023587419679307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56040850116015724946452871 84061275174023587419679307)
    ·
      refine ⟨126091912761035381129518961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84061275174023587419679307 126091912761035381129518961)
      ·
        refine ⟨94568934570776535847139221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126091912761035381129518961 94568934570776535847139221)
        ·
          refine ⟨4432918808005150117834651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94568934570776535847139221 4432918808005150117834651)
          ·
            refine ⟨6649378212007725176751977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432918808005150117834651 6649378212007725176751977)
            ·
              refine ⟨4987033659005793882563983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6649378212007725176751977 4987033659005793882563983)
              ·
                refine ⟨7480550488508690823845975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987033659005793882563983 7480550488508690823845975)
                ·
                  refine ⟨11220825732763036235768963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480550488508690823845975 11220825732763036235768963)
                  ·
                    refine ⟨16831238599144554353653445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11220825732763036235768963 16831238599144554353653445)
                    ·
                      refine ⟨3155857237339603941310021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16831238599144554353653445 3155857237339603941310021)
                      ·
                        rfl

theorem cell23_6146010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_6146010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146010 prefixEnd_6146010 := by exact prefixLift 6146010
  have htrace : WordTrace (prefixWord ++ tailWord_6146010) baseStart_6146010 baseEnd_6146010 := by
    simpa [prefixWord, tailWord_6146010, baseEnd_6146010] using wordTrace_append hprefix tailTrace_6146010
  have hstable : (prefixWord ++ tailWord_6146010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146010).length < 2 ^ (prefixWord ++ tailWord_6146010).sum := by decide
  have hdescent : baseEnd_6146010 < baseStart_6146010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146013 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 3]
def baseStart_6146013 : Nat := 118140960795 + 6146013 * 2 ^ 59
def prefixEnd_6146013 : Nat := 4983230072969 + 3 ^ 40 * 6146013 * 2
def baseEnd_6146013 : Nat := 3155858777781567429572507

theorem tailTrace_6146013 : CollatzResearch.WordTrace tailWord_6146013 prefixEnd_6146013 3155858777781567429572507 := by
  unfold tailWord_6146013
  simp only [CollatzResearch.WordTrace]
  refine ⟨224163509883052031298170693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149442339922034687532113795 224163509883052031298170693)
  ·
    refine ⟨42030658103072255868407005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224163509883052031298170693 42030658103072255868407005)
    ·
      refine ⟨15761496788652095950652627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42030658103072255868407005 15761496788652095950652627)
      ·
        refine ⟨23642245182978143925978941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15761496788652095950652627 23642245182978143925978941)
        ·
          refine ⟨8865841943616803972242103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23642245182978143925978941 8865841943616803972242103)
          ·
            refine ⟨13298762915425205958363155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8865841943616803972242103 13298762915425205958363155)
            ·
              refine ⟨19948144373137808937544733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13298762915425205958363155 19948144373137808937544733)
              ·
                refine ⟨7480554139926678351579275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19948144373137808937544733 7480554139926678351579275)
                ·
                  refine ⟨11220831209890017527368913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480554139926678351579275 11220831209890017527368913)
                  ·
                    refine ⟨8415623407417513145526685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11220831209890017527368913 8415623407417513145526685)
                    ·
                      refine ⟨3155858777781567429572507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8415623407417513145526685 3155858777781567429572507)
                      ·
                        rfl

theorem cell23_6146013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_6146013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146013 prefixEnd_6146013 := by exact prefixLift 6146013
  have htrace : WordTrace (prefixWord ++ tailWord_6146013) baseStart_6146013 baseEnd_6146013 := by
    simpa [prefixWord, tailWord_6146013, baseEnd_6146013] using wordTrace_append hprefix tailTrace_6146013
  have hstable : (prefixWord ++ tailWord_6146013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146013).length < 2 ^ (prefixWord ++ tailWord_6146013).sum := by decide
  have hdescent : baseEnd_6146013 < baseStart_6146013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146026 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_6146026 : Nat := 118140960795 + 6146026 * 2 ^ 59
def prefixEnd_6146026 : Nat := 4983230072969 + 3 ^ 40 * 6146026 * 2
def baseEnd_6146026 : Nat := 3155865453030075878709947

theorem tailTrace_6146026 : CollatzResearch.WordTrace tailWord_6146026 prefixEnd_6146026 3155865453030075878709947 := by
  unfold tailWord_6146026
  simp only [CollatzResearch.WordTrace]
  refine ⟨56040996008001233629598483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149442656021336623012262621 56040996008001233629598483)
  ·
    refine ⟨84061494012001850444397725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56040996008001233629598483 84061494012001850444397725)
    ·
      refine ⟨31523060254500693916649147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84061494012001850444397725 31523060254500693916649147)
      ·
        refine ⟨47284590381751040874973721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31523060254500693916649147 47284590381751040874973721)
        ·
          refine ⟨35463442786313280656230291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47284590381751040874973721 35463442786313280656230291)
          ·
            refine ⟨53195164179469920984345437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35463442786313280656230291 53195164179469920984345437)
            ·
              refine ⟨19948186567301220369129539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53195164179469920984345437 19948186567301220369129539)
              ·
                refine ⟨29922279850951830553694309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19948186567301220369129539 29922279850951830553694309)
                ·
                  refine ⟨5610427472053468228817683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29922279850951830553694309 5610427472053468228817683)
                  ·
                    refine ⟨8415641208080202343226525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5610427472053468228817683 8415641208080202343226525)
                    ·
                      refine ⟨3155865453030075878709947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8415641208080202343226525 3155865453030075878709947)
                      ·
                        rfl

theorem cell23_6146026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_6146026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146026 prefixEnd_6146026 := by exact prefixLift 6146026
  have htrace : WordTrace (prefixWord ++ tailWord_6146026) baseStart_6146026 baseEnd_6146026 := by
    simpa [prefixWord, tailWord_6146026, baseEnd_6146026] using wordTrace_append hprefix tailTrace_6146026
  have hstable : (prefixWord ++ tailWord_6146026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146026).length < 2 ^ (prefixWord ++ tailWord_6146026).sum := by decide
  have hdescent : baseEnd_6146026 < baseStart_6146026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146032 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_6146032 : Nat := 118140960795 + 6146032 * 2 ^ 59
def prefixEnd_6146032 : Nat := 4983230072969 + 3 ^ 40 * 6146032 * 2
def baseEnd_6146032 : Nat := 3155868533914002855234919

theorem tailTrace_6146032 : CollatzResearch.WordTrace tailWord_6146032 prefixEnd_6146032 3155868533914002855234919 := by
  unfold tailWord_6146032
  simp only [CollatzResearch.WordTrace]
  refine ⟨112082101434991598771556175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149442801913322131695408233 112082101434991598771556175)
  ·
    refine ⟨168123152152487398157334263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112082101434991598771556175 168123152152487398157334263)
    ·
      refine ⟨252184728228731097236001395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168123152152487398157334263 252184728228731097236001395)
      ·
        refine ⟨378277092343096645854002093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252184728228731097236001395 378277092343096645854002093)
        ·
          refine ⟨141853909628661242195250785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378277092343096645854002093 141853909628661242195250785)
          ·
            refine ⟨106390432221495931646438089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141853909628661242195250785 106390432221495931646438089)
            ·
              refine ⟨79792824166121948734828567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106390432221495931646438089 79792824166121948734828567)
              ·
                refine ⟨119689236249182923102242851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79792824166121948734828567 119689236249182923102242851)
                ·
                  refine ⟨179533854373774384653364277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119689236249182923102242851 179533854373774384653364277)
                  ·
                    refine ⟨16831298847541348561252901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179533854373774384653364277 16831298847541348561252901)
                    ·
                      refine ⟨3155868533914002855234919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16831298847541348561252901 3155868533914002855234919)
                      ·
                        rfl

theorem cell23_6146032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_6146032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146032 prefixEnd_6146032 := by exact prefixLift 6146032
  have htrace : WordTrace (prefixWord ++ tailWord_6146032) baseStart_6146032 baseEnd_6146032 := by
    simpa [prefixWord, tailWord_6146032, baseEnd_6146032] using wordTrace_append hprefix tailTrace_6146032
  have hstable : (prefixWord ++ tailWord_6146032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146032).length < 2 ^ (prefixWord ++ tailWord_6146032).sum := by decide
  have hdescent : baseEnd_6146032 < baseStart_6146032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146053 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 1, 3, 2]
def baseStart_6146053 : Nat := 118140960795 + 6146053 * 2 ^ 59
def prefixEnd_6146053 : Nat := 4983230072969 + 3 ^ 40 * 6146053 * 2
def baseEnd_6146053 : Nat := 3155879317007747273072323

theorem tailTrace_6146053 : CollatzResearch.WordTrace tailWord_6146053 prefixEnd_6146053 3155879317007747273072323 := by
  unfold tailWord_6146053
  simp only [CollatzResearch.WordTrace]
  refine ⟨224164968802907118129626813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149443312535271412086417875 224164968802907118129626813)
  ·
    refine ⟨84061863301090169298610055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224164968802907118129626813 84061863301090169298610055)
    ·
      refine ⟨126092794951635253947915083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84061863301090169298610055 126092794951635253947915083)
      ·
        refine ⟨189139192427452880921872625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126092794951635253947915083 189139192427452880921872625)
        ·
          refine ⟨141854394320589660691404469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189139192427452880921872625 141854394320589660691404469)
          ·
            refine ⟨13298849467555280689819169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141854394320589660691404469 13298849467555280689819169)
            ·
              refine ⟨9974137100666460517364377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13298849467555280689819169 9974137100666460517364377)
              ·
                refine ⟨7480602825499845388023283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974137100666460517364377 7480602825499845388023283)
                ·
                  refine ⟨11220904238249768082034925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480602825499845388023283 11220904238249768082034925)
                  ·
                    refine ⟨4207839089343663030763097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11220904238249768082034925 4207839089343663030763097)
                    ·
                      refine ⟨3155879317007747273072323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207839089343663030763097 3155879317007747273072323)
                      ·
                        rfl

theorem cell23_6146053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_6146053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146053 prefixEnd_6146053 := by exact prefixLift 6146053
  have htrace : WordTrace (prefixWord ++ tailWord_6146053) baseStart_6146053 baseEnd_6146053 := by
    simpa [prefixWord, tailWord_6146053, baseEnd_6146053] using wordTrace_append hprefix tailTrace_6146053
  have hstable : (prefixWord ++ tailWord_6146053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146053).length < 2 ^ (prefixWord ++ tailWord_6146053).sum := by decide
  have hdescent : baseEnd_6146053 < baseStart_6146053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146083 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 2, 2, 2]
def baseStart_6146083 : Nat := 118140960795 + 6146083 * 2 ^ 59
def prefixEnd_6146083 : Nat := 4983230072969 + 3 ^ 40 * 6146083 * 2
def baseEnd_6146083 : Nat := 3155894721427382155697185

theorem tailTrace_6146083 : CollatzResearch.WordTrace tailWord_6146083 prefixEnd_6146083 3155894721427382155697185 := by
  unfold tailWord_6146083
  simp only [CollatzResearch.WordTrace]
  refine ⟨224166062992798433253218903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149444041995198955502145935 224166062992798433253218903)
  ·
    refine ⟨336249094489197649879828355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224166062992798433253218903 336249094489197649879828355)
    ·
      refine ⟨504373641733796474819742533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336249094489197649879828355 504373641733796474819742533)
      ·
        refine ⟨94570057825086839028701725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 504373641733796474819742533 94570057825086839028701725)
        ·
          refine ⟨35463771684407564635763147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94570057825086839028701725 35463771684407564635763147)
          ·
            refine ⟨53195657526611346953644721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35463771684407564635763147 53195657526611346953644721)
            ·
              refine ⟨39896743144958510215233541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53195657526611346953644721 39896743144958510215233541)
              ·
                refine ⟨7480639339679720665356289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39896743144958510215233541 7480639339679720665356289)
                ·
                  refine ⟨5610479504759790499017217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7480639339679720665356289 5610479504759790499017217)
                  ·
                    refine ⟨4207859628569842874262913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610479504759790499017217 4207859628569842874262913)
                    ·
                      refine ⟨3155894721427382155697185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207859628569842874262913 3155894721427382155697185)
                      ·
                        rfl

theorem cell23_6146083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_6146083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146083 prefixEnd_6146083 := by exact prefixLift 6146083
  have htrace : WordTrace (prefixWord ++ tailWord_6146083) baseStart_6146083 baseEnd_6146083 := by
    simpa [prefixWord, tailWord_6146083, baseEnd_6146083] using wordTrace_append hprefix tailTrace_6146083
  have hstable : (prefixWord ++ tailWord_6146083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146083).length < 2 ^ (prefixWord ++ tailWord_6146083).sum := by decide
  have hdescent : baseEnd_6146083 < baseStart_6146083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146092 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_6146092 : Nat := 118140960795 + 6146092 * 2 ^ 59
def prefixEnd_6146092 : Nat := 4983230072969 + 3 ^ 40 * 6146092 * 2
def baseEnd_6146092 : Nat := 3155899342753272620484643

theorem tailTrace_6146092 : CollatzResearch.WordTrace tailWord_6146092 prefixEnd_6146092 3155899342753272620484643 := by
  unfold tailWord_6146092
  simp only [CollatzResearch.WordTrace]
  refine ⟨112083195624882913895148265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149444260833177218526864353 112083195624882913895148265)
  ·
    refine ⟨84062396718662185421361199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112083195624882913895148265 84062396718662185421361199)
    ·
      refine ⟨126093595077993278132041799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84062396718662185421361199 126093595077993278132041799)
      ·
        refine ⟨189140392616989917198062699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126093595077993278132041799 189140392616989917198062699)
        ·
          refine ⟨283710588925484875797094049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189140392616989917198062699 283710588925484875797094049)
          ·
            refine ⟨212782941694113656847820537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283710588925484875797094049 212782941694113656847820537)
            ·
              refine ⟨159587206270585242635865403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212782941694113656847820537 159587206270585242635865403)
              ·
                refine ⟨239380809405877863953798105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159587206270585242635865403 239380809405877863953798105)
                ·
                  refine ⟨179535607054408397965348579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239380809405877863953798105 179535607054408397965348579)
                  ·
                    refine ⟨269303410581612596948022869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179535607054408397965348579 269303410581612596948022869)
                    ·
                      refine ⟨3155899342753272620484643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 269303410581612596948022869 3155899342753272620484643)
                      ·
                        rfl

theorem cell23_6146092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_6146092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146092 prefixEnd_6146092 := by exact prefixLift 6146092
  have htrace : WordTrace (prefixWord ++ tailWord_6146092) baseStart_6146092 baseEnd_6146092 := by
    simpa [prefixWord, tailWord_6146092, baseEnd_6146092] using wordTrace_append hprefix tailTrace_6146092
  have hstable : (prefixWord ++ tailWord_6146092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146092).length < 2 ^ (prefixWord ++ tailWord_6146092).sum := by decide
  have hdescent : baseEnd_6146092 < baseStart_6146092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146099 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 3]
def baseStart_6146099 : Nat := 118140960795 + 6146099 * 2 ^ 59
def prefixEnd_6146099 : Nat := 4983230072969 + 3 ^ 40 * 6146099 * 2
def baseEnd_6146099 : Nat := 3155902937117854093097111

theorem tailTrace_6146099 : CollatzResearch.WordTrace tailWord_6146099 prefixEnd_6146099 3155902937117854093097111 := by
  unfold tailWord_6146099
  simp only [CollatzResearch.WordTrace]
  refine ⟨224166646560740467985801351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149444431040493645323867567 224166646560740467985801351)
  ·
    refine ⟨336249969841110701978702027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224166646560740467985801351 336249969841110701978702027)
    ·
      refine ⟨504374954761666052968053041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336249969841110701978702027 504374954761666052968053041)
      ·
        refine ⟨378281216071249539726039781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504374954761666052968053041 378281216071249539726039781)
        ·
          refine ⟨70927728013359288698632459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378281216071249539726039781 70927728013359288698632459)
          ·
            refine ⟨106391592020038933047948689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70927728013359288698632459 106391592020038933047948689)
            ·
              refine ⟨79793694015029199785961517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106391592020038933047948689 79793694015029199785961517)
              ·
                refine ⟨29922635255635949919735569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79793694015029199785961517 29922635255635949919735569)
                ·
                  refine ⟨22441976441726962439801677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29922635255635949919735569 22441976441726962439801677)
                  ·
                    refine ⟨8415741165647610914925629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22441976441726962439801677 8415741165647610914925629)
                    ·
                      refine ⟨3155902937117854093097111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8415741165647610914925629 3155902937117854093097111)
                      ·
                        rfl

theorem cell23_6146099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_6146099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146099 prefixEnd_6146099 := by exact prefixLift 6146099
  have htrace : WordTrace (prefixWord ++ tailWord_6146099) baseStart_6146099 baseEnd_6146099 := by
    simpa [prefixWord, tailWord_6146099, baseEnd_6146099] using wordTrace_append hprefix tailTrace_6146099
  have hstable : (prefixWord ++ tailWord_6146099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146099).length < 2 ^ (prefixWord ++ tailWord_6146099).sum := by decide
  have hdescent : baseEnd_6146099 < baseStart_6146099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146134 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6146134 : Nat := 118140960795 + 6146134 * 2 ^ 59
def prefixEnd_6146134 : Nat := 4983230072969 + 3 ^ 40 * 6146134 * 2
def baseEnd_6146134 : Nat := 3155920908940761456159451

theorem tailTrace_6146134 : CollatzResearch.WordTrace tailWord_6146134 prefixEnd_6146134 3155920908940761456159451 := by
  unfold tailWord_6146134
  simp only [CollatzResearch.WordTrace]
  refine ⟨14010495194725854310207841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149445282077075779308883637 14010495194725854310207841)
  ·
    refine ⟨10507871396044390732655881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14010495194725854310207841 10507871396044390732655881)
    ·
      refine ⟨7880903547033293049491911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10507871396044390732655881 7880903547033293049491911)
      ·
        refine ⟨11821355320549939574237867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7880903547033293049491911 11821355320549939574237867)
        ·
          refine ⟨17732032980824909361356801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11821355320549939574237867 17732032980824909361356801)
          ·
            refine ⟨13299024735618682021017601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17732032980824909361356801 13299024735618682021017601)
            ·
              refine ⟨9974268551714011515763201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13299024735618682021017601 9974268551714011515763201)
              ·
                refine ⟨7480701413785508636822401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974268551714011515763201 7480701413785508636822401)
                ·
                  refine ⟨5610526060339131477616801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7480701413785508636822401 5610526060339131477616801)
                  ·
                    refine ⟨4207894545254348608212601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610526060339131477616801 4207894545254348608212601)
                    ·
                      refine ⟨3155920908940761456159451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207894545254348608212601 3155920908940761456159451)
                      ·
                        rfl

theorem cell23_6146134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6146134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146134 prefixEnd_6146134 := by exact prefixLift 6146134
  have htrace : WordTrace (prefixWord ++ tailWord_6146134) baseStart_6146134 baseEnd_6146134 := by
    simpa [prefixWord, tailWord_6146134, baseEnd_6146134] using wordTrace_append hprefix tailTrace_6146134
  have hstable : (prefixWord ++ tailWord_6146134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146134).length < 2 ^ (prefixWord ++ tailWord_6146134).sum := by decide
  have hdescent : baseEnd_6146134 < baseStart_6146134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146140 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 5]
def baseStart_6146140 : Nat := 118140960795 + 6146140 * 2 ^ 59
def prefixEnd_6146140 : Nat := 4983230072969 + 3 ^ 40 * 6146140 * 2
def baseEnd_6146140 : Nat := 350658221091632048076047

theorem tailTrace_6146140 : CollatzResearch.WordTrace tailWord_6146140 prefixEnd_6146140 350658221091632048076047 := by
  unfold tailWord_6146140
  simp only [CollatzResearch.WordTrace]
  refine ⟨112084070976795965994021937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149445427969061287992029249 112084070976795965994021937)
  ·
    refine ⟨84063053232596974495516453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112084070976795965994021937 84063053232596974495516453)
    ·
      refine ⟨15761822481111932717909335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84063053232596974495516453 15761822481111932717909335)
      ·
        refine ⟨23642733721667899076864003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15761822481111932717909335 23642733721667899076864003)
        ·
          refine ⟨35464100582501848615296005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23642733721667899076864003 35464100582501848615296005)
          ·
            refine ⟨6649518859219096615368001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35464100582501848615296005 6649518859219096615368001)
            ·
              refine ⟨4987139144414322461526001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6649518859219096615368001 4987139144414322461526001)
              ·
                refine ⟨3740354358310741846144501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987139144414322461526001 3740354358310741846144501)
                ·
                  refine ⟨350658221091632048076047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3740354358310741846144501 350658221091632048076047)
                  ·
                    rfl

theorem cell23_6146140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 5].length) (baseStart_6146140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146140 prefixEnd_6146140 := by exact prefixLift 6146140
  have htrace : WordTrace (prefixWord ++ tailWord_6146140) baseStart_6146140 baseEnd_6146140 := by
    simpa [prefixWord, tailWord_6146140, baseEnd_6146140] using wordTrace_append hprefix tailTrace_6146140
  have hstable : (prefixWord ++ tailWord_6146140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146140).length < 2 ^ (prefixWord ++ tailWord_6146140).sum := by decide
  have hdescent : baseEnd_6146140 < baseStart_6146140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146156 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 6, 2]
def baseStart_6146156 : Nat := 118140960795 + 6146156 * 2 ^ 59
def prefixEnd_6146156 : Nat := 4983230072969 + 3 ^ 40 * 6146156 * 2
def baseEnd_6146156 : Nat := 3155932205515160370084349

theorem tailTrace_6146156 : CollatzResearch.WordTrace tailWord_6146156 prefixEnd_6146156 3155932205515160370084349 := by
  unfold tailWord_6146156
  simp only [CollatzResearch.WordTrace]
  refine ⟨112084362760766983360313161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149445817014355977813750881 112084362760766983360313161)
  ·
    refine ⟨84063272070575237520234871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112084362760766983360313161 84063272070575237520234871)
    ·
      refine ⟨126094908105862856280352307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84063272070575237520234871 126094908105862856280352307)
      ·
        refine ⟨189142362158794284420528461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126094908105862856280352307 189142362158794284420528461)
        ·
          refine ⟨70928385809547856657698173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189142362158794284420528461 70928385809547856657698173)
          ·
            refine ⟨26598144678580446246636815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70928385809547856657698173 26598144678580446246636815)
            ·
              refine ⟨39897217017870669369955223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26598144678580446246636815 39897217017870669369955223)
              ·
                refine ⟨59845825526806004054932835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39897217017870669369955223 59845825526806004054932835)
                ·
                  refine ⟨89768738290209006082399253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59845825526806004054932835 89768738290209006082399253)
                  ·
                    refine ⟨4207909607353547160112465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89768738290209006082399253 4207909607353547160112465)
                    ·
                      refine ⟨3155932205515160370084349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207909607353547160112465 3155932205515160370084349)
                      ·
                        rfl

theorem cell23_6146156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_6146156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146156 prefixEnd_6146156 := by exact prefixLift 6146156
  have htrace : WordTrace (prefixWord ++ tailWord_6146156) baseStart_6146156 baseEnd_6146156 := by
    simpa [prefixWord, tailWord_6146156, baseEnd_6146156] using wordTrace_append hprefix tailTrace_6146156
  have hstable : (prefixWord ++ tailWord_6146156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146156).length < 2 ^ (prefixWord ++ tailWord_6146156).sum := by decide
  have hdescent : baseEnd_6146156 < baseStart_6146156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146173 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 4]
def baseStart_6146173 : Nat := 118140960795 + 6146173 * 2 ^ 59
def prefixEnd_6146173 : Nat := 4983230072969 + 3 ^ 40 * 6146173 * 2
def baseEnd_6146173 : Nat := 3155940934686286803571771

theorem tailTrace_6146173 : CollatzResearch.WordTrace tailWord_6146173 prefixEnd_6146173 3155940934686286803571771 := by
  unfold tailWord_6146173
  simp only [CollatzResearch.WordTrace]
  refine ⟨224169345562472378623995173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149446230374981585749330115 224169345562472378623995173)
  ·
    refine ⟨42031752292963570991999095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224169345562472378623995173 42031752292963570991999095)
    ·
      refine ⟨63047628439445356487998643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42031752292963570991999095 63047628439445356487998643)
      ·
        refine ⟨94571442659168034731997965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63047628439445356487998643 94571442659168034731997965)
        ·
          refine ⟨35464290997188013024499237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94571442659168034731997965 35464290997188013024499237)
          ·
            refine ⟨6649554561972752442093607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35464290997188013024499237 6649554561972752442093607)
            ·
              refine ⟨9974331842959128663140411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649554561972752442093607 9974331842959128663140411)
              ·
                refine ⟨14961497764438692994710617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9974331842959128663140411 14961497764438692994710617)
                ·
                  refine ⟨11221123323329019746032963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14961497764438692994710617 11221123323329019746032963)
                  ·
                    refine ⟨16831684984993529619049445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11221123323329019746032963 16831684984993529619049445)
                    ·
                      refine ⟨3155940934686286803571771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16831684984993529619049445 3155940934686286803571771)
                      ·
                        rfl

theorem cell23_6146173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_6146173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146173 prefixEnd_6146173 := by exact prefixLift 6146173
  have htrace : WordTrace (prefixWord ++ tailWord_6146173) baseStart_6146173 baseEnd_6146173 := by
    simpa [prefixWord, tailWord_6146173, baseEnd_6146173] using wordTrace_append hprefix tailTrace_6146173
  have hstable : (prefixWord ++ tailWord_6146173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146173).length < 2 ^ (prefixWord ++ tailWord_6146173).sum := by decide
  have hdescent : baseEnd_6146173 < baseStart_6146173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146183 : List Nat := [1, 1, 4, 2, 1, 1, 3, 5, 1, 4]
def baseStart_6146183 : Nat := 118140960795 + 6146183 * 2 ^ 59
def prefixEnd_6146183 : Nat := 4983230072969 + 3 ^ 40 * 6146183 * 2
def baseEnd_6146183 : Nat := 1051982023164277254815575

theorem tailTrace_6146183 : CollatzResearch.WordTrace tailWord_6146183 prefixEnd_6146183 1051982023164277254815575 := by
  unfold tailWord_6146183
  simp only [CollatzResearch.WordTrace]
  refine ⟨224169710292436150331859203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149446473528290766887906135 224169710292436150331859203)
  ·
    refine ⟨336254565438654225497788805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224169710292436150331859203 336254565438654225497788805)
    ·
      refine ⟨63047731019747667280835401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336254565438654225497788805 63047731019747667280835401)
      ·
        refine ⟨47285798264810750460626551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63047731019747667280835401 47285798264810750460626551)
        ·
          refine ⟨70928697397216125690939827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47285798264810750460626551 70928697397216125690939827)
          ·
            refine ⟨106393046095824188536409741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70928697397216125690939827 106393046095824188536409741)
            ·
              refine ⟨39897392285934070701153653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106393046095824188536409741 39897392285934070701153653)
              ·
                refine ⟨3740380526806319128233155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39897392285934070701153653 3740380526806319128233155)
                ·
                  refine ⟨5610570790209478692349733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740380526806319128233155 5610570790209478692349733)
                  ·
                    refine ⟨1051982023164277254815575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610570790209478692349733 1051982023164277254815575)
                    ·
                      rfl

theorem cell23_6146183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_6146183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146183 prefixEnd_6146183 := by exact prefixLift 6146183
  have htrace : WordTrace (prefixWord ++ tailWord_6146183) baseStart_6146183 baseEnd_6146183 := by
    simpa [prefixWord, tailWord_6146183, baseEnd_6146183] using wordTrace_append hprefix tailTrace_6146183
  have hstable : (prefixWord ++ tailWord_6146183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146183).length < 2 ^ (prefixWord ++ tailWord_6146183).sum := by decide
  have hdescent : baseEnd_6146183 < baseStart_6146183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146233 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 2, 3, 2]
def baseStart_6146233 : Nat := 118140960795 + 6146233 * 2 ^ 59
def prefixEnd_6146233 : Nat := 4983230072969 + 3 ^ 40 * 6146233 * 2
def baseEnd_6146233 : Nat := 3155971743525556568821495

theorem tailTrace_6146233 : CollatzResearch.WordTrace tailWord_6146233 prefixEnd_6146233 3155971743525556568821495 := by
  unfold tailWord_6146233
  simp only [CollatzResearch.WordTrace]
  refine ⟨224171533942255008871179353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149447689294836672580786235 224171533942255008871179353)
  ·
    refine ⟨168128650456691256653384515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224171533942255008871179353 168128650456691256653384515)
    ·
      refine ⟨252192975685036884980076773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168128650456691256653384515 252192975685036884980076773)
      ·
        refine ⟨47286182940944415933764395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252192975685036884980076773 47286182940944415933764395)
        ·
          refine ⟨70929274411416623900646593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47286182940944415933764395 70929274411416623900646593)
          ·
            refine ⟨53196955808562467925484945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70929274411416623900646593 53196955808562467925484945)
            ·
              refine ⟨39897716856421850944113709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53196955808562467925484945 39897716856421850944113709)
              ·
                refine ⟨14961643821158194104042641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39897716856421850944113709 14961643821158194104042641)
                ·
                  refine ⟨11221232865868645578031981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14961643821158194104042641 11221232865868645578031981)
                  ·
                    refine ⟨4207962324700742091761993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11221232865868645578031981 4207962324700742091761993)
                    ·
                      refine ⟨3155971743525556568821495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207962324700742091761993 3155971743525556568821495)
                      ·
                        rfl

theorem cell23_6146233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_6146233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146233 prefixEnd_6146233 := by exact prefixLift 6146233
  have htrace : WordTrace (prefixWord ++ tailWord_6146233) baseStart_6146233 baseEnd_6146233 := by
    simpa [prefixWord, tailWord_6146233, baseEnd_6146233] using wordTrace_append hprefix tailTrace_6146233
  have hstable : (prefixWord ++ tailWord_6146233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146233).length < 2 ^ (prefixWord ++ tailWord_6146233).sum := by decide
  have hdescent : baseEnd_6146233 < baseStart_6146233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146239 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 3, 6]
def baseStart_6146239 : Nat := 118140960795 + 6146239 * 2 ^ 59
def prefixEnd_6146239 : Nat := 4983230072969 + 3 ^ 40 * 6146239 * 2
def baseEnd_6146239 : Nat := 1051991608136494515115489

theorem tailTrace_6146239 : CollatzResearch.WordTrace tailWord_6146239 prefixEnd_6146239 1051991608136494515115489 := by
  unfold tailWord_6146239
  simp only [CollatzResearch.WordTrace]
  refine ⟨224171752780233271895897771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149447835186822181263931847 224171752780233271895897771)
  ·
    refine ⟨336257629170349907843846657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224171752780233271895897771 336257629170349907843846657)
    ·
      refine ⟨252193221877762430882884993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336257629170349907843846657 252193221877762430882884993)
      ·
        refine ⟨189144916408321823162163745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252193221877762430882884993 189144916408321823162163745)
        ·
          refine ⟨141858687306241367371622809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189144916408321823162163745 141858687306241367371622809)
          ·
            refine ⟨106394015479681025528717107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141858687306241367371622809 106394015479681025528717107)
            ·
              refine ⟨159591023219521538293075661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106394015479681025528717107 159591023219521538293075661)
              ·
                refine ⟨59846633707320576859903373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159591023219521538293075661 59846633707320576859903373)
                ·
                  refine ⟨22442487640245216322463765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59846633707320576859903373 22442487640245216322463765)
                  ·
                    refine ⟨1051991608136494515115489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22442487640245216322463765 1051991608136494515115489)
                    ·
                      rfl

theorem cell23_6146239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_6146239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146239 prefixEnd_6146239 := by exact prefixLift 6146239
  have htrace : WordTrace (prefixWord ++ tailWord_6146239) baseStart_6146239 baseEnd_6146239 := by
    simpa [prefixWord, tailWord_6146239, baseEnd_6146239] using wordTrace_append hprefix tailTrace_6146239
  have hstable : (prefixWord ++ tailWord_6146239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146239).length < 2 ^ (prefixWord ++ tailWord_6146239).sum := by decide
  have hdescent : baseEnd_6146239 < baseStart_6146239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146259 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4]
def baseStart_6146259 : Nat := 118140960795 + 6146259 * 2 ^ 59
def prefixEnd_6146259 : Nat := 4983230072969 + 3 ^ 40 * 6146259 * 2
def baseEnd_6146259 : Nat := 3155985094022573467096375

theorem tailTrace_6146259 : CollatzResearch.WordTrace tailWord_6146259 prefixEnd_6146259 3155985094022573467096375 := by
  unfold tailWord_6146259
  simp only [CollatzResearch.WordTrace]
  refine ⟨224172482240160815311625831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149448321493440543541083887 224172482240160815311625831)
  ·
    refine ⟨336258723360241222967438747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224172482240160815311625831 336258723360241222967438747)
    ·
      refine ⟨504388085040361834451158121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336258723360241222967438747 504388085040361834451158121)
      ·
        refine ⟨378291063780271375838368591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504388085040361834451158121 378291063780271375838368591)
        ·
          refine ⟨567436595670407063757552887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378291063780271375838368591 567436595670407063757552887)
          ·
            refine ⟨851154893505610595636329331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567436595670407063757552887 851154893505610595636329331)
            ·
              refine ⟨1276732340258415893454493997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851154893505610595636329331 1276732340258415893454493997)
              ·
                refine ⟨478774627596905960045435249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1276732340258415893454493997 478774627596905960045435249)
                ·
                  refine ⟨359080970697679470034076437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478774627596905960045435249 359080970697679470034076437)
                  ·
                    refine ⟨16831920501453725157847333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 359080970697679470034076437 16831920501453725157847333)
                    ·
                      refine ⟨3155985094022573467096375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16831920501453725157847333 3155985094022573467096375)
                      ·
                        rfl

theorem cell23_6146259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_6146259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146259 prefixEnd_6146259 := by exact prefixLift 6146259
  have htrace : WordTrace (prefixWord ++ tailWord_6146259) baseStart_6146259 baseEnd_6146259 := by
    simpa [prefixWord, tailWord_6146259, baseEnd_6146259] using wordTrace_append hprefix tailTrace_6146259
  have hstable : (prefixWord ++ tailWord_6146259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146259).length < 2 ^ (prefixWord ++ tailWord_6146259).sum := by decide
  have hdescent : baseEnd_6146259 < baseStart_6146259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146266 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_6146266 : Nat := 118140960795 + 6146266 * 2 ^ 59
def prefixEnd_6146266 : Nat := 4983230072969 + 3 ^ 40 * 6146266 * 2
def baseEnd_6146266 : Nat := 3155988688387154939708843

theorem tailTrace_6146266 : CollatzResearch.WordTrace tailWord_6146266 prefixEnd_6146266 3155988688387154939708843 := by
  unfold tailWord_6146266
  simp only [CollatzResearch.WordTrace]
  refine ⟨56043184387783863876782663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149448491700756970338087101 56043184387783863876782663)
  ·
    refine ⟨84064776581675795815173995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56043184387783863876782663 84064776581675795815173995)
    ·
      refine ⟨126097164872513693722760993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84064776581675795815173995 126097164872513693722760993)
      ·
        refine ⟨94572873654385270292070745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126097164872513693722760993 94572873654385270292070745)
        ·
          refine ⟨70929655240788952719053059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94572873654385270292070745 70929655240788952719053059)
          ·
            refine ⟨106394482861183429078579589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70929655240788952719053059 106394482861183429078579589)
            ·
              refine ⟨19948965536471892952233673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106394482861183429078579589 19948965536471892952233673)
              ·
                refine ⟨14961724152353919714175255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19948965536471892952233673 14961724152353919714175255)
                ·
                  refine ⟨22442586228530879571262883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14961724152353919714175255 22442586228530879571262883)
                  ·
                    refine ⟨33663879342796319356894325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22442586228530879571262883 33663879342796319356894325)
                    ·
                      refine ⟨3155988688387154939708843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33663879342796319356894325 3155988688387154939708843)
                      ·
                        rfl

theorem cell23_6146266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_6146266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146266 prefixEnd_6146266 := by exact prefixLift 6146266
  have htrace : WordTrace (prefixWord ++ tailWord_6146266) baseStart_6146266 baseEnd_6146266 := by
    simpa [prefixWord, tailWord_6146266, baseEnd_6146266] using wordTrace_append hprefix tailTrace_6146266
  have hstable : (prefixWord ++ tailWord_6146266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146266).length < 2 ^ (prefixWord ++ tailWord_6146266).sum := by decide
  have hdescent : baseEnd_6146266 < baseStart_6146266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146273 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 2, 4]
def baseStart_6146273 : Nat := 118140960795 + 6146273 * 2 ^ 59
def prefixEnd_6146273 : Nat := 4983230072969 + 3 ^ 40 * 6146273 * 2
def baseEnd_6146273 : Nat := 1051997427583912137440437

theorem tailTrace_6146273 : CollatzResearch.WordTrace tailWord_6146273 prefixEnd_6146273 1051997427583912137440437 := by
  unfold tailWord_6146273
  simp only [CollatzResearch.WordTrace]
  refine ⟨224172992862110095702635473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149448661908073397135090315 224172992862110095702635473)
  ·
    refine ⟨168129744646582571776976605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224172992862110095702635473 168129744646582571776976605)
    ·
      refine ⟨63048654242468464416366227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168129744646582571776976605 63048654242468464416366227)
      ·
        refine ⟨94572981363702696624549341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63048654242468464416366227 94572981363702696624549341)
        ·
          refine ⟨35464868011388511234206003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94572981363702696624549341 35464868011388511234206003)
          ·
            refine ⟨53197302017082766851309005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35464868011388511234206003 53197302017082766851309005)
            ·
              refine ⟨19948988256406037569240877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53197302017082766851309005 19948988256406037569240877)
              ·
                refine ⟨7480870596152264088465329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19948988256406037569240877 7480870596152264088465329)
                ·
                  refine ⟨5610652947114198066348997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7480870596152264088465329 5610652947114198066348997)
                  ·
                    refine ⟨1051997427583912137440437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610652947114198066348997 1051997427583912137440437)
                    ·
                      rfl

theorem cell23_6146273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_6146273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146273 prefixEnd_6146273 := by exact prefixLift 6146273
  have htrace : WordTrace (prefixWord ++ tailWord_6146273) baseStart_6146273 baseEnd_6146273 := by
    simpa [prefixWord, tailWord_6146273, baseEnd_6146273] using wordTrace_append hprefix tailTrace_6146273
  have hstable : (prefixWord ++ tailWord_6146273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146273).length < 2 ^ (prefixWord ++ tailWord_6146273).sum := by decide
  have hdescent : baseEnd_6146273 < baseStart_6146273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146276 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_6146276 : Nat := 118140960795 + 6146276 * 2 ^ 59
def prefixEnd_6146276 : Nat := 4983230072969 + 3 ^ 40 * 6146276 * 2
def baseEnd_6146276 : Nat := 3155993823193699900583797

theorem tailTrace_6146276 : CollatzResearch.WordTrace tailWord_6146276 prefixEnd_6146276 3155993823193699900583797 := by
  unfold tailWord_6146276
  simp only [CollatzResearch.WordTrace]
  refine ⟨112086551140549613607497341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149448734854066151476663121 112086551140549613607497341)
  ·
    refine ⟨42032456677706105102811503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112086551140549613607497341 42032456677706105102811503)
    ·
      refine ⟨63048685016559157654217255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42032456677706105102811503 63048685016559157654217255)
      ·
        refine ⟨94573027524838736481325883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63048685016559157654217255 94573027524838736481325883)
        ·
          refine ⟨141859541287258104721988825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94573027524838736481325883 141859541287258104721988825)
          ·
            refine ⟨106394655965443578541491619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141859541287258104721988825 106394655965443578541491619)
            ·
              refine ⟨159591983948165367812237429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106394655965443578541491619 159591983948165367812237429)
              ·
                refine ⟨14961748495140503232397259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159591983948165367812237429 14961748495140503232397259)
                ·
                  refine ⟨22442622742710754848595889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14961748495140503232397259 22442622742710754848595889)
                  ·
                    refine ⟨16831967057033066136446917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22442622742710754848595889 16831967057033066136446917)
                    ·
                      refine ⟨3155993823193699900583797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16831967057033066136446917 3155993823193699900583797)
                      ·
                        rfl

theorem cell23_6146276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_6146276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146276 prefixEnd_6146276 := by exact prefixLift 6146276
  have htrace : WordTrace (prefixWord ++ tailWord_6146276) baseStart_6146276 baseEnd_6146276 := by
    simpa [prefixWord, tailWord_6146276, baseEnd_6146276] using wordTrace_append hprefix tailTrace_6146276
  have hstable : (prefixWord ++ tailWord_6146276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146276).length < 2 ^ (prefixWord ++ tailWord_6146276).sum := by decide
  have hdescent : baseEnd_6146276 < baseStart_6146276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146280 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 1, 1, 4]
def baseStart_6146280 : Nat := 118140960795 + 6146280 * 2 ^ 59
def prefixEnd_6146280 : Nat := 4983230072969 + 3 ^ 40 * 6146280 * 2
def baseEnd_6146280 : Nat := 3155995877116317884933779

theorem tailTrace_6146280 : CollatzResearch.WordTrace tailWord_6146280 prefixEnd_6146280 3155995877116317884933779 := by
  unfold tailWord_6146280
  simp only [CollatzResearch.WordTrace]
  refine ⟨112086624086542367949070147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149448832115389823932093529 112086624086542367949070147)
  ·
    refine ⟨168129936129813551923605221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112086624086542367949070147 168129936129813551923605221)
    ·
      refine ⟨31524363024340040985675979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168129936129813551923605221 31524363024340040985675979)
      ·
        refine ⟨47286544536510061478513969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31524363024340040985675979 47286544536510061478513969)
        ·
          refine ⟨35464908402382546108885477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47286544536510061478513969 35464908402382546108885477)
          ·
            refine ⟨6649670325446727395416027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35464908402382546108885477 6649670325446727395416027)
            ·
              refine ⟨9974505488170091093124041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6649670325446727395416027 9974505488170091093124041)
              ·
                refine ⟨7480879116127568319843031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9974505488170091093124041 7480879116127568319843031)
                ·
                  refine ⟨11221318674191352479764547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7480879116127568319843031 11221318674191352479764547)
                  ·
                    refine ⟨16831978011287028719646821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11221318674191352479764547 16831978011287028719646821)
                    ·
                      refine ⟨3155995877116317884933779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16831978011287028719646821 3155995877116317884933779)
                      ·
                        rfl

theorem cell23_6146280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_6146280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146280 prefixEnd_6146280 := by exact prefixLift 6146280
  have htrace : WordTrace (prefixWord ++ tailWord_6146280) baseStart_6146280 baseEnd_6146280 := by
    simpa [prefixWord, tailWord_6146280, baseEnd_6146280] using wordTrace_append hprefix tailTrace_6146280
  have hstable : (prefixWord ++ tailWord_6146280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146280).length < 2 ^ (prefixWord ++ tailWord_6146280).sum := by decide
  have hdescent : baseEnd_6146280 < baseStart_6146280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146299 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 6, 7]
def baseStart_6146299 : Nat := 118140960795 + 6146299 * 2 ^ 59
def prefixEnd_6146299 : Nat := 4983230072969 + 3 ^ 40 * 6146299 * 2
def baseEnd_6146299 : Nat := 1052001877749584436865397

theorem tailTrace_6146299 : CollatzResearch.WordTrace tailWord_6146299 prefixEnd_6146299 1052001877749584436865397 := by
  unfold tailWord_6146299
  simp only [CollatzResearch.WordTrace]
  refine ⟨224173941160015902143081951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149449294106677268095387967 224173941160015902143081951)
  ·
    refine ⟨336260911740023853214622927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224173941160015902143081951 336260911740023853214622927)
    ·
      refine ⟨504391367610035779821934391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336260911740023853214622927 504391367610035779821934391)
      ·
        refine ⟨756587051415053669732901587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504391367610035779821934391 756587051415053669732901587)
        ·
          refine ⟨1134880577122580504599352381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756587051415053669732901587 1134880577122580504599352381)
          ·
            refine ⟨425580216420967689224757143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1134880577122580504599352381 425580216420967689224757143)
            ·
              refine ⟨638370324631451533837135715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425580216420967689224757143 638370324631451533837135715)
              ·
                refine ⟨957555486947177300755703573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638370324631451533837135715 957555486947177300755703573)
                ·
                  refine ⟨44885413450648935972923605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 957555486947177300755703573 44885413450648935972923605)
                  ·
                    refine ⟨1052001877749584436865397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44885413450648935972923605 1052001877749584436865397)
                    ·
                      rfl

theorem cell23_6146299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_6146299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146299 prefixEnd_6146299 := by exact prefixLift 6146299
  have htrace : WordTrace (prefixWord ++ tailWord_6146299) baseStart_6146299 baseEnd_6146299 := by
    simpa [prefixWord, tailWord_6146299, baseEnd_6146299] using wordTrace_append hprefix tailTrace_6146299
  have hstable : (prefixWord ++ tailWord_6146299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146299).length < 2 ^ (prefixWord ++ tailWord_6146299).sum := by decide
  have hdescent : baseEnd_6146299 < baseStart_6146299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146314 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_6146314 : Nat := 118140960795 + 6146314 * 2 ^ 59
def prefixEnd_6146314 : Nat := 4983230072969 + 3 ^ 40 * 6146314 * 2
def baseEnd_6146314 : Nat := 3156013335458570751908623

theorem tailTrace_6146314 : CollatzResearch.WordTrace tailWord_6146314 prefixEnd_6146314 3156013335458570751908623 := by
  unfold tailWord_6146314
  simp only [CollatzResearch.WordTrace]
  refine ⟨56043622063740389926219499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149449658836641039803251997 56043622063740389926219499)
  ·
    refine ⟨84065433095610584889329249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56043622063740389926219499 84065433095610584889329249)
    ·
      refine ⟨63049074821707938666996937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84065433095610584889329249 63049074821707938666996937)
      ·
        refine ⟨47286806116280954000247703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63049074821707938666996937 47286806116280954000247703)
        ·
          refine ⟨70930209174421431000371555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47286806116280954000247703 70930209174421431000371555)
          ·
            refine ⟨106395313761632146500557333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70930209174421431000371555 106395313761632146500557333)
            ·
              refine ⟨4987280332576506867213625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 106395313761632146500557333 4987280332576506867213625)
              ·
                refine ⟨3740460249432380150410219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987280332576506867213625 3740460249432380150410219)
                ·
                  refine ⟨5610690374148570225615329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740460249432380150410219 5610690374148570225615329)
                  ·
                    refine ⟨4208017780611427669211497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610690374148570225615329 4208017780611427669211497)
                    ·
                      refine ⟨3156013335458570751908623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208017780611427669211497 3156013335458570751908623)
                      ·
                        rfl

theorem cell23_6146314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_6146314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146314 prefixEnd_6146314 := by exact prefixLift 6146314
  have htrace : WordTrace (prefixWord ++ tailWord_6146314) baseStart_6146314 baseEnd_6146314 := by
    simpa [prefixWord, tailWord_6146314, baseEnd_6146314] using wordTrace_append hprefix tailTrace_6146314
  have hstable : (prefixWord ++ tailWord_6146314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146314).length < 2 ^ (prefixWord ++ tailWord_6146314).sum := by decide
  have hdescent : baseEnd_6146314 < baseStart_6146314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146330 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_6146330 : Nat := 118140960795 + 6146330 * 2 ^ 59
def prefixEnd_6146330 : Nat := 4983230072969 + 3 ^ 40 * 6146330 * 2
def baseEnd_6146330 : Nat := 3156021551149042689308549

theorem tailTrace_6146330 : CollatzResearch.WordTrace tailWord_6146330 prefixEnd_6146330 3156021551149042689308549 := by
  unfold tailWord_6146330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56043767955725898609365111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149450047881935729624973629 56043767955725898609365111)
  ·
    refine ⟨84065651933588847914047667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56043767955725898609365111 84065651933588847914047667)
    ·
      refine ⟨126098477900383271871071501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84065651933588847914047667 126098477900383271871071501)
      ·
        refine ⟨47286929212643726951651813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126098477900383271871071501 47286929212643726951651813)
        ·
          refine ⟨8866299227370698803434715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47286929212643726951651813 8866299227370698803434715)
          ·
            refine ⟨13299448841056048205152073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866299227370698803434715 13299448841056048205152073)
            ·
              refine ⟨9974586630792036153864055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13299448841056048205152073 9974586630792036153864055)
              ·
                refine ⟨14961879946188054230796083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9974586630792036153864055 14961879946188054230796083)
                ·
                  refine ⟨22442819919282081346194125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14961879946188054230796083 22442819919282081346194125)
                  ·
                    refine ⟨8416057469730780504822797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22442819919282081346194125 8416057469730780504822797)
                    ·
                      refine ⟨3156021551149042689308549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8416057469730780504822797 3156021551149042689308549)
                      ·
                        rfl

theorem cell23_6146330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_6146330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146330 prefixEnd_6146330 := by exact prefixLift 6146330
  have htrace : WordTrace (prefixWord ++ tailWord_6146330) baseStart_6146330 baseEnd_6146330 := by
    simpa [prefixWord, tailWord_6146330, baseEnd_6146330] using wordTrace_append hprefix tailTrace_6146330
  have hstable : (prefixWord ++ tailWord_6146330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146330).length < 2 ^ (prefixWord ++ tailWord_6146330).sum := by decide
  have hdescent : baseEnd_6146330 < baseStart_6146330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146340 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 3, 3, 2]
def baseStart_6146340 : Nat := 118140960795 + 6146340 * 2 ^ 59
def prefixEnd_6146340 : Nat := 4983230072969 + 3 ^ 40 * 6146340 * 2
def baseEnd_6146340 : Nat := 3156026685955587650183503

theorem tailTrace_6146340 : CollatzResearch.WordTrace tailWord_6146340 prefixEnd_6146340 3156026685955587650183503 := by
  unfold tailWord_6146340
  simp only [CollatzResearch.WordTrace]
  refine ⟨112087718276433683072662237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149450291035244910763549649 112087718276433683072662237)
  ·
    refine ⟨42032894353662631152248339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112087718276433683072662237 42032894353662631152248339)
    ·
      refine ⟨63049341530493946728372509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42032894353662631152248339 63049341530493946728372509)
      ·
        refine ⟨23643503073935230023139691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63049341530493946728372509 23643503073935230023139691)
        ·
          refine ⟨35465254610902845034709537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23643503073935230023139691 35465254610902845034709537)
          ·
            refine ⟨26598940958177133776032153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35465254610902845034709537 26598940958177133776032153)
            ·
              refine ⟨19949205718632850332024115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26598940958177133776032153 19949205718632850332024115)
              ·
                refine ⟨29923808577949275498036173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19949205718632850332024115 29923808577949275498036173)
                ·
                  refine ⟨11221428216730978311763565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29923808577949275498036173 11221428216730978311763565)
                  ·
                    refine ⟨4208035581274116866911337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11221428216730978311763565 4208035581274116866911337)
                    ·
                      refine ⟨3156026685955587650183503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208035581274116866911337 3156026685955587650183503)
                      ·
                        rfl

theorem cell23_6146340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_6146340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146340 prefixEnd_6146340 := by exact prefixLift 6146340
  have htrace : WordTrace (prefixWord ++ tailWord_6146340) baseStart_6146340 baseEnd_6146340 := by
    simpa [prefixWord, tailWord_6146340, baseEnd_6146340] using wordTrace_append hprefix tailTrace_6146340
  have hstable : (prefixWord ++ tailWord_6146340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146340).length < 2 ^ (prefixWord ++ tailWord_6146340).sum := by decide
  have hdescent : baseEnd_6146340 < baseStart_6146340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146376 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 7]
def baseStart_6146376 : Nat := 118140960795 + 6146376 * 2 ^ 59
def prefixEnd_6146376 : Nat := 4983230072969 + 3 ^ 40 * 6146376 * 2
def baseEnd_6146376 : Nat := 350671685695461056592593

theorem tailTrace_6146376 : CollatzResearch.WordTrace tailWord_6146376 prefixEnd_6146376 350671685695461056592593 := by
  unfold tailWord_6146376
  simp only [CollatzResearch.WordTrace]
  refine ⟨112088374790368472146817491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149451166387157962862423321 112088374790368472146817491)
  ·
    refine ⟨168132562185552708220226237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112088374790368472146817491 168132562185552708220226237)
    ·
      refine ⟨63049710819582265582584839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168132562185552708220226237 63049710819582265582584839)
      ·
        refine ⟨94574566229373398373877259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63049710819582265582584839 94574566229373398373877259)
        ·
          refine ⟨141861849344060097560815889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94574566229373398373877259 141861849344060097560815889)
          ·
            refine ⟨106396387008045073170611917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141861849344060097560815889 106396387008045073170611917)
            ·
              refine ⟨39898645128016902438979469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106396387008045073170611917 39898645128016902438979469)
              ·
                refine ⟨14961991923006338414617301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39898645128016902438979469 14961991923006338414617301)
                ·
                  refine ⟨350671685695461056592593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14961991923006338414617301 350671685695461056592593)
                  ·
                    rfl

theorem cell23_6146376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 7].length) (baseStart_6146376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146376 prefixEnd_6146376 := by exact prefixLift 6146376
  have htrace : WordTrace (prefixWord ++ tailWord_6146376) baseStart_6146376 baseEnd_6146376 := by
    simpa [prefixWord, tailWord_6146376, baseEnd_6146376] using wordTrace_append hprefix tailTrace_6146376
  have hstable : (prefixWord ++ tailWord_6146376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146376).length < 2 ^ (prefixWord ++ tailWord_6146376).sum := by decide
  have hdescent : baseEnd_6146376 < baseStart_6146376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146433 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_6146433 : Nat := 118140960795 + 6146433 * 2 ^ 59
def prefixEnd_6146433 : Nat := 4983230072969 + 3 ^ 40 * 6146433 * 2
def baseEnd_6146433 : Nat := 3156074439656455786320575

theorem tailTrace_6146433 : CollatzResearch.WordTrace tailWord_6146433 prefixEnd_6146433 3156074439656455786320575 := by
  unfold tailWord_6146433
  simp only [CollatzResearch.WordTrace]
  refine ⟨224178828541530443028459953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149452552361020295352306635 224178828541530443028459953)
  ·
    refine ⟨168134121406147832271344965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224178828541530443028459953 168134121406147832271344965)
    ·
      refine ⟨31525147763652718550877181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168134121406147832271344965 31525147763652718550877181)
      ·
        refine ⟨11821930411369769456578943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31525147763652718550877181 11821930411369769456578943)
        ·
          refine ⟨17732895617054654184868415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11821930411369769456578943 17732895617054654184868415)
          ·
            refine ⟨26599343425581981277302623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17732895617054654184868415 26599343425581981277302623)
            ·
              refine ⟨39899015138372971915953935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26599343425581981277302623 39899015138372971915953935)
              ·
                refine ⟨59848522707559457873930903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39899015138372971915953935 59848522707559457873930903)
                ·
                  refine ⟨89772784061339186810896355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59848522707559457873930903 89772784061339186810896355)
                  ·
                    refine ⟨134659176092008780216344533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89772784061339186810896355 134659176092008780216344533)
                    ·
                      refine ⟨3156074439656455786320575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134659176092008780216344533 3156074439656455786320575)
                      ·
                        rfl

theorem cell23_6146433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_6146433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146433 prefixEnd_6146433 := by exact prefixLift 6146433
  have htrace : WordTrace (prefixWord ++ tailWord_6146433) baseStart_6146433 baseEnd_6146433 := by
    simpa [prefixWord, tailWord_6146433, baseEnd_6146433] using wordTrace_append hprefix tailTrace_6146433
  have hstable : (prefixWord ++ tailWord_6146433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146433).length < 2 ^ (prefixWord ++ tailWord_6146433).sum := by decide
  have hdescent : baseEnd_6146433 < baseStart_6146433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146453 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_6146453 : Nat := 118140960795 + 6146453 * 2 ^ 59
def prefixEnd_6146453 : Nat := 4983230072969 + 3 ^ 40 * 6146453 * 2
def baseEnd_6146453 : Nat := 1052028236423181902690161

theorem tailTrace_6146453 : CollatzResearch.WordTrace tailWord_6146453 prefixEnd_6146453 1052028236423181902690161 := by
  unfold tailWord_6146453
  simp only [CollatzResearch.WordTrace]
  refine ⟨224179558001457986444188013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149453038667638657629458675 224179558001457986444188013)
  ·
    refine ⟨84067334250546744916570505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224179558001457986444188013 84067334250546744916570505)
    ·
      refine ⟨63050500687910058687427879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84067334250546744916570505 63050500687910058687427879)
      ·
        refine ⟨94575751031865088031141819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63050500687910058687427879 94575751031865088031141819)
        ·
          refine ⟨141863626547797632046712729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94575751031865088031141819 141863626547797632046712729)
          ·
            refine ⟨106397719910848224035034547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141863626547797632046712729 106397719910848224035034547)
            ·
              refine ⟨159596579866272336052551821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106397719910848224035034547 159596579866272336052551821)
              ·
                refine ⟨59848717449852126019706933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159596579866272336052551821 59848717449852126019706933)
                ·
                  refine ⟨5610817260923636814347525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59848717449852126019706933 5610817260923636814347525)
                  ·
                    refine ⟨1052028236423181902690161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610817260923636814347525 1052028236423181902690161)
                    ·
                      rfl

theorem cell23_6146453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_6146453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146453 prefixEnd_6146453 := by exact prefixLift 6146453
  have htrace : WordTrace (prefixWord ++ tailWord_6146453) baseStart_6146453 baseEnd_6146453 := by
    simpa [prefixWord, tailWord_6146453, baseEnd_6146453] using wordTrace_append hprefix tailTrace_6146453
  have hstable : (prefixWord ++ tailWord_6146453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146453).length < 2 ^ (prefixWord ++ tailWord_6146453).sum := by decide
  have hdescent : baseEnd_6146453 < baseStart_6146453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146487 : List Nat := [1, 1, 3, 1, 3, 4, 1, 4, 1, 4]
def baseStart_6146487 : Nat := 118140960795 + 6146487 * 2 ^ 59
def prefixEnd_6146487 : Nat := 4983230072969 + 3 ^ 40 * 6146487 * 2
def baseEnd_6146487 : Nat := 1052034055870599525015109

theorem tailTrace_6146487 : CollatzResearch.WordTrace tailWord_6146487 prefixEnd_6146487 1052034055870599525015109 := by
  unfold tailWord_6146487
  simp only [CollatzResearch.WordTrace]
  refine ⟨224180798083334810250925715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149453865388889873500617143 224180798083334810250925715)
  ·
    refine ⟨336271197125002215376388573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224180798083334810250925715 336271197125002215376388573)
    ·
      refine ⟨126101698921875830766145715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336271197125002215376388573 126101698921875830766145715)
      ·
        refine ⟨189152548382813746149218573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126101698921875830766145715 189152548382813746149218573)
        ·
          refine ⟨70932205643555154805956965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189152548382813746149218573 70932205643555154805956965)
          ·
            refine ⟨13299788558166591526116931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70932205643555154805956965 13299788558166591526116931)
            ·
              refine ⟨19949682837249887289175397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13299788558166591526116931 19949682837249887289175397)
              ·
                refine ⟨3740565531984353866720387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19949682837249887289175397 3740565531984353866720387)
                ·
                  refine ⟨5610848297976530800080581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740565531984353866720387 5610848297976530800080581)
                  ·
                    refine ⟨1052034055870599525015109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5610848297976530800080581 1052034055870599525015109)
                    ·
                      rfl

theorem cell23_6146487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_6146487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146487 prefixEnd_6146487 := by exact prefixLift 6146487
  have htrace : WordTrace (prefixWord ++ tailWord_6146487) baseStart_6146487 baseEnd_6146487 := by
    simpa [prefixWord, tailWord_6146487, baseEnd_6146487] using wordTrace_append hprefix tailTrace_6146487
  have hstable : (prefixWord ++ tailWord_6146487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146487).length < 2 ^ (prefixWord ++ tailWord_6146487).sum := by decide
  have hdescent : baseEnd_6146487 < baseStart_6146487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146553 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_6146553 : Nat := 118140960795 + 6146553 * 2 ^ 59
def prefixEnd_6146553 : Nat := 4983230072969 + 3 ^ 40 * 6146553 * 2
def baseEnd_6146553 : Nat := 3156136057334995316820023

theorem tailTrace_6146553 : CollatzResearch.WordTrace tailWord_6146553 prefixEnd_6146553 3156136057334995316820023 := by
  unfold tailWord_6146553
  simp only [CollatzResearch.WordTrace]
  refine ⟨224183205301095703522828313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149455470200730469015218875 224183205301095703522828313)
  ·
    refine ⟨168137403975821777642121235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224183205301095703522828313 168137403975821777642121235)
    ·
      refine ⟨252206105963732666463181853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168137403975821777642121235 252206105963732666463181853)
      ·
        refine ⟨94577289736399749923693195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252206105963732666463181853 94577289736399749923693195)
        ·
          refine ⟨141865934604599624885539793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94577289736399749923693195 141865934604599624885539793)
          ·
            refine ⟨106399450953449718664154845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141865934604599624885539793 106399450953449718664154845)
            ·
              refine ⟨39899794107543644499058067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106399450953449718664154845 39899794107543644499058067)
              ·
                refine ⟨59849691161315466748587101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39899794107543644499058067 59849691161315466748587101)
                ·
                  refine ⟨22443634185493300030720163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59849691161315466748587101 22443634185493300030720163)
                  ·
                    refine ⟨33665451278239950046080245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22443634185493300030720163 33665451278239950046080245)
                    ·
                      refine ⟨3156136057334995316820023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33665451278239950046080245 3156136057334995316820023)
                      ·
                        rfl

theorem cell23_6146553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_6146553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146553 prefixEnd_6146553 := by exact prefixLift 6146553
  have htrace : WordTrace (prefixWord ++ tailWord_6146553) baseStart_6146553 baseEnd_6146553 := by
    simpa [prefixWord, tailWord_6146553, baseEnd_6146553] using wordTrace_append hprefix tailTrace_6146553
  have hstable : (prefixWord ++ tailWord_6146553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146553).length < 2 ^ (prefixWord ++ tailWord_6146553).sum := by decide
  have hdescent : baseEnd_6146553 < baseStart_6146553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146563 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6]
def baseStart_6146563 : Nat := 118140960795 + 6146563 * 2 ^ 59
def prefixEnd_6146563 : Nat := 4983230072969 + 3 ^ 40 * 6146563 * 2
def baseEnd_6146563 : Nat := 3156141192141540277694977

theorem tailTrace_6146563 : CollatzResearch.WordTrace tailWord_6146563 prefixEnd_6146563 3156141192141540277694977 := by
  unfold tailWord_6146563
  simp only [CollatzResearch.WordTrace]
  refine ⟨224183570031059475230692343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149455713354039650153794895 224183570031059475230692343)
  ·
    refine ⟨336275355046589212846038515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224183570031059475230692343 336275355046589212846038515)
    ·
      refine ⟨504413032569883819269057773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336275355046589212846038515 504413032569883819269057773)
      ·
        refine ⟨189154887213706432225896665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504413032569883819269057773 189154887213706432225896665)
        ·
          refine ⟨141866165410279824169422499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189154887213706432225896665 141866165410279824169422499)
          ·
            refine ⟨212799248115419736254133749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141866165410279824169422499 212799248115419736254133749)
            ·
              refine ⟨19949929510820600273825039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212799248115419736254133749 19949929510820600273825039)
              ·
                refine ⟨29924894266230900410737559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19949929510820600273825039 29924894266230900410737559)
                ·
                  refine ⟨44887341399346350616106339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29924894266230900410737559 44887341399346350616106339)
                  ·
                    refine ⟨67331012099019525924159509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44887341399346350616106339 67331012099019525924159509)
                    ·
                      refine ⟨3156141192141540277694977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67331012099019525924159509 3156141192141540277694977)
                      ·
                        rfl

theorem cell23_6146563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_6146563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146563 prefixEnd_6146563 := by exact prefixLift 6146563
  have htrace : WordTrace (prefixWord ++ tailWord_6146563) baseStart_6146563 baseEnd_6146563 := by
    simpa [prefixWord, tailWord_6146563, baseEnd_6146563] using wordTrace_append hprefix tailTrace_6146563
  have hstable : (prefixWord ++ tailWord_6146563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146563).length < 2 ^ (prefixWord ++ tailWord_6146563).sum := by decide
  have hdescent : baseEnd_6146563 < baseStart_6146563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146633 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_6146633 : Nat := 118140960795 + 6146633 * 2 ^ 59
def prefixEnd_6146633 : Nat := 4983230072969 + 3 ^ 40 * 6146633 * 2
def baseEnd_6146633 : Nat := 1052059045262451667939885

theorem tailTrace_6146633 : CollatzResearch.WordTrace tailWord_6146633 prefixEnd_6146633 1052059045262451667939885 := by
  unfold tailWord_6146633
  simp only [CollatzResearch.WordTrace]
  refine ⟨224186123140805877185740553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149457415427203918123827035 224186123140805877185740553)
  ·
    refine ⟨168139592355604407889305415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224186123140805877185740553 168139592355604407889305415)
    ·
      refine ⟨252209388533406611833958123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168139592355604407889305415 252209388533406611833958123)
      ·
        refine ⟨378314082800109917750937185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252209388533406611833958123 378314082800109917750937185)
        ·
          refine ⟨283735562100082438313202889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378314082800109917750937185 283735562100082438313202889)
          ·
            refine ⟨212801671575061828734902167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283735562100082438313202889 212801671575061828734902167)
            ·
              refine ⟨319202507362592743102353251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212801671575061828734902167 319202507362592743102353251)
              ·
                refine ⟨478803761043889114653529877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319202507362592743102353251 478803761043889114653529877)
                ·
                  refine ⟨22443926298932302249384213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 478803761043889114653529877 22443926298932302249384213)
                  ·
                    refine ⟨1052059045262451667939885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22443926298932302249384213 1052059045262451667939885)
                    ·
                      rfl

theorem cell23_6146633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_6146633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146633 prefixEnd_6146633 := by exact prefixLift 6146633
  have htrace : WordTrace (prefixWord ++ tailWord_6146633) baseStart_6146633 baseEnd_6146633 := by
    simpa [prefixWord, tailWord_6146633, baseEnd_6146633] using wordTrace_append hprefix tailTrace_6146633
  have hstable : (prefixWord ++ tailWord_6146633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146633).length < 2 ^ (prefixWord ++ tailWord_6146633).sum := by decide
  have hdescent : baseEnd_6146633 < baseStart_6146633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146652 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_6146652 : Nat := 118140960795 + 6146652 * 2 ^ 59
def prefixEnd_6146652 : Nat := 4983230072969 + 3 ^ 40 * 6146652 * 2
def baseEnd_6146652 : Nat := 3156186891919790429482069

theorem tailTrace_6146652 : CollatzResearch.WordTrace tailWord_6146652 prefixEnd_6146652 3156186891919790429482069 := by
  unfold tailWord_6146652
  simp only [CollatzResearch.WordTrace]
  refine ⟨112093408063868521715341105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149457877418491362287121473 112093408063868521715341105)
  ·
    refine ⟨84070056047901391286505829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112093408063868521715341105 84070056047901391286505829)
    ·
      refine ⟨15763135508981510866219843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84070056047901391286505829 15763135508981510866219843)
      ·
        refine ⟨23644703263472266299329765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15763135508981510866219843 23644703263472266299329765)
        ·
          refine ⟨4433381861901049931124331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23644703263472266299329765 4433381861901049931124331)
          ·
            refine ⟨6650072792851574896686497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4433381861901049931124331 6650072792851574896686497)
            ·
              refine ⟨4987554594638681172514873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6650072792851574896686497 4987554594638681172514873)
              ·
                refine ⟨3740665945979010879386155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987554594638681172514873 3740665945979010879386155)
                ·
                  refine ⟨5610998918968516319079233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740665945979010879386155 5610998918968516319079233)
                  ·
                    refine ⟨4208249189226387239309425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5610998918968516319079233 4208249189226387239309425)
                    ·
                      refine ⟨3156186891919790429482069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208249189226387239309425 3156186891919790429482069)
                      ·
                        rfl

theorem cell23_6146652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_6146652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146652 prefixEnd_6146652 := by exact prefixLift 6146652
  have htrace : WordTrace (prefixWord ++ tailWord_6146652) baseStart_6146652 baseEnd_6146652 := by
    simpa [prefixWord, tailWord_6146652, baseEnd_6146652] using wordTrace_append hprefix tailTrace_6146652
  have hstable : (prefixWord ++ tailWord_6146652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146652).length < 2 ^ (prefixWord ++ tailWord_6146652).sum := by decide
  have hdescent : baseEnd_6146652 < baseStart_6146652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146660 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_6146660 : Nat := 118140960795 + 6146660 * 2 ^ 59
def prefixEnd_6146660 : Nat := 4983230072969 + 3 ^ 40 * 6146660 * 2
def baseEnd_6146660 : Nat := 3156190999765026398182031

theorem tailTrace_6146660 : CollatzResearch.WordTrace tailWord_6146660 prefixEnd_6146660 3156190999765026398182031 := by
  unfold tailWord_6146660
  simp only [CollatzResearch.WordTrace]
  refine ⟨112093553955854030398486717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149458071941138707197982289 112093553955854030398486717)
  ·
    refine ⟨42035082733445261399432519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112093553955854030398486717 42035082733445261399432519)
    ·
      refine ⟨63052624100167892099148779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42035082733445261399432519 63052624100167892099148779)
      ·
        refine ⟨94578936150251838148723169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63052624100167892099148779 94578936150251838148723169)
        ·
          refine ⟨70934202112688878611542377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94578936150251838148723169 70934202112688878611542377)
          ·
            refine ⟨53200651584516658958656783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70934202112688878611542377 53200651584516658958656783)
            ·
              refine ⟨79800977376774988437985175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53200651584516658958656783 79800977376774988437985175)
              ·
                refine ⟨119701466065162482656977763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79800977376774988437985175 119701466065162482656977763)
                ·
                  refine ⟨179552199097743723985466645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119701466065162482656977763 179552199097743723985466645)
                  ·
                    refine ⟨8416509332706737061818749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 179552199097743723985466645 8416509332706737061818749)
                    ·
                      refine ⟨3156190999765026398182031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8416509332706737061818749 3156190999765026398182031)
                      ·
                        rfl

theorem cell23_6146660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_6146660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146660 prefixEnd_6146660 := by exact prefixLift 6146660
  have htrace : WordTrace (prefixWord ++ tailWord_6146660) baseStart_6146660 baseEnd_6146660 := by
    simpa [prefixWord, tailWord_6146660, baseEnd_6146660] using wordTrace_append hprefix tailTrace_6146660
  have hstable : (prefixWord ++ tailWord_6146660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146660).length < 2 ^ (prefixWord ++ tailWord_6146660).sum := by decide
  have hdescent : baseEnd_6146660 < baseStart_6146660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146708 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_6146708 : Nat := 118140960795 + 6146708 * 2 ^ 59
def prefixEnd_6146708 : Nat := 4983230072969 + 3 ^ 40 * 6146708 * 2
def baseEnd_6146708 : Nat := 3156215646836442210381811

theorem tailTrace_6146708 : CollatzResearch.WordTrace tailWord_6146708 prefixEnd_6146708 3156215646836442210381811 := by
  unfold tailWord_6146708
  simp only [CollatzResearch.WordTrace]
  refine ⟨112094429307767082497360389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149459239077022776663147185 112094429307767082497360389)
  ·
    refine ⟨21017705495206327968255073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112094429307767082497360389 21017705495206327968255073)
    ·
      refine ⟨15763279121404745976191305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21017705495206327968255073 15763279121404745976191305)
      ·
        refine ⟨11822459341053559482143479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15763279121404745976191305 11822459341053559482143479)
        ·
          refine ⟨17733689011580339223215219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822459341053559482143479 17733689011580339223215219)
          ·
            refine ⟨26600533517370508834822829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17733689011580339223215219 26600533517370508834822829)
            ·
              refine ⟨9975200069013940813058561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26600533517370508834822829 9975200069013940813058561)
              ·
                refine ⟨7481400051760455609793921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9975200069013940813058561 7481400051760455609793921)
                ·
                  refine ⟨5611050038820341707345441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7481400051760455609793921 5611050038820341707345441)
                  ·
                    refine ⟨4208287529115256280509081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5611050038820341707345441 4208287529115256280509081)
                    ·
                      refine ⟨3156215646836442210381811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208287529115256280509081 3156215646836442210381811)
                      ·
                        rfl

theorem cell23_6146708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_6146708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146708 prefixEnd_6146708 := by exact prefixLift 6146708
  have htrace : WordTrace (prefixWord ++ tailWord_6146708) baseStart_6146708 baseEnd_6146708 := by
    simpa [prefixWord, tailWord_6146708, baseEnd_6146708] using wordTrace_append hprefix tailTrace_6146708
  have hstable : (prefixWord ++ tailWord_6146708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146708).length < 2 ^ (prefixWord ++ tailWord_6146708).sum := by decide
  have hdescent : baseEnd_6146708 < baseStart_6146708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146714 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 7]
def baseStart_6146714 : Nat := 118140960795 + 6146714 * 2 ^ 59
def prefixEnd_6146714 : Nat := 4983230072969 + 3 ^ 40 * 6146714 * 2
def baseEnd_6146714 : Nat := 350690969746707687434087

theorem tailTrace_6146714 : CollatzResearch.WordTrace tailWord_6146714 prefixEnd_6146714 350690969746707687434087 := by
  unfold tailWord_6146714
  simp only [CollatzResearch.WordTrace]
  refine ⟨56047269363378107004859799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149459384969008285346292797 56047269363378107004859799)
  ·
    refine ⟨84070904045067160507289699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56047269363378107004859799 84070904045067160507289699)
    ·
      refine ⟨126106356067600740760934549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84070904045067160507289699 126106356067600740760934549)
      ·
        refine ⟨5911235440668784723168807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126106356067600740760934549 5911235440668784723168807)
        ·
          refine ⟨8866853161003177084753211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911235440668784723168807 8866853161003177084753211)
          ·
            refine ⟨13300279741504765627129817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866853161003177084753211 13300279741504765627129817)
            ·
              refine ⟨9975209806128574220347363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13300279741504765627129817 9975209806128574220347363)
              ·
                refine ⟨14962814709192861330521045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9975209806128574220347363 14962814709192861330521045)
                ·
                  refine ⟨350690969746707687434087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14962814709192861330521045 350690969746707687434087)
                  ·
                    rfl

theorem cell23_6146714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_6146714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146714 prefixEnd_6146714 := by exact prefixLift 6146714
  have htrace : WordTrace (prefixWord ++ tailWord_6146714) baseStart_6146714 baseEnd_6146714 := by
    simpa [prefixWord, tailWord_6146714, baseEnd_6146714] using wordTrace_append hprefix tailTrace_6146714
  have hstable : (prefixWord ++ tailWord_6146714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146714).length < 2 ^ (prefixWord ++ tailWord_6146714).sum := by decide
  have hdescent : baseEnd_6146714 < baseStart_6146714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146717 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 7, 2]
def baseStart_6146717 : Nat := 118140960795 + 6146717 * 2 ^ 59
def prefixEnd_6146717 : Nat := 4983230072969 + 3 ^ 40 * 6146717 * 2
def baseEnd_6146717 : Nat := 3156220268162332675169269

theorem tailTrace_6146717 : CollatzResearch.WordTrace tailWord_6146717 prefixEnd_6146717 3156220268162332675169269 := by
  unfold tailWord_6146717
  simp only [CollatzResearch.WordTrace]
  refine ⟨224189186872501559531798405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149459457915001039687865603 224189186872501559531798405)
  ·
    refine ⟨42035472538594042412212201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224189186872501559531798405 42035472538594042412212201)
    ·
      refine ⟨31526604403945531809159151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42035472538594042412212201 31526604403945531809159151)
      ·
        refine ⟨47289906605918297713738727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31526604403945531809159151 47289906605918297713738727)
        ·
          refine ⟨70934859908877446570608091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47289906605918297713738727 70934859908877446570608091)
          ·
            refine ⟨106402289863316169855912137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70934859908877446570608091 106402289863316169855912137)
            ·
              refine ⟨79801717397487127391934103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106402289863316169855912137 79801717397487127391934103)
              ·
                refine ⟨119702576096230691087901155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79801717397487127391934103 119702576096230691087901155)
                ·
                  refine ⟨179553864144346036631851733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119702576096230691087901155 179553864144346036631851733)
                  ·
                    refine ⟨4208293690883110233559025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179553864144346036631851733 4208293690883110233559025)
                    ·
                      refine ⟨3156220268162332675169269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208293690883110233559025 3156220268162332675169269)
                      ·
                        rfl

theorem cell23_6146717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_6146717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146717 prefixEnd_6146717 := by exact prefixLift 6146717
  have htrace : WordTrace (prefixWord ++ tailWord_6146717) baseStart_6146717 baseEnd_6146717 := by
    simpa [prefixWord, tailWord_6146717, baseEnd_6146717] using wordTrace_append hprefix tailTrace_6146717
  have hstable : (prefixWord ++ tailWord_6146717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146717).length < 2 ^ (prefixWord ++ tailWord_6146717).sum := by decide
  have hdescent : baseEnd_6146717 < baseStart_6146717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146764 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_6146764 : Nat := 118140960795 + 6146764 * 2 ^ 59
def prefixEnd_6146764 : Nat := 4983230072969 + 3 ^ 40 * 6146764 * 2
def baseEnd_6146764 : Nat := 3156244401753093991281553

theorem tailTrace_6146764 : CollatzResearch.WordTrace tailWord_6146764 prefixEnd_6146764 3156244401753093991281553 := by
  unfold tailWord_6146764
  simp only [CollatzResearch.WordTrace]
  refine ⟨112095450551665643279379673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149460600735554191039172897 112095450551665643279379673)
  ·
    refine ⟨84071587913749232459534755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112095450551665643279379673 84071587913749232459534755)
    ·
      refine ⟨126107381870623848689302133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84071587913749232459534755 126107381870623848689302133)
      ·
        refine ⟨11822567050370985814622075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126107381870623848689302133 11822567050370985814622075)
        ·
          refine ⟨17733850575556478721933113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822567050370985814622075 17733850575556478721933113)
          ·
            refine ⟨13300387931667359041449835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17733850575556478721933113 13300387931667359041449835)
            ·
              refine ⟨19950581897501038562174753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300387931667359041449835 19950581897501038562174753)
              ·
                refine ⟨14962936423125778921631065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19950581897501038562174753 14962936423125778921631065)
                ·
                  refine ⟨11222202317344334191223299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14962936423125778921631065 11222202317344334191223299)
                  ·
                    refine ⟨16833303476016501286834949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11222202317344334191223299 16833303476016501286834949)
                    ·
                      refine ⟨3156244401753093991281553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16833303476016501286834949 3156244401753093991281553)
                      ·
                        rfl

theorem cell23_6146764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_6146764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146764 prefixEnd_6146764 := by exact prefixLift 6146764
  have htrace : WordTrace (prefixWord ++ tailWord_6146764) baseStart_6146764 baseEnd_6146764 := by
    simpa [prefixWord, tailWord_6146764, baseEnd_6146764] using wordTrace_append hprefix tailTrace_6146764
  have hstable : (prefixWord ++ tailWord_6146764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146764).length < 2 ^ (prefixWord ++ tailWord_6146764).sum := by decide
  have hdescent : baseEnd_6146764 < baseStart_6146764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146831 : List Nat := [1, 1, 2, 1, 1, 1, 7, 4, 1, 1, 3]
def baseStart_6146831 : Nat := 118140960795 + 6146831 * 2 ^ 59
def prefixEnd_6146831 : Nat := 4983230072969 + 3 ^ 40 * 6146831 * 2
def baseEnd_6146831 : Nat := 3156278804956945229143745

theorem tailTrace_6146831 : CollatzResearch.WordTrace tailWord_6146831 prefixEnd_6146831 3156278804956945229143745 := by
  unfold tailWord_6146831
  simp only [CollatzResearch.WordTrace]
  refine ⟨224193344794088557001448347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149462229862725704667632231 224193344794088557001448347)
  ·
    refine ⟨336290017191132835502172521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224193344794088557001448347 336290017191132835502172521)
    ·
      refine ⟨252217512893349626626629391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336290017191132835502172521 252217512893349626626629391)
      ·
        refine ⟨378326269340024439939944087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252217512893349626626629391 378326269340024439939944087)
        ·
          refine ⟨567489404010036659909916131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378326269340024439939944087 567489404010036659909916131)
          ·
            refine ⟨851234106015054989864874197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567489404010036659909916131 851234106015054989864874197)
            ·
              refine ⟨19950799359727851324957989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 851234106015054989864874197 19950799359727851324957989)
              ·
                refine ⟨3740774879948972123429623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19950799359727851324957989 3740774879948972123429623)
                ·
                  refine ⟨5611162319923458185144435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740774879948972123429623 5611162319923458185144435)
                  ·
                    refine ⟨8416743479885187277716653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5611162319923458185144435 8416743479885187277716653)
                    ·
                      refine ⟨3156278804956945229143745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8416743479885187277716653 3156278804956945229143745)
                      ·
                        rfl

theorem cell23_6146831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 4, 1, 1, 3].length) (baseStart_6146831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146831 prefixEnd_6146831 := by exact prefixLift 6146831
  have htrace : WordTrace (prefixWord ++ tailWord_6146831) baseStart_6146831 baseEnd_6146831 := by
    simpa [prefixWord, tailWord_6146831, baseEnd_6146831] using wordTrace_append hprefix tailTrace_6146831
  have hstable : (prefixWord ++ tailWord_6146831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146831).length < 2 ^ (prefixWord ++ tailWord_6146831).sum := by decide
  have hdescent : baseEnd_6146831 < baseStart_6146831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146837 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_6146837 : Nat := 118140960795 + 6146837 * 2 ^ 59
def prefixEnd_6146837 : Nat := 4983230072969 + 3 ^ 40 * 6146837 * 2
def baseEnd_6146837 : Nat := 3156281885840872205668717

theorem tailTrace_6146837 : CollatzResearch.WordTrace tailWord_6146837 prefixEnd_6146837 3156281885840872205668717 := by
  unfold tailWord_6146837
  simp only [CollatzResearch.WordTrace]
  refine ⟨224193563632066820026166765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149462375754711213350777843 224193563632066820026166765)
  ·
    refine ⟨84072586362025057509812537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224193563632066820026166765 84072586362025057509812537)
    ·
      refine ⟨63054439771518793132359403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84072586362025057509812537 63054439771518793132359403)
      ·
        refine ⟨94581659657278189698539105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63054439771518793132359403 94581659657278189698539105)
        ·
          refine ⟨70936244742958642273904329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94581659657278189698539105 70936244742958642273904329)
          ·
            refine ⟨53202183557218981705428247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70936244742958642273904329 53202183557218981705428247)
            ·
              refine ⟨79803275335828472558142371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53202183557218981705428247 79803275335828472558142371)
              ·
                refine ⟨119704913003742708837213557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79803275335828472558142371 119704913003742708837213557)
                ·
                  refine ⟨11222335594100878953488771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119704913003742708837213557 11222335594100878953488771)
                  ·
                    refine ⟨16833503391151318430233157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11222335594100878953488771 16833503391151318430233157)
                    ·
                      refine ⟨3156281885840872205668717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16833503391151318430233157 3156281885840872205668717)
                      ·
                        rfl

theorem cell23_6146837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_6146837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146837 prefixEnd_6146837 := by exact prefixLift 6146837
  have htrace : WordTrace (prefixWord ++ tailWord_6146837) baseStart_6146837 baseEnd_6146837 := by
    simpa [prefixWord, tailWord_6146837, baseEnd_6146837] using wordTrace_append hprefix tailTrace_6146837
  have hstable : (prefixWord ++ tailWord_6146837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146837).length < 2 ^ (prefixWord ++ tailWord_6146837).sum := by decide
  have hdescent : baseEnd_6146837 < baseStart_6146837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146847 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 1, 6]
def baseStart_6146847 : Nat := 118140960795 + 6146847 * 2 ^ 59
def prefixEnd_6146847 : Nat := 4983230072969 + 3 ^ 40 * 6146847 * 2
def baseEnd_6146847 : Nat := 1052095673549139055514557

theorem tailTrace_6146847 : CollatzResearch.WordTrace tailWord_6146847 prefixEnd_6146847 1052095673549139055514557 := by
  unfold tailWord_6146847
  simp only [CollatzResearch.WordTrace]
  refine ⟨224193928362030591734030795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149462618908020394489353863 224193928362030591734030795)
  ·
    refine ⟨336290892543045887601046193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224193928362030591734030795 336290892543045887601046193)
    ·
      refine ⟨252218169407284415700784645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336290892543045887601046193 252218169407284415700784645)
      ·
        refine ⟨47290906763865827943897121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252218169407284415700784645 47290906763865827943897121)
        ·
          refine ⟨35468180072899370957922841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47290906763865827943897121 35468180072899370957922841)
          ·
            refine ⟨26601135054674528218442131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35468180072899370957922841 26601135054674528218442131)
            ·
              refine ⟨39901702582011792327663197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26601135054674528218442131 39901702582011792327663197)
              ·
                refine ⟨14963138468254422122873699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39901702582011792327663197 14963138468254422122873699)
                ·
                  refine ⟨22444707702381633184310549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14963138468254422122873699 22444707702381633184310549)
                  ·
                    refine ⟨1052095673549139055514557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22444707702381633184310549 1052095673549139055514557)
                    ·
                      rfl

theorem cell23_6146847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_6146847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146847 prefixEnd_6146847 := by exact prefixLift 6146847
  have htrace : WordTrace (prefixWord ++ tailWord_6146847) baseStart_6146847 baseEnd_6146847 := by
    simpa [prefixWord, tailWord_6146847, baseEnd_6146847] using wordTrace_append hprefix tailTrace_6146847
  have hstable : (prefixWord ++ tailWord_6146847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146847).length < 2 ^ (prefixWord ++ tailWord_6146847).sum := by decide
  have hdescent : baseEnd_6146847 < baseStart_6146847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146858 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6146858 : Nat := 118140960795 + 6146858 * 2 ^ 59
def prefixEnd_6146858 : Nat := 4983230072969 + 3 ^ 40 * 6146858 * 2
def baseEnd_6146858 : Nat := 3156292668934616623506121

theorem tailTrace_6146858 : CollatzResearch.WordTrace tailWord_6146858 prefixEnd_6146858 3156292668934616623506121 := by
  unfold tailWord_6146858
  simp only [CollatzResearch.WordTrace]
  refine ⟨56048582391247685153170307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149462886376660493741787485 56048582391247685153170307)
  ·
    refine ⟨84072873586871527729755461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56048582391247685153170307 84072873586871527729755461)
    ·
      refine ⟨15763663797538411449329149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84072873586871527729755461 15763663797538411449329149)
      ·
        refine ⟨5911373924076904293498431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15763663797538411449329149 5911373924076904293498431)
        ·
          refine ⟨8867060886115356440247647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911373924076904293498431 8867060886115356440247647)
          ·
            refine ⟨13300591329173034660371471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867060886115356440247647 13300591329173034660371471)
            ·
              refine ⟨19950886993759551990557207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300591329173034660371471 19950886993759551990557207)
              ·
                refine ⟨29926330490639327985835811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19950886993759551990557207 29926330490639327985835811)
                ·
                  refine ⟨44889495735958991978753717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29926330490639327985835811 44889495735958991978753717)
                  ·
                    refine ⟨4208390225246155498008161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44889495735958991978753717 4208390225246155498008161)
                    ·
                      refine ⟨3156292668934616623506121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208390225246155498008161 3156292668934616623506121)
                      ·
                        rfl

theorem cell23_6146858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6146858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146858 prefixEnd_6146858 := by exact prefixLift 6146858
  have htrace : WordTrace (prefixWord ++ tailWord_6146858) baseStart_6146858 baseEnd_6146858 := by
    simpa [prefixWord, tailWord_6146858, baseEnd_6146858] using wordTrace_append hprefix tailTrace_6146858
  have hstable : (prefixWord ++ tailWord_6146858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146858).length < 2 ^ (prefixWord ++ tailWord_6146858).sum := by decide
  have hdescent : baseEnd_6146858 < baseStart_6146858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146888 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 1, 2, 2]
def baseStart_6146888 : Nat := 118140960795 + 6146888 * 2 ^ 59
def prefixEnd_6146888 : Nat := 4983230072969 + 3 ^ 40 * 6146888 * 2
def baseEnd_6146888 : Nat := 3156308073354251506130983

theorem tailTrace_6146888 : CollatzResearch.WordTrace tailWord_6146888 prefixEnd_6146888 3156308073354251506130983 := by
  unfold tailWord_6146888
  simp only [CollatzResearch.WordTrace]
  refine ⟨112097711877441027868136659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149463615836588037157515545 112097711877441027868136659)
  ·
    refine ⟨168146567816161541802204989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112097711877441027868136659 168146567816161541802204989)
    ·
      refine ⟨63054962931060578175826871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168146567816161541802204989 63054962931060578175826871)
      ·
        refine ⟨94582444396590867263740307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63054962931060578175826871 94582444396590867263740307)
        ·
          refine ⟨141873666594886300895610461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94582444396590867263740307 141873666594886300895610461)
          ·
            refine ⟨53202624973082362835853923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141873666594886300895610461 53202624973082362835853923)
            ·
              refine ⟨79803937459623544253780885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53202624973082362835853923 79803937459623544253780885)
              ·
                refine ⟨3740809568419853636895979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79803937459623544253780885 3740809568419853636895979)
                ·
                  refine ⟨5611214352629780455343969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740809568419853636895979 5611214352629780455343969)
                  ·
                    refine ⟨4208410764472335341507977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5611214352629780455343969 4208410764472335341507977)
                    ·
                      refine ⟨3156308073354251506130983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208410764472335341507977 3156308073354251506130983)
                      ·
                        rfl

theorem cell23_6146888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_6146888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146888 prefixEnd_6146888 := by exact prefixLift 6146888
  have htrace : WordTrace (prefixWord ++ tailWord_6146888) baseStart_6146888 baseEnd_6146888 := by
    simpa [prefixWord, tailWord_6146888, baseEnd_6146888] using wordTrace_append hprefix tailTrace_6146888
  have hstable : (prefixWord ++ tailWord_6146888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146888).length < 2 ^ (prefixWord ++ tailWord_6146888).sum := by decide
  have hdescent : baseEnd_6146888 < baseStart_6146888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146908 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6146908 : Nat := 118140960795 + 6146908 * 2 ^ 59
def prefixEnd_6146908 : Nat := 4983230072969 + 3 ^ 40 * 6146908 * 2
def baseEnd_6146908 : Nat := 3156318342967341427880891

theorem tailTrace_6146908 : CollatzResearch.WordTrace tailWord_6146908 prefixEnd_6146908 3156318342967341427880891 := by
  unfold tailWord_6146908
  simp only [CollatzResearch.WordTrace]
  refine ⟨112098076607404799576000689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149464102143206399434667585 112098076607404799576000689)
  ·
    refine ⟨84073557455553599682000517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112098076607404799576000689 84073557455553599682000517)
    ·
      refine ⟨15763792022916299940375097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84073557455553599682000517 15763792022916299940375097)
      ·
        refine ⟨11822844017187224955281323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15763792022916299940375097 11822844017187224955281323)
        ·
          refine ⟨17734266025780837432921985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11822844017187224955281323 17734266025780837432921985)
          ·
            refine ⟨13300699519335628074691489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17734266025780837432921985 13300699519335628074691489)
            ·
              refine ⟨9975524639501721056018617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13300699519335628074691489 9975524639501721056018617)
              ·
                refine ⟨7481643479626290792013963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9975524639501721056018617 7481643479626290792013963)
                ·
                  refine ⟨11222465219439436188020945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7481643479626290792013963 11222465219439436188020945)
                  ·
                    refine ⟨8416848914579577141015709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11222465219439436188020945 8416848914579577141015709)
                    ·
                      refine ⟨3156318342967341427880891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8416848914579577141015709 3156318342967341427880891)
                      ·
                        rfl

theorem cell23_6146908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6146908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146908 prefixEnd_6146908 := by exact prefixLift 6146908
  have htrace : WordTrace (prefixWord ++ tailWord_6146908) baseStart_6146908 baseEnd_6146908 := by
    simpa [prefixWord, tailWord_6146908, baseEnd_6146908] using wordTrace_append hprefix tailTrace_6146908
  have hstable : (prefixWord ++ tailWord_6146908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146908).length < 2 ^ (prefixWord ++ tailWord_6146908).sum := by decide
  have hdescent : baseEnd_6146908 < baseStart_6146908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146917 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6146917 : Nat := 118140960795 + 6146917 * 2 ^ 59
def prefixEnd_6146917 : Nat := 4983230072969 + 3 ^ 40 * 6146917 * 2
def baseEnd_6146917 : Nat := 3156322964293231892668349

theorem tailTrace_6146917 : CollatzResearch.WordTrace tailWord_6146917 prefixEnd_6146917 3156322964293231892668349 := by
  unfold tailWord_6146917
  simp only [CollatzResearch.WordTrace]
  refine ⟨224196481471776993689079005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149464320981184662459386003 224196481471776993689079005)
  ·
    refine ⟨84073680551916372633404627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224196481471776993689079005 84073680551916372633404627)
    ·
      refine ⟨126110520827874558950106941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84073680551916372633404627 126110520827874558950106941)
      ·
        refine ⟨47291445310452959606290103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126110520827874558950106941 47291445310452959606290103)
        ·
          refine ⟨70937167965679439409435155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47291445310452959606290103 70937167965679439409435155)
          ·
            refine ⟨106405751948519159114152733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70937167965679439409435155 106405751948519159114152733)
            ·
              refine ⟨39902156980694684667807275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106405751948519159114152733 39902156980694684667807275)
              ·
                refine ⟨59853235471042027001710913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39902156980694684667807275 59853235471042027001710913)
                ·
                  refine ⟨44889926603281520251283185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59853235471042027001710913 44889926603281520251283185)
                  ·
                    refine ⟨33667444952461140188462389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44889926603281520251283185 33667444952461140188462389)
                    ·
                      refine ⟨3156322964293231892668349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33667444952461140188462389 3156322964293231892668349)
                      ·
                        rfl

theorem cell23_6146917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6146917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146917 prefixEnd_6146917 := by exact prefixLift 6146917
  have htrace : WordTrace (prefixWord ++ tailWord_6146917) baseStart_6146917 baseEnd_6146917 := by
    simpa [prefixWord, tailWord_6146917, baseEnd_6146917] using wordTrace_append hprefix tailTrace_6146917
  have hstable : (prefixWord ++ tailWord_6146917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146917).length < 2 ^ (prefixWord ++ tailWord_6146917).sum := by decide
  have hdescent : baseEnd_6146917 < baseStart_6146917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146931 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 1, 3, 2]
def baseStart_6146931 : Nat := 118140960795 + 6146931 * 2 ^ 59
def prefixEnd_6146931 : Nat := 4983230072969 + 3 ^ 40 * 6146931 * 2
def baseEnd_6146931 : Nat := 3156330153022394837893285

theorem tailTrace_6146931 : CollatzResearch.WordTrace tailWord_6146931 prefixEnd_6146931 3156330153022394837893285 := by
  unfold tailWord_6146931
  simp only [CollatzResearch.WordTrace]
  refine ⟨224196992093726274080088647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149464661395817516053392431 224196992093726274080088647)
  ·
    refine ⟨336295488140589411120132971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224196992093726274080088647 336295488140589411120132971)
    ·
      refine ⟨504443232210884116680199457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336295488140589411120132971 504443232210884116680199457)
      ·
        refine ⟨378332424158163087510149593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504443232210884116680199457 378332424158163087510149593)
        ·
          refine ⟨283749318118622315632612195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378332424158163087510149593 283749318118622315632612195)
          ·
            refine ⟨425623977177933473448918293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283749318118622315632612195 425623977177933473448918293)
            ·
              refine ⟨19951123930215631567918045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 425623977177933473448918293 19951123930215631567918045)
              ·
                refine ⟨7481671473830861837969267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19951123930215631567918045 7481671473830861837969267)
                ·
                  refine ⟨11222507210746292756953901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7481671473830861837969267 11222507210746292756953901)
                  ·
                    refine ⟨4208440204029859783857713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11222507210746292756953901 4208440204029859783857713)
                    ·
                      refine ⟨3156330153022394837893285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208440204029859783857713 3156330153022394837893285)
                      ·
                        rfl

theorem cell23_6146931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 3, 2].length) (baseStart_6146931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146931 prefixEnd_6146931 := by exact prefixLift 6146931
  have htrace : WordTrace (prefixWord ++ tailWord_6146931) baseStart_6146931 baseEnd_6146931 := by
    simpa [prefixWord, tailWord_6146931, baseEnd_6146931] using wordTrace_append hprefix tailTrace_6146931
  have hstable : (prefixWord ++ tailWord_6146931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146931).length < 2 ^ (prefixWord ++ tailWord_6146931).sum := by decide
  have hdescent : baseEnd_6146931 < baseStart_6146931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146944 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 5, 4, 2]
def baseStart_6146944 : Nat := 118140960795 + 6146944 * 2 ^ 59
def prefixEnd_6146944 : Nat := 4983230072969 + 3 ^ 40 * 6146944 * 2
def baseEnd_6146944 : Nat := 3156336828270903287030725

theorem tailTrace_6146944 : CollatzResearch.WordTrace tailWord_6146944 prefixEnd_6146944 3156336828270903287030725 := by
  unfold tailWord_6146944
  simp only [CollatzResearch.WordTrace]
  refine ⟨112098733121339588650155943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149464977495119451533541257 112098733121339588650155943)
  ·
    refine ⟨168148099682009382975233915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112098733121339588650155943 168148099682009382975233915)
    ·
      refine ⟨252222149523014074462850873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168148099682009382975233915 252222149523014074462850873)
      ·
        refine ⟨189166612142260555847138155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252222149523014074462850873 189166612142260555847138155)
        ·
          refine ⟨283749918213390833770707233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189166612142260555847138155 283749918213390833770707233)
          ·
            refine ⟨212812438660043125328030425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283749918213390833770707233 212812438660043125328030425)
            ·
              refine ⟨159609328995032343996022819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212812438660043125328030425 159609328995032343996022819)
              ·
                refine ⟨239413993492548515994034229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159609328995032343996022819 239413993492548515994034229)
                ·
                  refine ⟨22445061889926423374440709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 239413993492548515994034229 22445061889926423374440709)
                  ·
                    refine ⟨4208449104361204382707633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22445061889926423374440709 4208449104361204382707633)
                    ·
                      refine ⟨3156336828270903287030725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208449104361204382707633 3156336828270903287030725)
                      ·
                        rfl

theorem cell23_6146944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_6146944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146944 prefixEnd_6146944 := by exact prefixLift 6146944
  have htrace : WordTrace (prefixWord ++ tailWord_6146944) baseStart_6146944 baseEnd_6146944 := by
    simpa [prefixWord, tailWord_6146944, baseEnd_6146944] using wordTrace_append hprefix tailTrace_6146944
  have hstable : (prefixWord ++ tailWord_6146944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146944).length < 2 ^ (prefixWord ++ tailWord_6146944).sum := by decide
  have hdescent : baseEnd_6146944 < baseStart_6146944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146947 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_6146947 : Nat := 118140960795 + 6146947 * 2 ^ 59
def prefixEnd_6146947 : Nat := 4983230072969 + 3 ^ 40 * 6146947 * 2
def baseEnd_6146947 : Nat := 3156338368712866775293211

theorem tailTrace_6146947 : CollatzResearch.WordTrace tailWord_6146947 prefixEnd_6146947 3156338368712866775293211 := by
  unfold tailWord_6146947
  simp only [CollatzResearch.WordTrace]
  refine ⟨224197575661668308812671095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149465050441112205875114063 224197575661668308812671095)
  ·
    refine ⟨336296363492502463219006643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224197575661668308812671095 336296363492502463219006643)
    ·
      refine ⟨504444545238753694828509965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336296363492502463219006643 504444545238753694828509965)
      ·
        refine ⟨189166704464532635560691237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504444545238753694828509965 189166704464532635560691237)
        ·
          refine ⟨35468757087099869167629607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189166704464532635560691237 35468757087099869167629607)
          ·
            refine ⟨53203135630649803751444411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35468757087099869167629607 53203135630649803751444411)
            ·
              refine ⟨79804703445974705627166617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53203135630649803751444411 79804703445974705627166617)
              ·
                refine ⟨59853527584481029220374963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79804703445974705627166617 59853527584481029220374963)
                ·
                  refine ⟨89780291376721543830562445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59853527584481029220374963 89780291376721543830562445)
                  ·
                    refine ⟨33667609266270578936460917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89780291376721543830562445 33667609266270578936460917)
                    ·
                      refine ⟨3156338368712866775293211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33667609266270578936460917 3156338368712866775293211)
                      ·
                        rfl

theorem cell23_6146947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_6146947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146947 prefixEnd_6146947 := by exact prefixLift 6146947
  have htrace : WordTrace (prefixWord ++ tailWord_6146947) baseStart_6146947 baseEnd_6146947 := by
    simpa [prefixWord, tailWord_6146947, baseEnd_6146947] using wordTrace_append hprefix tailTrace_6146947
  have hstable : (prefixWord ++ tailWord_6146947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146947).length < 2 ^ (prefixWord ++ tailWord_6146947).sum := by decide
  have hdescent : baseEnd_6146947 < baseStart_6146947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146964 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6146964 : Nat := 118140960795 + 6146964 * 2 ^ 59
def prefixEnd_6146964 : Nat := 4983230072969 + 3 ^ 40 * 6146964 * 2
def baseEnd_6146964 : Nat := 3156347097883993208780633

theorem tailTrace_6146964 : CollatzResearch.WordTrace tailWord_6146964 prefixEnd_6146964 3156347097883993208780633 := by
  unfold tailWord_6146964
  simp only [CollatzResearch.WordTrace]
  refine ⟨112099097851303360358019973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149465463801737813810693297 112099097851303360358019973)
  ·
    refine ⟨21018580847119380067128745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112099097851303360358019973 21018580847119380067128745)
    ·
      refine ⟨15763935635339535050346559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21018580847119380067128745 15763935635339535050346559)
      ·
        refine ⟨23645903453009302575519839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15763935635339535050346559 23645903453009302575519839)
        ·
          refine ⟨35468855179513953863279759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23645903453009302575519839 35468855179513953863279759)
          ·
            refine ⟨53203282769270930794919639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35468855179513953863279759 53203282769270930794919639)
            ·
              refine ⟨79804924153906396192379459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53203282769270930794919639 79804924153906396192379459)
              ·
                refine ⟨119707386230859594288569189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79804924153906396192379459 119707386230859594288569189)
                ·
                  refine ⟨22445134918286173929106723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119707386230859594288569189 22445134918286173929106723)
                  ·
                    refine ⟨33667702377429260893660085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22445134918286173929106723 33667702377429260893660085)
                    ·
                      refine ⟨3156347097883993208780633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33667702377429260893660085 3156347097883993208780633)
                      ·
                        rfl

theorem cell23_6146964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6146964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146964 prefixEnd_6146964 := by exact prefixLift 6146964
  have htrace : WordTrace (prefixWord ++ tailWord_6146964) baseStart_6146964 baseEnd_6146964 := by
    simpa [prefixWord, tailWord_6146964, baseEnd_6146964] using wordTrace_append hprefix tailTrace_6146964
  have hstable : (prefixWord ++ tailWord_6146964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146964).length < 2 ^ (prefixWord ++ tailWord_6146964).sum := by decide
  have hdescent : baseEnd_6146964 < baseStart_6146964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146967 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 9]
def baseStart_6146967 : Nat := 118140960795 + 6146967 * 2 ^ 59
def prefixEnd_6146967 : Nat := 4983230072969 + 3 ^ 40 * 6146967 * 2
def baseEnd_6146967 : Nat := 350705404258439633004791

theorem tailTrace_6146967 : CollatzResearch.WordTrace tailWord_6146967 prefixEnd_6146967 350705404258439633004791 := by
  unfold tailWord_6146967
  simp only [CollatzResearch.WordTrace]
  refine ⟨224198305121595852228399155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149465536747730568152266103 224198305121595852228399155)
  ·
    refine ⟨336297457682393778342598733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224198305121595852228399155 336297457682393778342598733)
    ·
      refine ⟨126111546630897666878474525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336297457682393778342598733 126111546630897666878474525)
      ·
        refine ⟨47291829986586625079427947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126111546630897666878474525 47291829986586625079427947)
        ·
          refine ⟨70937744979879937619141921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47291829986586625079427947 70937744979879937619141921)
          ·
            refine ⟨53203308734909953214356441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70937744979879937619141921 53203308734909953214356441)
            ·
              refine ⟨39902481551182464910767331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53203308734909953214356441 39902481551182464910767331)
              ·
                refine ⟨59853722326773697366150997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39902481551182464910767331 59853722326773697366150997)
                ·
                  refine ⟨350705404258439633004791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59853722326773697366150997 350705404258439633004791)
                  ·
                    rfl

theorem cell23_6146967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 9].length) (baseStart_6146967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146967 prefixEnd_6146967 := by exact prefixLift 6146967
  have htrace : WordTrace (prefixWord ++ tailWord_6146967) baseStart_6146967 baseEnd_6146967 := by
    simpa [prefixWord, tailWord_6146967, baseEnd_6146967] using wordTrace_append hprefix tailTrace_6146967
  have hstable : (prefixWord ++ tailWord_6146967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146967).length < 2 ^ (prefixWord ++ tailWord_6146967).sum := by decide
  have hdescent : baseEnd_6146967 < baseStart_6146967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6146978 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_6146978 : Nat := 118140960795 + 6146978 * 2 ^ 59
def prefixEnd_6146978 : Nat := 4983230072969 + 3 ^ 40 * 6146978 * 2
def baseEnd_6146978 : Nat := 3156354286613156154005569

theorem tailTrace_6146978 : CollatzResearch.WordTrace tailWord_6146978 prefixEnd_6146978 3156354286613156154005569 := by
  unfold tailWord_6146978
  simp only [CollatzResearch.WordTrace]
  refine ⟨56049676581139000276762397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149465804216370667404699725 56049676581139000276762397)
  ·
    refine ⟨21018628717927125103785899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56049676581139000276762397 21018628717927125103785899)
    ·
      refine ⟨31527943076890687655678849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21018628717927125103785899 31527943076890687655678849)
      ·
        refine ⟨23645957307668015741759137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31527943076890687655678849 23645957307668015741759137)
        ·
          refine ⟨17734467980751011806319353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23645957307668015741759137 17734467980751011806319353)
          ·
            refine ⟨13300850985563258854739515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17734467980751011806319353 13300850985563258854739515)
            ·
              refine ⟨19951276478344888282109273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300850985563258854739515 19951276478344888282109273)
              ·
                refine ⟨14963457358758666211581955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19951276478344888282109273 14963457358758666211581955)
                ·
                  refine ⟨22445186038137999317372933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14963457358758666211581955 22445186038137999317372933)
                  ·
                    refine ⟨4208472382150874872007425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22445186038137999317372933 4208472382150874872007425)
                    ·
                      refine ⟨3156354286613156154005569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208472382150874872007425 3156354286613156154005569)
                      ·
                        rfl

theorem cell23_6146978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_6146978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6146978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6146978 prefixEnd_6146978 := by exact prefixLift 6146978
  have htrace : WordTrace (prefixWord ++ tailWord_6146978) baseStart_6146978 baseEnd_6146978 := by
    simpa [prefixWord, tailWord_6146978, baseEnd_6146978] using wordTrace_append hprefix tailTrace_6146978
  have hstable : (prefixWord ++ tailWord_6146978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6146978).length < 2 ^ (prefixWord ++ tailWord_6146978).sum := by decide
  have hdescent : baseEnd_6146978 < baseStart_6146978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6146978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147001 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 5]
def baseStart_6147001 : Nat := 118140960795 + 6147001 * 2 ^ 59
def prefixEnd_6147001 : Nat := 4983230072969 + 3 ^ 40 * 6147001 * 2
def baseEnd_6147001 : Nat := 350707344074245507113107

theorem tailTrace_6147001 : CollatzResearch.WordTrace tailWord_6147001 prefixEnd_6147001 350707344074245507113107 := by
  unfold tailWord_6147001
  simp only [CollatzResearch.WordTrace]
  refine ⟨224199545203472676035136857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149466363468981784023424571 224199545203472676035136857)
  ·
    refine ⟨168149658902604507026352643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224199545203472676035136857 168149658902604507026352643)
    ·
      refine ⟨252224488353906760539528965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168149658902604507026352643 252224488353906760539528965)
      ·
        refine ⟨47292091566357517601161681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252224488353906760539528965 47292091566357517601161681)
        ·
          refine ⟨35469068674768138200871261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47292091566357517601161681 35469068674768138200871261)
          ·
            refine ⟨13300900753038051825326723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35469068674768138200871261 13300900753038051825326723)
            ·
              refine ⟨19951351129557077737990085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300900753038051825326723 19951351129557077737990085)
              ·
                refine ⟨3740878336791952075873141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19951351129557077737990085 3740878336791952075873141)
                ·
                  refine ⟨350707344074245507113107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3740878336791952075873141 350707344074245507113107)
                  ·
                    rfl

theorem cell23_6147001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 5].length) (baseStart_6147001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147001 prefixEnd_6147001 := by exact prefixLift 6147001
  have htrace : WordTrace (prefixWord ++ tailWord_6147001) baseStart_6147001 baseEnd_6147001 := by
    simpa [prefixWord, tailWord_6147001, baseEnd_6147001] using wordTrace_append hprefix tailTrace_6147001
  have hstable : (prefixWord ++ tailWord_6147001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147001).length < 2 ^ (prefixWord ++ tailWord_6147001).sum := by decide
  have hdescent : baseEnd_6147001 < baseStart_6147001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147007 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_6147007 : Nat := 118140960795 + 6147007 * 2 ^ 59
def prefixEnd_6147007 : Nat := 4983230072969 + 3 ^ 40 * 6147007 * 2
def baseEnd_6147007 : Nat := 3156369177552136540542935

theorem tailTrace_6147007 : CollatzResearch.WordTrace tailWord_6147007 prefixEnd_6147007 3156369177552136540542935 := by
  unfold tailWord_6147007
  simp only [CollatzResearch.WordTrace]
  refine ⟨224199764041450939059855275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149466509360967292706570183 224199764041450939059855275)
  ·
    refine ⟨336299646062176408589782913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224199764041450939059855275 336299646062176408589782913)
    ·
      refine ⟨252224734546632306442337185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336299646062176408589782913 252224734546632306442337185)
      ·
        refine ⟨189168550909974229831752889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252224734546632306442337185 189168550909974229831752889)
        ·
          refine ⟨141876413182480672373814667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189168550909974229831752889 141876413182480672373814667)
          ·
            refine ⟨212814619773721008560722001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141876413182480672373814667 212814619773721008560722001)
            ·
              refine ⟨159610964830290756420541501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212814619773721008560722001 159610964830290756420541501)
              ·
                refine ⟨59854111811359033657703063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159610964830290756420541501 59854111811359033657703063)
                ·
                  refine ⟨89781167717038550486554595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59854111811359033657703063 89781167717038550486554595)
                  ·
                    refine ⟨134671751575557825729831893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89781167717038550486554595 134671751575557825729831893)
                    ·
                      refine ⟨3156369177552136540542935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134671751575557825729831893 3156369177552136540542935)
                      ·
                        rfl

theorem cell23_6147007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_6147007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147007 prefixEnd_6147007 := by exact prefixLift 6147007
  have htrace : WordTrace (prefixWord ++ tailWord_6147007) baseStart_6147007 baseEnd_6147007 := by
    simpa [prefixWord, tailWord_6147007, baseEnd_6147007] using wordTrace_append hprefix tailTrace_6147007
  have hstable : (prefixWord ++ tailWord_6147007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147007).length < 2 ^ (prefixWord ++ tailWord_6147007).sum := by decide
  have hdescent : baseEnd_6147007 < baseStart_6147007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147095 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 1, 4]
def baseStart_6147095 : Nat := 118140960795 + 6147095 * 2 ^ 59
def prefixEnd_6147095 : Nat := 4983230072969 + 3 ^ 40 * 6147095 * 2
def baseEnd_6147095 : Nat := 1052138121283244065414177

theorem tailTrace_6147095 : CollatzResearch.WordTrace tailWord_6147095 prefixEnd_6147095 1052138121283244065414177 := by
  unfold tailWord_6147095
  simp only [CollatzResearch.WordTrace]
  refine ⟨224202973665132130089058739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149468649110088086726039159 224202973665132130089058739)
  ·
    refine ⟨336304460497698195133588109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224202973665132130089058739 336304460497698195133588109)
    ·
      refine ⟨126114172686636823175095541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336304460497698195133588109 126114172686636823175095541)
      ·
        refine ⟨11823203689372202172665207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126114172686636823175095541 11823203689372202172665207)
        ·
          refine ⟨17734805534058303258997811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11823203689372202172665207 17734805534058303258997811)
          ·
            refine ⟨26602208301087454888496717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17734805534058303258997811 26602208301087454888496717)
            ·
              refine ⟨9975828112907795583186269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26602208301087454888496717 9975828112907795583186269)
              ·
                refine ⟨3740935542340423343694851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9975828112907795583186269 3740935542340423343694851)
                ·
                  refine ⟨5611403313510635015542277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740935542340423343694851 5611403313510635015542277)
                  ·
                    refine ⟨1052138121283244065414177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5611403313510635015542277 1052138121283244065414177)
                    ·
                      rfl

theorem cell23_6147095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_6147095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147095 prefixEnd_6147095 := by exact prefixLift 6147095
  have htrace : WordTrace (prefixWord ++ tailWord_6147095) baseStart_6147095 baseEnd_6147095 := by
    simpa [prefixWord, tailWord_6147095, baseEnd_6147095] using wordTrace_append hprefix tailTrace_6147095
  have hstable : (prefixWord ++ tailWord_6147095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147095).length < 2 ^ (prefixWord ++ tailWord_6147095).sum := by decide
  have hdescent : baseEnd_6147095 < baseStart_6147095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147141 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 6, 2]
def baseStart_6147141 : Nat := 118140960795 + 6147141 * 2 ^ 59
def prefixEnd_6147141 : Nat := 4983230072969 + 3 ^ 40 * 6147141 * 2
def baseEnd_6147141 : Nat := 3156437983959839016267319

theorem tailTrace_6147141 : CollatzResearch.WordTrace tailWord_6147141 prefixEnd_6147141 3156437983959839016267319 := by
  unfold tailWord_6147141
  simp only [CollatzResearch.WordTrace]
  refine ⟨224204651422965479945233277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149469767615310319963488851 224204651422965479945233277)
  ·
    refine ⟨84076744283612054979462479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224204651422965479945233277 84076744283612054979462479)
    ·
      refine ⟨126115116425418082469193719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84076744283612054979462479 126115116425418082469193719)
      ·
        refine ⟨189172674638127123703790579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126115116425418082469193719 189172674638127123703790579)
        ·
          refine ⟨283759011957190685555685869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189172674638127123703790579 283759011957190685555685869)
          ·
            refine ⟨106409629483946507083382201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283759011957190685555685869 106409629483946507083382201)
            ·
              refine ⟨79807222112959880312536651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106409629483946507083382201 79807222112959880312536651)
              ·
                refine ⟨119710833169439820468804977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79807222112959880312536651 119710833169439820468804977)
                ·
                  refine ⟨89783124877079865351603733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119710833169439820468804977 89783124877079865351603733)
                  ·
                    refine ⟨4208583978613118688356425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89783124877079865351603733 4208583978613118688356425)
                    ·
                      refine ⟨3156437983959839016267319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208583978613118688356425 3156437983959839016267319)
                      ·
                        rfl

theorem cell23_6147141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_6147141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147141 prefixEnd_6147141 := by exact prefixLift 6147141
  have htrace : WordTrace (prefixWord ++ tailWord_6147141) baseStart_6147141 baseEnd_6147141 := by
    simpa [prefixWord, tailWord_6147141, baseEnd_6147141] using wordTrace_append hprefix tailTrace_6147141
  have hstable : (prefixWord ++ tailWord_6147141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147141).length < 2 ^ (prefixWord ++ tailWord_6147141).sum := by decide
  have hdescent : baseEnd_6147141 < baseStart_6147141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147168 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 2, 4]
def baseStart_6147168 : Nat := 118140960795 + 6147168 * 2 ^ 59
def prefixEnd_6147168 : Nat := 4983230072969 + 3 ^ 40 * 6147168 * 2
def baseEnd_6147168 : Nat := 1052150615979170136876565

theorem tailTrace_6147168 : CollatzResearch.WordTrace tailWord_6147168 prefixEnd_6147168 1052150615979170136876565 := by
  unfold tailWord_6147168
  simp only [CollatzResearch.WordTrace]
  refine ⟨112102818096933831778233079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149470424129245109037644105 112102818096933831778233079)
  ·
    refine ⟨168154227145400747667349619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112102818096933831778233079 168154227145400747667349619)
    ·
      refine ⟨252231340718101121501024429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168154227145400747667349619 252231340718101121501024429)
      ·
        refine ⟨94586752769287920562884161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252231340718101121501024429 94586752769287920562884161)
        ·
          refine ⟨70940064576965940422163121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94586752769287920562884161 70940064576965940422163121)
          ·
            refine ⟨53205048432724455316622341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70940064576965940422163121 53205048432724455316622341)
            ·
              refine ⟨9975946581135835371866689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53205048432724455316622341 9975946581135835371866689)
              ·
                refine ⟨7481959935851876528900017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9975946581135835371866689 7481959935851876528900017)
                ·
                  refine ⟨5611469951888907396675013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7481959935851876528900017 5611469951888907396675013)
                  ·
                    refine ⟨1052150615979170136876565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5611469951888907396675013 1052150615979170136876565)
                    ·
                      rfl

theorem cell23_6147168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 2, 4].length) (baseStart_6147168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147168 prefixEnd_6147168 := by exact prefixLift 6147168
  have htrace : WordTrace (prefixWord ++ tailWord_6147168) baseStart_6147168 baseEnd_6147168 := by
    simpa [prefixWord, tailWord_6147168, baseEnd_6147168] using wordTrace_append hprefix tailTrace_6147168
  have hstable : (prefixWord ++ tailWord_6147168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147168).length < 2 ^ (prefixWord ++ tailWord_6147168).sum := by decide
  have hdescent : baseEnd_6147168 < baseStart_6147168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147178 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_6147178 : Nat := 118140960795 + 6147178 * 2 ^ 59
def prefixEnd_6147178 : Nat := 4983230072969 + 3 ^ 40 * 6147178 * 2
def baseEnd_6147178 : Nat := 3156456982744055371504649

theorem tailTrace_6147178 : CollatzResearch.WordTrace tailWord_6147178 prefixEnd_6147178 3156456982744055371504649 := by
  unfold tailWord_6147178
  simp only [CollatzResearch.WordTrace]
  refine ⟨56051500230957858816082547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149470667282554290176220125 56051500230957858816082547)
  ·
    refine ⟨84077250346436788224123821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56051500230957858816082547 84077250346436788224123821)
    ·
      refine ⟨31528968879913795584046433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84077250346436788224123821 31528968879913795584046433)
      ·
        refine ⟨23646726659935346688034825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31528968879913795584046433 23646726659935346688034825)
        ·
          refine ⟨17735044994951510016026119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23646726659935346688034825 17735044994951510016026119)
          ·
            refine ⟨26602567492427265024039179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17735044994951510016026119 26602567492427265024039179)
            ·
              refine ⟨39903851238640897536058769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26602567492427265024039179 39903851238640897536058769)
              ·
                refine ⟨29927888428980673152044077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39903851238640897536058769 29927888428980673152044077)
                ·
                  refine ⟨11222958160867752432016529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29927888428980673152044077 11222958160867752432016529)
                  ·
                    refine ⟨8417218620650814324012397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11222958160867752432016529 8417218620650814324012397)
                    ·
                      refine ⟨3156456982744055371504649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8417218620650814324012397 3156456982744055371504649)
                      ·
                        rfl

theorem cell23_6147178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_6147178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147178 prefixEnd_6147178 := by exact prefixLift 6147178
  have htrace : WordTrace (prefixWord ++ tailWord_6147178) baseStart_6147178 baseEnd_6147178 := by
    simpa [prefixWord, tailWord_6147178, baseEnd_6147178] using wordTrace_append hprefix tailTrace_6147178
  have hstable : (prefixWord ++ tailWord_6147178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147178).length < 2 ^ (prefixWord ++ tailWord_6147178).sum := by decide
  have hdescent : baseEnd_6147178 < baseStart_6147178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147181 : List Nat := [1, 5, 1, 1, 2, 2, 3, 8]
def baseStart_6147181 : Nat := 118140960795 + 6147181 * 2 ^ 59
def prefixEnd_6147181 : Nat := 4983230072969 + 3 ^ 40 * 6147181 * 2
def baseEnd_6147181 : Nat := 116905871229111809621005

theorem tailTrace_6147181 : CollatzResearch.WordTrace tailWord_6147181 prefixEnd_6147181 116905871229111809621005 := by
  unfold tailWord_6147181
  simp only [CollatzResearch.WordTrace]
  refine ⟨224206110342820566776689397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149470740228547044517792931 224206110342820566776689397)
  ·
    refine ⟨21019322844639428135314631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224206110342820566776689397 21019322844639428135314631)
    ·
      refine ⟨31528984266959142202971947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21019322844639428135314631 31528984266959142202971947)
      ·
        refine ⟨47293476400438713304457921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31528984266959142202971947 47293476400438713304457921)
        ·
          refine ⟨35470107300329034978343441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47293476400438713304457921 35470107300329034978343441)
          ·
            refine ⟨26602580475246776233757581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35470107300329034978343441 26602580475246776233757581)
            ·
              refine ⟨9975967678217541087659093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26602580475246776233757581 9975967678217541087659093)
              ·
                refine ⟨116905871229111809621005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9975967678217541087659093 116905871229111809621005)
                ·
                  rfl

theorem cell23_6147181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 8].length) (baseStart_6147181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147181 prefixEnd_6147181 := by exact prefixLift 6147181
  have htrace : WordTrace (prefixWord ++ tailWord_6147181) baseStart_6147181 baseEnd_6147181 := by
    simpa [prefixWord, tailWord_6147181, baseEnd_6147181] using wordTrace_append hprefix tailTrace_6147181
  have hstable : (prefixWord ++ tailWord_6147181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147181).length < 2 ^ (prefixWord ++ tailWord_6147181).sum := by decide
  have hdescent : baseEnd_6147181 < baseStart_6147181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147242 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6147242 : Nat := 118140960795 + 6147242 * 2 ^ 59
def prefixEnd_6147242 : Nat := 4983230072969 + 3 ^ 40 * 6147242 * 2
def baseEnd_6147242 : Nat := 3156489845505943121104355

theorem tailTrace_6147242 : CollatzResearch.WordTrace tailWord_6147242 prefixEnd_6147242 3156489845505943121104355 := by
  unfold tailWord_6147242
  simp only [CollatzResearch.WordTrace]
  refine ⟨56052083798899893548664995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149472223463733049463106653 56052083798899893548664995)
  ·
    refine ⟨84078125698349840322997493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56052083798899893548664995 84078125698349840322997493)
    ·
      refine ⟨7882324284220297530281015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84078125698349840322997493 7882324284220297530281015)
      ·
        refine ⟨11823486426330446295421523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882324284220297530281015 11823486426330446295421523)
        ·
          refine ⟨17735229639495669443132285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11823486426330446295421523 17735229639495669443132285)
          ·
            refine ⟨6650711114810876041174607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17735229639495669443132285 6650711114810876041174607)
            ·
              refine ⟨9976066672216314061761911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650711114810876041174607 9976066672216314061761911)
              ·
                refine ⟨14964100008324471092642867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9976066672216314061761911 14964100008324471092642867)
                ·
                  refine ⟨22446150012486706638964301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14964100008324471092642867 22446150012486706638964301)
                  ·
                    refine ⟨8417306254682514989611613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22446150012486706638964301 8417306254682514989611613)
                    ·
                      refine ⟨3156489845505943121104355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8417306254682514989611613 3156489845505943121104355)
                      ·
                        rfl

theorem cell23_6147242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6147242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147242 prefixEnd_6147242 := by exact prefixLift 6147242
  have htrace : WordTrace (prefixWord ++ tailWord_6147242) baseStart_6147242 baseEnd_6147242 := by
    simpa [prefixWord, tailWord_6147242, baseEnd_6147242] using wordTrace_append hprefix tailTrace_6147242
  have hstable : (prefixWord ++ tailWord_6147242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147242).length < 2 ^ (prefixWord ++ tailWord_6147242).sum := by decide
  have hdescent : baseEnd_6147242 < baseStart_6147242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147251 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 3]
def baseStart_6147251 : Nat := 118140960795 + 6147251 * 2 ^ 59
def prefixEnd_6147251 : Nat := 4983230072969 + 3 ^ 40 * 6147251 * 2
def baseEnd_6147251 : Nat := 3156494466831833585891813

theorem tailTrace_6147251 : CollatzResearch.WordTrace tailWord_6147251 prefixEnd_6147251 3156494466831833585891813 := by
  unfold tailWord_6147251
  simp only [CollatzResearch.WordTrace]
  refine ⟨224208663452566968731737607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149472442301711312487825071 224208663452566968731737607)
  ·
    refine ⟨336312995178850453097606411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224208663452566968731737607 336312995178850453097606411)
    ·
      refine ⟨504469492768275679646409617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336312995178850453097606411 504469492768275679646409617)
      ·
        refine ⟨378352119576206759734807213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504469492768275679646409617 378352119576206759734807213)
        ·
          refine ⟨141882044841077534900552705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378352119576206759734807213 141882044841077534900552705)
          ·
            refine ⟨106411533630808151175414529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141882044841077534900552705 106411533630808151175414529)
            ·
              refine ⟨79808650223106113381560897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106411533630808151175414529 79808650223106113381560897)
              ·
                refine ⟨59856487667329585036170673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79808650223106113381560897 59856487667329585036170673)
                ·
                  refine ⟨44892365750497188777128005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59856487667329585036170673 44892365750497188777128005)
                  ·
                    refine ⟨8417318578218222895711501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44892365750497188777128005 8417318578218222895711501)
                    ·
                      refine ⟨3156494466831833585891813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8417318578218222895711501 3156494466831833585891813)
                      ·
                        rfl

theorem cell23_6147251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_6147251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147251 prefixEnd_6147251 := by exact prefixLift 6147251
  have htrace : WordTrace (prefixWord ++ tailWord_6147251) baseStart_6147251 baseEnd_6147251 := by
    simpa [prefixWord, tailWord_6147251, baseEnd_6147251] using wordTrace_append hprefix tailTrace_6147251
  have hstable : (prefixWord ++ tailWord_6147251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147251).length < 2 ^ (prefixWord ++ tailWord_6147251).sum := by decide
  have hdescent : baseEnd_6147251 < baseStart_6147251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147261 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_6147261 : Nat := 118140960795 + 6147261 * 2 ^ 59
def prefixEnd_6147261 : Nat := 4983230072969 + 3 ^ 40 * 6147261 * 2
def baseEnd_6147261 : Nat := 3156499601638378546766767

theorem tailTrace_6147261 : CollatzResearch.WordTrace tailWord_6147261 prefixEnd_6147261 3156499601638378546766767 := by
  unfold tailWord_6147261
  simp only [CollatzResearch.WordTrace]
  refine ⟨224209028182530740439601637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149472685455020493626401091 224209028182530740439601637)
  ·
    refine ⟨42039192784224513832425307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224209028182530740439601637 42039192784224513832425307)
    ·
      refine ⟨63058789176336770748637961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42039192784224513832425307 63058789176336770748637961)
      ·
        refine ⟨47294091882252578061478471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63058789176336770748637961 47294091882252578061478471)
        ·
          refine ⟨70941137823378867092217707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47294091882252578061478471 70941137823378867092217707)
          ·
            refine ⟨106411706735068300638326561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70941137823378867092217707 106411706735068300638326561)
            ·
              refine ⟨79808780051301225478744921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106411706735068300638326561 79808780051301225478744921)
              ·
                refine ⟨59856585038475919109058691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79808780051301225478744921 59856585038475919109058691)
                ·
                  refine ⟨89784877557713878663588037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59856585038475919109058691 89784877557713878663588037)
                  ·
                    refine ⟨16834664542071352249422757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89784877557713878663588037 16834664542071352249422757)
                    ·
                      refine ⟨3156499601638378546766767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16834664542071352249422757 3156499601638378546766767)
                      ·
                        rfl

theorem cell23_6147261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_6147261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147261 prefixEnd_6147261 := by exact prefixLift 6147261
  have htrace : WordTrace (prefixWord ++ tailWord_6147261) baseStart_6147261 baseEnd_6147261 := by
    simpa [prefixWord, tailWord_6147261, baseEnd_6147261] using wordTrace_append hprefix tailTrace_6147261
  have hstable : (prefixWord ++ tailWord_6147261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147261).length < 2 ^ (prefixWord ++ tailWord_6147261).sum := by decide
  have hdescent : baseEnd_6147261 < baseStart_6147261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147282 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 2, 2, 2]
def baseStart_6147282 : Nat := 118140960795 + 6147282 * 2 ^ 59
def prefixEnd_6147282 : Nat := 4983230072969 + 3 ^ 40 * 6147282 * 2
def baseEnd_6147282 : Nat := 3156510384732122964604171

theorem tailTrace_6147282 : CollatzResearch.WordTrace tailWord_6147282 prefixEnd_6147282 3156510384732122964604171 := by
  unfold tailWord_6147282
  simp only [CollatzResearch.WordTrace]
  refine ⟨56052448528863665256529025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149473196076969774017410733 56052448528863665256529025)
  ·
    refine ⟨42039336396647748942396769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56052448528863665256529025 42039336396647748942396769)
    ·
      refine ⟨31529502297485811706797577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42039336396647748942396769 31529502297485811706797577)
      ·
        refine ⟨23647126723114358780098183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31529502297485811706797577 23647126723114358780098183)
        ·
          refine ⟨35470690084671538170147275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23647126723114358780098183 35470690084671538170147275)
          ·
            refine ⟨53206035127007307255220913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35470690084671538170147275 53206035127007307255220913)
            ·
              refine ⟨39904526345255480441415685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53206035127007307255220913 39904526345255480441415685)
              ·
                refine ⟨7482098689735402582765441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39904526345255480441415685 7482098689735402582765441)
                ·
                  refine ⟨5611574017301551937074081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7482098689735402582765441 5611574017301551937074081)
                  ·
                    refine ⟨4208680512976163952805561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5611574017301551937074081 4208680512976163952805561)
                    ·
                      refine ⟨3156510384732122964604171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208680512976163952805561 3156510384732122964604171)
                      ·
                        rfl

theorem cell23_6147282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_6147282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147282 prefixEnd_6147282 := by exact prefixLift 6147282
  have htrace : WordTrace (prefixWord ++ tailWord_6147282) baseStart_6147282 baseEnd_6147282 := by
    simpa [prefixWord, tailWord_6147282, baseEnd_6147282] using wordTrace_append hprefix tailTrace_6147282
  have hstable : (prefixWord ++ tailWord_6147282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147282).length < 2 ^ (prefixWord ++ tailWord_6147282).sum := by decide
  have hdescent : baseEnd_6147282 < baseStart_6147282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147316 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6147316 : Nat := 118140960795 + 6147316 * 2 ^ 59
def prefixEnd_6147316 : Nat := 4983230072969 + 3 ^ 40 * 6147316 * 2
def baseEnd_6147316 : Nat := 3156527843074375831579015

theorem tailTrace_6147316 : CollatzResearch.WordTrace tailWord_6147316 prefixEnd_6147316 3156527843074375831579015 := by
  unfold tailWord_6147316
  simp only [CollatzResearch.WordTrace]
  refine ⟨112105517098665742416426901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149474022798220989888569201 112105517098665742416426901)
  ·
    refine ⟨5254946113999956675770011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112105517098665742416426901 5254946113999956675770011)
    ·
      refine ⟨7882419170999935013655017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5254946113999956675770011 7882419170999935013655017)
      ·
        refine ⟨5911814378249951260241263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7882419170999935013655017 5911814378249951260241263)
        ·
          refine ⟨8867721567374926890361895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911814378249951260241263 8867721567374926890361895)
          ·
            refine ⟨13301582351062390335542843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867721567374926890361895 13301582351062390335542843)
            ·
              refine ⟨19952373526593585503314265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13301582351062390335542843 19952373526593585503314265)
              ·
                refine ⟨14964280144945189127485699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19952373526593585503314265 14964280144945189127485699)
                ·
                  refine ⟨22446420217417783691228549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14964280144945189127485699 22446420217417783691228549)
                  ·
                    refine ⟨4208703790765834442105353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22446420217417783691228549 4208703790765834442105353)
                    ·
                      refine ⟨3156527843074375831579015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208703790765834442105353 3156527843074375831579015)
                      ·
                        rfl

theorem cell23_6147316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6147316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147316 prefixEnd_6147316 := by exact prefixLift 6147316
  have htrace : WordTrace (prefixWord ++ tailWord_6147316) baseStart_6147316 baseEnd_6147316 := by
    simpa [prefixWord, tailWord_6147316, baseEnd_6147316] using wordTrace_append hprefix tailTrace_6147316
  have hstable : (prefixWord ++ tailWord_6147316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147316).length < 2 ^ (prefixWord ++ tailWord_6147316).sum := by decide
  have hdescent : baseEnd_6147316 < baseStart_6147316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147361 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 10]
def baseStart_6147361 : Nat := 118140960795 + 6147361 * 2 ^ 59
def prefixEnd_6147361 : Nat := 4983230072969 + 3 ^ 40 * 6147361 * 2
def baseEnd_6147361 : Nat := 350727883300425350612923

theorem tailTrace_6147361 : CollatzResearch.WordTrace tailWord_6147361 prefixEnd_6147361 350727883300425350612923 := by
  unfold tailWord_6147361
  simp only [CollatzResearch.WordTrace]
  refine ⟨224212675482168457518241937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149475116988112305012161291 224212675482168457518241937)
  ·
    refine ⟨168159506611626343138681453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224212675482168457518241937 168159506611626343138681453)
    ·
      refine ⟨63059814979359878677005545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168159506611626343138681453 63059814979359878677005545)
      ·
        refine ⟨47294861234519909007754159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63059814979359878677005545 47294861234519909007754159)
        ·
          refine ⟨70942291851779863511631239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47294861234519909007754159 70942291851779863511631239)
          ·
            refine ⟨106413437777669795267446859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70942291851779863511631239 106413437777669795267446859)
            ·
              refine ⟨159620156666504692901170289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106413437777669795267446859 159620156666504692901170289)
              ·
                refine ⟨119715117499878519675877717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159620156666504692901170289 119715117499878519675877717)
                ·
                  refine ⟨350727883300425350612923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 119715117499878519675877717 350727883300425350612923)
                  ·
                    rfl

theorem cell23_6147361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 10].length) (baseStart_6147361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147361 prefixEnd_6147361 := by exact prefixLift 6147361
  have htrace : WordTrace (prefixWord ++ tailWord_6147361) baseStart_6147361 baseEnd_6147361 := by
    simpa [prefixWord, tailWord_6147361, baseEnd_6147361] using wordTrace_append hprefix tailTrace_6147361
  have hstable : (prefixWord ++ tailWord_6147361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147361).length < 2 ^ (prefixWord ++ tailWord_6147361).sum := by decide
  have hdescent : baseEnd_6147361 < baseStart_6147361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147365 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_6147365 : Nat := 118140960795 + 6147365 * 2 ^ 59
def prefixEnd_6147365 : Nat := 4983230072969 + 3 ^ 40 * 6147365 * 2
def baseEnd_6147365 : Nat := 1052184334542148713288763

theorem tailTrace_6147365 : CollatzResearch.WordTrace tailWord_6147365 prefixEnd_6147365 1052184334542148713288763 := by
  unfold tailWord_6147365
  simp only [CollatzResearch.WordTrace]
  refine ⟨224212821374153966201387549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149475214249435977467591699 224212821374153966201387549)
  ·
    refine ⟨84079808015307737325520331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224212821374153966201387549 84079808015307737325520331)
    ·
      refine ⟨126119712022961605988280497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84079808015307737325520331 126119712022961605988280497)
      ·
        refine ⟨94589784017221204491210373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126119712022961605988280497 94589784017221204491210373)
        ·
          refine ⟨17735584503228975842101945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94589784017221204491210373 17735584503228975842101945)
          ·
            refine ⟨13301688377421731881576459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17735584503228975842101945 13301688377421731881576459)
            ·
              refine ⟨19952532566132597822364689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13301688377421731881576459 19952532566132597822364689)
              ·
                refine ⟨14964399424599448366773517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19952532566132597822364689 14964399424599448366773517)
                ·
                  refine ⟨5611649784224793137540069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14964399424599448366773517 5611649784224793137540069)
                  ·
                    refine ⟨1052184334542148713288763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5611649784224793137540069 1052184334542148713288763)
                    ·
                      rfl

theorem cell23_6147365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_6147365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147365 prefixEnd_6147365 := by exact prefixLift 6147365
  have htrace : WordTrace (prefixWord ++ tailWord_6147365) baseStart_6147365 baseEnd_6147365 := by
    simpa [prefixWord, tailWord_6147365, baseEnd_6147365] using wordTrace_append hprefix tailTrace_6147365
  have hstable : (prefixWord ++ tailWord_6147365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147365).length < 2 ^ (prefixWord ++ tailWord_6147365).sum := by decide
  have hdescent : baseEnd_6147365 < baseStart_6147365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147415 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 1, 5, 2]
def baseStart_6147415 : Nat := 118140960795 + 6147415 * 2 ^ 59
def prefixEnd_6147415 : Nat := 4983230072969 + 3 ^ 40 * 6147415 * 2
def baseEnd_6147415 : Nat := 3156578677659170944241059

theorem tailTrace_6147415 : CollatzResearch.WordTrace tailWord_6147415 prefixEnd_6147415 3156578677659170944241059 := by
  unfold tailWord_6147415
  simp only [CollatzResearch.WordTrace]
  refine ⟨224214645023972824740707699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149476430015981883160471799 224214645023972824740707699)
  ·
    refine ⟨336321967535959237111061549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224214645023972824740707699 336321967535959237111061549)
    ·
      refine ⟨126120737825984713916648081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336321967535959237111061549 126120737825984713916648081)
      ·
        refine ⟨94590553369488535437486061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126120737825984713916648081 94590553369488535437486061)
        ·
          refine ⟨35471457513558200789057273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94590553369488535437486061 35471457513558200789057273)
          ·
            refine ⟨26603593135168650591792955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35471457513558200789057273 26603593135168650591792955)
            ·
              refine ⟨39905389702752975887689433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26603593135168650591792955 39905389702752975887689433)
              ·
                refine ⟨29929042277064731915767075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39905389702752975887689433 29929042277064731915767075)
                ·
                  refine ⟨44893563415597097873650613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29929042277064731915767075 44893563415597097873650613)
                  ·
                    refine ⟨4208771570212227925654745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44893563415597097873650613 4208771570212227925654745)
                    ·
                      refine ⟨3156578677659170944241059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208771570212227925654745 3156578677659170944241059)
                      ·
                        rfl

theorem cell23_6147415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_6147415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147415 prefixEnd_6147415 := by exact prefixLift 6147415
  have htrace : WordTrace (prefixWord ++ tailWord_6147415) baseStart_6147415 baseEnd_6147415 := by
    simpa [prefixWord, tailWord_6147415, baseEnd_6147415] using wordTrace_append hprefix tailTrace_6147415
  have hstable : (prefixWord ++ tailWord_6147415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147415).length < 2 ^ (prefixWord ++ tailWord_6147415).sum := by decide
  have hdescent : baseEnd_6147415 < baseStart_6147415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147468 : List Nat := [2, 2, 1, 2, 1, 3, 4, 8]
def baseStart_6147468 : Nat := 118140960795 + 6147468 * 2 ^ 59
def prefixEnd_6147468 : Nat := 4983230072969 + 3 ^ 40 * 6147468 * 2
def baseEnd_6147468 : Nat := 116911329338291082847345

theorem tailTrace_6147468 : CollatzResearch.WordTrace tailWord_6147468 prefixEnd_6147468 116911329338291082847345 := by
  unfold tailWord_6147468
  simp only [CollatzResearch.WordTrace]
  refine ⟨112108289046390407396193529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149477718728520543194924705 112108289046390407396193529)
  ·
    refine ⟨84081216784792805547145147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112108289046390407396193529 84081216784792805547145147)
    ·
      refine ⟨126121825177189208320717721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84081216784792805547145147 126121825177189208320717721)
      ·
        refine ⟨94591368882891906240538291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126121825177189208320717721 94591368882891906240538291)
        ·
          refine ⟨141887053324337859360807437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94591368882891906240538291 141887053324337859360807437)
          ·
            refine ⟨53207644996626697260302789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141887053324337859360807437 53207644996626697260302789)
            ·
              refine ⟨9976433436867505736306773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53207644996626697260302789 9976433436867505736306773)
              ·
                refine ⟨116911329338291082847345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9976433436867505736306773 116911329338291082847345)
                ·
                  rfl

theorem cell23_6147468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 8].length) (baseStart_6147468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147468 prefixEnd_6147468 := by exact prefixLift 6147468
  have htrace : WordTrace (prefixWord ++ tailWord_6147468) baseStart_6147468 baseEnd_6147468 := by
    simpa [prefixWord, tailWord_6147468, baseEnd_6147468] using wordTrace_append hprefix tailTrace_6147468
  have hstable : (prefixWord ++ tailWord_6147468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147468).length < 2 ^ (prefixWord ++ tailWord_6147468).sum := by decide
  have hdescent : baseEnd_6147468 < baseStart_6147468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147496 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6147496 : Nat := 118140960795 + 6147496 * 2 ^ 59
def prefixEnd_6147496 : Nat := 4983230072969 + 3 ^ 40 * 6147496 * 2
def baseEnd_6147496 : Nat := 3156620269592185127328187

theorem tailTrace_6147496 : CollatzResearch.WordTrace tailWord_6147496 prefixEnd_6147496 3156620269592185127328187 := by
  unfold tailWord_6147496
  simp only [CollatzResearch.WordTrace]
  refine ⟨112108799668339687787203171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149478399557786250382937561 112108799668339687787203171)
  ·
    refine ⟨168163199502509531680804757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112108799668339687787203171 168163199502509531680804757)
    ·
      refine ⟨7882649976680134297537723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168163199502509531680804757 7882649976680134297537723)
      ·
        refine ⟨11823974965020201446306585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882649976680134297537723 11823974965020201446306585)
        ·
          refine ⟨8867981223765151084729939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11823974965020201446306585 8867981223765151084729939)
          ·
            refine ⟨13301971835647726627094909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8867981223765151084729939 13301971835647726627094909)
            ·
              refine ⟨4988239438367897485160591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13301971835647726627094909 4988239438367897485160591)
              ·
                refine ⟨7482359157551846227740887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4988239438367897485160591 7482359157551846227740887)
                ·
                  refine ⟨11223538736327769341611331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482359157551846227740887 11223538736327769341611331)
                  ·
                    refine ⟨16835308104491654012416997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11223538736327769341611331 16835308104491654012416997)
                    ·
                      refine ⟨3156620269592185127328187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16835308104491654012416997 3156620269592185127328187)
                      ·
                        rfl

theorem cell23_6147496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6147496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147496 prefixEnd_6147496 := by exact prefixLift 6147496
  have htrace : WordTrace (prefixWord ++ tailWord_6147496) baseStart_6147496 baseEnd_6147496 := by
    simpa [prefixWord, tailWord_6147496, baseEnd_6147496] using wordTrace_append hprefix tailTrace_6147496
  have hstable : (prefixWord ++ tailWord_6147496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147496).length < 2 ^ (prefixWord ++ tailWord_6147496).sum := by decide
  have hdescent : baseEnd_6147496 < baseStart_6147496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147512 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 2, 1, 3]
def baseStart_6147512 : Nat := 118140960795 + 6147512 * 2 ^ 59
def prefixEnd_6147512 : Nat := 4983230072969 + 3 ^ 40 * 6147512 * 2
def baseEnd_6147512 : Nat := 3156628485282657064728113

theorem tailTrace_6147512 : CollatzResearch.WordTrace tailWord_6147512 prefixEnd_6147512 3156628485282657064728113 := by
  unfold tailWord_6147512
  simp only [CollatzResearch.WordTrace]
  refine ⟨112109091452310705153494395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149478788603080940204659193 112109091452310705153494395)
  ·
    refine ⟨168163637178466057730241593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112109091452310705153494395 168163637178466057730241593)
    ·
      refine ⟨126122727883849543297681195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168163637178466057730241593 126122727883849543297681195)
      ·
        refine ⟨189184091825774314946521793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126122727883849543297681195 189184091825774314946521793)
        ·
          refine ⟨141888068869330736209891345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189184091825774314946521793 141888068869330736209891345)
          ·
            refine ⟨106416051651998052157418509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141888068869330736209891345 106416051651998052157418509)
            ·
              refine ⟨39906019369499269559031941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106416051651998052157418509 39906019369499269559031941)
              ·
                refine ⟨7482378631781113042318489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39906019369499269559031941 7482378631781113042318489)
                ·
                  refine ⟨5611783973835834781738867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7482378631781113042318489 5611783973835834781738867)
                  ·
                    refine ⟨8417675960753752172608301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5611783973835834781738867 8417675960753752172608301)
                    ·
                      refine ⟨3156628485282657064728113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8417675960753752172608301 3156628485282657064728113)
                      ·
                        rfl

theorem cell23_6147512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 2, 1, 3].length) (baseStart_6147512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147512 prefixEnd_6147512 := by exact prefixLift 6147512
  have htrace : WordTrace (prefixWord ++ tailWord_6147512) baseStart_6147512 baseEnd_6147512 := by
    simpa [prefixWord, tailWord_6147512, baseEnd_6147512] using wordTrace_append hprefix tailTrace_6147512
  have hstable : (prefixWord ++ tailWord_6147512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147512).length < 2 ^ (prefixWord ++ tailWord_6147512).sum := by decide
  have hdescent : baseEnd_6147512 < baseStart_6147512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147569 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 4, 2, 2]
def baseStart_6147569 : Nat := 118140960795 + 6147569 * 2 ^ 59
def prefixEnd_6147569 : Nat := 4983230072969 + 3 ^ 40 * 6147569 * 2
def baseEnd_6147569 : Nat := 3156657753679963341715351

theorem tailTrace_6147569 : CollatzResearch.WordTrace tailWord_6147569 prefixEnd_6147569 3156657753679963341715351 := by
  unfold tailWord_6147569
  simp only [CollatzResearch.WordTrace]
  refine ⟨224220261865414909041813761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149480174576943272694542507 224220261865414909041813761)
  ·
    refine ⟨168165196399061181781360321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224220261865414909041813761 168165196399061181781360321)
    ·
      refine ⟨126123897299295886336020241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168165196399061181781360321 126123897299295886336020241)
      ·
        refine ⟨94592922974471914752015181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126123897299295886336020241 94592922974471914752015181)
        ·
          refine ⟨35472346115426968032005693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94592922974471914752015181 35472346115426968032005693)
          ·
            refine ⟨13302129793285113012002135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35472346115426968032005693 13302129793285113012002135)
            ·
              refine ⟨19953194689927669518003203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13302129793285113012002135 19953194689927669518003203)
              ·
                refine ⟨29929792034891504277004805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19953194689927669518003203 29929792034891504277004805)
                ·
                  refine ⟨5611836006542157051938401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29929792034891504277004805 5611836006542157051938401)
                  ·
                    refine ⟨4208877004906617788953801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5611836006542157051938401 4208877004906617788953801)
                    ·
                      refine ⟨3156657753679963341715351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208877004906617788953801 3156657753679963341715351)
                      ·
                        rfl

theorem cell23_6147569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 2, 2].length) (baseStart_6147569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147569 prefixEnd_6147569 := by exact prefixLift 6147569
  have htrace : WordTrace (prefixWord ++ tailWord_6147569) baseStart_6147569 baseEnd_6147569 := by
    simpa [prefixWord, tailWord_6147569, baseEnd_6147569] using wordTrace_append hprefix tailTrace_6147569
  have hstable : (prefixWord ++ tailWord_6147569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147569).length < 2 ^ (prefixWord ++ tailWord_6147569).sum := by decide
  have hdescent : baseEnd_6147569 < baseStart_6147569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147586 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6147586 : Nat := 118140960795 + 6147586 * 2 ^ 59
def prefixEnd_6147586 : Nat := 4983230072969 + 3 ^ 40 * 6147586 * 2
def baseEnd_6147586 : Nat := 3156666482851089775202773

theorem tailTrace_6147586 : CollatzResearch.WordTrace tailWord_6147586 prefixEnd_6147586 3156666482851089775202773 := by
  unfold tailWord_6147586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56055220476588330236295653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149480587937568880630121741 56055220476588330236295653)
  ·
    refine ⟨10510353839360311919305435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56055220476588330236295653 10510353839360311919305435)
    ·
      refine ⟨15765530759040467878958153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10510353839360311919305435 15765530759040467878958153)
      ·
        refine ⟨11824148069280350909218615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15765530759040467878958153 11824148069280350909218615)
        ·
          refine ⟨17736222103920526363827923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11824148069280350909218615 17736222103920526363827923)
          ·
            refine ⟨26604333155880789545741885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17736222103920526363827923 26604333155880789545741885)
            ·
              refine ⟨9976624933455296079653207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26604333155880789545741885 9976624933455296079653207)
              ·
                refine ⟨14964937400182944119479811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9976624933455296079653207 14964937400182944119479811)
                ·
                  refine ⟨22447406100274416179219717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14964937400182944119479811 22447406100274416179219717)
                  ·
                    refine ⟨4208888643801453033603697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22447406100274416179219717 4208888643801453033603697)
                    ·
                      refine ⟨3156666482851089775202773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208888643801453033603697 3156666482851089775202773)
                      ·
                        rfl

theorem cell23_6147586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6147586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147586 prefixEnd_6147586 := by exact prefixLift 6147586
  have htrace : WordTrace (prefixWord ++ tailWord_6147586) baseStart_6147586 baseEnd_6147586 := by
    simpa [prefixWord, tailWord_6147586, baseEnd_6147586] using wordTrace_append hprefix tailTrace_6147586
  have hstable : (prefixWord ++ tailWord_6147586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147586).length < 2 ^ (prefixWord ++ tailWord_6147586).sum := by decide
  have hdescent : baseEnd_6147586 < baseStart_6147586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147605 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_6147605 : Nat := 118140960795 + 6147605 * 2 ^ 59
def prefixEnd_6147605 : Nat := 4983230072969 + 3 ^ 40 * 6147605 * 2
def baseEnd_6147605 : Nat := 1052225412994508400288395

theorem tailTrace_6147605 : CollatzResearch.WordTrace tailWord_6147605 prefixEnd_6147605 1052225412994508400288395 := by
  unfold tailWord_6147605
  simp only [CollatzResearch.WordTrace]
  refine ⟨224221574893284487190124269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149481049928856324793416179 224221574893284487190124269)
  ·
    refine ⟨84083090584981682696296601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224221574893284487190124269 84083090584981682696296601)
    ·
      refine ⟨63062317938736262022222451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84083090584981682696296601 63062317938736262022222451)
      ·
        refine ⟨94593476908104393033333677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63062317938736262022222451 94593476908104393033333677)
        ·
          refine ⟨35472553840539147387500129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94593476908104393033333677 35472553840539147387500129)
          ·
            refine ⟨26604415380404360540625097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35472553840539147387500129 26604415380404360540625097)
            ·
              refine ⟨19953311535303270405468823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26604415380404360540625097 19953311535303270405468823)
              ·
                refine ⟨29929967302954905608203235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19953311535303270405468823 29929967302954905608203235)
                ·
                  refine ⟨44894950954432358412304853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29929967302954905608203235 44894950954432358412304853)
                  ·
                    refine ⟨1052225412994508400288395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44894950954432358412304853 1052225412994508400288395)
                    ·
                      rfl

theorem cell23_6147605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_6147605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147605 prefixEnd_6147605 := by exact prefixLift 6147605
  have htrace : WordTrace (prefixWord ++ tailWord_6147605) baseStart_6147605 baseEnd_6147605 := by
    simpa [prefixWord, tailWord_6147605, baseEnd_6147605] using wordTrace_append hprefix tailTrace_6147605
  have hstable : (prefixWord ++ tailWord_6147605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147605).length < 2 ^ (prefixWord ++ tailWord_6147605).sum := by decide
  have hdescent : baseEnd_6147605 < baseStart_6147605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147642 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2]
def baseStart_6147642 : Nat := 118140960795 + 6147642 * 2 ^ 59
def prefixEnd_6147642 : Nat := 4983230072969 + 3 ^ 40 * 6147642 * 2
def baseEnd_6147642 : Nat := 3156695237767741556102515

theorem tailTrace_6147642 : CollatzResearch.WordTrace tailWord_6147642 prefixEnd_6147642 3156695237767741556102515 := by
  unfold tailWord_6147642
  simp only [CollatzResearch.WordTrace]
  refine ⟨56055731098537610627305295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149481949596100295006147453 56055731098537610627305295)
  ·
    refine ⟨84083596647806415940957943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56055731098537610627305295 84083596647806415940957943)
    ·
      refine ⟨126125394971709623911436915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84083596647806415940957943 126125394971709623911436915)
      ·
        refine ⟨189188092457564435867155373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126125394971709623911436915 189188092457564435867155373)
        ·
          refine ⟨70945534671586663450183265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189188092457564435867155373 70945534671586663450183265)
          ·
            refine ⟨53209151003689997587637449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70945534671586663450183265 53209151003689997587637449)
            ·
              refine ⟨39906863252767498190728087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53209151003689997587637449 39906863252767498190728087)
              ·
                refine ⟨59860294879151247286092131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39906863252767498190728087 59860294879151247286092131)
                ·
                  refine ⟨89790442318726870929138197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59860294879151247286092131 89790442318726870929138197)
                  ·
                    refine ⟨4208926983690322074803353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89790442318726870929138197 4208926983690322074803353)
                    ·
                      refine ⟨3156695237767741556102515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208926983690322074803353 3156695237767741556102515)
                      ·
                        rfl

theorem cell23_6147642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2].length) (baseStart_6147642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147642 prefixEnd_6147642 := by exact prefixLift 6147642
  have htrace : WordTrace (prefixWord ++ tailWord_6147642) baseStart_6147642 baseEnd_6147642 := by
    simpa [prefixWord, tailWord_6147642, baseEnd_6147642] using wordTrace_append hprefix tailTrace_6147642
  have hstable : (prefixWord ++ tailWord_6147642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147642).length < 2 ^ (prefixWord ++ tailWord_6147642).sum := by decide
  have hdescent : baseEnd_6147642 < baseStart_6147642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147669 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_6147669 : Nat := 118140960795 + 6147669 * 2 ^ 59
def prefixEnd_6147669 : Nat := 4983230072969 + 3 ^ 40 * 6147669 * 2
def baseEnd_6147669 : Nat := 1052236367248470983488297

theorem tailTrace_6147669 : CollatzResearch.WordTrace tailWord_6147669 prefixEnd_6147669 1052236367248470983488297 := by
  unfold tailWord_6147669
  simp only [CollatzResearch.WordTrace]
  refine ⟨224223909165052626120454061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149482606110035084080302707 224223909165052626120454061)
  ·
    refine ⟨84083965936894734795170273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224223909165052626120454061 84083965936894734795170273)
    ·
      refine ⟨63062974452671051096377705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84083965936894734795170273 63062974452671051096377705)
      ·
        refine ⟨47297230839503288322283279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63062974452671051096377705 47297230839503288322283279)
        ·
          refine ⟨70945846259254932483424919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47297230839503288322283279 70945846259254932483424919)
          ·
            refine ⟨106418769388882398725137379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70945846259254932483424919 106418769388882398725137379)
            ·
              refine ⟨159628154083323598087706069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106418769388882398725137379 159628154083323598087706069)
              ·
                refine ⟨3741284861327896830180611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159628154083323598087706069 3741284861327896830180611)
                ·
                  refine ⟨5611927291991845245270917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3741284861327896830180611 5611927291991845245270917)
                  ·
                    refine ⟨1052236367248470983488297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5611927291991845245270917 1052236367248470983488297)
                    ·
                      rfl

theorem cell23_6147669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_6147669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147669 prefixEnd_6147669 := by exact prefixLift 6147669
  have htrace : WordTrace (prefixWord ++ tailWord_6147669) baseStart_6147669 baseEnd_6147669 := by
    simpa [prefixWord, tailWord_6147669, baseEnd_6147669] using wordTrace_append hprefix tailTrace_6147669
  have hstable : (prefixWord ++ tailWord_6147669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147669).length < 2 ^ (prefixWord ++ tailWord_6147669).sum := by decide
  have hdescent : baseEnd_6147669 < baseStart_6147669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147705 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_6147705 : Nat := 118140960795 + 6147705 * 2 ^ 59
def prefixEnd_6147705 : Nat := 4983230072969 + 3 ^ 40 * 6147705 * 2
def baseEnd_6147705 : Nat := 3156727587048974809614725

theorem tailTrace_6147705 : CollatzResearch.WordTrace tailWord_6147705 prefixEnd_6147705 3156727587048974809614725 := by
  unfold tailWord_6147705
  simp only [CollatzResearch.WordTrace]
  refine ⟨224225222192922204268764569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149483481461948136179176379 224225222192922204268764569)
  ·
    refine ⟨168168916644691653201573427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224225222192922204268764569 168168916644691653201573427)
    ·
      refine ⟨252253374967037479802360141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168168916644691653201573427 252253374967037479802360141)
      ·
        refine ⟨94595015612639054925885053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252253374967037479802360141 94595015612639054925885053)
        ·
          refine ⟨35473130854739645597206895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94595015612639054925885053 35473130854739645597206895)
          ·
            refine ⟨53209696282109468395810343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35473130854739645597206895 53209696282109468395810343)
            ·
              refine ⟨79814544423164202593715515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53209696282109468395810343 79814544423164202593715515)
              ·
                refine ⟨119721816634746303890573273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79814544423164202593715515 119721816634746303890573273)
                ·
                  refine ⟨89791362476059727917929955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119721816634746303890573273 89791362476059727917929955)
                  ·
                    refine ⟨134687043714089591876894933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89791362476059727917929955 134687043714089591876894933)
                    ·
                      refine ⟨3156727587048974809614725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134687043714089591876894933 3156727587048974809614725)
                      ·
                        rfl

theorem cell23_6147705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_6147705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147705 prefixEnd_6147705 := by exact prefixLift 6147705
  have htrace : WordTrace (prefixWord ++ tailWord_6147705) baseStart_6147705 baseEnd_6147705 := by
    simpa [prefixWord, tailWord_6147705, baseEnd_6147705] using wordTrace_append hprefix tailTrace_6147705
  have hstable : (prefixWord ++ tailWord_6147705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147705).length < 2 ^ (prefixWord ++ tailWord_6147705).sum := by decide
  have hdescent : baseEnd_6147705 < baseStart_6147705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147709 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 3]
def baseStart_6147709 : Nat := 118140960795 + 6147709 * 2 ^ 59
def prefixEnd_6147709 : Nat := 4983230072969 + 3 ^ 40 * 6147709 * 2
def baseEnd_6147709 : Nat := 3156729640971592793964707

theorem tailTrace_6147709 : CollatzResearch.WordTrace tailWord_6147709 prefixEnd_6147709 3156729640971592793964707 := by
  unfold tailWord_6147709
  simp only [CollatzResearch.WordTrace]
  refine ⟨224225368084907712951910181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149483578723271808634606787 224225368084907712951910181)
  ·
    refine ⟨42042256515920196178483159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224225368084907712951910181 42042256515920196178483159)
    ·
      refine ⟨63063384773880294267724739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42042256515920196178483159 63063384773880294267724739)
      ·
        refine ⟨94595077160820441401587109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63063384773880294267724739 94595077160820441401587109)
        ·
          refine ⟨17736576967653832762797583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94595077160820441401587109 17736576967653832762797583)
          ·
            refine ⟨26604865451480749144196375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17736576967653832762797583 26604865451480749144196375)
            ·
              refine ⟨39907298177221123716294563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26604865451480749144196375 39907298177221123716294563)
              ·
                refine ⟨59860947265831685574441845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39907298177221123716294563 59860947265831685574441845)
                ·
                  refine ⟨5611963806171720522603923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59860947265831685574441845 5611963806171720522603923)
                  ·
                    refine ⟨8417945709257580783905885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5611963806171720522603923 8417945709257580783905885)
                    ·
                      refine ⟨3156729640971592793964707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8417945709257580783905885 3156729640971592793964707)
                      ·
                        rfl

theorem cell23_6147709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_6147709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147709 prefixEnd_6147709 := by exact prefixLift 6147709
  have htrace : WordTrace (prefixWord ++ tailWord_6147709) baseStart_6147709 baseEnd_6147709 := by
    simpa [prefixWord, tailWord_6147709, baseEnd_6147709] using wordTrace_append hprefix tailTrace_6147709
  have hstable : (prefixWord ++ tailWord_6147709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147709).length < 2 ^ (prefixWord ++ tailWord_6147709).sum := by decide
  have hdescent : baseEnd_6147709 < baseStart_6147709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147712 : List Nat := [2, 1, 1, 2, 1, 4, 2, 4, 1, 5]
def baseStart_6147712 : Nat := 118140960795 + 6147712 * 2 ^ 59
def prefixEnd_6147712 : Nat := 4983230072969 + 3 ^ 40 * 6147712 * 2
def baseEnd_6147712 : Nat := 1052243727137852094075731

theorem tailTrace_6147712 : CollatzResearch.WordTrace tailWord_6147712 prefixEnd_6147712 1052243727137852094075731 := by
  unfold tailWord_6147712
  simp only [CollatzResearch.WordTrace]
  refine ⟨112112738751948422232134695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149483651669264562976179593 112112738751948422232134695)
  ·
    refine ⟨168169108127922633348202043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112112738751948422232134695 168169108127922633348202043)
    ·
      refine ⟨252253662191883950022303065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168169108127922633348202043 252253662191883950022303065)
      ·
        refine ⟨189190246643912962516727299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252253662191883950022303065 189190246643912962516727299)
        ·
          refine ⟨283785369965869443775090949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189190246643912962516727299 283785369965869443775090949)
          ·
            refine ⟨53209756868600520707829553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283785369965869443775090949 53209756868600520707829553)
            ·
              refine ⟨39907317651450390530872165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53209756868600520707829553 39907317651450390530872165)
              ·
                refine ⟨7482622059646948224538531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39907317651450390530872165 7482622059646948224538531)
                ·
                  refine ⟨11223933089470422336807797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482622059646948224538531 11223933089470422336807797)
                  ·
                    refine ⟨1052243727137852094075731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11223933089470422336807797 1052243727137852094075731)
                    ·
                      rfl

theorem cell23_6147712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 4, 1, 5].length) (baseStart_6147712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147712 prefixEnd_6147712 := by exact prefixLift 6147712
  have htrace : WordTrace (prefixWord ++ tailWord_6147712) baseStart_6147712 baseEnd_6147712 := by
    simpa [prefixWord, tailWord_6147712, baseEnd_6147712] using wordTrace_append hprefix tailTrace_6147712
  have hstable : (prefixWord ++ tailWord_6147712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147712).length < 2 ^ (prefixWord ++ tailWord_6147712).sum := by decide
  have hdescent : baseEnd_6147712 < baseStart_6147712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147719 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_6147719 : Nat := 118140960795 + 6147719 * 2 ^ 59
def prefixEnd_6147719 : Nat := 4983230072969 + 3 ^ 40 * 6147719 * 2
def baseEnd_6147719 : Nat := 3156734775778137754839661

theorem tailTrace_6147719 : CollatzResearch.WordTrace tailWord_6147719 prefixEnd_6147719 3156734775778137754839661 := by
  unfold tailWord_6147719
  simp only [CollatzResearch.WordTrace]
  refine ⟨224225732814871484659774211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149483821876580989773182807 224225732814871484659774211)
  ·
    refine ⟨336338599222307226989661317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224225732814871484659774211 336338599222307226989661317)
    ·
      refine ⟨63063487354182605060561497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336338599222307226989661317 63063487354182605060561497)
      ·
        refine ⟨47297615515636953795421123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63063487354182605060561497 47297615515636953795421123)
        ·
          refine ⟨70946423273455430693131685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47297615515636953795421123 70946423273455430693131685)
          ·
            refine ⟨13302454363772893254962191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70946423273455430693131685 13302454363772893254962191)
            ·
              refine ⟨19953681545659339882443287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13302454363772893254962191 19953681545659339882443287)
              ·
                refine ⟨29930522318489009823664931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19953681545659339882443287 29930522318489009823664931)
                ·
                  refine ⟨44895783477733514735497397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29930522318489009823664931 44895783477733514735497397)
                  ·
                    refine ⟨4208979701037517006452881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44895783477733514735497397 4208979701037517006452881)
                    ·
                      refine ⟨3156734775778137754839661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4208979701037517006452881 3156734775778137754839661)
                      ·
                        rfl

theorem cell23_6147719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_6147719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147719 prefixEnd_6147719 := by exact prefixLift 6147719
  have htrace : WordTrace (prefixWord ++ tailWord_6147719) baseStart_6147719 baseEnd_6147719 := by
    simpa [prefixWord, tailWord_6147719, baseEnd_6147719] using wordTrace_append hprefix tailTrace_6147719
  have hstable : (prefixWord ++ tailWord_6147719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147719).length < 2 ^ (prefixWord ++ tailWord_6147719).sum := by decide
  have hdescent : baseEnd_6147719 < baseStart_6147719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147743 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6147743 : Nat := 118140960795 + 6147743 * 2 ^ 59
def prefixEnd_6147743 : Nat := 4983230072969 + 3 ^ 40 * 6147743 * 2
def baseEnd_6147743 : Nat := 3156747099313845660939551

theorem tailTrace_6147743 : CollatzResearch.WordTrace tailWord_6147743 prefixEnd_6147743 3156747099313845660939551 := by
  unfold tailWord_6147743
  simp only [CollatzResearch.WordTrace]
  refine ⟨224226608166784536758647883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149484405444523024505765255 224226608166784536758647883)
  ·
    refine ⟨336339912250176805137971825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224226608166784536758647883 336339912250176805137971825)
    ·
      refine ⟨252254934187632603853478869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336339912250176805137971825 252254934187632603853478869)
      ·
        refine ⟨5912225020022639152815911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 252254934187632603853478869 5912225020022639152815911)
        ·
          refine ⟨8868337530033958729223867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912225020022639152815911 8868337530033958729223867)
          ·
            refine ⟨13302506295050938093835801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8868337530033958729223867 13302506295050938093835801)
            ·
              refine ⟨9976879721288203570376851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13302506295050938093835801 9976879721288203570376851)
              ·
                refine ⟨14965319581932305355565277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9976879721288203570376851 14965319581932305355565277)
                ·
                  refine ⟨5611994843224614508336979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14965319581932305355565277 5611994843224614508336979)
                  ·
                    refine ⟨8417992264836921762505469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5611994843224614508336979 8417992264836921762505469)
                    ·
                      refine ⟨3156747099313845660939551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8417992264836921762505469 3156747099313845660939551)
                      ·
                        rfl

theorem cell23_6147743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6147743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147743 prefixEnd_6147743 := by exact prefixLift 6147743
  have htrace : WordTrace (prefixWord ++ tailWord_6147743) baseStart_6147743 baseEnd_6147743 := by
    simpa [prefixWord, tailWord_6147743, baseEnd_6147743] using wordTrace_append hprefix tailTrace_6147743
  have hstable : (prefixWord ++ tailWord_6147743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147743).length < 2 ^ (prefixWord ++ tailWord_6147743).sum := by decide
  have hdescent : baseEnd_6147743 < baseStart_6147743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147769 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 3]
def baseStart_6147769 : Nat := 118140960795 + 6147769 * 2 ^ 59
def prefixEnd_6147769 : Nat := 4983230072969 + 3 ^ 40 * 6147769 * 2
def baseEnd_6147769 : Nat := 3156760449810862559214431

theorem tailTrace_6147769 : CollatzResearch.WordTrace tailWord_6147769 prefixEnd_6147769 3156760449810862559214431 := by
  unfold tailWord_6147769
  simp only [CollatzResearch.WordTrace]
  refine ⟨224227556464690343199094361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149485037643126895466062907 224227556464690343199094361)
  ·
    refine ⟨168170667348517757399320771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224227556464690343199094361 168170667348517757399320771)
    ·
      refine ⟨252256001022776636098981157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168170667348517757399320771 252256001022776636098981157)
      ·
        refine ⟨47298000191770619268558967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252256001022776636098981157 47298000191770619268558967)
        ·
          refine ⟨70947000287655928902838451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47298000191770619268558967 70947000287655928902838451)
          ·
            refine ⟨106420500431483893354257677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70947000287655928902838451 106420500431483893354257677)
            ·
              refine ⟨39907687661806460007846629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106420500431483893354257677 39907687661806460007846629)
              ·
                refine ⟨7482691436588711251471243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39907687661806460007846629 7482691436588711251471243)
                ·
                  refine ⟨11224037154883066877206865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7482691436588711251471243 11224037154883066877206865)
                  ·
                    refine ⟨8418027866162300157905149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11224037154883066877206865 8418027866162300157905149)
                    ·
                      refine ⟨3156760449810862559214431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8418027866162300157905149 3156760449810862559214431)
                      ·
                        rfl

theorem cell23_6147769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_6147769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147769 prefixEnd_6147769 := by exact prefixLift 6147769
  have htrace : WordTrace (prefixWord ++ tailWord_6147769) baseStart_6147769 baseEnd_6147769 := by
    simpa [prefixWord, tailWord_6147769, baseEnd_6147769] using wordTrace_append hprefix tailTrace_6147769
  have hstable : (prefixWord ++ tailWord_6147769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147769).length < 2 ^ (prefixWord ++ tailWord_6147769).sum := by decide
  have hdescent : baseEnd_6147769 < baseStart_6147769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147772 : List Nat := [2, 2, 2, 3, 1, 3, 1, 9]
def baseStart_6147772 : Nat := 118140960795 + 6147772 * 2 ^ 59
def prefixEnd_6147772 : Nat := 4983230072969 + 3 ^ 40 * 6147772 * 2
def baseEnd_6147772 : Nat := 116917110750104668425071

theorem tailTrace_6147772 : CollatzResearch.WordTrace tailWord_6147772 prefixEnd_6147772 116917110750104668425071 := by
  unfold tailWord_6147772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112113832941839737355726785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149485110589119649807635713 112113832941839737355726785)
  ·
    refine ⟨84085374706379803016795089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112113832941839737355726785 84085374706379803016795089)
    ·
      refine ⟨63064031029784852262596317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84085374706379803016795089 63064031029784852262596317)
      ·
        refine ⟨23649011636169319598473619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63064031029784852262596317 23649011636169319598473619)
        ·
          refine ⟨35473517454253979397710429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23649011636169319598473619 35473517454253979397710429)
          ·
            refine ⟨13302569045345242274141411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35473517454253979397710429 13302569045345242274141411)
            ·
              refine ⟨19953853568017863411212117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13302569045345242274141411 19953853568017863411212117)
              ·
                refine ⟨116917110750104668425071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19953853568017863411212117 116917110750104668425071)
                ·
                  rfl

theorem cell23_6147772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 9].length) (baseStart_6147772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147772 prefixEnd_6147772 := by exact prefixLift 6147772
  have htrace : WordTrace (prefixWord ++ tailWord_6147772) baseStart_6147772 baseEnd_6147772 := by
    simpa [prefixWord, tailWord_6147772, baseEnd_6147772] using wordTrace_append hprefix tailTrace_6147772
  have hstable : (prefixWord ++ tailWord_6147772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147772).length < 2 ^ (prefixWord ++ tailWord_6147772).sum := by decide
  have hdescent : baseEnd_6147772 < baseStart_6147772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147789 : List Nat := [1, 6, 2, 1, 1, 1, 11]
def baseStart_6147789 : Nat := 118140960795 + 6147789 * 2 ^ 59
def prefixEnd_6147789 : Nat := 4983230072969 + 3 ^ 40 * 6147789 * 2
def baseEnd_6147789 : Nat := 38972478017579660258819

theorem tailTrace_6147789 : CollatzResearch.WordTrace tailWord_6147789 prefixEnd_6147789 38972478017579660258819 := by
  unfold tailWord_6147789
  simp only [CollatzResearch.WordTrace]
  refine ⟨224228285924617886614822421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149485523949745257743214947 224228285924617886614822421)
  ·
    refine ⟨10510700902716463435069801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 224228285924617886614822421 10510700902716463435069801)
    ·
      refine ⟨7883025677037347576302351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10510700902716463435069801 7883025677037347576302351)
      ·
        refine ⟨11824538515556021364453527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883025677037347576302351 11824538515556021364453527)
        ·
          refine ⟨17736807773334032046680291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11824538515556021364453527 17736807773334032046680291)
          ·
            refine ⟨26605211660001048070020437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17736807773334032046680291 26605211660001048070020437)
            ·
              refine ⟨38972478017579660258819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26605211660001048070020437 38972478017579660258819)
              ·
                rfl

theorem cell23_6147789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 11].length) (baseStart_6147789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147789 prefixEnd_6147789 := by exact prefixLift 6147789
  have htrace : WordTrace (prefixWord ++ tailWord_6147789) baseStart_6147789 baseEnd_6147789 := by
    simpa [prefixWord, tailWord_6147789, baseEnd_6147789] using wordTrace_append hprefix tailTrace_6147789
  have hstable : (prefixWord ++ tailWord_6147789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147789).length < 2 ^ (prefixWord ++ tailWord_6147789).sum := by decide
  have hdescent : baseEnd_6147789 < baseStart_6147789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147799 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 3]
def baseStart_6147799 : Nat := 118140960795 + 6147799 * 2 ^ 59
def prefixEnd_6147799 : Nat := 4983230072969 + 3 ^ 40 * 6147799 * 2
def baseEnd_6147799 : Nat := 3156775854230497441839293

theorem tailTrace_6147799 : CollatzResearch.WordTrace tailWord_6147799 prefixEnd_6147799 3156775854230497441839293 := by
  unfold tailWord_6147799
  simp only [CollatzResearch.WordTrace]
  refine ⟨224228650654581658322686451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149485767103054438881790967 224228650654581658322686451)
  ·
    refine ⟨336342975981872487484029677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224228650654581658322686451 336342975981872487484029677)
    ·
      refine ⟨126128615993202182806511129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336342975981872487484029677 126128615993202182806511129)
      ·
        refine ⟨94596461994901637104883347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126128615993202182806511129 94596461994901637104883347)
        ·
          refine ⟨141894692992352455657325021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94596461994901637104883347 141894692992352455657325021)
          ·
            refine ⟨53210509872132170871496883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141894692992352455657325021 53210509872132170871496883)
            ·
              refine ⟨79815764808198256307245325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53210509872132170871496883 79815764808198256307245325)
              ·
                refine ⟨29930911803074346115216997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79815764808198256307245325 29930911803074346115216997)
                ·
                  refine ⟨5612045963076439896603187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29930911803074346115216997 5612045963076439896603187)
                  ·
                    refine ⟨8418068944614659844904781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5612045963076439896603187 8418068944614659844904781)
                    ·
                      refine ⟨3156775854230497441839293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8418068944614659844904781 3156775854230497441839293)
                      ·
                        rfl

theorem cell23_6147799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_6147799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147799 prefixEnd_6147799 := by exact prefixLift 6147799
  have htrace : WordTrace (prefixWord ++ tailWord_6147799) baseStart_6147799 baseEnd_6147799 := by
    simpa [prefixWord, tailWord_6147799, baseEnd_6147799] using wordTrace_append hprefix tailTrace_6147799
  have hstable : (prefixWord ++ tailWord_6147799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147799).length < 2 ^ (prefixWord ++ tailWord_6147799).sum := by decide
  have hdescent : baseEnd_6147799 < baseStart_6147799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147800 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 1, 2, 2]
def baseStart_6147800 : Nat := 118140960795 + 6147800 * 2 ^ 59
def prefixEnd_6147800 : Nat := 4983230072969 + 3 ^ 40 * 6147800 * 2
def baseEnd_6147800 : Nat := 3156776367711151937926789

theorem tailTrace_6147800 : CollatzResearch.WordTrace tailWord_6147800 prefixEnd_6147800 3156776367711151937926789 := by
  unfold tailWord_6147800
  simp only [CollatzResearch.WordTrace]
  refine ⟨112114343563789017746736427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149485791418385356995648569 112114343563789017746736427)
  ·
    refine ⟨168171515345683526620104641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112114343563789017746736427 168171515345683526620104641)
    ·
      refine ⟨126128636509262644965078481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168171515345683526620104641 126128636509262644965078481)
      ·
        refine ⟨94596477381946983723808861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126128636509262644965078481 94596477381946983723808861)
        ·
          refine ⟨35473679018230118896428323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94596477381946983723808861 35473679018230118896428323)
          ·
            refine ⟨53210518527345178344642485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35473679018230118896428323 53210518527345178344642485)
            ·
              refine ⟨4988486111938610469810233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53210518527345178344642485 4988486111938610469810233)
              ·
                refine ⟨3741364583953957852357675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4988486111938610469810233 3741364583953957852357675)
                ·
                  refine ⟨5612046875930936778536513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3741364583953957852357675 5612046875930936778536513)
                  ·
                    refine ⟨4209035156948202583902385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5612046875930936778536513 4209035156948202583902385)
                    ·
                      refine ⟨3156776367711151937926789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209035156948202583902385 3156776367711151937926789)
                      ·
                        rfl

theorem cell23_6147800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_6147800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147800 prefixEnd_6147800 := by exact prefixLift 6147800
  have htrace : WordTrace (prefixWord ++ tailWord_6147800) baseStart_6147800 baseEnd_6147800 := by
    simpa [prefixWord, tailWord_6147800, baseEnd_6147800] using wordTrace_append hprefix tailTrace_6147800
  have hstable : (prefixWord ++ tailWord_6147800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147800).length < 2 ^ (prefixWord ++ tailWord_6147800).sum := by decide
  have hdescent : baseEnd_6147800 < baseStart_6147800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147826 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6147826 : Nat := 118140960795 + 6147826 * 2 ^ 59
def prefixEnd_6147826 : Nat := 4983230072969 + 3 ^ 40 * 6147826 * 2
def baseEnd_6147826 : Nat := 3156789718208168836201669

theorem tailTrace_6147826 : CollatzResearch.WordTrace tailWord_6147826 prefixEnd_6147826 3156789718208168836201669 := by
  unfold tailWord_6147826
  simp only [CollatzResearch.WordTrace]
  refine ⟨56057408856370960483479833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149486423616989227955946221 56057408856370960483479833)
  ·
    refine ⟨42043056642278220362609875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56057408856370960483479833 42043056642278220362609875)
    ·
      refine ⟨63064584963417330543914813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42043056642278220362609875 63064584963417330543914813)
      ·
        refine ⟨23649219361281498953968055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63064584963417330543914813 23649219361281498953968055)
        ·
          refine ⟨35473829041922248430952083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23649219361281498953968055 35473829041922248430952083)
          ·
            refine ⟨53210743562883372646428125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35473829041922248430952083 53210743562883372646428125)
            ·
              refine ⟨19954028836081264742410547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53210743562883372646428125 19954028836081264742410547)
              ·
                refine ⟨29931043254121897113615821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19954028836081264742410547 29931043254121897113615821)
                ·
                  refine ⟨11224141220295711417605933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29931043254121897113615821 11224141220295711417605933)
                  ·
                    refine ⟨4209052957610891781602225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11224141220295711417605933 4209052957610891781602225)
                    ·
                      refine ⟨3156789718208168836201669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209052957610891781602225 3156789718208168836201669)
                      ·
                        rfl

theorem cell23_6147826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6147826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147826 prefixEnd_6147826 := by exact prefixLift 6147826
  have htrace : WordTrace (prefixWord ++ tailWord_6147826) baseStart_6147826 baseEnd_6147826 := by
    simpa [prefixWord, tailWord_6147826, baseEnd_6147826] using wordTrace_append hprefix tailTrace_6147826
  have hstable : (prefixWord ++ tailWord_6147826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147826).length < 2 ^ (prefixWord ++ tailWord_6147826).sum := by decide
  have hdescent : baseEnd_6147826 < baseStart_6147826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147839 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 3, 4, 2]
def baseStart_6147839 : Nat := 118140960795 + 6147839 * 2 ^ 59
def prefixEnd_6147839 : Nat := 4983230072969 + 3 ^ 40 * 6147839 * 2
def baseEnd_6147839 : Nat := 3156796393456677285339109

theorem tailTrace_6147839 : CollatzResearch.WordTrace tailWord_6147839 prefixEnd_6147839 3156796393456677285339109 := by
  unfold tailWord_6147839
  simp only [CollatzResearch.WordTrace]
  refine ⟨224230109574436745154142571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149486739716291163436095047 224230109574436745154142571)
  ·
    refine ⟨336345164361655117731213857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224230109574436745154142571 336345164361655117731213857)
    ·
      refine ⟨252258873271241338298410393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336345164361655117731213857 252258873271241338298410393)
      ·
        refine ⟨189194154953431003723807795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252258873271241338298410393 189194154953431003723807795)
        ·
          refine ⟨283791232430146505585711693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189194154953431003723807795 283791232430146505585711693)
          ·
            refine ⟨106421712161304939594641885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283791232430146505585711693 106421712161304939594641885)
            ·
              refine ⟨39908142060489352347990707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106421712161304939594641885 39908142060489352347990707)
              ·
                refine ⟨59862213090734028521986061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39908142060489352347990707 59862213090734028521986061)
                ·
                  refine ⟨22448329909025260695744773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59862213090734028521986061 22448329909025260695744773)
                  ·
                    refine ⟨4209061857942236380452145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22448329909025260695744773 4209061857942236380452145)
                    ·
                      refine ⟨3156796393456677285339109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209061857942236380452145 3156796393456677285339109)
                      ·
                        rfl

theorem cell23_6147839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_6147839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147839 prefixEnd_6147839 := by exact prefixLift 6147839
  have htrace : WordTrace (prefixWord ++ tailWord_6147839) baseStart_6147839 baseEnd_6147839 := by
    simpa [prefixWord, tailWord_6147839, baseEnd_6147839] using wordTrace_append hprefix tailTrace_6147839
  have hstable : (prefixWord ++ tailWord_6147839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147839).length < 2 ^ (prefixWord ++ tailWord_6147839).sum := by decide
  have hdescent : baseEnd_6147839 < baseStart_6147839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147873 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 2, 2, 2]
def baseStart_6147873 : Nat := 118140960795 + 6147873 * 2 ^ 59
def prefixEnd_6147873 : Nat := 4983230072969 + 3 ^ 40 * 6147873 * 2
def baseEnd_6147873 : Nat := 3156813851798930152313953

theorem tailTrace_6147873 : CollatzResearch.WordTrace tailWord_6147873 prefixEnd_6147873 3156813851798930152313953 := by
  unfold tailWord_6147873
  simp only [CollatzResearch.WordTrace]
  refine ⟨224231349656313568960880273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149487566437542379307253515 224231349656313568960880273)
  ·
    refine ⟨168173512242235176720660205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224231349656313568960880273 168173512242235176720660205)
    ·
      refine ⟨63065067090838191270247577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168173512242235176720660205 63065067090838191270247577)
      ·
        refine ⟨47298800318128643452685683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63065067090838191270247577 47298800318128643452685683)
        ·
          refine ⟨70948200477192965179028525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47298800318128643452685683 70948200477192965179028525)
          ·
            refine ⟨26605575178947361942135697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70948200477192965179028525 26605575178947361942135697)
            ·
              refine ⟨19954181384210521456601773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26605575178947361942135697 19954181384210521456601773)
              ·
                refine ⟨7482818019078945546225665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19954181384210521456601773 7482818019078945546225665)
                ·
                  refine ⟨5612113514309209159669249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7482818019078945546225665 5612113514309209159669249)
                  ·
                    refine ⟨4209085135731906869751937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5612113514309209159669249 4209085135731906869751937)
                    ·
                      refine ⟨3156813851798930152313953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209085135731906869751937 3156813851798930152313953)
                      ·
                        rfl

theorem cell23_6147873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_6147873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147873 prefixEnd_6147873 := by exact prefixLift 6147873
  have htrace : WordTrace (prefixWord ++ tailWord_6147873) baseStart_6147873 baseEnd_6147873 := by
    simpa [prefixWord, tailWord_6147873, baseEnd_6147873] using wordTrace_append hprefix tailTrace_6147873
  have hstable : (prefixWord ++ tailWord_6147873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147873).length < 2 ^ (prefixWord ++ tailWord_6147873).sum := by decide
  have hdescent : baseEnd_6147873 < baseStart_6147873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6147896 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 5]
def baseStart_6147896 : Nat := 118140960795 + 6147896 * 2 ^ 59
def prefixEnd_6147896 : Nat := 4983230072969 + 3 ^ 40 * 6147896 * 2
def baseEnd_6147896 : Nat := 350758406872664840258483

theorem tailTrace_6147896 : CollatzResearch.WordTrace tailWord_6147896 prefixEnd_6147896 350758406872664840258483 := by
  unfold tailWord_6147896
  simp only [CollatzResearch.WordTrace]
  refine ⟨112116094267615121944483771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149488125690153495925978361 112116094267615121944483771)
  ·
    refine ⟨168174141401422682916725657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112116094267615121944483771 168174141401422682916725657)
    ·
      refine ⟨126130606051067012187544243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168174141401422682916725657 126130606051067012187544243)
      ·
        refine ⟨189195909076600518281316365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126130606051067012187544243 189195909076600518281316365)
        ·
          refine ⟨70948465903725194355493637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189195909076600518281316365 70948465903725194355493637)
          ·
            refine ⟨13302837356948473941655057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70948465903725194355493637 13302837356948473941655057)
            ·
              refine ⟨9977128017711355456241293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13302837356948473941655057 9977128017711355456241293)
              ·
                refine ⟨3741423006641758296090485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9977128017711355456241293 3741423006641758296090485)
                ·
                  refine ⟨350758406872664840258483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3741423006641758296090485 350758406872664840258483)
                  ·
                    rfl

theorem cell23_6147896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 5].length) (baseStart_6147896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6147896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6147896 prefixEnd_6147896 := by exact prefixLift 6147896
  have htrace : WordTrace (prefixWord ++ tailWord_6147896) baseStart_6147896 baseEnd_6147896 := by
    simpa [prefixWord, tailWord_6147896, baseEnd_6147896] using wordTrace_append hprefix tailTrace_6147896
  have hstable : (prefixWord ++ tailWord_6147896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6147896).length < 2 ^ (prefixWord ++ tailWord_6147896).sum := by decide
  have hdescent : baseEnd_6147896 < baseStart_6147896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6147896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148020 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6148020 : Nat := 118140960795 + 6148020 * 2 ^ 59
def prefixEnd_6148020 : Nat := 4983230072969 + 3 ^ 40 * 6148020 * 2
def baseEnd_6148020 : Nat := 350765481495015675241753

theorem tailTrace_6148020 : CollatzResearch.WordTrace tailWord_6148020 prefixEnd_6148020 350765481495015675241753 := by
  unfold tailWord_6148020
  simp only [CollatzResearch.WordTrace]
  refine ⟨112118355593390506533240757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149491140791187342044321009 112118355593390506533240757)
  ·
    refine ⟨10511095836880359987491321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112118355593390506533240757 10511095836880359987491321)
    ·
      refine ⟨7883321877660269990618491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10511095836880359987491321 7883321877660269990618491)
      ·
        refine ⟨11824982816490404985927737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883321877660269990618491 11824982816490404985927737)
        ·
          refine ⟨8868737112367803739445803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11824982816490404985927737 8868737112367803739445803)
          ·
            refine ⟨13303105668551705609168705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8868737112367803739445803 13303105668551705609168705)
            ·
              refine ⟨9977329251413779206876529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13303105668551705609168705 9977329251413779206876529)
              ·
                refine ⟨7482996938560334405157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9977329251413779206876529 7482996938560334405157397)
                ·
                  refine ⟨350765481495015675241753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7482996938560334405157397 350765481495015675241753)
                  ·
                    rfl

theorem cell23_6148020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6148020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148020 prefixEnd_6148020 := by exact prefixLift 6148020
  have htrace : WordTrace (prefixWord ++ tailWord_6148020) baseStart_6148020 baseEnd_6148020 := by
    simpa [prefixWord, tailWord_6148020, baseEnd_6148020] using wordTrace_append hprefix tailTrace_6148020
  have hstable : (prefixWord ++ tailWord_6148020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148020).length < 2 ^ (prefixWord ++ tailWord_6148020).sum := by decide
  have hdescent : baseEnd_6148020 < baseStart_6148020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148039 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_6148039 : Nat := 118140960795 + 6148039 * 2 ^ 59
def prefixEnd_6148039 : Nat := 4983230072969 + 3 ^ 40 * 6148039 * 2
def baseEnd_6148039 : Nat := 3156899089587576502838189

theorem tailTrace_6148039 : CollatzResearch.WordTrace tailWord_6148039 prefixEnd_6148039 3156899089587576502838189 := by
  unfold tailWord_6148039
  simp only [CollatzResearch.WordTrace]
  refine ⟨224237404173712179311423171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149491602782474786207615447 224237404173712179311423171)
  ·
    refine ⟨336356106260568268967134757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224237404173712179311423171 336356106260568268967134757)
    ·
      refine ⟨63066769923856550431337767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336356106260568268967134757 63066769923856550431337767)
      ·
        refine ⟨94600154885784825647006651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63066769923856550431337767 94600154885784825647006651)
        ·
          refine ⟨141900232328677238470509977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94600154885784825647006651 141900232328677238470509977)
          ·
            refine ⟨106425174246507928852882483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141900232328677238470509977 106425174246507928852882483)
            ·
              refine ⟨159637761369761893279323725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106425174246507928852882483 159637761369761893279323725)
              ·
                refine ⟨59864160513660709979746397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159637761369761893279323725 59864160513660709979746397)
                ·
                  refine ⟨22449060192622766242404899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59864160513660709979746397 22449060192622766242404899)
                  ·
                    refine ⟨33673590288934149363607349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22449060192622766242404899 33673590288934149363607349)
                    ·
                      refine ⟨3156899089587576502838189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33673590288934149363607349 3156899089587576502838189)
                      ·
                        rfl

theorem cell23_6148039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_6148039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148039 prefixEnd_6148039 := by exact prefixLift 6148039
  have htrace : WordTrace (prefixWord ++ tailWord_6148039) baseStart_6148039 baseEnd_6148039 := by
    simpa [prefixWord, tailWord_6148039, baseEnd_6148039] using wordTrace_append hprefix tailTrace_6148039
  have hstable : (prefixWord ++ tailWord_6148039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148039).length < 2 ^ (prefixWord ++ tailWord_6148039).sum := by decide
  have hdescent : baseEnd_6148039 < baseStart_6148039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148046 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_6148046 : Nat := 118140960795 + 6148046 * 2 ^ 59
def prefixEnd_6148046 : Nat := 4983230072969 + 3 ^ 40 * 6148046 * 2
def baseEnd_6148046 : Nat := 1052300894650719325150219

theorem tailTrace_6148046 : CollatzResearch.WordTrace tailWord_6148046 prefixEnd_6148046 1052300894650719325150219 := by
  unfold tailWord_6148046
  simp only [CollatzResearch.WordTrace]
  refine ⟨28029707435585852438365999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149491772989791213004618661 28029707435585852438365999)
  ·
    refine ⟨42044561153378778657548999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28029707435585852438365999 42044561153378778657548999)
    ·
      refine ⟨63066841730068167986323499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42044561153378778657548999 63066841730068167986323499)
      ·
        refine ⟨94600262595102251979485249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63066841730068167986323499 94600262595102251979485249)
        ·
          refine ⟨70950196946326688984613937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94600262595102251979485249 70950196946326688984613937)
          ·
            refine ⟨53212647709745016738460453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70950196946326688984613937 53212647709745016738460453)
            ·
              refine ⟨9977371445577190638461335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53212647709745016738460453 9977371445577190638461335)
              ·
                refine ⟨14966057168365785957692003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9977371445577190638461335 14966057168365785957692003)
                ·
                  refine ⟨22449085752548678936538005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14966057168365785957692003 22449085752548678936538005)
                  ·
                    refine ⟨1052300894650719325150219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22449085752548678936538005 1052300894650719325150219)
                    ·
                      rfl

theorem cell23_6148046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_6148046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148046 prefixEnd_6148046 := by exact prefixLift 6148046
  have htrace : WordTrace (prefixWord ++ tailWord_6148046) baseStart_6148046 baseEnd_6148046 := by
    simpa [prefixWord, tailWord_6148046, baseEnd_6148046] using wordTrace_append hprefix tailTrace_6148046
  have hstable : (prefixWord ++ tailWord_6148046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148046).length < 2 ^ (prefixWord ++ tailWord_6148046).sum := by decide
  have hdescent : baseEnd_6148046 < baseStart_6148046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148056 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 3, 2, 3]
def baseStart_6148056 : Nat := 118140960795 + 6148056 * 2 ^ 59
def prefixEnd_6148056 : Nat := 4983230072969 + 3 ^ 40 * 6148056 * 2
def baseEnd_6148056 : Nat := 3156907818758702936325611

theorem tailTrace_6148056 : CollatzResearch.WordTrace tailWord_6148056 prefixEnd_6148056 3156907818758702936325611 := by
  unfold tailWord_6148056
  simp only [CollatzResearch.WordTrace]
  refine ⟨112119012107325295607396011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149492016143100394143194681 112119012107325295607396011)
  ·
    refine ⟨168178518160987943411094017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112119012107325295607396011 168178518160987943411094017)
    ·
      refine ⟨126133888620740957558320513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168178518160987943411094017 126133888620740957558320513)
      ·
        refine ⟨94600416465555718168740385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126133888620740957558320513 94600416465555718168740385)
        ·
          refine ⟨70950312349166788626555289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94600416465555718168740385 70950312349166788626555289)
          ·
            refine ⟨53212734261875091469916467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70950312349166788626555289 53212734261875091469916467)
            ·
              refine ⟨79819101392812637204874701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53212734261875091469916467 79819101392812637204874701)
              ·
                refine ⟨29932163022304738951828013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79819101392812637204874701 29932163022304738951828013)
                ·
                  refine ⟨11224561133364277106935505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29932163022304738951828013 11224561133364277106935505)
                  ·
                    refine ⟨8418420850023207830201629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11224561133364277106935505 8418420850023207830201629)
                    ·
                      refine ⟨3156907818758702936325611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8418420850023207830201629 3156907818758702936325611)
                      ·
                        rfl

theorem cell23_6148056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_6148056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148056 prefixEnd_6148056 := by exact prefixLift 6148056
  have htrace : WordTrace (prefixWord ++ tailWord_6148056) baseStart_6148056 baseEnd_6148056 := by
    simpa [prefixWord, tailWord_6148056, baseEnd_6148056] using wordTrace_append hprefix tailTrace_6148056
  have hstable : (prefixWord ++ tailWord_6148056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148056).length < 2 ^ (prefixWord ++ tailWord_6148056).sum := by decide
  have hdescent : baseEnd_6148056 < baseStart_6148056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148057 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 2, 3, 2]
def baseStart_6148057 : Nat := 118140960795 + 6148057 * 2 ^ 59
def prefixEnd_6148057 : Nat := 4983230072969 + 3 ^ 40 * 6148057 * 2
def baseEnd_6148057 : Nat := 3156908332239357432413107

theorem tailTrace_6148057 : CollatzResearch.WordTrace tailWord_6148057 prefixEnd_6148057 3156908332239357432413107 := by
  unfold tailWord_6148057
  simp only [CollatzResearch.WordTrace]
  refine ⟨224238060687646968385578425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149492040458431312257052283 224238060687646968385578425)
  ·
    refine ⟨168178545515735226289183819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224238060687646968385578425 168178545515735226289183819)
    ·
      refine ⟨252267818273602839433775729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168178545515735226289183819 252267818273602839433775729)
      ·
        refine ⟨189200863705202129575331797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252267818273602839433775729 189200863705202129575331797)
        ·
          refine ⟨4434395243090674911921839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189200863705202129575331797 4434395243090674911921839)
          ·
            refine ⟨6651592864636012367882759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434395243090674911921839 6651592864636012367882759)
            ·
              refine ⟨9977389296954018551824139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651592864636012367882759 9977389296954018551824139)
              ·
                refine ⟨14966083945431027827736209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9977389296954018551824139 14966083945431027827736209)
                ·
                  refine ⟨11224562959073270870802157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14966083945431027827736209 11224562959073270870802157)
                  ·
                    refine ⟨4209211109652476576550809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11224562959073270870802157 4209211109652476576550809)
                    ·
                      refine ⟨3156908332239357432413107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209211109652476576550809 3156908332239357432413107)
                      ·
                        rfl

theorem cell23_6148057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 3, 2].length) (baseStart_6148057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148057 prefixEnd_6148057 := by exact prefixLift 6148057
  have htrace : WordTrace (prefixWord ++ tailWord_6148057) baseStart_6148057 baseEnd_6148057 := by
    simpa [prefixWord, tailWord_6148057, baseEnd_6148057] using wordTrace_append hprefix tailTrace_6148057
  have hstable : (prefixWord ++ tailWord_6148057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148057).length < 2 ^ (prefixWord ++ tailWord_6148057).sum := by decide
  have hdescent : baseEnd_6148057 < baseStart_6148057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148096 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 7, 2]
def baseStart_6148096 : Nat := 118140960795 + 6148096 * 2 ^ 59
def prefixEnd_6148096 : Nat := 4983230072969 + 3 ^ 40 * 6148096 * 2
def baseEnd_6148096 : Nat := 3156928357984882779825427

theorem tailTrace_6148096 : CollatzResearch.WordTrace tailWord_6148096 prefixEnd_6148096 3156928357984882779825427 := by
  unfold tailWord_6148096
  simp only [CollatzResearch.WordTrace]
  refine ⟨112119741567252839023124071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149492988756337118697498761 112119741567252839023124071)
  ·
    refine ⟨168179612350879258534686107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112119741567252839023124071 168179612350879258534686107)
    ·
      refine ⟨252269418526318887802029161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168179612350879258534686107 252269418526318887802029161)
      ·
        refine ⟨189202063894739165851521871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252269418526318887802029161 189202063894739165851521871)
        ·
          refine ⟨283803095842108748777282807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189202063894739165851521871 283803095842108748777282807)
          ·
            refine ⟨425704643763163123165924211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283803095842108748777282807 425704643763163123165924211)
            ·
              refine ⟨638556965644744684748886317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425704643763163123165924211 638556965644744684748886317)
              ·
                refine ⟨239458862116779256780832369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 638556965644744684748886317 239458862116779256780832369)
                ·
                  refine ⟨179594146587584442585624277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239458862116779256780832369 179594146587584442585624277)
                  ·
                    refine ⟨4209237810646510373100569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179594146587584442585624277 4209237810646510373100569)
                    ·
                      refine ⟨3156928357984882779825427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209237810646510373100569 3156928357984882779825427)
                      ·
                        rfl

theorem cell23_6148096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_6148096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148096 prefixEnd_6148096 := by exact prefixLift 6148096
  have htrace : WordTrace (prefixWord ++ tailWord_6148096) baseStart_6148096 baseEnd_6148096 := by
    simpa [prefixWord, tailWord_6148096, baseEnd_6148096] using wordTrace_append hprefix tailTrace_6148096
  have hstable : (prefixWord ++ tailWord_6148096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148096).length < 2 ^ (prefixWord ++ tailWord_6148096).sum := by decide
  have hdescent : baseEnd_6148096 < baseStart_6148096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148099 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5]
def baseStart_6148099 : Nat := 118140960795 + 6148099 * 2 ^ 59
def prefixEnd_6148099 : Nat := 4983230072969 + 3 ^ 40 * 6148099 * 2
def baseEnd_6148099 : Nat := 3156929898426846268087913

theorem tailTrace_6148099 : CollatzResearch.WordTrace tailWord_6148099 prefixEnd_6148099 3156929898426846268087913 := by
  unfold tailWord_6148099
  simp only [CollatzResearch.WordTrace]
  refine ⟨224239592553494809558607351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149493061702329873039071567 224239592553494809558607351)
  ·
    refine ⟨336359388830242214337911027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224239592553494809558607351 336359388830242214337911027)
    ·
      refine ⟨504539083245363321506866541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336359388830242214337911027 504539083245363321506866541)
      ·
        refine ⟨189202156217011245565074953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504539083245363321506866541 189202156217011245565074953)
        ·
          refine ⟨141901617162758434173806215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189202156217011245565074953 141901617162758434173806215)
          ·
            refine ⟨212852425744137651260709323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141901617162758434173806215 212852425744137651260709323)
            ·
              refine ⟨319278638616206476891063985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212852425744137651260709323 319278638616206476891063985)
              ·
                refine ⟨239458978962154857668297989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319278638616206476891063985 239458978962154857668297989)
                ·
                  refine ⟨44898558555404035812805873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239458978962154857668297989 44898558555404035812805873)
                  ·
                    refine ⟨33673918916553026859604405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44898558555404035812805873 33673918916553026859604405)
                    ·
                      refine ⟨3156929898426846268087913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33673918916553026859604405 3156929898426846268087913)
                      ·
                        rfl

theorem cell23_6148099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_6148099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148099 prefixEnd_6148099 := by exact prefixLift 6148099
  have htrace : WordTrace (prefixWord ++ tailWord_6148099) baseStart_6148099 baseEnd_6148099 := by
    simpa [prefixWord, tailWord_6148099, baseEnd_6148099] using wordTrace_append hprefix tailTrace_6148099
  have hstable : (prefixWord ++ tailWord_6148099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148099).length < 2 ^ (prefixWord ++ tailWord_6148099).sum := by decide
  have hdescent : baseEnd_6148099 < baseStart_6148099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148103 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_6148103 : Nat := 118140960795 + 6148103 * 2 ^ 59
def prefixEnd_6148103 : Nat := 4983230072969 + 3 ^ 40 * 6148103 * 2
def baseEnd_6148103 : Nat := 3156931952349464252437895

theorem tailTrace_6148103 : CollatzResearch.WordTrace tailWord_6148103 prefixEnd_6148103 3156931952349464252437895 := by
  unfold tailWord_6148103
  simp only [CollatzResearch.WordTrace]
  refine ⟨224239738445480318241752963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149493158963653545494501975 224239738445480318241752963)
  ·
    refine ⟨336359607668220477362629445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224239738445480318241752963 336359607668220477362629445)
    ·
      refine ⟨63067426437791339505493021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336359607668220477362629445 63067426437791339505493021)
      ·
        refine ⟨23650284914171752314559883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63067426437791339505493021 23650284914171752314559883)
        ·
          refine ⟨35475427371257628471839825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23650284914171752314559883 35475427371257628471839825)
          ·
            refine ⟨26606570528443221353879869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35475427371257628471839825 26606570528443221353879869)
            ·
              refine ⟨9977463948166208007704951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26606570528443221353879869 9977463948166208007704951)
              ·
                refine ⟨14966195922249312011557427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9977463948166208007704951 14966195922249312011557427)
                ·
                  refine ⟨22449293883373968017336141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14966195922249312011557427 22449293883373968017336141)
                  ·
                    refine ⟨8418485206265238006501053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22449293883373968017336141 8418485206265238006501053)
                    ·
                      refine ⟨3156931952349464252437895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8418485206265238006501053 3156931952349464252437895)
                      ·
                        rfl

theorem cell23_6148103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_6148103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148103 prefixEnd_6148103 := by exact prefixLift 6148103
  have htrace : WordTrace (prefixWord ++ tailWord_6148103) baseStart_6148103 baseEnd_6148103 := by
    simpa [prefixWord, tailWord_6148103, baseEnd_6148103] using wordTrace_append hprefix tailTrace_6148103
  have hstable : (prefixWord ++ tailWord_6148103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148103).length < 2 ^ (prefixWord ++ tailWord_6148103).sum := by decide
  have hdescent : baseEnd_6148103 < baseStart_6148103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148130 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_6148130 : Nat := 118140960795 + 6148130 * 2 ^ 59
def prefixEnd_6148130 : Nat := 4983230072969 + 3 ^ 40 * 6148130 * 2
def baseEnd_6148130 : Nat := 3156945816327135646800271

theorem tailTrace_6148130 : CollatzResearch.WordTrace tailWord_6148130 prefixEnd_6148130 3156945816327135646800271 := by
  unfold tailWord_6148130
  simp only [CollatzResearch.WordTrace]
  refine ⟨56060180804095625463246461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149493815477588334568657229 56060180804095625463246461)
  ·
    refine ⟨21022567801535859548717423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56060180804095625463246461 21022567801535859548717423)
    ·
      refine ⟨31533851702303789323076135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21022567801535859548717423 31533851702303789323076135)
      ·
        refine ⟨47300777553455683984614203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31533851702303789323076135 47300777553455683984614203)
        ·
          refine ⟨70951166330183525976921305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47300777553455683984614203 70951166330183525976921305)
          ·
            refine ⟨53213374747637644482690979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70951166330183525976921305 53213374747637644482690979)
            ·
              refine ⟨79820062121456466724036469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53213374747637644482690979 79820062121456466724036469)
              ·
                refine ⟨7483130823886543755378419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79820062121456466724036469 7483130823886543755378419)
                ·
                  refine ⟨11224696235829815633067629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483130823886543755378419 11224696235829815633067629)
                  ·
                    refine ⟨4209261088436180862400361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11224696235829815633067629 4209261088436180862400361)
                    ·
                      refine ⟨3156945816327135646800271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209261088436180862400361 3156945816327135646800271)
                      ·
                        rfl

theorem cell23_6148130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_6148130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148130 prefixEnd_6148130 := by exact prefixLift 6148130
  have htrace : WordTrace (prefixWord ++ tailWord_6148130) baseStart_6148130 baseEnd_6148130 := by
    simpa [prefixWord, tailWord_6148130, baseEnd_6148130] using wordTrace_append hprefix tailTrace_6148130
  have hstable : (prefixWord ++ tailWord_6148130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148130).length < 2 ^ (prefixWord ++ tailWord_6148130).sum := by decide
  have hdescent : baseEnd_6148130 < baseStart_6148130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148139 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6]
def baseStart_6148139 : Nat := 118140960795 + 6148139 * 2 ^ 59
def prefixEnd_6148139 : Nat := 4983230072969 + 3 ^ 40 * 6148139 * 2
def baseEnd_6148139 : Nat := 3156950437653026111587729

theorem tailTrace_6148139 : CollatzResearch.WordTrace tailWord_6148139 prefixEnd_6148139 3156950437653026111587729 := by
  unfold tailWord_6148139
  simp only [CollatzResearch.WordTrace]
  refine ⟨224241051473349896390063471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149494034315566597593375647 224241051473349896390063471)
  ·
    refine ⟨336361577210024844585095207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224241051473349896390063471 336361577210024844585095207)
    ·
      refine ⟨504542365815037266877642811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336361577210024844585095207 504542365815037266877642811)
      ·
        refine ⟨756813548722555900316464217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504542365815037266877642811 756813548722555900316464217)
        ·
          refine ⟨567610161541916925237348163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756813548722555900316464217 567610161541916925237348163)
          ·
            refine ⟨851415242312875387856022245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567610161541916925237348163 851415242312875387856022245)
            ·
              refine ⟨159640357933664135223004171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 851415242312875387856022245 159640357933664135223004171)
              ·
                refine ⟨239460536900496202834506257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159640357933664135223004171 239460536900496202834506257)
                ·
                  refine ⟨179595402675372152125879693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239460536900496202834506257 179595402675372152125879693)
                  ·
                    refine ⟨67348276003264557047204885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179595402675372152125879693 67348276003264557047204885)
                    ·
                      refine ⟨3156950437653026111587729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67348276003264557047204885 3156950437653026111587729)
                      ·
                        rfl

theorem cell23_6148139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_6148139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148139 prefixEnd_6148139 := by exact prefixLift 6148139
  have htrace : WordTrace (prefixWord ++ tailWord_6148139) baseStart_6148139 baseEnd_6148139 := by
    simpa [prefixWord, tailWord_6148139, baseEnd_6148139] using wordTrace_append hprefix tailTrace_6148139
  have hstable : (prefixWord ++ tailWord_6148139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148139).length < 2 ^ (prefixWord ++ tailWord_6148139).sum := by decide
  have hdescent : baseEnd_6148139 < baseStart_6148139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148156 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_6148156 : Nat := 118140960795 + 6148156 * 2 ^ 59
def prefixEnd_6148156 : Nat := 4983230072969 + 3 ^ 40 * 6148156 * 2
def baseEnd_6148156 : Nat := 3156959166824152545075151

theorem tailTrace_6148156 : CollatzResearch.WordTrace tailWord_6148156 prefixEnd_6148156 3156959166824152545075151 := by
  unfold tailWord_6148156
  simp only [CollatzResearch.WordTrace]
  refine ⟨112120835757144154146716161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149494447676192205528954881 112120835757144154146716161)
  ·
    refine ⟨84090626817858115610037121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112120835757144154146716161 84090626817858115610037121)
    ·
      refine ⟨63067970113393586707527841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84090626817858115610037121 63067970113393586707527841)
      ·
        refine ⟨47300977585045190030645881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63067970113393586707527841 47300977585045190030645881)
        ·
          refine ⟨35475733188783892522984411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47300977585045190030645881 35475733188783892522984411)
          ·
            refine ⟨53213599783175838784476617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35475733188783892522984411 53213599783175838784476617)
            ·
              refine ⟨39910199837381879088357463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53213599783175838784476617 39910199837381879088357463)
              ·
                refine ⟨59865299756072818632536195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39910199837381879088357463 59865299756072818632536195)
                ·
                  refine ⟨89797949634109227948804293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59865299756072818632536195 89797949634109227948804293)
                  ·
                    refine ⟨16837115556395480240400805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89797949634109227948804293 16837115556395480240400805)
                    ·
                      refine ⟨3156959166824152545075151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16837115556395480240400805 3156959166824152545075151)
                      ·
                        rfl

theorem cell23_6148156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_6148156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148156 prefixEnd_6148156 := by exact prefixLift 6148156
  have htrace : WordTrace (prefixWord ++ tailWord_6148156) baseStart_6148156 baseEnd_6148156 := by
    simpa [prefixWord, tailWord_6148156, baseEnd_6148156] using wordTrace_append hprefix tailTrace_6148156
  have hstable : (prefixWord ++ tailWord_6148156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148156).length < 2 ^ (prefixWord ++ tailWord_6148156).sum := by decide
  have hdescent : baseEnd_6148156 < baseStart_6148156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148176 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3]
def baseStart_6148176 : Nat := 118140960795 + 6148176 * 2 ^ 59
def prefixEnd_6148176 : Nat := 4983230072969 + 3 ^ 40 * 6148176 * 2
def baseEnd_6148176 : Nat := 3156969436437242466825059

theorem tailTrace_6148176 : CollatzResearch.WordTrace tailWord_6148176 prefixEnd_6148176 3156969436437242466825059 := by
  unfold tailWord_6148176
  simp only [CollatzResearch.WordTrace]
  refine ⟨112121200487107925854580191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149494933982810567806106921 112121200487107925854580191)
  ·
    refine ⟨168181800730661888781870287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112121200487107925854580191 168181800730661888781870287)
    ·
      refine ⟨252272701095992833172805431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168181800730661888781870287 252272701095992833172805431)
      ·
        refine ⟨378409051643989249759208147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252272701095992833172805431 378409051643989249759208147)
        ·
          refine ⟨567613577465983874638812221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378409051643989249759208147 567613577465983874638812221)
          ·
            refine ⟨212855091549743952989554583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567613577465983874638812221 212855091549743952989554583)
            ·
              refine ⟨319282637324615929484331875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212855091549743952989554583 319282637324615929484331875)
              ·
                refine ⟨478923955986923894226497813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319282637324615929484331875 478923955986923894226497813)
                ·
                  refine ⟨22449560436887057541867085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 478923955986923894226497813 22449560436887057541867085)
                  ·
                    refine ⟨8418585163832646578200157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22449560436887057541867085 8418585163832646578200157)
                    ·
                      refine ⟨3156969436437242466825059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8418585163832646578200157 3156969436437242466825059)
                      ·
                        rfl

theorem cell23_6148176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_6148176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148176 prefixEnd_6148176 := by exact prefixLift 6148176
  have htrace : WordTrace (prefixWord ++ tailWord_6148176) baseStart_6148176 baseEnd_6148176 := by
    simpa [prefixWord, tailWord_6148176, baseEnd_6148176] using wordTrace_append hprefix tailTrace_6148176
  have hstable : (prefixWord ++ tailWord_6148176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148176).length < 2 ^ (prefixWord ++ tailWord_6148176).sum := by decide
  have hdescent : baseEnd_6148176 < baseStart_6148176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148216 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_6148216 : Nat := 118140960795 + 6148216 * 2 ^ 59
def prefixEnd_6148216 : Nat := 4983230072969 + 3 ^ 40 * 6148216 * 2
def baseEnd_6148216 : Nat := 3156989975663422310324875

theorem tailTrace_6148216 : CollatzResearch.WordTrace tailWord_6148216 prefixEnd_6148216 3156989975663422310324875 := by
  unfold tailWord_6148216
  simp only [CollatzResearch.WordTrace]
  refine ⟨112121929947035469270308251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149495906596047292360411001 112121929947035469270308251)
  ·
    refine ⟨168182894920553203905462377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112121929947035469270308251 168182894920553203905462377)
    ·
      refine ⟨126137171190414902929096783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168182894920553203905462377 126137171190414902929096783)
      ·
        refine ⟨189205756785622354393645175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126137171190414902929096783 189205756785622354393645175)
        ·
          refine ⟨283808635178433531590467763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189205756785622354393645175 283808635178433531590467763)
          ·
            refine ⟨425712952767650297385701645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283808635178433531590467763 425712952767650297385701645)
            ·
              refine ⟨159642357287868861519638117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 425712952767650297385701645 159642357287868861519638117)
              ·
                refine ⟨29932941991475411534932147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159642357287868861519638117 29932941991475411534932147)
                ·
                  refine ⟨44899412987213117302398221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29932941991475411534932147 44899412987213117302398221)
                  ·
                    refine ⟨16837279870204918988399333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44899412987213117302398221 16837279870204918988399333)
                    ·
                      refine ⟨3156989975663422310324875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16837279870204918988399333 3156989975663422310324875)
                      ·
                        rfl

theorem cell23_6148216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_6148216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148216 prefixEnd_6148216 := by exact prefixLift 6148216
  have htrace : WordTrace (prefixWord ++ tailWord_6148216) baseStart_6148216 baseEnd_6148216 := by
    simpa [prefixWord, tailWord_6148216, baseEnd_6148216] using wordTrace_append hprefix tailTrace_6148216
  have hstable : (prefixWord ++ tailWord_6148216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148216).length < 2 ^ (prefixWord ++ tailWord_6148216).sum := by decide
  have hdescent : baseEnd_6148216 < baseStart_6148216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148233 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 6, 2]
def baseStart_6148233 : Nat := 118140960795 + 6148233 * 2 ^ 59
def prefixEnd_6148233 : Nat := 4983230072969 + 3 ^ 40 * 6148233 * 2
def baseEnd_6148233 : Nat := 3156998704834548743812297

theorem tailTrace_6148233 : CollatzResearch.WordTrace tailWord_6148233 prefixEnd_6148233 3156998704834548743812297 := by
  unfold tailWord_6148233
  simp only [CollatzResearch.WordTrace]
  refine ⟨224244479935009350443985353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149496319956672900295990235 224244479935009350443985353)
  ·
    refine ⟨168183359951257012832989015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224244479935009350443985353 168183359951257012832989015)
    ·
      refine ⟨252275039926885519249483523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168183359951257012832989015 252275039926885519249483523)
      ·
        refine ⟨378412559890328278874225285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252275039926885519249483523 378412559890328278874225285)
        ·
          refine ⟨70952354979436552288917241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378412559890328278874225285 70952354979436552288917241)
          ·
            refine ⟨53214266234577414216687931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70952354979436552288917241 53214266234577414216687931)
            ·
              refine ⟨79821399351866121325031897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53214266234577414216687931 79821399351866121325031897)
              ·
                refine ⟨59866049513899590993773923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79821399351866121325031897 59866049513899590993773923)
                ·
                  refine ⟨89799074270849386490660885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59866049513899590993773923 89799074270849386490660885)
                  ·
                    refine ⟨4209331606446064991749729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89799074270849386490660885 4209331606446064991749729)
                    ·
                      refine ⟨3156998704834548743812297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209331606446064991749729 3156998704834548743812297)
                      ·
                        rfl

theorem cell23_6148233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 6, 2].length) (baseStart_6148233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148233 prefixEnd_6148233 := by exact prefixLift 6148233
  have htrace : WordTrace (prefixWord ++ tailWord_6148233) baseStart_6148233 baseEnd_6148233 := by
    simpa [prefixWord, tailWord_6148233, baseEnd_6148233] using wordTrace_append hprefix tailTrace_6148233
  have hstable : (prefixWord ++ tailWord_6148233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148233).length < 2 ^ (prefixWord ++ tailWord_6148233).sum := by decide
  have hdescent : baseEnd_6148233 < baseStart_6148233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148303 : List Nat := [1, 1, 2, 1, 1, 3, 3, 5, 1, 5]
def baseStart_6148303 : Nat := 118140960795 + 6148303 * 2 ^ 59
def prefixEnd_6148303 : Nat := 4983230072969 + 3 ^ 40 * 6148303 * 2
def baseEnd_6148303 : Nat := 1052344882826787823312325

theorem tailTrace_6148303 : CollatzResearch.WordTrace tailWord_6148303 prefixEnd_6148303 1052344882826787823312325 := by
  unfold tailWord_6148303
  simp only [CollatzResearch.WordTrace]
  refine ⟨224247033044755752399033563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149498022029837168266022375 224247033044755752399033563)
  ·
    refine ⟨336370549567133628598550345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224247033044755752399033563 336370549567133628598550345)
    ·
      refine ⟨252277912175350221448912759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336370549567133628598550345 252277912175350221448912759)
      ·
        refine ⟨378416868263025332173369139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252277912175350221448912759 378416868263025332173369139)
        ·
          refine ⟨567625302394537998260053709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378416868263025332173369139 567625302394537998260053709)
          ·
            refine ⟨212859488397951749347520141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567625302394537998260053709 212859488397951749347520141)
            ·
              refine ⟨79822308149231906005320053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212859488397951749347520141 79822308149231906005320053)
              ·
                refine ⟨7483341388990491187998755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79822308149231906005320053 7483341388990491187998755)
                ·
                  refine ⟨11225012083485736781998133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483341388990491187998755 11225012083485736781998133)
                  ·
                    refine ⟨1052344882826787823312325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11225012083485736781998133 1052344882826787823312325)
                    ·
                      rfl

theorem cell23_6148303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 5].length) (baseStart_6148303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148303 prefixEnd_6148303 := by exact prefixLift 6148303
  have htrace : WordTrace (prefixWord ++ tailWord_6148303) baseStart_6148303 baseEnd_6148303 := by
    simpa [prefixWord, tailWord_6148303, baseEnd_6148303] using wordTrace_append hprefix tailTrace_6148303
  have hstable : (prefixWord ++ tailWord_6148303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148303).length < 2 ^ (prefixWord ++ tailWord_6148303).sum := by decide
  have hdescent : baseEnd_6148303 < baseStart_6148303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148350 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_6148350 : Nat := 118140960795 + 6148350 * 2 ^ 59
def prefixEnd_6148350 : Nat := 4983230072969 + 3 ^ 40 * 6148350 * 2
def baseEnd_6148350 : Nat := 1052352927357041595349753

theorem tailTrace_6148350 : CollatzResearch.WordTrace tailWord_6148350 prefixEnd_6148350 1052352927357041595349753 := by
  unfold tailWord_6148350
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031093409448184928249313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149499164850390319617329669 28031093409448184928249313)
  ·
    refine ⟨21023320057086138696186985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28031093409448184928249313 21023320057086138696186985)
    ·
      refine ⟨15767490042814604022140239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21023320057086138696186985 15767490042814604022140239)
      ·
        refine ⟨23651235064221906033210359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15767490042814604022140239 23651235064221906033210359)
        ·
          refine ⟨35476852596332859049815539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23651235064221906033210359 35476852596332859049815539)
          ·
            refine ⟨53215278894499288574723309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35476852596332859049815539 53215278894499288574723309)
            ·
              refine ⟨19955729585437233215521241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53215278894499288574723309 19955729585437233215521241)
              ·
                refine ⟨14966797189077924911640931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19955729585437233215521241 14966797189077924911640931)
                ·
                  refine ⟨22450195783616887367461397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14966797189077924911640931 22450195783616887367461397)
                  ·
                    refine ⟨1052352927357041595349753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22450195783616887367461397 1052352927357041595349753)
                    ·
                      rfl

theorem cell23_6148350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_6148350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148350 prefixEnd_6148350 := by exact prefixLift 6148350
  have htrace : WordTrace (prefixWord ++ tailWord_6148350) baseStart_6148350 baseEnd_6148350 := by
    simpa [prefixWord, tailWord_6148350, baseEnd_6148350] using wordTrace_append hprefix tailTrace_6148350
  have hstable : (prefixWord ++ tailWord_6148350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148350).length < 2 ^ (prefixWord ++ tailWord_6148350).sum := by decide
  have hdescent : baseEnd_6148350 < baseStart_6148350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148354 : List Nat := [3, 4, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6148354 : Nat := 118140960795 + 6148354 * 2 ^ 59
def prefixEnd_6148354 : Nat := 4983230072969 + 3 ^ 40 * 6148354 * 2
def baseEnd_6148354 : Nat := 1052353611997914256799747

theorem tailTrace_6148354 : CollatzResearch.WordTrace tailWord_6148354 prefixEnd_6148354 1052353611997914256799747 := by
  unfold tailWord_6148354
  simp only [CollatzResearch.WordTrace]
  refine ⟨56062223291892747027285029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149499262111713992072760077 56062223291892747027285029)
  ·
    refine ⟨10511666867229890067615943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56062223291892747027285029 10511666867229890067615943)
    ·
      refine ⟨15767500300844835101423915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10511666867229890067615943 15767500300844835101423915)
      ·
        refine ⟨23651250451267252652135873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15767500300844835101423915 23651250451267252652135873)
        ·
          refine ⟨17738437838450439489101905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23651250451267252652135873 17738437838450439489101905)
          ·
            refine ⟨13303828378837829616826429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17738437838450439489101905 13303828378837829616826429)
            ·
              refine ⟨4988935642064186106309911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13303828378837829616826429 4988935642064186106309911)
              ·
                refine ⟨7483403463096279159464867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4988935642064186106309911 7483403463096279159464867)
                ·
                  refine ⟨11225105194644418739197301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483403463096279159464867 11225105194644418739197301)
                  ·
                    refine ⟨1052353611997914256799747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11225105194644418739197301 1052353611997914256799747)
                    ·
                      rfl

theorem cell23_6148354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6148354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148354 prefixEnd_6148354 := by exact prefixLift 6148354
  have htrace : WordTrace (prefixWord ++ tailWord_6148354) baseStart_6148354 baseEnd_6148354 := by
    simpa [prefixWord, tailWord_6148354, baseEnd_6148354] using wordTrace_append hprefix tailTrace_6148354
  have hstable : (prefixWord ++ tailWord_6148354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148354).length < 2 ^ (prefixWord ++ tailWord_6148354).sum := by decide
  have hdescent : baseEnd_6148354 < baseStart_6148354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148360 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 1, 1, 5]
def baseStart_6148360 : Nat := 118140960795 + 6148360 * 2 ^ 59
def prefixEnd_6148360 : Nat := 4983230072969 + 3 ^ 40 * 6148360 * 2
def baseEnd_6148360 : Nat := 3157063916877669746924213

theorem tailTrace_6148360 : CollatzResearch.WordTrace tailWord_6148360 prefixEnd_6148360 3157063916877669746924213 := by
  unfold tailWord_6148360
  simp only [CollatzResearch.WordTrace]
  refine ⟨112124556002774625566929267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149499408003699500755905689 112124556002774625566929267)
  ·
    refine ⟨168186834004161938350393901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112124556002774625566929267 168186834004161938350393901)
    ·
      refine ⟨63070062751560726881397713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168186834004161938350393901 63070062751560726881397713)
      ·
        refine ⟨47302547063670545161048285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63070062751560726881397713 47302547063670545161048285)
        ·
          refine ⟨17738455148876454435393107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47302547063670545161048285 17738455148876454435393107)
          ·
            refine ⟨26607682723314681653089661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17738455148876454435393107 26607682723314681653089661)
            ·
              refine ⟨9977881021243005619908623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26607682723314681653089661 9977881021243005619908623)
              ·
                refine ⟨14966821531864508429862935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9977881021243005619908623 14966821531864508429862935)
                ·
                  refine ⟨22450232297796762644794403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14966821531864508429862935 22450232297796762644794403)
                  ·
                    refine ⟨33675348446695143967191605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22450232297796762644794403 33675348446695143967191605)
                    ·
                      refine ⟨3157063916877669746924213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33675348446695143967191605 3157063916877669746924213)
                      ·
                        rfl

theorem cell23_6148360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_6148360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148360 prefixEnd_6148360 := by exact prefixLift 6148360
  have htrace : WordTrace (prefixWord ++ tailWord_6148360) baseStart_6148360 baseEnd_6148360 := by
    simpa [prefixWord, tailWord_6148360, baseEnd_6148360] using wordTrace_append hprefix tailTrace_6148360
  have hstable : (prefixWord ++ tailWord_6148360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148360).length < 2 ^ (prefixWord ++ tailWord_6148360).sum := by decide
  have hdescent : baseEnd_6148360 < baseStart_6148360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148403 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5]
def baseStart_6148403 : Nat := 118140960795 + 6148403 * 2 ^ 59
def prefixEnd_6148403 : Nat := 4983230072969 + 3 ^ 40 * 6148403 * 2
def baseEnd_6148403 : Nat := 3157085996545813078686515

theorem tailTrace_6148403 : CollatzResearch.WordTrace tailWord_6148403 prefixEnd_6148403 3157085996545813078686515 := by
  unfold tailWord_6148403
  simp only [CollatzResearch.WordTrace]
  refine ⟨224250680344393469477673863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149500453562928979651782575 224250680344393469477673863)
  ·
    refine ⟨336376020516590204216510795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224250680344393469477673863 336376020516590204216510795)
    ·
      refine ⟨504564030774885306324766193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336376020516590204216510795 504564030774885306324766193)
      ·
        refine ⟨378423023081163979743574645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504564030774885306324766193 378423023081163979743574645)
        ·
          refine ⟨35477158413859123100960123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 378423023081163979743574645 35477158413859123100960123)
          ·
            refine ⟨53215737620788684651440185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35477158413859123100960123 53215737620788684651440185)
            ·
              refine ⟨39911803215591513488580139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53215737620788684651440185 39911803215591513488580139)
              ·
                refine ⟨59867704823387270232870209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39911803215591513488580139 59867704823387270232870209)
                ·
                  refine ⟨44900778617540452674652657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59867704823387270232870209 44900778617540452674652657)
                  ·
                    refine ⟨33675583963155339505989493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44900778617540452674652657 33675583963155339505989493)
                    ·
                      refine ⟨3157085996545813078686515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33675583963155339505989493 3157085996545813078686515)
                      ·
                        rfl

theorem cell23_6148403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_6148403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148403 prefixEnd_6148403 := by exact prefixLift 6148403
  have htrace : WordTrace (prefixWord ++ tailWord_6148403) baseStart_6148403 baseEnd_6148403 := by
    simpa [prefixWord, tailWord_6148403, baseEnd_6148403] using wordTrace_append hprefix tailTrace_6148403
  have hstable : (prefixWord ++ tailWord_6148403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148403).length < 2 ^ (prefixWord ++ tailWord_6148403).sum := by decide
  have hdescent : baseEnd_6148403 < baseStart_6148403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148423 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 4, 6]
def baseStart_6148423 : Nat := 118140960795 + 6148423 * 2 ^ 59
def prefixEnd_6148423 : Nat := 4983230072969 + 3 ^ 40 * 6148423 * 2
def baseEnd_6148423 : Nat := 1052365422052967666812141

theorem tailTrace_6148423 : CollatzResearch.WordTrace tailWord_6148423 prefixEnd_6148423 1052365422052967666812141 := by
  unfold tailWord_6148423
  simp only [CollatzResearch.WordTrace]
  refine ⟨224251409804321012893401923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149500939869547341928934615 224251409804321012893401923)
  ·
    refine ⟨336377114706481519340102885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224251409804321012893401923 336377114706481519340102885)
    ·
      refine ⟨63070709007465284876269291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336377114706481519340102885 63070709007465284876269291)
      ·
        refine ⟨94606063511197927314403937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63070709007465284876269291 94606063511197927314403937)
        ·
          refine ⟨70954547633398445485802953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94606063511197927314403937 70954547633398445485802953)
          ·
            refine ⟨53215910725048834114352215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70954547633398445485802953 53215910725048834114352215)
            ·
              refine ⟨79823866087573251171528323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53215910725048834114352215 79823866087573251171528323)
              ·
                refine ⟨119735799131359876757292485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79823866087573251171528323 119735799131359876757292485)
                ·
                  refine ⟨22450462337129976891992341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119735799131359876757292485 22450462337129976891992341)
                  ·
                    refine ⟨1052365422052967666812141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22450462337129976891992341 1052365422052967666812141)
                    ·
                      rfl

theorem cell23_6148423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_6148423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148423 prefixEnd_6148423 := by exact prefixLift 6148423
  have htrace : WordTrace (prefixWord ++ tailWord_6148423) baseStart_6148423 baseEnd_6148423 := by
    simpa [prefixWord, tailWord_6148423, baseEnd_6148423] using wordTrace_append hprefix tailTrace_6148423
  have hstable : (prefixWord ++ tailWord_6148423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148423).length < 2 ^ (prefixWord ++ tailWord_6148423).sum := by decide
  have hdescent : baseEnd_6148423 < baseStart_6148423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148447 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 1, 4, 2]
def baseStart_6148447 : Nat := 118140960795 + 6148447 * 2 ^ 59
def prefixEnd_6148447 : Nat := 4983230072969 + 3 ^ 40 * 6148447 * 2
def baseEnd_6148447 : Nat := 3157108589694610906536313

theorem tailTrace_6148447 : CollatzResearch.WordTrace tailWord_6148447 prefixEnd_6148447 3157108589694610906536313 := by
  unfold tailWord_6148447
  simp only [CollatzResearch.WordTrace]
  refine ⟨224252285156234064992275595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149501523437489376661517063 224252285156234064992275595)
  ·
    refine ⟨336378427734351097488413393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224252285156234064992275595 336378427734351097488413393)
    ·
      refine ⟨252283820800763323116310045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336378427734351097488413393 252283820800763323116310045)
      ·
        refine ⟨94606432800286246168616267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252283820800763323116310045 94606432800286246168616267)
        ·
          refine ⟨141909649200429369252924401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94606432800286246168616267 141909649200429369252924401)
          ·
            refine ⟨106432236900322026939693301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141909649200429369252924401 106432236900322026939693301)
            ·
              refine ⟨9978022209405190025596247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106432236900322026939693301 9978022209405190025596247)
              ·
                refine ⟨14967033314107785038394371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978022209405190025596247 14967033314107785038394371)
                ·
                  refine ⟨22450549971161677557591557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14967033314107785038394371 22450549971161677557591557)
                  ·
                    refine ⟨4209478119592814542048417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22450549971161677557591557 4209478119592814542048417)
                    ·
                      refine ⟨3157108589694610906536313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209478119592814542048417 3157108589694610906536313)
                      ·
                        rfl

theorem cell23_6148447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_6148447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148447 prefixEnd_6148447 := by exact prefixLift 6148447
  have htrace : WordTrace (prefixWord ++ tailWord_6148447) baseStart_6148447 baseEnd_6148447 := by
    simpa [prefixWord, tailWord_6148447, baseEnd_6148447] using wordTrace_append hprefix tailTrace_6148447
  have hstable : (prefixWord ++ tailWord_6148447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148447).length < 2 ^ (prefixWord ++ tailWord_6148447).sum := by decide
  have hdescent : baseEnd_6148447 < baseStart_6148447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148502 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6148502 : Nat := 118140960795 + 6148502 * 2 ^ 59
def prefixEnd_6148502 : Nat := 4983230072969 + 3 ^ 40 * 6148502 * 2
def baseEnd_6148502 : Nat := 3157136831130608191348561

theorem tailTrace_6148502 : CollatzResearch.WordTrace tailWord_6148502 prefixEnd_6148502 3157136831130608191348561 := by
  unfold tailWord_6148502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015893198189675586595485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149502860780689872923685173 14015893198189675586595485)
  ·
    refine ⟨5255959949321128344973307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14015893198189675586595485 5255959949321128344973307)
    ·
      refine ⟨7883939923981692517459961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5255959949321128344973307 7883939923981692517459961)
      ·
        refine ⟨5912954942986269388094971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7883939923981692517459961 5912954942986269388094971)
        ·
          refine ⟨8869432414479404082142457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912954942986269388094971 8869432414479404082142457)
          ·
            refine ⟨6652074310859553061606843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8869432414479404082142457 6652074310859553061606843)
            ·
              refine ⟨9978111466289329592410265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652074310859553061606843 9978111466289329592410265)
              ·
                refine ⟨7483583599716997194307699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9978111466289329592410265 7483583599716997194307699)
                ·
                  refine ⟨11225375399575495791461549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483583599716997194307699 11225375399575495791461549)
                  ·
                    refine ⟨4209515774840810921798081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11225375399575495791461549 4209515774840810921798081)
                    ·
                      refine ⟨3157136831130608191348561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209515774840810921798081 3157136831130608191348561)
                      ·
                        rfl

theorem cell23_6148502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6148502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148502 prefixEnd_6148502 := by exact prefixLift 6148502
  have htrace : WordTrace (prefixWord ++ tailWord_6148502) baseStart_6148502 baseEnd_6148502 := by
    simpa [prefixWord, tailWord_6148502, baseEnd_6148502] using wordTrace_append hprefix tailTrace_6148502
  have hstable : (prefixWord ++ tailWord_6148502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148502).length < 2 ^ (prefixWord ++ tailWord_6148502).sum := by decide
  have hdescent : baseEnd_6148502 < baseStart_6148502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148537 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6148537 : Nat := 118140960795 + 6148537 * 2 ^ 59
def prefixEnd_6148537 : Nat := 4983230072969 + 3 ^ 40 * 6148537 * 2
def baseEnd_6148537 : Nat := 3157154802953515554410899

theorem tailTrace_6148537 : CollatzResearch.WordTrace tailWord_6148537 prefixEnd_6148537 3157154802953515554410899 := by
  unfold tailWord_6148537
  simp only [CollatzResearch.WordTrace]
  refine ⟨224255567725908010363051865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149503711817272006908701243 224255567725908010363051865)
  ·
    refine ⟨168191675794431007772288899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224255567725908010363051865 168191675794431007772288899)
    ·
      refine ⟨252287513691646511658433349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168191675794431007772288899 252287513691646511658433349)
      ·
        refine ⟨47303908817183720935956253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252287513691646511658433349 47303908817183720935956253)
        ·
          refine ⟨17738965806443895350983595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47303908817183720935956253 17738965806443895350983595)
          ·
            refine ⟨26608448709665843026475393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17738965806443895350983595 26608448709665843026475393)
            ·
              refine ⟨19956336532249382269856545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26608448709665843026475393 19956336532249382269856545)
              ·
                refine ⟨14967252399187036702392409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19956336532249382269856545 14967252399187036702392409)
                ·
                  refine ⟨11225439299390277526794307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14967252399187036702392409 11225439299390277526794307)
                  ·
                    refine ⟨16838158949085416290191461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11225439299390277526794307 16838158949085416290191461)
                    ·
                      refine ⟨3157154802953515554410899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16838158949085416290191461 3157154802953515554410899)
                      ·
                        rfl

theorem cell23_6148537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6148537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148537 prefixEnd_6148537 := by exact prefixLift 6148537
  have htrace : WordTrace (prefixWord ++ tailWord_6148537) baseStart_6148537 baseEnd_6148537 := by
    simpa [prefixWord, tailWord_6148537, baseEnd_6148537] using wordTrace_append hprefix tailTrace_6148537
  have hstable : (prefixWord ++ tailWord_6148537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148537).length < 2 ^ (prefixWord ++ tailWord_6148537).sum := by decide
  have hdescent : baseEnd_6148537 < baseStart_6148537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148564 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_6148564 : Nat := 118140960795 + 6148564 * 2 ^ 59
def prefixEnd_6148564 : Nat := 4983230072969 + 3 ^ 40 * 6148564 * 2
def baseEnd_6148564 : Nat := 1052389555643728982924425

theorem tailTrace_6148564 : CollatzResearch.WordTrace tailWord_6148564 prefixEnd_6148564 1052389555643728982924425 := by
  unfold tailWord_6148564
  simp only [CollatzResearch.WordTrace]
  refine ⟨112128276248405096987142373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149504368331206795982856497 112128276248405096987142373)
  ·
    refine ⟨21024051796575955685089195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112128276248405096987142373 21024051796575955685089195)
    ·
      refine ⟨31536077694863933527633793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21024051796575955685089195 31536077694863933527633793)
      ·
        refine ⟨23652058271147950145725345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31536077694863933527633793 23652058271147950145725345)
        ·
          refine ⟨17739043703360962609294009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23652058271147950145725345 17739043703360962609294009)
          ·
            refine ⟨13304282777520721956970507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17739043703360962609294009 13304282777520721956970507)
            ·
              refine ⟨19956424166281082935455761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13304282777520721956970507 19956424166281082935455761)
              ·
                refine ⟨14967318124710812201591821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19956424166281082935455761 14967318124710812201591821)
                ·
                  refine ⟨5612744296766554575596933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14967318124710812201591821 5612744296766554575596933)
                  ·
                    refine ⟨1052389555643728982924425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5612744296766554575596933 1052389555643728982924425)
                    ·
                      rfl

theorem cell23_6148564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_6148564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148564 prefixEnd_6148564 := by exact prefixLift 6148564
  have htrace : WordTrace (prefixWord ++ tailWord_6148564) baseStart_6148564 baseEnd_6148564 := by
    simpa [prefixWord, tailWord_6148564, baseEnd_6148564] using wordTrace_append hprefix tailTrace_6148564
  have hstable : (prefixWord ++ tailWord_6148564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148564).length < 2 ^ (prefixWord ++ tailWord_6148564).sum := by decide
  have hdescent : baseEnd_6148564 < baseStart_6148564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148587 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 3]
def baseStart_6148587 : Nat := 118140960795 + 6148587 * 2 ^ 59
def prefixEnd_6148587 : Nat := 4983230072969 + 3 ^ 40 * 6148587 * 2
def baseEnd_6148587 : Nat := 3157180476986240358785669

theorem tailTrace_6148587 : CollatzResearch.WordTrace tailWord_6148587 prefixEnd_6148587 3157180476986240358785669 := by
  unfold tailWord_6148587
  simp only [CollatzResearch.WordTrace]
  refine ⟨224257391375726868902372015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149504927583817912601581343 224257391375726868902372015)
  ·
    refine ⟨336386087063590303353558023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224257391375726868902372015 336386087063590303353558023)
    ·
      refine ⟨504579130595385455030337035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336386087063590303353558023 504579130595385455030337035)
      ·
        refine ⟨756868695893078182545505553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504579130595385455030337035 756868695893078182545505553)
        ·
          refine ⟨567651521919808636909129165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756868695893078182545505553 567651521919808636909129165)
          ·
            refine ⟨212869320719928238840923437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567651521919808636909129165 212869320719928238840923437)
            ·
              refine ⟨79825995269973089565346289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212869320719928238840923437 79825995269973089565346289)
              ·
                refine ⟨59869496452479817174009717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79825995269973089565346289 59869496452479817174009717)
                ·
                  refine ⟨5612765292419982860063411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59869496452479817174009717 5612765292419982860063411)
                  ·
                    refine ⟨8419147938629974290095117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5612765292419982860063411 8419147938629974290095117)
                    ·
                      refine ⟨3157180476986240358785669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8419147938629974290095117 3157180476986240358785669)
                      ·
                        rfl

theorem cell23_6148587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 3].length) (baseStart_6148587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148587 prefixEnd_6148587 := by exact prefixLift 6148587
  have htrace : WordTrace (prefixWord ++ tailWord_6148587) baseStart_6148587 baseEnd_6148587 := by
    simpa [prefixWord, tailWord_6148587, baseEnd_6148587] using wordTrace_append hprefix tailTrace_6148587
  have hstable : (prefixWord ++ tailWord_6148587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148587).length < 2 ^ (prefixWord ++ tailWord_6148587).sum := by decide
  have hdescent : baseEnd_6148587 < baseStart_6148587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148627 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 6, 2]
def baseStart_6148627 : Nat := 118140960795 + 6148627 * 2 ^ 59
def prefixEnd_6148627 : Nat := 4983230072969 + 3 ^ 40 * 6148627 * 2
def baseEnd_6148627 : Nat := 3157201016212420202285485

theorem tailTrace_6148627 : CollatzResearch.WordTrace tailWord_6148627 prefixEnd_6148627 3157201016212420202285485 := by
  unfold tailWord_6148627
  simp only [CollatzResearch.WordTrace]
  refine ⟨224258850295581955733828135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149505900197054637155885423 224258850295581955733828135)
  ·
    refine ⟨336388275443372933600742203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224258850295581955733828135 336388275443372933600742203)
    ·
      refine ⟨504582413165059400401113305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336388275443372933600742203 504582413165059400401113305)
      ·
        refine ⟨378436809873794550300834979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504582413165059400401113305 378436809873794550300834979)
        ·
          refine ⟨567655214810691825451252469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378436809873794550300834979 567655214810691825451252469)
          ·
            refine ⟨53217676388502358636054919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 567655214810691825451252469 53217676388502358636054919)
            ·
              refine ⟨79826514582753537954082379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53217676388502358636054919 79826514582753537954082379)
              ·
                refine ⟨119739771874130306931123569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79826514582753537954082379 119739771874130306931123569)
                ·
                  refine ⟨89804828905597730198342677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119739771874130306931123569 89804828905597730198342677)
                  ·
                    refine ⟨4209601354949893603047313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89804828905597730198342677 4209601354949893603047313)
                    ·
                      refine ⟨3157201016212420202285485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209601354949893603047313 3157201016212420202285485)
                      ·
                        rfl

theorem cell23_6148627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6, 2].length) (baseStart_6148627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148627 prefixEnd_6148627 := by exact prefixLift 6148627
  have htrace : WordTrace (prefixWord ++ tailWord_6148627) baseStart_6148627 baseEnd_6148627 := by
    simpa [prefixWord, tailWord_6148627, baseEnd_6148627] using wordTrace_append hprefix tailTrace_6148627
  have hstable : (prefixWord ++ tailWord_6148627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148627).length < 2 ^ (prefixWord ++ tailWord_6148627).sum := by decide
  have hdescent : baseEnd_6148627 < baseStart_6148627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148678 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6148678 : Nat := 118140960795 + 6148678 * 2 ^ 59
def prefixEnd_6148678 : Nat := 4983230072969 + 3 ^ 40 * 6148678 * 2
def baseEnd_6148678 : Nat := 3157227203725799502747751

theorem tailTrace_6148678 : CollatzResearch.WordTrace tailWord_6148678 prefixEnd_6148678 3157227203725799502747751 := by
  unfold tailWord_6148678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008147200574912232622959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149507140278931460962623125 7008147200574912232622959)
  ·
    refine ⟨10512220800862368348934439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7008147200574912232622959 10512220800862368348934439)
    ·
      refine ⟨15768331201293552523401659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10512220800862368348934439 15768331201293552523401659)
      ·
        refine ⟨23652496801940328785102489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768331201293552523401659 23652496801940328785102489)
        ·
          refine ⟨17739372601455246588826867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23652496801940328785102489 17739372601455246588826867)
          ·
            refine ⟨26609058902182869883240301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17739372601455246588826867 26609058902182869883240301)
            ·
              refine ⟨9978397088318576206215113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26609058902182869883240301 9978397088318576206215113)
              ·
                refine ⟨7483797816238932154661335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9978397088318576206215113 7483797816238932154661335)
                ·
                  refine ⟨11225696724358398231992003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483797816238932154661335 11225696724358398231992003)
                  ·
                    refine ⟨16838545086537597347988005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11225696724358398231992003 16838545086537597347988005)
                    ·
                      refine ⟨3157227203725799502747751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16838545086537597347988005 3157227203725799502747751)
                      ·
                        rfl

theorem cell23_6148678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6148678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148678 prefixEnd_6148678 := by exact prefixLift 6148678
  have htrace : WordTrace (prefixWord ++ tailWord_6148678) baseStart_6148678 baseEnd_6148678 := by
    simpa [prefixWord, tailWord_6148678, baseEnd_6148678] using wordTrace_append hprefix tailTrace_6148678
  have hstable : (prefixWord ++ tailWord_6148678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148678).length < 2 ^ (prefixWord ++ tailWord_6148678).sum := by decide
  have hdescent : baseEnd_6148678 < baseStart_6148678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148762 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6148762 : Nat := 118140960795 + 6148762 * 2 ^ 59
def prefixEnd_6148762 : Nat := 4983230072969 + 3 ^ 40 * 6148762 * 2
def baseEnd_6148762 : Nat := 3157270336100777174097365

theorem tailTrace_6148762 : CollatzResearch.WordTrace tailWord_6148762 prefixEnd_6148762 3157270336100777174097365 := by
  unfold tailWord_6148762
  simp only [CollatzResearch.WordTrace]
  refine ⟨56065943537523218447498135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149509182766728582526661693 56065943537523218447498135)
  ·
    refine ⟨84098915306284827671247203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56065943537523218447498135 84098915306284827671247203)
    ·
      refine ⟨126148372959427241506870805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84098915306284827671247203 126148372959427241506870805)
      ·
        refine ⟨5913204982473151945634569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126148372959427241506870805 5913204982473151945634569)
        ·
          refine ⟨4434903736854863959225927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5913204982473151945634569 4434903736854863959225927)
          ·
            refine ⟨6652355605282295938838891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434903736854863959225927 6652355605282295938838891)
            ·
              refine ⟨9978533407923443908258337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652355605282295938838891 9978533407923443908258337)
              ·
                refine ⟨7483900055942582931193753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9978533407923443908258337 7483900055942582931193753)
                ·
                  refine ⟨5612925041956937198395315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7483900055942582931193753 5612925041956937198395315)
                  ·
                    refine ⟨8419387562935405797592973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5612925041956937198395315 8419387562935405797592973)
                    ·
                      refine ⟨3157270336100777174097365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8419387562935405797592973 3157270336100777174097365)
                      ·
                        rfl

theorem cell23_6148762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6148762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148762 prefixEnd_6148762 := by exact prefixLift 6148762
  have htrace : WordTrace (prefixWord ++ tailWord_6148762) baseStart_6148762 baseEnd_6148762 := by
    simpa [prefixWord, tailWord_6148762, baseEnd_6148762] using wordTrace_append hprefix tailTrace_6148762
  have hstable : (prefixWord ++ tailWord_6148762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148762).length < 2 ^ (prefixWord ++ tailWord_6148762).sum := by decide
  have hdescent : baseEnd_6148762 < baseStart_6148762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148764 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6148764 : Nat := 118140960795 + 6148764 * 2 ^ 59
def prefixEnd_6148764 : Nat := 4983230072969 + 3 ^ 40 * 6148764 * 2
def baseEnd_6148764 : Nat := 3157271363062086166272355

theorem tailTrace_6148764 : CollatzResearch.WordTrace tailWord_6148764 prefixEnd_6148764 3157271363062086166272355 := by
  unfold tailWord_6148764
  simp only [CollatzResearch.WordTrace]
  refine ⟨112131923548042814065782673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149509231397390418754376897 112131923548042814065782673)
  ·
    refine ⟨84098942661032110549337005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112131923548042814065782673 84098942661032110549337005)
    ·
      refine ⟨31537103497887041456001377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84098942661032110549337005 31537103497887041456001377)
      ·
        refine ⟨23652827623415281092001033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31537103497887041456001377 23652827623415281092001033)
        ·
          refine ⟨17739620717561460819000775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23652827623415281092001033 17739620717561460819000775)
          ·
            refine ⟨26609431076342191228501163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17739620717561460819000775 26609431076342191228501163)
            ·
              refine ⟨39914146614513286842751745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26609431076342191228501163 39914146614513286842751745)
              ·
                refine ⟨29935609960884965132063809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39914146614513286842751745 29935609960884965132063809)
                ·
                  refine ⟨22451707470663723849047857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29935609960884965132063809 22451707470663723849047857)
                  ·
                    refine ⟨16838780602997792886785893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22451707470663723849047857 16838780602997792886785893)
                    ·
                      refine ⟨3157271363062086166272355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16838780602997792886785893 3157271363062086166272355)
                      ·
                        rfl

theorem cell23_6148764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6148764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148764 prefixEnd_6148764 := by exact prefixLift 6148764
  have htrace : WordTrace (prefixWord ++ tailWord_6148764) baseStart_6148764 baseEnd_6148764 := by
    simpa [prefixWord, tailWord_6148764, baseEnd_6148764] using wordTrace_append hprefix tailTrace_6148764
  have hstable : (prefixWord ++ tailWord_6148764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148764).length < 2 ^ (prefixWord ++ tailWord_6148764).sum := by decide
  have hdescent : baseEnd_6148764 < baseStart_6148764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148768 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 4, 2, 2]
def baseStart_6148768 : Nat := 118140960795 + 6148768 * 2 ^ 59
def prefixEnd_6148768 : Nat := 4983230072969 + 3 ^ 40 * 6148768 * 2
def baseEnd_6148768 : Nat := 3157273416984704150622337

theorem tailTrace_6148768 : CollatzResearch.WordTrace tailWord_6148768 prefixEnd_6148768 3157273416984704150622337 := by
  unfold tailWord_6148768
  simp only [CollatzResearch.WordTrace]
  refine ⟨112131996494035568407355479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149509328658714091209807305 112131996494035568407355479)
  ·
    refine ⟨168197994741053352611033219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112131996494035568407355479 168197994741053352611033219)
    ·
      refine ⟨252296992111580028916549829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168197994741053352611033219 252296992111580028916549829)
      ·
        refine ⟨47305686020921255421853093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252296992111580028916549829 47305686020921255421853093)
        ·
          refine ⟨8869816128922735391597455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47305686020921255421853093 8869816128922735391597455)
          ·
            refine ⟨13304724193384103087396183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8869816128922735391597455 13304724193384103087396183)
            ·
              refine ⟨19957086290076154631094275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13304724193384103087396183 19957086290076154631094275)
              ·
                refine ⟨29935629435114231946641413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19957086290076154631094275 29935629435114231946641413)
                ·
                  refine ⟨5612930519083918489995265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29935629435114231946641413 5612930519083918489995265)
                  ·
                    refine ⟨4209697889312938867496449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5612930519083918489995265 4209697889312938867496449)
                    ·
                      refine ⟨3157273416984704150622337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209697889312938867496449 3157273416984704150622337)
                      ·
                        rfl

theorem cell23_6148768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_6148768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148768 prefixEnd_6148768 := by exact prefixLift 6148768
  have htrace : WordTrace (prefixWord ++ tailWord_6148768) baseStart_6148768 baseEnd_6148768 := by
    simpa [prefixWord, tailWord_6148768, baseEnd_6148768] using wordTrace_append hprefix tailTrace_6148768
  have hstable : (prefixWord ++ tailWord_6148768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148768).length < 2 ^ (prefixWord ++ tailWord_6148768).sum := by decide
  have hdescent : baseEnd_6148768 < baseStart_6148768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148785 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6148785 : Nat := 118140960795 + 6148785 * 2 ^ 59
def prefixEnd_6148785 : Nat := 4983230072969 + 3 ^ 40 * 6148785 * 2
def baseEnd_6148785 : Nat := 3157282146155830584109759

theorem tailTrace_6148785 : CollatzResearch.WordTrace tailWord_6148785 prefixEnd_6148785 3157282146155830584109759 := by
  unfold tailWord_6148785
  simp only [CollatzResearch.WordTrace]
  refine ⟨224264613029009548718079809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149509742019339699145386539 224264613029009548718079809)
  ·
    refine ⟨168198459771757161538559857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224264613029009548718079809 168198459771757161538559857)
    ·
      refine ⟨126148844828817871153919893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168198459771757161538559857 126148844828817871153919893)
      ·
        refine ⟨5913227101350837710339995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126148844828817871153919893 5913227101350837710339995)
        ·
          refine ⟨8869840652026256565509993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5913227101350837710339995 8869840652026256565509993)
          ·
            refine ⟨6652380489019692424132495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8869840652026256565509993 6652380489019692424132495)
            ·
              refine ⟨9978570733529538636198743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652380489019692424132495 9978570733529538636198743)
              ·
                refine ⟨14967856100294307954298115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978570733529538636198743 14967856100294307954298115)
                ·
                  refine ⟨22451784150441461931447173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14967856100294307954298115 22451784150441461931447173)
                  ·
                    refine ⟨4209709528207774112146345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22451784150441461931447173 4209709528207774112146345)
                    ·
                      refine ⟨3157282146155830584109759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209709528207774112146345 3157282146155830584109759)
                      ·
                        rfl

theorem cell23_6148785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6148785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148785 prefixEnd_6148785 := by exact prefixLift 6148785
  have htrace : WordTrace (prefixWord ++ tailWord_6148785) baseStart_6148785 baseEnd_6148785 := by
    simpa [prefixWord, tailWord_6148785, baseEnd_6148785] using wordTrace_append hprefix tailTrace_6148785
  have hstable : (prefixWord ++ tailWord_6148785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148785).length < 2 ^ (prefixWord ++ tailWord_6148785).sum := by decide
  have hdescent : baseEnd_6148785 < baseStart_6148785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148787 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 1, 7]
def baseStart_6148787 : Nat := 118140960795 + 6148787 * 2 ^ 59
def prefixEnd_6148787 : Nat := 4983230072969 + 3 ^ 40 * 6148787 * 2
def baseEnd_6148787 : Nat := 1052427724372379858761583

theorem tailTrace_6148787 : CollatzResearch.WordTrace tailWord_6148787 prefixEnd_6148787 1052427724372379858761583 := by
  unfold tailWord_6148787
  simp only [CollatzResearch.WordTrace]
  refine ⟨224264685975002303059652615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149509790650001535373101743 224264685975002303059652615)
  ·
    refine ⟨336397028962503454589478923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224264685975002303059652615 336397028962503454589478923)
    ·
      refine ⟨504595543443755181884218385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336397028962503454589478923 504595543443755181884218385)
      ·
        refine ⟨378446657582816386413163789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504595543443755181884218385 378446657582816386413163789)
        ·
          refine ⟨141917496593556144904936421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378446657582816386413163789 141917496593556144904936421)
          ·
            refine ⟨26609530611291777169675579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141917496593556144904936421 26609530611291777169675579)
            ·
              refine ⟨39914295916937665754513369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26609530611291777169675579 39914295916937665754513369)
              ·
                refine ⟨29935721937703249315885027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39914295916937665754513369 29935721937703249315885027)
                ·
                  refine ⟨44903582906554873973827541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29935721937703249315885027 44903582906554873973827541)
                  ·
                    refine ⟨1052427724372379858761583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44903582906554873973827541 1052427724372379858761583)
                    ·
                      rfl

theorem cell23_6148787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 7].length) (baseStart_6148787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148787 prefixEnd_6148787 := by exact prefixLift 6148787
  have htrace : WordTrace (prefixWord ++ tailWord_6148787) baseStart_6148787 baseEnd_6148787 := by
    simpa [prefixWord, tailWord_6148787, baseEnd_6148787] using wordTrace_append hprefix tailTrace_6148787
  have hstable : (prefixWord ++ tailWord_6148787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148787).length < 2 ^ (prefixWord ++ tailWord_6148787).sum := by decide
  have hdescent : baseEnd_6148787 < baseStart_6148787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148804 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 1, 7]
def baseStart_6148804 : Nat := 118140960795 + 6148804 * 2 ^ 59
def prefixEnd_6148804 : Nat := 4983230072969 + 3 ^ 40 * 6148804 * 2
def baseEnd_6148804 : Nat := 1052430634096088669924057

theorem tailTrace_6148804 : CollatzResearch.WordTrace tailWord_6148804 prefixEnd_6148804 1052430634096088669924057 := by
  unfold tailWord_6148804
  simp only [CollatzResearch.WordTrace]
  refine ⟨112132653007970357481510733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149510204010627143308680977 112132653007970357481510733)
  ·
    refine ⟨42049744877988884055566525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112132653007970357481510733 42049744877988884055566525)
    ·
      refine ⟨15768654329245831520837447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42049744877988884055566525 15768654329245831520837447)
      ·
        refine ⟨23652981493868747281256171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768654329245831520837447 23652981493868747281256171)
        ·
          refine ⟨35479472240803120921884257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23652981493868747281256171 35479472240803120921884257)
          ·
            refine ⟨26609604180602340691413193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35479472240803120921884257 26609604180602340691413193)
            ·
              refine ⟨19957203135451755518559895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26609604180602340691413193 19957203135451755518559895)
              ·
                refine ⟨29935804703177633277839843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19957203135451755518559895 29935804703177633277839843)
                ·
                  refine ⟨44903707054766449916759765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29935804703177633277839843 44903707054766449916759765)
                  ·
                    refine ⟨1052430634096088669924057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44903707054766449916759765 1052430634096088669924057)
                    ·
                      rfl

theorem cell23_6148804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_6148804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148804 prefixEnd_6148804 := by exact prefixLift 6148804
  have htrace : WordTrace (prefixWord ++ tailWord_6148804) baseStart_6148804 baseEnd_6148804 := by
    simpa [prefixWord, tailWord_6148804, baseEnd_6148804] using wordTrace_append hprefix tailTrace_6148804
  have hstable : (prefixWord ++ tailWord_6148804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148804).length < 2 ^ (prefixWord ++ tailWord_6148804).sum := by decide
  have hdescent : baseEnd_6148804 < baseStart_6148804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148824 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6148824 : Nat := 118140960795 + 6148824 * 2 ^ 59
def prefixEnd_6148824 : Nat := 4983230072969 + 3 ^ 40 * 6148824 * 2
def baseEnd_6148824 : Nat := 3157302171901355931522079

theorem tailTrace_6148824 : CollatzResearch.WordTrace tailWord_6148824 prefixEnd_6148824 3157302171901355931522079 := by
  unfold tailWord_6148824
  simp only [CollatzResearch.WordTrace]
  refine ⟨112133017737934129189374763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149510690317245505585833017 112133017737934129189374763)
  ·
    refine ⟨168199526606901193784062145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112133017737934129189374763 168199526606901193784062145)
    ·
      refine ⟨126149644955175895338046609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168199526606901193784062145 126149644955175895338046609)
      ·
        refine ⟨94612233716381921503534957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126149644955175895338046609 94612233716381921503534957)
        ·
          refine ⟨35479587643643220563825609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94612233716381921503534957 35479587643643220563825609)
          ·
            refine ⟨26609690732732415422869207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35479587643643220563825609 26609690732732415422869207)
            ·
              refine ⟨39914536099098623134303811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26609690732732415422869207 39914536099098623134303811)
              ·
                refine ⟨59871804148647934701455717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39914536099098623134303811 59871804148647934701455717)
                ·
                  refine ⟨11225963277871487756522947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59871804148647934701455717 11225963277871487756522947)
                  ·
                    refine ⟨16838944916807231634784421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11225963277871487756522947 16838944916807231634784421)
                    ·
                      refine ⟨3157302171901355931522079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16838944916807231634784421 3157302171901355931522079)
                      ·
                        rfl

theorem cell23_6148824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6148824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148824 prefixEnd_6148824 := by exact prefixLift 6148824
  have htrace : WordTrace (prefixWord ++ tailWord_6148824) baseStart_6148824 baseEnd_6148824 := by
    simpa [prefixWord, tailWord_6148824, baseEnd_6148824] using wordTrace_append hprefix tailTrace_6148824
  have hstable : (prefixWord ++ tailWord_6148824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148824).length < 2 ^ (prefixWord ++ tailWord_6148824).sum := by decide
  have hdescent : baseEnd_6148824 < baseStart_6148824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148844 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_6148844 : Nat := 118140960795 + 6148844 * 2 ^ 59
def prefixEnd_6148844 : Nat := 4983230072969 + 3 ^ 40 * 6148844 * 2
def baseEnd_6148844 : Nat := 3157312441514445853271987

theorem tailTrace_6148844 : CollatzResearch.WordTrace tailWord_6148844 prefixEnd_6148844 3157312441514445853271987 := by
  unfold tailWord_6148844
  simp only [CollatzResearch.WordTrace]
  refine ⟨112133382467897900897238793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149511176623863867862985057 112133382467897900897238793)
  ·
    refine ⟨84100036850923425672929095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112133382467897900897238793 84100036850923425672929095)
    ·
      refine ⟨126150055276385138509393643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84100036850923425672929095 126150055276385138509393643)
      ·
        refine ⟨189225082914577707764090465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126150055276385138509393643 189225082914577707764090465)
        ·
          refine ⟨141918812185933280823067849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189225082914577707764090465 141918812185933280823067849)
          ·
            refine ⟨106439109139449960617300887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141918812185933280823067849 106439109139449960617300887)
            ·
              refine ⟨159658663709174940925951331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106439109139449960617300887 159658663709174940925951331)
              ·
                refine ⟨239487995563762411388926997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159658663709174940925951331 239487995563762411388926997)
                ·
                  refine ⟨11225999792051363033855953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239487995563762411388926997 11225999792051363033855953)
                  ·
                    refine ⟨8419499844038522275391965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11225999792051363033855953 8419499844038522275391965)
                    ·
                      refine ⟨3157312441514445853271987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8419499844038522275391965 3157312441514445853271987)
                      ·
                        rfl

theorem cell23_6148844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_6148844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148844 prefixEnd_6148844 := by exact prefixLift 6148844
  have htrace : WordTrace (prefixWord ++ tailWord_6148844) baseStart_6148844 baseEnd_6148844 := by
    simpa [prefixWord, tailWord_6148844, baseEnd_6148844] using wordTrace_append hprefix tailTrace_6148844
  have hstable : (prefixWord ++ tailWord_6148844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148844).length < 2 ^ (prefixWord ++ tailWord_6148844).sum := by decide
  have hdescent : baseEnd_6148844 < baseStart_6148844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148861 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 3]
def baseStart_6148861 : Nat := 118140960795 + 6148861 * 2 ^ 59
def prefixEnd_6148861 : Nat := 4983230072969 + 3 ^ 40 * 6148861 * 2
def baseEnd_6148861 : Nat := 3157321170685572286759409

theorem tailTrace_6148861 : CollatzResearch.WordTrace tailWord_6148861 prefixEnd_6148861 3157321170685572286759409 := by
  unfold tailWord_6148861
  simp only [CollatzResearch.WordTrace]
  refine ⟨224267384976734213697846437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149511589984489475798564291 224267384976734213697846437)
  ·
    refine ⟨42050134683137665068346207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224267384976734213697846437 42050134683137665068346207)
    ·
      refine ⟨63075202024706497602519311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42050134683137665068346207 63075202024706497602519311)
      ·
        refine ⟨94612803037059746403778967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63075202024706497602519311 94612803037059746403778967)
        ·
          refine ⟨141919204555589619605668451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94612803037059746403778967 141919204555589619605668451)
          ·
            refine ⟨212878806833384429408502677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141919204555589619605668451 212878806833384429408502677)
            ·
              refine ⟨9978694070314895128523563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212878806833384429408502677 9978694070314895128523563)
              ·
                refine ⟨14968041105472342692785345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978694070314895128523563 14968041105472342692785345)
                ·
                  refine ⟨11226030829104257019589009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14968041105472342692785345 11226030829104257019589009)
                  ·
                    refine ⟨8419523121828192764691757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11226030829104257019589009 8419523121828192764691757)
                    ·
                      refine ⟨3157321170685572286759409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8419523121828192764691757 3157321170685572286759409)
                      ·
                        rfl

theorem cell23_6148861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_6148861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148861 prefixEnd_6148861 := by exact prefixLift 6148861
  have htrace : WordTrace (prefixWord ++ tailWord_6148861) baseStart_6148861 baseEnd_6148861 := by
    simpa [prefixWord, tailWord_6148861, baseEnd_6148861] using wordTrace_append hprefix tailTrace_6148861
  have hstable : (prefixWord ++ tailWord_6148861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148861).length < 2 ^ (prefixWord ++ tailWord_6148861).sum := by decide
  have hdescent : baseEnd_6148861 < baseStart_6148861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148867 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8]
def baseStart_6148867 : Nat := 118140960795 + 6148867 * 2 ^ 59
def prefixEnd_6148867 : Nat := 4983230072969 + 3 ^ 40 * 6148867 * 2
def baseEnd_6148867 : Nat := 3157324251569499263284381

theorem tailTrace_6148867 : CollatzResearch.WordTrace tailWord_6148867 prefixEnd_6148867 3157324251569499263284381 := by
  unfold tailWord_6148867
  simp only [CollatzResearch.WordTrace]
  refine ⟨224267603814712476722564855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149511735876474984481709903 224267603814712476722564855)
  ·
    refine ⟨336401405722068715083847283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224267603814712476722564855 336401405722068715083847283)
    ·
      refine ⟨504602108583103072625770925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336401405722068715083847283 504602108583103072625770925)
      ·
        refine ⟨189225790718663652234664097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504602108583103072625770925 189225790718663652234664097)
        ·
          refine ⟨141919343038997739175998073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189225790718663652234664097 141919343038997739175998073)
          ·
            refine ⟨106439507279248304381998555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141919343038997739175998073 106439507279248304381998555)
            ·
              refine ⟨159659260918872456572997833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106439507279248304381998555 159659260918872456572997833)
              ·
                refine ⟨119744445689154342429748375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159659260918872456572997833 119744445689154342429748375)
                ·
                  refine ⟨179616668533731513644622563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119744445689154342429748375 179616668533731513644622563)
                  ·
                    refine ⟨269425002800597270466933845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 179616668533731513644622563 269425002800597270466933845)
                    ·
                      refine ⟨3157324251569499263284381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 269425002800597270466933845 3157324251569499263284381)
                      ·
                        rfl

theorem cell23_6148867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_6148867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148867 prefixEnd_6148867 := by exact prefixLift 6148867
  have htrace : WordTrace (prefixWord ++ tailWord_6148867) baseStart_6148867 baseEnd_6148867 := by
    simpa [prefixWord, tailWord_6148867, baseEnd_6148867] using wordTrace_append hprefix tailTrace_6148867
  have hstable : (prefixWord ++ tailWord_6148867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148867).length < 2 ^ (prefixWord ++ tailWord_6148867).sum := by decide
  have hdescent : baseEnd_6148867 < baseStart_6148867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148868 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 1, 4]
def baseStart_6148868 : Nat := 118140960795 + 6148868 * 2 ^ 59
def prefixEnd_6148868 : Nat := 4983230072969 + 3 ^ 40 * 6148868 * 2
def baseEnd_6148868 : Nat := 1052441588350051253123959

theorem tailTrace_6148868 : CollatzResearch.WordTrace tailWord_6148868 prefixEnd_6148868 1052441588350051253123959 := by
  unfold tailWord_6148868
  simp only [CollatzResearch.WordTrace]
  refine ⟨112133820143854426946675629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149511760191805902595567505 112133820143854426946675629)
  ·
    refine ⟨42050182553945410105003361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112133820143854426946675629 42050182553945410105003361)
    ·
      refine ⟨31537636915459057578752521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42050182553945410105003361 31537636915459057578752521)
      ·
        refine ⟨23653227686594293184064391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31537636915459057578752521 23653227686594293184064391)
        ·
          refine ⟨35479841529891439776096587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23653227686594293184064391 35479841529891439776096587)
          ·
            refine ⟨53219762294837159664144881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35479841529891439776096587 53219762294837159664144881)
            ·
              refine ⟨39914821721127869748108661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53219762294837159664144881 39914821721127869748108661)
              ·
                refine ⟨3742014536355737788885187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39914821721127869748108661 3742014536355737788885187)
                ·
                  refine ⟨5613021804533606683327781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742014536355737788885187 5613021804533606683327781)
                  ·
                    refine ⟨1052441588350051253123959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613021804533606683327781 1052441588350051253123959)
                    ·
                      rfl

theorem cell23_6148868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_6148868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148868 prefixEnd_6148868 := by exact prefixLift 6148868
  have htrace : WordTrace (prefixWord ++ tailWord_6148868) baseStart_6148868 baseEnd_6148868 := by
    simpa [prefixWord, tailWord_6148868, baseEnd_6148868] using wordTrace_append hprefix tailTrace_6148868
  have hstable : (prefixWord ++ tailWord_6148868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148868).length < 2 ^ (prefixWord ++ tailWord_6148868).sum := by decide
  have hdescent : baseEnd_6148868 < baseStart_6148868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148901 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 1, 5, 2]
def baseStart_6148901 : Nat := 118140960795 + 6148901 * 2 ^ 59
def prefixEnd_6148901 : Nat := 4983230072969 + 3 ^ 40 * 6148901 * 2
def baseEnd_6148901 : Nat := 3157341709911752130259225

theorem tailTrace_6148901 : CollatzResearch.WordTrace tailWord_6148901 prefixEnd_6148901 3157341709911752130259225 := by
  unfold tailWord_6148901
  simp only [CollatzResearch.WordTrace]
  refine ⟨224268843896589300529302557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149512562597726200352868371 224268843896589300529302557)
  ·
    refine ⟨84100816461220987698488459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224268843896589300529302557 84100816461220987698488459)
    ·
      refine ⟨126151224691831481547732689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84100816461220987698488459 126151224691831481547732689)
      ·
        refine ⟨94613418518873611160799517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126151224691831481547732689 94613418518873611160799517)
        ·
          refine ⟨35480031944577604185299819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94613418518873611160799517 35480031944577604185299819)
          ·
            refine ⟨53220047916866406277949729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35480031944577604185299819 53220047916866406277949729)
            ·
              refine ⟨39915035937649804708462297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53220047916866406277949729 39915035937649804708462297)
              ·
                refine ⟨29936276953237353531346723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39915035937649804708462297 29936276953237353531346723)
                ·
                  refine ⟨44904415429856030297020085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29936276953237353531346723 44904415429856030297020085)
                  ·
                    refine ⟨4209788946549002840345633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44904415429856030297020085 4209788946549002840345633)
                    ·
                      refine ⟨3157341709911752130259225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209788946549002840345633 3157341709911752130259225)
                      ·
                        rfl

theorem cell23_6148901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_6148901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148901 prefixEnd_6148901 := by exact prefixLift 6148901
  have htrace : WordTrace (prefixWord ++ tailWord_6148901) baseStart_6148901 baseEnd_6148901 := by
    simpa [prefixWord, tailWord_6148901, baseEnd_6148901] using wordTrace_append hprefix tailTrace_6148901
  have hstable : (prefixWord ++ tailWord_6148901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148901).length < 2 ^ (prefixWord ++ tailWord_6148901).sum := by decide
  have hdescent : baseEnd_6148901 < baseStart_6148901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148904 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6148904 : Nat := 118140960795 + 6148904 * 2 ^ 59
def prefixEnd_6148904 : Nat := 4983230072969 + 3 ^ 40 * 6148904 * 2
def baseEnd_6148904 : Nat := 3157343250353715618521711

theorem tailTrace_6148904 : CollatzResearch.WordTrace tailWord_6148904 prefixEnd_6148904 3157343250353715618521711 := by
  unfold tailWord_6148904
  simp only [CollatzResearch.WordTrace]
  refine ⟨112134476657789216020830883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149512635543718954694441177 112134476657789216020830883)
  ·
    refine ⟨168201714986683824031246325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112134476657789216020830883 168201714986683824031246325)
    ·
      refine ⟨15768910780001608502929343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168201714986683824031246325 15768910780001608502929343)
      ·
        refine ⟨23653366170002412754394015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768910780001608502929343 23653366170002412754394015)
        ·
          refine ⟨35480049255003619131591023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23653366170002412754394015 35480049255003619131591023)
          ·
            refine ⟨53220073882505428697386535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35480049255003619131591023 53220073882505428697386535)
            ·
              refine ⟨79830110823758143046079803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53220073882505428697386535 79830110823758143046079803)
              ·
                refine ⟨119745166235637214569119705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79830110823758143046079803 119745166235637214569119705)
                ·
                  refine ⟨89808874676727910926839779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119745166235637214569119705 89808874676727910926839779)
                  ·
                    refine ⟨134713312015091866390259669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89808874676727910926839779 134713312015091866390259669)
                    ·
                      refine ⟨3157343250353715618521711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134713312015091866390259669 3157343250353715618521711)
                      ·
                        rfl

theorem cell23_6148904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6148904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148904 prefixEnd_6148904 := by exact prefixLift 6148904
  have htrace : WordTrace (prefixWord ++ tailWord_6148904) baseStart_6148904 baseEnd_6148904 := by
    simpa [prefixWord, tailWord_6148904, baseEnd_6148904] using wordTrace_append hprefix tailTrace_6148904
  have hstable : (prefixWord ++ tailWord_6148904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148904).length < 2 ^ (prefixWord ++ tailWord_6148904).sum := by decide
  have hdescent : baseEnd_6148904 < baseStart_6148904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148931 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 4]
def baseStart_6148931 : Nat := 118140960795 + 6148931 * 2 ^ 59
def prefixEnd_6148931 : Nat := 4983230072969 + 3 ^ 40 * 6148931 * 2
def baseEnd_6148931 : Nat := 3157357114331387012884087

theorem tailTrace_6148931 : CollatzResearch.WordTrace tailWord_6148931 prefixEnd_6148931 3157357114331387012884087 := by
  unfold tailWord_6148931
  simp only [CollatzResearch.WordTrace]
  refine ⟨224269938086480615652894647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149513292057653743768596431 224269938086480615652894647)
  ·
    refine ⟨336404907129720923479341971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224269938086480615652894647 336404907129720923479341971)
    ·
      refine ⟨504607360694581385219012957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336404907129720923479341971 504607360694581385219012957)
      ·
        refine ⟨189227760260468019457129859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504607360694581385219012957 189227760260468019457129859)
        ·
          refine ⟨283841640390702029185694789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189227760260468019457129859 283841640390702029185694789)
          ·
            refine ⟨53220307573256630472317773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283841640390702029185694789 53220307573256630472317773)
            ·
              refine ⟨19957615339971236427119165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53220307573256630472317773 19957615339971236427119165)
              ·
                refine ⟨7484105752489213660169687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19957615339971236427119165 7484105752489213660169687)
                ·
                  refine ⟨11226158628733820490254531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484105752489213660169687 11226158628733820490254531)
                  ·
                    refine ⟨16839237943100730735381797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11226158628733820490254531 16839237943100730735381797)
                    ·
                      refine ⟨3157357114331387012884087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16839237943100730735381797 3157357114331387012884087)
                      ·
                        rfl

theorem cell23_6148931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_6148931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148931 prefixEnd_6148931 := by exact prefixLift 6148931
  have htrace : WordTrace (prefixWord ++ tailWord_6148931) baseStart_6148931 baseEnd_6148931 := by
    simpa [prefixWord, tailWord_6148931, baseEnd_6148931] using wordTrace_append hprefix tailTrace_6148931
  have hstable : (prefixWord ++ tailWord_6148931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148931).length < 2 ^ (prefixWord ++ tailWord_6148931).sum := by decide
  have hdescent : baseEnd_6148931 < baseStart_6148931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148932 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 6]
def baseStart_6148932 : Nat := 118140960795 + 6148932 * 2 ^ 59
def prefixEnd_6148932 : Nat := 4983230072969 + 3 ^ 40 * 6148932 * 2
def baseEnd_6148932 : Nat := 350817514201337945441287

theorem tailTrace_6148932 : CollatzResearch.WordTrace tailWord_6148932 prefixEnd_6148932 350817514201337945441287 := by
  unfold tailWord_6148932
  simp only [CollatzResearch.WordTrace]
  refine ⟨112134987279738496411840525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149513316372984661882454033 112134987279738496411840525)
  ·
    refine ⟨42050620229901936154440197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112134987279738496411840525 42050620229901936154440197)
    ·
      refine ⟨7884491293106613028957537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42050620229901936154440197 7884491293106613028957537)
      ·
        refine ⟨5913368469829959771718153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7884491293106613028957537 5913368469829959771718153)
        ·
          refine ⟨4435026352372469828788615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5913368469829959771718153 4435026352372469828788615)
          ·
            refine ⟨6652539528558704743182923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435026352372469828788615 6652539528558704743182923)
            ·
              refine ⟨9978809292838057114774385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652539528558704743182923 9978809292838057114774385)
              ·
                refine ⟨7484106969628542836080789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9978809292838057114774385 7484106969628542836080789)
                ·
                  refine ⟨350817514201337945441287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7484106969628542836080789 350817514201337945441287)
                  ·
                    rfl

theorem cell23_6148932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_6148932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148932 prefixEnd_6148932 := by exact prefixLift 6148932
  have htrace : WordTrace (prefixWord ++ tailWord_6148932) baseStart_6148932 baseEnd_6148932 := by
    simpa [prefixWord, tailWord_6148932, baseEnd_6148932] using wordTrace_append hprefix tailTrace_6148932
  have hstable : (prefixWord ++ tailWord_6148932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148932).length < 2 ^ (prefixWord ++ tailWord_6148932).sum := by decide
  have hdescent : baseEnd_6148932 < baseStart_6148932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148944 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4]
def baseStart_6148944 : Nat := 118140960795 + 6148944 * 2 ^ 59
def prefixEnd_6148944 : Nat := 4983230072969 + 3 ^ 40 * 6148944 * 2
def baseEnd_6148944 : Nat := 3157363789579895462021527

theorem tailTrace_6148944 : CollatzResearch.WordTrace tailWord_6148944 prefixEnd_6148944 3157363789579895462021527 := by
  unfold tailWord_6148944
  simp only [CollatzResearch.WordTrace]
  refine ⟨112135206117716759436558943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149513608156955679248745257 112135206117716759436558943)
  ·
    refine ⟨168202809176575139154838415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112135206117716759436558943 168202809176575139154838415)
    ·
      refine ⟨252304213764862708732257623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168202809176575139154838415 252304213764862708732257623)
      ·
        refine ⟨378456320647294063098386435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252304213764862708732257623 378456320647294063098386435)
        ·
          refine ⟨567684480970941094647579653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378456320647294063098386435 567684480970941094647579653)
          ·
            refine ⟨106440840182051455246421185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 567684480970941094647579653 106440840182051455246421185)
            ·
              refine ⟨79830630136538591434815889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106440840182051455246421185 79830630136538591434815889)
              ·
                refine ⟨59872972602403943576111917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79830630136538591434815889 59872972602403943576111917)
                ·
                  refine ⟨22452364725901478841041969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59872972602403943576111917 22452364725901478841041969)
                  ·
                    refine ⟨16839273544426109130781477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22452364725901478841041969 16839273544426109130781477)
                    ·
                      refine ⟨3157363789579895462021527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16839273544426109130781477 3157363789579895462021527)
                      ·
                        rfl

theorem cell23_6148944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_6148944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148944 prefixEnd_6148944 := by exact prefixLift 6148944
  have htrace : WordTrace (prefixWord ++ tailWord_6148944) baseStart_6148944 baseEnd_6148944 := by
    simpa [prefixWord, tailWord_6148944, baseEnd_6148944] using wordTrace_append hprefix tailTrace_6148944
  have hstable : (prefixWord ++ tailWord_6148944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148944).length < 2 ^ (prefixWord ++ tailWord_6148944).sum := by decide
  have hdescent : baseEnd_6148944 < baseStart_6148944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148951 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_6148951 : Nat := 118140960795 + 6148951 * 2 ^ 59
def prefixEnd_6148951 : Nat := 4983230072969 + 3 ^ 40 * 6148951 * 2
def baseEnd_6148951 : Nat := 3157367383944476934633995

theorem tailTrace_6148951 : CollatzResearch.WordTrace tailWord_6148951 prefixEnd_6148951 3157367383944476934633995 := by
  unfold tailWord_6148951
  simp only [CollatzResearch.WordTrace]
  refine ⟨224270667546408159068622707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149513778364272106045748471 224270667546408159068622707)
  ·
    refine ⟨336406001319612238602934061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224270667546408159068622707 336406001319612238602934061)
    ·
      refine ⟨126152250494854589476100273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336406001319612238602934061 126152250494854589476100273)
      ·
        refine ⟨94614187871140942107075205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126152250494854589476100273 94614187871140942107075205)
        ·
          refine ⟨17740160225838926645076601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94614187871140942107075205 17740160225838926645076601)
          ·
            refine ⟨13305120169379194983807451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17740160225838926645076601 13305120169379194983807451)
            ·
              refine ⟨19957680254068792475711177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305120169379194983807451 19957680254068792475711177)
              ·
                refine ⟨14968260190551594356783383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19957680254068792475711177 14968260190551594356783383)
                ·
                  refine ⟨22452390285827391535175075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14968260190551594356783383 22452390285827391535175075)
                  ·
                    refine ⟨33678585428741087302762613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22452390285827391535175075 33678585428741087302762613)
                    ·
                      refine ⟨3157367383944476934633995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33678585428741087302762613 3157367383944476934633995)
                      ·
                        rfl

theorem cell23_6148951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_6148951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148951 prefixEnd_6148951 := by exact prefixLift 6148951
  have htrace : WordTrace (prefixWord ++ tailWord_6148951) baseStart_6148951 baseEnd_6148951 := by
    simpa [prefixWord, tailWord_6148951, baseEnd_6148951] using wordTrace_append hprefix tailTrace_6148951
  have hstable : (prefixWord ++ tailWord_6148951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148951).length < 2 ^ (prefixWord ++ tailWord_6148951).sum := by decide
  have hdescent : baseEnd_6148951 < baseStart_6148951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148968 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6148968 : Nat := 118140960795 + 6148968 * 2 ^ 59
def prefixEnd_6148968 : Nat := 4983230072969 + 3 ^ 40 * 6148968 * 2
def baseEnd_6148968 : Nat := 3157376113115603368121417

theorem tailTrace_6148968 : CollatzResearch.WordTrace tailWord_6148968 prefixEnd_6148968 3157376113115603368121417 := by
  unfold tailWord_6148968
  simp only [CollatzResearch.WordTrace]
  refine ⟨112135643793673285485995779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149514191724897713981327705 112135643793673285485995779)
  ·
    refine ⟨168203465690509928228993669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112135643793673285485995779 168203465690509928228993669)
    ·
      refine ⟨31538149816970611542936313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168203465690509928228993669 31538149816970611542936313)
      ·
        refine ⟨23653612362727958657202235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31538149816970611542936313 23653612362727958657202235)
        ·
          refine ⟨35480418544091937985803353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23653612362727958657202235 35480418544091937985803353)
          ·
            refine ⟨26610313908068953489352515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35480418544091937985803353 26610313908068953489352515)
            ·
              refine ⟨39915470862103430234028773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26610313908068953489352515 39915470862103430234028773)
              ·
                refine ⟨7484150786644393168880395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39915470862103430234028773 7484150786644393168880395)
                ·
                  refine ⟨11226226179966589753320593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484150786644393168880395 11226226179966589753320593)
                  ·
                    refine ⟨8419669634974942314990445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11226226179966589753320593 8419669634974942314990445)
                    ·
                      refine ⟨3157376113115603368121417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8419669634974942314990445 3157376113115603368121417)
                      ·
                        rfl

theorem cell23_6148968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6148968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148968 prefixEnd_6148968 := by exact prefixLift 6148968
  have htrace : WordTrace (prefixWord ++ tailWord_6148968) baseStart_6148968 baseEnd_6148968 := by
    simpa [prefixWord, tailWord_6148968, baseEnd_6148968] using wordTrace_append hprefix tailTrace_6148968
  have hstable : (prefixWord ++ tailWord_6148968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148968).length < 2 ^ (prefixWord ++ tailWord_6148968).sum := by decide
  have hdescent : baseEnd_6148968 < baseStart_6148968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6148999 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_6148999 : Nat := 118140960795 + 6148999 * 2 ^ 59
def prefixEnd_6148999 : Nat := 4983230072969 + 3 ^ 40 * 6148999 * 2
def baseEnd_6148999 : Nat := 3157392031015892746833775

theorem tailTrace_6148999 : CollatzResearch.WordTrace tailWord_6148999 prefixEnd_6148999 3157392031015892746833775 := by
  unfold tailWord_6148999
  simp only [CollatzResearch.WordTrace]
  refine ⟨224272418250234263266370051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149514945500156175510913367 224272418250234263266370051)
  ·
    refine ⟨336408627375351394899555077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224272418250234263266370051 336408627375351394899555077)
    ·
      refine ⟨63076617632878386543666577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336408627375351394899555077 63076617632878386543666577)
      ·
        refine ⟨47307463224658789907749933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63076617632878386543666577 47307463224658789907749933)
        ·
          refine ⟨17740298709247046215406225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47307463224658789907749933 17740298709247046215406225)
          ·
            refine ⟨13305224031935284661554669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17740298709247046215406225 13305224031935284661554669)
            ·
              refine ⟨4989459011975731748083001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13305224031935284661554669 4989459011975731748083001)
              ·
                refine ⟨3742094258981798811062251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4989459011975731748083001 3742094258981798811062251)
                ·
                  refine ⟨5613141388472698216593377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742094258981798811062251 5613141388472698216593377)
                  ·
                    refine ⟨4209856041354523662445033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5613141388472698216593377 4209856041354523662445033)
                    ·
                      refine ⟨3157392031015892746833775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209856041354523662445033 3157392031015892746833775)
                      ·
                        rfl

theorem cell23_6148999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_6148999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6148999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6148999 prefixEnd_6148999 := by exact prefixLift 6148999
  have htrace : WordTrace (prefixWord ++ tailWord_6148999) baseStart_6148999 baseEnd_6148999 := by
    simpa [prefixWord, tailWord_6148999, baseEnd_6148999] using wordTrace_append hprefix tailTrace_6148999
  have hstable : (prefixWord ++ tailWord_6148999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6148999).length < 2 ^ (prefixWord ++ tailWord_6148999).sum := by decide
  have hdescent : baseEnd_6148999 < baseStart_6148999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6148999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149025 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6149025 : Nat := 118140960795 + 6149025 * 2 ^ 59
def prefixEnd_6149025 : Nat := 4983230072969 + 3 ^ 40 * 6149025 * 2
def baseEnd_6149025 : Nat := 3157405381512909645108655

theorem tailTrace_6149025 : CollatzResearch.WordTrace tailWord_6149025 prefixEnd_6149025 3157405381512909645108655 := by
  unfold tailWord_6149025
  simp only [CollatzResearch.WordTrace]
  refine ⟨224273366548140069706816529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149515577698760046471211019 224273366548140069706816529)
  ·
    refine ⟨168205024911105052280112397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224273366548140069706816529 168205024911105052280112397)
    ·
      refine ⟨63076884341664394605042149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168205024911105052280112397 63076884341664394605042149)
      ·
        refine ⟨11826915814062073988445403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63076884341664394605042149 11826915814062073988445403)
        ·
          refine ⟨17740373721093110982668105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11826915814062073988445403 17740373721093110982668105)
          ·
            refine ⟨13305280290819833237001079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17740373721093110982668105 13305280290819833237001079)
            ·
              refine ⟨19957920436229749855501619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305280290819833237001079 19957920436229749855501619)
              ·
                refine ⟨29936880654344624783252429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19957920436229749855501619 29936880654344624783252429)
                ·
                  refine ⟨11226330245379234293719661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29936880654344624783252429 11226330245379234293719661)
                  ·
                    refine ⟨4209873842017212860144873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11226330245379234293719661 4209873842017212860144873)
                    ·
                      refine ⟨3157405381512909645108655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209873842017212860144873 3157405381512909645108655)
                      ·
                        rfl

theorem cell23_6149025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6149025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149025 prefixEnd_6149025 := by exact prefixLift 6149025
  have htrace : WordTrace (prefixWord ++ tailWord_6149025) baseStart_6149025 baseEnd_6149025 := by
    simpa [prefixWord, tailWord_6149025, baseEnd_6149025] using wordTrace_append hprefix tailTrace_6149025
  have hstable : (prefixWord ++ tailWord_6149025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149025).length < 2 ^ (prefixWord ++ tailWord_6149025).sum := by decide
  have hdescent : baseEnd_6149025 < baseStart_6149025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149071 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 3]
def baseStart_6149071 : Nat := 118140960795 + 6149071 * 2 ^ 59
def prefixEnd_6149071 : Nat := 4983230072969 + 3 ^ 40 * 6149071 * 2
def baseEnd_6149071 : Nat := 3157429001623016465133443

theorem tailTrace_6149071 : CollatzResearch.WordTrace tailWord_6149071 prefixEnd_6149071 3157429001623016465133443 := by
  unfold tailWord_6149071
  simp only [CollatzResearch.WordTrace]
  refine ⟨224275044305973419562991067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149516696203982279708660711 224275044305973419562991067)
  ·
    refine ⟨336412566458960129344486601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224275044305973419562991067 336412566458960129344486601)
    ·
      refine ⟨252309424844220097008364951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336412566458960129344486601 252309424844220097008364951)
      ·
        refine ⟨378464137266330145512547427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252309424844220097008364951 378464137266330145512547427)
        ·
          refine ⟨567696205899495218268821141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378464137266330145512547427 567696205899495218268821141)
          ·
            refine ⟨26610759651538838356350991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 567696205899495218268821141 26610759651538838356350991)
            ·
              refine ⟨39916139477308257534526487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26610759651538838356350991 39916139477308257534526487)
              ·
                refine ⟨59874209215962386301789731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39916139477308257534526487 59874209215962386301789731)
                ·
                  refine ⟨89811313823943579452684597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59874209215962386301789731 89811313823943579452684597)
                  ·
                    refine ⟨8419810670994710573689181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89811313823943579452684597 8419810670994710573689181)
                    ·
                      refine ⟨3157429001623016465133443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8419810670994710573689181 3157429001623016465133443)
                      ·
                        rfl

theorem cell23_6149071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 3].length) (baseStart_6149071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149071 prefixEnd_6149071 := by exact prefixLift 6149071
  have htrace : WordTrace (prefixWord ++ tailWord_6149071) baseStart_6149071 baseEnd_6149071 := by
    simpa [prefixWord, tailWord_6149071, baseEnd_6149071] using wordTrace_append hprefix tailTrace_6149071
  have hstable : (prefixWord ++ tailWord_6149071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149071).length < 2 ^ (prefixWord ++ tailWord_6149071).sum := by decide
  have hdescent : baseEnd_6149071 < baseStart_6149071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149078 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_6149078 : Nat := 118140960795 + 6149078 * 2 ^ 59
def prefixEnd_6149078 : Nat := 4983230072969 + 3 ^ 40 * 6149078 * 2
def baseEnd_6149078 : Nat := 350825843998621993082879

theorem tailTrace_6149078 : CollatzResearch.WordTrace tailWord_6149078 prefixEnd_6149078 350825843998621993082879 := by
  unfold tailWord_6149078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14017206226059253734905993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149516866411298706505663925 14017206226059253734905993)
  ·
    refine ⟨10512904669544440301179495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14017206226059253734905993 10512904669544440301179495)
    ·
      refine ⟨15769357004316660451769243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10512904669544440301179495 15769357004316660451769243)
      ·
        refine ⟨23654035506474990677653865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15769357004316660451769243 23654035506474990677653865)
        ·
          refine ⟨17740526629856243008240399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23654035506474990677653865 17740526629856243008240399)
          ·
            refine ⟨26610789944784364512360599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17740526629856243008240399 26610789944784364512360599)
            ·
              refine ⟨39916184917176546768540899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26610789944784364512360599 39916184917176546768540899)
              ·
                refine ⟨59874277375764820152811349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39916184917176546768540899 59874277375764820152811349)
                ·
                  refine ⟨350825843998621993082879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59874277375764820152811349 350825843998621993082879)
                  ·
                    rfl

theorem cell23_6149078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_6149078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149078 prefixEnd_6149078 := by exact prefixLift 6149078
  have htrace : WordTrace (prefixWord ++ tailWord_6149078) baseStart_6149078 baseEnd_6149078 := by
    simpa [prefixWord, tailWord_6149078, baseEnd_6149078] using wordTrace_append hprefix tailTrace_6149078
  have hstable : (prefixWord ++ tailWord_6149078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149078).length < 2 ^ (prefixWord ++ tailWord_6149078).sum := by decide
  have hdescent : baseEnd_6149078 < baseStart_6149078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149091 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 1, 7]
def baseStart_6149091 : Nat := 118140960795 + 6149091 * 2 ^ 59
def prefixEnd_6149091 : Nat := 4983230072969 + 3 ^ 40 * 6149091 * 2
def baseEnd_6149091 : Nat := 1052479757078702128961117

theorem tailTrace_6149091 : CollatzResearch.WordTrace tailWord_6149091 prefixEnd_6149091 1052479757078702128961117 := by
  unfold tailWord_6149091
  simp only [CollatzResearch.WordTrace]
  refine ⟨224275773765900962978719127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149517182510600641985812751 224275773765900962978719127)
  ·
    refine ⟨336413660648851444468078691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224275773765900962978719127 336413660648851444468078691)
    ·
      refine ⟨504620490973277166702118037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336413660648851444468078691 504620490973277166702118037)
      ·
        refine ⟨23654085514372367189161783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 504620490973277166702118037 23654085514372367189161783)
        ·
          refine ⟨35481128271558550783742675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23654085514372367189161783 35481128271558550783742675)
          ·
            refine ⟨53221692407337826175614013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35481128271558550783742675 53221692407337826175614013)
            ·
              refine ⟨19958134652751684815855255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53221692407337826175614013 19958134652751684815855255)
              ·
                refine ⟨29937201979127527223782883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19958134652751684815855255 29937201979127527223782883)
                ·
                  refine ⟨44905802968691290835674325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29937201979127527223782883 44905802968691290835674325)
                  ·
                    refine ⟨1052479757078702128961117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44905802968691290835674325 1052479757078702128961117)
                    ·
                      rfl

theorem cell23_6149091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 7].length) (baseStart_6149091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149091 prefixEnd_6149091 := by exact prefixLift 6149091
  have htrace : WordTrace (prefixWord ++ tailWord_6149091) baseStart_6149091 baseEnd_6149091 := by
    simpa [prefixWord, tailWord_6149091, baseEnd_6149091] using wordTrace_append hprefix tailTrace_6149091
  have hstable : (prefixWord ++ tailWord_6149091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149091).length < 2 ^ (prefixWord ++ tailWord_6149091).sum := by decide
  have hdescent : baseEnd_6149091 < baseStart_6149091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149095 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 5]
def baseStart_6149095 : Nat := 118140960795 + 6149095 * 2 ^ 59
def prefixEnd_6149095 : Nat := 4983230072969 + 3 ^ 40 * 6149095 * 2
def baseEnd_6149095 : Nat := 350826813906524930137037

theorem tailTrace_6149095 : CollatzResearch.WordTrace tailWord_6149095 prefixEnd_6149095 350826813906524930137037 := by
  unfold tailWord_6149095
  simp only [CollatzResearch.WordTrace]
  refine ⟨224275919657886471661864739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149517279771924314441243159 224275919657886471661864739)
  ·
    refine ⟨336413879486829707492797109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224275919657886471661864739 336413879486829707492797109)
    ·
      refine ⟨31538801201890285077449729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336413879486829707492797109 31538801201890285077449729)
      ·
        refine ⟨23654100901417713808087297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31538801201890285077449729 23654100901417713808087297)
        ·
          refine ⟨17740575676063285356065473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23654100901417713808087297 17740575676063285356065473)
          ·
            refine ⟨13305431757047464017049105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17740575676063285356065473 13305431757047464017049105)
            ·
              refine ⟨9979073817785598012786829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13305431757047464017049105 9979073817785598012786829)
              ·
                refine ⟨3742152681669599254795061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9979073817785598012786829 3742152681669599254795061)
                ·
                  refine ⟨350826813906524930137037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3742152681669599254795061 350826813906524930137037)
                  ·
                    rfl

theorem cell23_6149095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 5].length) (baseStart_6149095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149095 prefixEnd_6149095 := by exact prefixLift 6149095
  have htrace : WordTrace (prefixWord ++ tailWord_6149095) baseStart_6149095 baseEnd_6149095 := by
    simpa [prefixWord, tailWord_6149095, baseEnd_6149095] using wordTrace_append hprefix tailTrace_6149095
  have hstable : (prefixWord ++ tailWord_6149095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149095).length < 2 ^ (prefixWord ++ tailWord_6149095).sum := by decide
  have hdescent : baseEnd_6149095 < baseStart_6149095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149106 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6149106 : Nat := 118140960795 + 6149106 * 2 ^ 59
def prefixEnd_6149106 : Nat := 4983230072969 + 3 ^ 40 * 6149106 * 2
def baseEnd_6149106 : Nat := 3157446973445923828195783

theorem tailTrace_6149106 : CollatzResearch.WordTrace tailWord_6149106 prefixEnd_6149106 3157446973445923828195783 := by
  unfold tailWord_6149106
  simp only [CollatzResearch.WordTrace]
  refine ⟨56069080215211655135128793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149517547240564413693676781 56069080215211655135128793)
  ·
    refine ⟨42051810161408741351346595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56069080215211655135128793 42051810161408741351346595)
    ·
      refine ⟨63077715242113112027019893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42051810161408741351346595 63077715242113112027019893)
      ·
        refine ⟨5913535803948104252533115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63077715242113112027019893 5913535803948104252533115)
        ·
          refine ⟨8870303705922156378799673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5913535803948104252533115 8870303705922156378799673)
          ·
            refine ⟨6652727779441617284099755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8870303705922156378799673 6652727779441617284099755)
            ·
              refine ⟨9979091669162425926149633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652727779441617284099755 9979091669162425926149633)
              ·
                refine ⟨7484318751871819444612225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9979091669162425926149633 7484318751871819444612225)
                ·
                  refine ⟨5613239063903864583459169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7484318751871819444612225 5613239063903864583459169)
                  ·
                    refine ⟨4209929297927898437594377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5613239063903864583459169 4209929297927898437594377)
                    ·
                      refine ⟨3157446973445923828195783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4209929297927898437594377 3157446973445923828195783)
                      ·
                        rfl

theorem cell23_6149106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6149106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149106 prefixEnd_6149106 := by exact prefixLift 6149106
  have htrace : WordTrace (prefixWord ++ tailWord_6149106) baseStart_6149106 baseEnd_6149106 := by
    simpa [prefixWord, tailWord_6149106, baseEnd_6149106] using wordTrace_append hprefix tailTrace_6149106
  have hstable : (prefixWord ++ tailWord_6149106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149106).length < 2 ^ (prefixWord ++ tailWord_6149106).sum := by decide
  have hdescent : baseEnd_6149106 < baseStart_6149106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149151 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 8]
def baseStart_6149151 : Nat := 118140960795 + 6149151 * 2 ^ 59
def prefixEnd_6149151 : Nat := 4983230072969 + 3 ^ 40 * 6149151 * 2
def baseEnd_6149151 : Nat := 350830008897264016903675

theorem tailTrace_6149151 : CollatzResearch.WordTrace tailWord_6149151 prefixEnd_6149151 350830008897264016903675 := by
  unfold tailWord_6149151
  simp only [CollatzResearch.WordTrace]
  refine ⟨224277962145683593225903307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149518641430455728817268871 224277962145683593225903307)
  ·
    refine ⟨336416943218525389838854961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224277962145683593225903307 336416943218525389838854961)
    ·
      refine ⟨252312707413894042379141221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336416943218525389838854961 252312707413894042379141221)
      ·
        refine ⟨47308632640105132946088979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252312707413894042379141221 47308632640105132946088979)
        ·
          refine ⟨70962948960157699419133469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47308632640105132946088979 70962948960157699419133469)
          ·
            refine ⟨26611105860059137282175051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70962948960157699419133469 26611105860059137282175051)
            ·
              refine ⟨39916658790088705923262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26611105860059137282175051 39916658790088705923262577)
              ·
                refine ⟨29937494092566529442446933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39916658790088705923262577 29937494092566529442446933)
                ·
                  refine ⟨350830008897264016903675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29937494092566529442446933 350830008897264016903675)
                  ·
                    rfl

theorem cell23_6149151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 8].length) (baseStart_6149151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149151 prefixEnd_6149151 := by exact prefixLift 6149151
  have htrace : WordTrace (prefixWord ++ tailWord_6149151) baseStart_6149151 baseEnd_6149151 := by
    simpa [prefixWord, tailWord_6149151, baseEnd_6149151] using wordTrace_append hprefix tailTrace_6149151
  have hstable : (prefixWord ++ tailWord_6149151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149151).length < 2 ^ (prefixWord ++ tailWord_6149151).sum := by decide
  have hdescent : baseEnd_6149151 < baseStart_6149151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149172 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_6149172 : Nat := 118140960795 + 6149172 * 2 ^ 59
def prefixEnd_6149172 : Nat := 4983230072969 + 3 ^ 40 * 6149172 * 2
def baseEnd_6149172 : Nat := 1052493621056373523323493

theorem tailTrace_6149172 : CollatzResearch.WordTrace tailWord_6149172 prefixEnd_6149172 1052493621056373523323493 := by
  unfold tailWord_6149172
  simp only [CollatzResearch.WordTrace]
  refine ⟨112139364039303756906208885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149519152052405009208278513 112139364039303756906208885)
  ·
    refine ⟨10513065378684727209957083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112139364039303756906208885 10513065378684727209957083)
    ·
      refine ⟨15769598068027090814935625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10513065378684727209957083 15769598068027090814935625)
      ·
        refine ⟨11827198551020318111201719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15769598068027090814935625 11827198551020318111201719)
        ·
          refine ⟨17740797826530477166802579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11827198551020318111201719 17740797826530477166802579)
          ·
            refine ⟨26611196739795715750203869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17740797826530477166802579 26611196739795715750203869)
            ·
              refine ⟨9979198777423393406326451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26611196739795715750203869 9979198777423393406326451)
              ·
                refine ⟨14968798166135090109489677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9979198777423393406326451 14968798166135090109489677)
                ·
                  refine ⟨5613299312300658791058629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14968798166135090109489677 5613299312300658791058629)
                  ·
                    refine ⟨1052493621056373523323493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613299312300658791058629 1052493621056373523323493)
                    ·
                      rfl

theorem cell23_6149172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_6149172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149172 prefixEnd_6149172 := by exact prefixLift 6149172
  have htrace : WordTrace (prefixWord ++ tailWord_6149172) baseStart_6149172 baseEnd_6149172 := by
    simpa [prefixWord, tailWord_6149172, baseEnd_6149172] using wordTrace_append hprefix tailTrace_6149172
  have hstable : (prefixWord ++ tailWord_6149172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149172).length < 2 ^ (prefixWord ++ tailWord_6149172).sum := by decide
  have hdescent : baseEnd_6149172 < baseStart_6149172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149185 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 6]
def baseStart_6149185 : Nat := 118140960795 + 6149185 * 2 ^ 59
def prefixEnd_6149185 : Nat := 4983230072969 + 3 ^ 40 * 6149185 * 2
def baseEnd_6149185 : Nat := 350831948713069891011991

theorem tailTrace_6149185 : CollatzResearch.WordTrace tailWord_6149185 prefixEnd_6149185 350831948713069891011991 := by
  unfold tailWord_6149185
  simp only [CollatzResearch.WordTrace]
  refine ⟨224279202227560417032641009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149519468151706944688427339 224279202227560417032641009)
  ·
    refine ⟨168209401670670312774480757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224279202227560417032641009 168209401670670312774480757)
    ·
      refine ⟨15769631406625341822607571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168209401670670312774480757 15769631406625341822607571)
      ·
        refine ⟨23654447109938012733911357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15769631406625341822607571 23654447109938012733911357)
        ·
          refine ⟨8870417666226754775216759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23654447109938012733911357 8870417666226754775216759)
          ·
            refine ⟨13305626499340132162825139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8870417666226754775216759 13305626499340132162825139)
            ·
              refine ⟨19958439749010198244237709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305626499340132162825139 19958439749010198244237709)
              ·
                refine ⟨7484414905878824341589141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19958439749010198244237709 7484414905878824341589141)
                ·
                  refine ⟨350831948713069891011991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7484414905878824341589141 350831948713069891011991)
                  ·
                    rfl

theorem cell23_6149185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 6].length) (baseStart_6149185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149185 prefixEnd_6149185 := by exact prefixLift 6149185
  have htrace : WordTrace (prefixWord ++ tailWord_6149185) baseStart_6149185 baseEnd_6149185 := by
    simpa [prefixWord, tailWord_6149185, baseEnd_6149185] using wordTrace_append hprefix tailTrace_6149185
  have hstable : (prefixWord ++ tailWord_6149185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149185).length < 2 ^ (prefixWord ++ tailWord_6149185).sum := by decide
  have hdescent : baseEnd_6149185 < baseStart_6149185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149198 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_6149198 : Nat := 118140960795 + 6149198 * 2 ^ 59
def prefixEnd_6149198 : Nat := 4983230072969 + 3 ^ 40 * 6149198 * 2
def baseEnd_6149198 : Nat := 1052498071222045822748453

theorem tailTrace_6149198 : CollatzResearch.WordTrace tailWord_6149198 prefixEnd_6149198 1052498071222045822748453 := by
  unfold tailWord_6149198
  simp only [CollatzResearch.WordTrace]
  refine ⟨28034959547064165031608031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149519784251008880168576165 28034959547064165031608031)
  ·
    refine ⟨42052439320596247547412047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28034959547064165031608031 42052439320596247547412047)
    ·
      refine ⟨63078658980894371321118071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42052439320596247547412047 63078658980894371321118071)
      ·
        refine ⟨94617988471341556981677107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63078658980894371321118071 94617988471341556981677107)
        ·
          refine ⟨141926982707012335472515661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94617988471341556981677107 141926982707012335472515661)
          ·
            refine ⟨53222618515129625802193373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141926982707012335472515661 53222618515129625802193373)
            ·
              refine ⟨19958481943173609675822515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53222618515129625802193373 19958481943173609675822515)
              ·
                refine ⟨29937722914760414513733773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19958481943173609675822515 29937722914760414513733773)
                ·
                  refine ⟨11226646093035155442650165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29937722914760414513733773 11226646093035155442650165)
                  ·
                    refine ⟨1052498071222045822748453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11226646093035155442650165 1052498071222045822748453)
                    ·
                      rfl

theorem cell23_6149198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_6149198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149198 prefixEnd_6149198 := by exact prefixLift 6149198
  have htrace : WordTrace (prefixWord ++ tailWord_6149198) baseStart_6149198 baseEnd_6149198 := by
    simpa [prefixWord, tailWord_6149198, baseEnd_6149198] using wordTrace_append hprefix tailTrace_6149198
  have hstable : (prefixWord ++ tailWord_6149198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149198).length < 2 ^ (prefixWord ++ tailWord_6149198).sum := by decide
  have hdescent : baseEnd_6149198 < baseStart_6149198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149215 : List Nat := [1, 1, 2, 3, 1, 1, 7, 1, 1, 5]
def baseStart_6149215 : Nat := 118140960795 + 6149215 * 2 ^ 59
def prefixEnd_6149215 : Nat := 4983230072969 + 3 ^ 40 * 6149215 * 2
def baseEnd_6149215 : Nat := 1052500980945754633910927

theorem tailTrace_6149215 : CollatzResearch.WordTrace tailWord_6149215 prefixEnd_6149215 1052500980945754633910927 := by
  unfold tailWord_6149215
  simp only [CollatzResearch.WordTrace]
  refine ⟨224280296417451732156233099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149520197611634488104155399 224280296417451732156233099)
  ·
    refine ⟨336420444626177598234349649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224280296417451732156233099 336420444626177598234349649)
    ·
      refine ⟨252315333469633198675762237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336420444626177598234349649 252315333469633198675762237)
      ·
        refine ⟨94618250051112449503410839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252315333469633198675762237 94618250051112449503410839)
        ·
          refine ⟨141927375076668674255116259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94618250051112449503410839 141927375076668674255116259)
          ·
            refine ⟨212891062615003011382674389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141927375076668674255116259 212891062615003011382674389)
            ·
              refine ⟨4989634280039133079281431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212891062615003011382674389 4989634280039133079281431)
              ·
                refine ⟨7484451420058699618922147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989634280039133079281431 7484451420058699618922147)
                ·
                  refine ⟨11226677130088049428383221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484451420058699618922147 11226677130088049428383221)
                  ·
                    refine ⟨1052500980945754633910927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11226677130088049428383221 1052500980945754633910927)
                    ·
                      rfl

theorem cell23_6149215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 1, 1, 5].length) (baseStart_6149215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149215 prefixEnd_6149215 := by exact prefixLift 6149215
  have htrace : WordTrace (prefixWord ++ tailWord_6149215) baseStart_6149215 baseEnd_6149215 := by
    simpa [prefixWord, tailWord_6149215, baseEnd_6149215] using wordTrace_append hprefix tailTrace_6149215
  have hstable : (prefixWord ++ tailWord_6149215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149215).length < 2 ^ (prefixWord ++ tailWord_6149215).sum := by decide
  have hdescent : baseEnd_6149215 < baseStart_6149215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149229 : List Nat := [1, 5, 1, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6149229 : Nat := 118140960795 + 6149229 * 2 ^ 59
def prefixEnd_6149229 : Nat := 4983230072969 + 3 ^ 40 * 6149229 * 2
def baseEnd_6149229 : Nat := 3157510131566426846957717

theorem tailTrace_6149229 : CollatzResearch.WordTrace tailWord_6149229 prefixEnd_6149229 3157510131566426846957717 := by
  unfold tailWord_6149229
  simp only [CollatzResearch.WordTrace]
  refine ⟨224280807039401012547242741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149520538026267341698161827 224280807039401012547242741)
  ·
    refine ⟨21026325659943844926304007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224280807039401012547242741 21026325659943844926304007)
    ·
      refine ⟨31539488489915767389456011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21026325659943844926304007 31539488489915767389456011)
      ·
        refine ⟨47309232734873651084184017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31539488489915767389456011 47309232734873651084184017)
        ·
          refine ⟨35481924551155238313138013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47309232734873651084184017 35481924551155238313138013)
          ·
            refine ⟨13305721706683214367426755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35481924551155238313138013 13305721706683214367426755)
            ·
              refine ⟨19958582560024821551140133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305721706683214367426755 19958582560024821551140133)
              ·
                refine ⟨3742234230004654040838775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19958582560024821551140133 3742234230004654040838775)
                ·
                  refine ⟨5613351345006981061258163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742234230004654040838775 5613351345006981061258163)
                  ·
                    refine ⟨8420027017510471591887245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5613351345006981061258163 8420027017510471591887245)
                    ·
                      refine ⟨3157510131566426846957717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8420027017510471591887245 3157510131566426846957717)
                      ·
                        rfl

theorem cell23_6149229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6149229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149229 prefixEnd_6149229 := by exact prefixLift 6149229
  have htrace : WordTrace (prefixWord ++ tailWord_6149229) baseStart_6149229 baseEnd_6149229 := by
    simpa [prefixWord, tailWord_6149229, baseEnd_6149229] using wordTrace_append hprefix tailTrace_6149229
  have hstable : (prefixWord ++ tailWord_6149229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149229).length < 2 ^ (prefixWord ++ tailWord_6149229).sum := by decide
  have hdescent : baseEnd_6149229 < baseStart_6149229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149235 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 9, 2, 2]
def baseStart_6149235 : Nat := 118140960795 + 6149235 * 2 ^ 59
def prefixEnd_6149235 : Nat := 4983230072969 + 3 ^ 40 * 6149235 * 2
def baseEnd_6149235 : Nat := 3157513212450353823482689

theorem tailTrace_6149235 : CollatzResearch.WordTrace tailWord_6149235 prefixEnd_6149235 3157513212450353823482689 := by
  unfold tailWord_6149235
  simp only [CollatzResearch.WordTrace]
  refine ⟨224281025877379275571961159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149520683918252850381307439 224281025877379275571961159)
  ·
    refine ⟨336421538816068913357941739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224281025877379275571961159 336421538816068913357941739)
    ·
      refine ⟨504632308224103370036912609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336421538816068913357941739 504632308224103370036912609)
      ·
        refine ⟨378474231168077527527684457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504632308224103370036912609 378474231168077527527684457)
        ·
          refine ⟨283855673376058145645763343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378474231168077527527684457 283855673376058145645763343)
          ·
            refine ⟨425783510064087218468645015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283855673376058145645763343 425783510064087218468645015)
            ·
              refine ⟨638675265096130827702967523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425783510064087218468645015 638675265096130827702967523)
              ·
                refine ⟨958012897644196241554451285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638675265096130827702967523 958012897644196241554451285)
                ·
                  refine ⟨5613356822133962352858113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 958012897644196241554451285 5613356822133962352858113)
                  ·
                    refine ⟨4210017616600471764643585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5613356822133962352858113 4210017616600471764643585)
                    ·
                      refine ⟨3157513212450353823482689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210017616600471764643585 3157513212450353823482689)
                      ·
                        rfl

theorem cell23_6149235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 2, 2].length) (baseStart_6149235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149235 prefixEnd_6149235 := by exact prefixLift 6149235
  have htrace : WordTrace (prefixWord ++ tailWord_6149235) baseStart_6149235 baseEnd_6149235 := by
    simpa [prefixWord, tailWord_6149235, baseEnd_6149235] using wordTrace_append hprefix tailTrace_6149235
  have hstable : (prefixWord ++ tailWord_6149235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149235).length < 2 ^ (prefixWord ++ tailWord_6149235).sum := by decide
  have hdescent : baseEnd_6149235 < baseStart_6149235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149245 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_6149245 : Nat := 118140960795 + 6149245 * 2 ^ 59
def prefixEnd_6149245 : Nat := 4983230072969 + 3 ^ 40 * 6149245 * 2
def baseEnd_6149245 : Nat := 1052506115752299594785881

theorem tailTrace_6149245 : CollatzResearch.WordTrace tailWord_6149245 prefixEnd_6149245 1052506115752299594785881 := by
  unfold tailWord_6149245
  simp only [CollatzResearch.WordTrace]
  refine ⟨224281390607343047279825189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149520927071562031519883459 224281390607343047279825189)
  ·
    refine ⟨42052760738876821364967223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224281390607343047279825189 42052760738876821364967223)
    ·
      refine ⟨63079141108315232047450835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42052760738876821364967223 63079141108315232047450835)
      ·
        refine ⟨94618711662472848071176253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63079141108315232047450835 94618711662472848071176253)
        ·
          refine ⟨35482016873427318026691095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94618711662472848071176253 35482016873427318026691095)
          ·
            refine ⟨53223025310140977040036643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35482016873427318026691095 53223025310140977040036643)
            ·
              refine ⟨79834537965211465560054965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53223025310140977040036643 79834537965211465560054965)
              ·
                refine ⟨7484487934238574896255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79834537965211465560054965 7484487934238574896255153)
                ·
                  refine ⟨5613365950678931172191365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7484487934238574896255153 5613365950678931172191365)
                  ·
                    refine ⟨1052506115752299594785881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613365950678931172191365 1052506115752299594785881)
                    ·
                      rfl

theorem cell23_6149245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_6149245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149245 prefixEnd_6149245 := by exact prefixLift 6149245
  have htrace : WordTrace (prefixWord ++ tailWord_6149245) baseStart_6149245 baseEnd_6149245 := by
    simpa [prefixWord, tailWord_6149245, baseEnd_6149245] using wordTrace_append hprefix tailTrace_6149245
  have hstable : (prefixWord ++ tailWord_6149245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149245).length < 2 ^ (prefixWord ++ tailWord_6149245).sum := by decide
  have hdescent : baseEnd_6149245 < baseStart_6149245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149248 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4]
def baseStart_6149248 : Nat := 118140960795 + 6149248 * 2 ^ 59
def prefixEnd_6149248 : Nat := 4983230072969 + 3 ^ 40 * 6149248 * 2
def baseEnd_6149248 : Nat := 3157519887698862272620129

theorem tailTrace_6149248 : CollatzResearch.WordTrace tailWord_6149248 prefixEnd_6149248 3157519887698862272620129 := by
  unfold tailWord_6149248
  simp only [CollatzResearch.WordTrace]
  refine ⟨112140750013166089396092199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149521000017554785861456265 112140750013166089396092199)
  ·
    refine ⟨168211125019749134094138299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112140750013166089396092199 168211125019749134094138299)
    ·
      refine ⟨252316687529623701141207449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168211125019749134094138299 252316687529623701141207449)
      ·
        refine ⟨189237515647217775855905587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252316687529623701141207449 189237515647217775855905587)
        ·
          refine ⟨283856273470826663783858381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189237515647217775855905587 283856273470826663783858381)
          ·
            refine ⟨106446102551559998918946893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283856273470826663783858381 106446102551559998918946893)
            ·
              refine ⟨39917288456834999594605085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106446102551559998918946893 39917288456834999594605085)
              ·
                refine ⟨14968983171313124847976907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39917288456834999594605085 14968983171313124847976907)
                ·
                  refine ⟨22453474756969687271965361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14968983171313124847976907 22453474756969687271965361)
                  ·
                    refine ⟨16840106067727265453974021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22453474756969687271965361 16840106067727265453974021)
                    ·
                      refine ⟨3157519887698862272620129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16840106067727265453974021 3157519887698862272620129)
                      ·
                        rfl

theorem cell23_6149248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_6149248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149248 prefixEnd_6149248 := by exact prefixLift 6149248
  have htrace : WordTrace (prefixWord ++ tailWord_6149248) baseStart_6149248 baseEnd_6149248 := by
    simpa [prefixWord, tailWord_6149248, baseEnd_6149248] using wordTrace_append hprefix tailTrace_6149248
  have hstable : (prefixWord ++ tailWord_6149248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149248).length < 2 ^ (prefixWord ++ tailWord_6149248).sum := by decide
  have hdescent : baseEnd_6149248 < baseStart_6149248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149252 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 5, 2, 2]
def baseStart_6149252 : Nat := 118140960795 + 6149252 * 2 ^ 59
def prefixEnd_6149252 : Nat := 4983230072969 + 3 ^ 40 * 6149252 * 2
def baseEnd_6149252 : Nat := 3157521941621480256970111

theorem tailTrace_6149252 : CollatzResearch.WordTrace tailWord_6149252 prefixEnd_6149252 3157521941621480256970111 := by
  unfold tailWord_6149252
  simp only [CollatzResearch.WordTrace]
  refine ⟨112140822959158843737665005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149521097278878458316886673 112140822959158843737665005)
  ·
    refine ⟨42052808609684566401624377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112140822959158843737665005 42052808609684566401624377)
    ·
      refine ⟨31539606457263424801218283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42052808609684566401624377 31539606457263424801218283)
      ·
        refine ⟨47309409685895137201827425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31539606457263424801218283 47309409685895137201827425)
        ·
          refine ⟨35482057264421352901370569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47309409685895137201827425 35482057264421352901370569)
          ·
            refine ⟨26611542948316014676027927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35482057264421352901370569 26611542948316014676027927)
            ·
              refine ⟨39917314422474022014041891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26611542948316014676027927 39917314422474022014041891)
              ·
                refine ⟨59875971633711033021062837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39917314422474022014041891 59875971633711033021062837)
                ·
                  refine ⟨5613372340660409345724641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59875971633711033021062837 5613372340660409345724641)
                  ·
                    refine ⟨4210029255495307009293481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5613372340660409345724641 4210029255495307009293481)
                    ·
                      refine ⟨3157521941621480256970111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210029255495307009293481 3157521941621480256970111)
                      ·
                        rfl

theorem cell23_6149252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_6149252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149252 prefixEnd_6149252 := by exact prefixLift 6149252
  have htrace : WordTrace (prefixWord ++ tailWord_6149252) baseStart_6149252 baseEnd_6149252 := by
    simpa [prefixWord, tailWord_6149252, baseEnd_6149252] using wordTrace_append hprefix tailTrace_6149252
  have hstable : (prefixWord ++ tailWord_6149252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149252).length < 2 ^ (prefixWord ++ tailWord_6149252).sum := by decide
  have hdescent : baseEnd_6149252 < baseStart_6149252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149255 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_6149255 : Nat := 118140960795 + 6149255 * 2 ^ 59
def prefixEnd_6149255 : Nat := 4983230072969 + 3 ^ 40 * 6149255 * 2
def baseEnd_6149255 : Nat := 3157523482063443745232597

theorem tailTrace_6149255 : CollatzResearch.WordTrace tailWord_6149255 prefixEnd_6149255 3157523482063443745232597 := by
  unfold tailWord_6149255
  simp only [CollatzResearch.WordTrace]
  refine ⟨224281755337306818987689219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149521170224871212658459479 224281755337306818987689219)
  ·
    refine ⟨336422633005960228481533829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224281755337306818987689219 336422633005960228481533829)
    ·
      refine ⟨63079243688617542840287593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336422633005960228481533829 63079243688617542840287593)
      ·
        refine ⟨47309432766463157130215695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63079243688617542840287593 47309432766463157130215695)
        ·
          refine ⟨70964149149694735695323543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47309432766463157130215695 70964149149694735695323543)
          ·
            refine ⟨106446223724542103542985315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70964149149694735695323543 106446223724542103542985315)
            ·
              refine ⟨159669335586813155314477973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106446223724542103542985315 159669335586813155314477973)
              ·
                refine ⟨7484500105631866655366155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159669335586813155314477973 7484500105631866655366155)
                ·
                  refine ⟨11226750158447799983049233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484500105631866655366155 11226750158447799983049233)
                  ·
                    refine ⟨8420062618835849987286925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11226750158447799983049233 8420062618835849987286925)
                    ·
                      refine ⟨3157523482063443745232597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8420062618835849987286925 3157523482063443745232597)
                      ·
                        rfl

theorem cell23_6149255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_6149255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149255 prefixEnd_6149255 := by exact prefixLift 6149255
  have htrace : WordTrace (prefixWord ++ tailWord_6149255) baseStart_6149255 baseEnd_6149255 := by
    simpa [prefixWord, tailWord_6149255, baseEnd_6149255] using wordTrace_append hprefix tailTrace_6149255
  have hstable : (prefixWord ++ tailWord_6149255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149255).length < 2 ^ (prefixWord ++ tailWord_6149255).sum := by decide
  have hdescent : baseEnd_6149255 < baseStart_6149255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149256 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6149256 : Nat := 118140960795 + 6149256 * 2 ^ 59
def prefixEnd_6149256 : Nat := 4983230072969 + 3 ^ 40 * 6149256 * 2
def baseEnd_6149256 : Nat := 3157523995544098241320093

theorem tailTrace_6149256 : CollatzResearch.WordTrace tailWord_6149256 prefixEnd_6149256 3157523995544098241320093 := by
  unfold tailWord_6149256
  simp only [CollatzResearch.WordTrace]
  refine ⟨112140895905151598079237811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149521194540202130772317081 112140895905151598079237811)
  ·
    refine ⟨168211343857727397118856717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112140895905151598079237811 168211343857727397118856717)
    ·
      refine ⟨63079253946647773919571269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168211343857727397118856717 63079253946647773919571269)
      ·
        refine ⟨11827360114996457609919613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63079253946647773919571269 11827360114996457609919613)
        ·
          refine ⟨4435260043123671603719855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11827360114996457609919613 4435260043123671603719855)
          ·
            refine ⟨6652890064685507405579783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435260043123671603719855 6652890064685507405579783)
            ·
              refine ⟨9979335097028261108369675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652890064685507405579783 9979335097028261108369675)
              ·
                refine ⟨14969002645542391662554513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9979335097028261108369675 14969002645542391662554513)
                ·
                  refine ⟨11226751984156793746915885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14969002645542391662554513 11226751984156793746915885)
                  ·
                    refine ⟨4210031994058797655093457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11226751984156793746915885 4210031994058797655093457)
                    ·
                      refine ⟨3157523995544098241320093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210031994058797655093457 3157523995544098241320093)
                      ·
                        rfl

theorem cell23_6149256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6149256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149256 prefixEnd_6149256 := by exact prefixLift 6149256
  have htrace : WordTrace (prefixWord ++ tailWord_6149256) baseStart_6149256 baseEnd_6149256 := by
    simpa [prefixWord, tailWord_6149256, baseEnd_6149256] using wordTrace_append hprefix tailTrace_6149256
  have hstable : (prefixWord ++ tailWord_6149256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149256).length < 2 ^ (prefixWord ++ tailWord_6149256).sum := by decide
  have hdescent : baseEnd_6149256 < baseStart_6149256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149272 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6149272 : Nat := 118140960795 + 6149272 * 2 ^ 59
def prefixEnd_6149272 : Nat := 4983230072969 + 3 ^ 40 * 6149272 * 2
def baseEnd_6149272 : Nat := 3157532211234570178720019

theorem tailTrace_6149272 : CollatzResearch.WordTrace tailWord_6149272 prefixEnd_6149272 3157532211234570178720019 := by
  unfold tailWord_6149272
  simp only [CollatzResearch.WordTrace]
  refine ⟨112141187689122615445529035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149521583585496820594038713 112141187689122615445529035)
  ·
    refine ⟨168211781533683923168293553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112141187689122615445529035 168211781533683923168293553)
    ·
      refine ⟨126158836150262942376220165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168211781533683923168293553 126158836150262942376220165)
      ·
        refine ⟨23654781778174301695541281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126158836150262942376220165 23654781778174301695541281)
        ·
          refine ⟨17741086333630726271655961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23654781778174301695541281 17741086333630726271655961)
          ·
            refine ⟨13305814750223044703741971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17741086333630726271655961 13305814750223044703741971)
            ·
              refine ⟨19958722125334567055612957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13305814750223044703741971 19958722125334567055612957)
              ·
                refine ⟨7484520797000462645854859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19958722125334567055612957 7484520797000462645854859)
                ·
                  refine ⟨11226781195500693968782289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484520797000462645854859 11226781195500693968782289)
                  ·
                    refine ⟨8420085896625520476586717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11226781195500693968782289 8420085896625520476586717)
                    ·
                      refine ⟨3157532211234570178720019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8420085896625520476586717 3157532211234570178720019)
                      ·
                        rfl

theorem cell23_6149272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6149272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149272 prefixEnd_6149272 := by exact prefixLift 6149272
  have htrace : WordTrace (prefixWord ++ tailWord_6149272) baseStart_6149272 baseEnd_6149272 := by
    simpa [prefixWord, tailWord_6149272, baseEnd_6149272] using wordTrace_append hprefix tailTrace_6149272
  have hstable : (prefixWord ++ tailWord_6149272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149272).length < 2 ^ (prefixWord ++ tailWord_6149272).sum := by decide
  have hdescent : baseEnd_6149272 < baseStart_6149272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149279 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 2, 4]
def baseStart_6149279 : Nat := 118140960795 + 6149279 * 2 ^ 59
def prefixEnd_6149279 : Nat := 4983230072969 + 3 ^ 40 * 6149279 * 2
def baseEnd_6149279 : Nat := 1052511935199717217110829

theorem tailTrace_6149279 : CollatzResearch.WordTrace tailWord_6149279 prefixEnd_6149279 1052511935199717217110829 := by
  unfold tailWord_6149279
  simp only [CollatzResearch.WordTrace]
  refine ⟨224282630689219871086562891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149521753792813247391041927 224282630689219871086562891)
  ·
    refine ⟨336423946033829806629844337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224282630689219871086562891 336423946033829806629844337)
    ·
      refine ⟨252317959525372354972383253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336423946033829806629844337 252317959525372354972383253)
      ·
        refine ⟨11827404352751829139330465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 252317959525372354972383253 11827404352751829139330465)
        ·
          refine ⟨8870553264563871854497849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11827404352751829139330465 8870553264563871854497849)
          ·
            refine ⟨6652914948422903890873387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8870553264563871854497849 6652914948422903890873387)
            ·
              refine ⟨9979372422634355836310081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652914948422903890873387 9979372422634355836310081)
              ·
                refine ⟨7484529316975766877232561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9979372422634355836310081 7484529316975766877232561)
                ·
                  refine ⟨5613396987731825157924421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7484529316975766877232561 5613396987731825157924421)
                  ·
                    refine ⟨1052511935199717217110829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613396987731825157924421 1052511935199717217110829)
                    ·
                      rfl

theorem cell23_6149279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_6149279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149279 prefixEnd_6149279 := by exact prefixLift 6149279
  have htrace : WordTrace (prefixWord ++ tailWord_6149279) baseStart_6149279 baseEnd_6149279 := by
    simpa [prefixWord, tailWord_6149279, baseEnd_6149279] using wordTrace_append hprefix tailTrace_6149279
  have hstable : (prefixWord ++ tailWord_6149279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149279).length < 2 ^ (prefixWord ++ tailWord_6149279).sum := by decide
  have hdescent : baseEnd_6149279 < baseStart_6149279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149295 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 5, 3, 2]
def baseStart_6149295 : Nat := 118140960795 + 6149295 * 2 ^ 59
def prefixEnd_6149295 : Nat := 4983230072969 + 3 ^ 40 * 6149295 * 2
def baseEnd_6149295 : Nat := 3157544021289623588732413

theorem tailTrace_6149295 : CollatzResearch.WordTrace tailWord_6149295 prefixEnd_6149295 3157544021289623588732413 := by
  unfold tailWord_6149295
  simp only [CollatzResearch.WordTrace]
  refine ⟨224283214257161905819145339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149522142838107937212763559 224283214257161905819145339)
  ·
    refine ⟨336424821385742858728718009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224283214257161905819145339 336424821385742858728718009)
    ·
      refine ⟨252318616039307144046538507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336424821385742858728718009 252318616039307144046538507)
      ·
        refine ⟨378477924058960716069807761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252318616039307144046538507 378477924058960716069807761)
        ·
          refine ⟨283858443044220537052355821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378477924058960716069807761 283858443044220537052355821)
          ·
            refine ⟨106446916141582701394633433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283858443044220537052355821 106446916141582701394633433)
            ·
              refine ⟨79835187106187026045975075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106446916141582701394633433 79835187106187026045975075)
              ·
                refine ⟨119752780659280539068962613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79835187106187026045975075 119752780659280539068962613)
                ·
                  refine ⟨11226823186807550537715245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119752780659280539068962613 11226823186807550537715245)
                  ·
                    refine ⟨4210058695052831451643217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11226823186807550537715245 4210058695052831451643217)
                    ·
                      refine ⟨3157544021289623588732413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210058695052831451643217 3157544021289623588732413)
                      ·
                        rfl

theorem cell23_6149295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 3, 2].length) (baseStart_6149295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149295 prefixEnd_6149295 := by exact prefixLift 6149295
  have htrace : WordTrace (prefixWord ++ tailWord_6149295) baseStart_6149295 baseEnd_6149295 := by
    simpa [prefixWord, tailWord_6149295, baseEnd_6149295] using wordTrace_append hprefix tailTrace_6149295
  have hstable : (prefixWord ++ tailWord_6149295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149295).length < 2 ^ (prefixWord ++ tailWord_6149295).sum := by decide
  have hdescent : baseEnd_6149295 < baseStart_6149295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149402 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2]
def baseStart_6149402 : Nat := 118140960795 + 6149402 * 2 ^ 59
def prefixEnd_6149402 : Nat := 4983230072969 + 3 ^ 40 * 6149402 * 2
def baseEnd_6149402 : Nat := 3157598963719654670094421

theorem tailTrace_6149402 : CollatzResearch.WordTrace tailWord_6149402 prefixEnd_6149402 3157598963719654670094421 := by
  unfold tailWord_6149402
  simp only [CollatzResearch.WordTrace]
  refine ⟨56071779216943565773322615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149524744578516175395526973 56071779216943565773322615)
  ·
    refine ⟨84107668825415348659983923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56071779216943565773322615 84107668825415348659983923)
    ·
      refine ⟨126161503238123022989975885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84107668825415348659983923 126161503238123022989975885)
      ·
        refine ⟨47310563714296133621240957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126161503238123022989975885 47310563714296133621240957)
        ·
          refine ⟨17741461392861050107965359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47310563714296133621240957 17741461392861050107965359)
          ·
            refine ⟨26612192089291575161948039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17741461392861050107965359 26612192089291575161948039)
            ·
              refine ⟨39918288133937362742922059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26612192089291575161948039 39918288133937362742922059)
              ·
                refine ⟨59877432200906044114383089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39918288133937362742922059 59877432200906044114383089)
                ·
                  refine ⟨44908074150679533085787317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59877432200906044114383089 44908074150679533085787317)
                  ·
                    refine ⟨4210131951626206226792561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44908074150679533085787317 4210131951626206226792561)
                    ·
                      refine ⟨3157598963719654670094421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210131951626206226792561 3157598963719654670094421)
                      ·
                        rfl

theorem cell23_6149402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_6149402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149402 prefixEnd_6149402 := by exact prefixLift 6149402
  have htrace : WordTrace (prefixWord ++ tailWord_6149402) baseStart_6149402 baseEnd_6149402 := by
    simpa [prefixWord, tailWord_6149402, baseEnd_6149402] using wordTrace_append hprefix tailTrace_6149402
  have hstable : (prefixWord ++ tailWord_6149402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149402).length < 2 ^ (prefixWord ++ tailWord_6149402).sum := by decide
  have hdescent : baseEnd_6149402 < baseStart_6149402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149493 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6149493 : Nat := 118140960795 + 6149493 * 2 ^ 59
def prefixEnd_6149493 : Nat := 4983230072969 + 3 ^ 40 * 6149493 * 2
def baseEnd_6149493 : Nat := 1052548563486404604685501

theorem tailTrace_6149493 : CollatzResearch.WordTrace tailWord_6149493 prefixEnd_6149493 1052548563486404604685501 := by
  unfold tailWord_6149493
  simp only [CollatzResearch.WordTrace]
  refine ⟨224290435910444585634853133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149526957273629723756568755 224290435910444585634853133)
  ·
    refine ⟨84108913466416719613069925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224290435910444585634853133 84108913466416719613069925)
    ·
      refine ⟨15770421274953134927450611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84108913466416719613069925 15770421274953134927450611)
      ·
        refine ⟨23655631912429702391175917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15770421274953134927450611 23655631912429702391175917)
        ·
          refine ⟨8870861967161138396690969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23655631912429702391175917 8870861967161138396690969)
          ·
            refine ⟨6653146475370853797518227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8870861967161138396690969 6653146475370853797518227)
            ·
              refine ⟨9979719713056280696277341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6653146475370853797518227 9979719713056280696277341)
              ·
                refine ⟨3742394892396105261104003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9979719713056280696277341 3742394892396105261104003)
                ·
                  refine ⟨5613592338594157891656005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742394892396105261104003 5613592338594157891656005)
                  ·
                    refine ⟨1052548563486404604685501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5613592338594157891656005 1052548563486404604685501)
                    ·
                      rfl

theorem cell23_6149493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6149493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149493 prefixEnd_6149493 := by exact prefixLift 6149493
  have htrace : WordTrace (prefixWord ++ tailWord_6149493) baseStart_6149493 baseEnd_6149493 := by
    simpa [prefixWord, tailWord_6149493, baseEnd_6149493] using wordTrace_append hprefix tailTrace_6149493
  have hstable : (prefixWord ++ tailWord_6149493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149493).length < 2 ^ (prefixWord ++ tailWord_6149493).sum := by decide
  have hdescent : baseEnd_6149493 < baseStart_6149493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149539 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 5, 2, 2]
def baseStart_6149539 : Nat := 118140960795 + 6149539 * 2 ^ 59
def prefixEnd_6149539 : Nat := 4983230072969 + 3 ^ 40 * 6149539 * 2
def baseEnd_6149539 : Nat := 3157669310569320634081291

theorem tailTrace_6149539 : CollatzResearch.WordTrace tailWord_6149539 prefixEnd_6149539 3157669310569320634081291 := by
  unfold tailWord_6149539
  simp only [CollatzResearch.WordTrace]
  refine ⟨224292113668277935491027671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149528075778851956994018447 224292113668277935491027671)
  ·
    refine ⟨336438170502416903236541507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224292113668277935491027671 336438170502416903236541507)
    ·
      refine ⟨504657255753625354854812261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336438170502416903236541507 504657255753625354854812261)
      ·
        refine ⟨94623235453804754035277299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 504657255753625354854812261 94623235453804754035277299)
        ·
          refine ⟨141934853180707131052915949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94623235453804754035277299 141934853180707131052915949)
          ·
            refine ⟨53225569942765174144843481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141934853180707131052915949 53225569942765174144843481)
            ·
              refine ⟨39919177457073880608632611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53225569942765174144843481 39919177457073880608632611)
              ·
                refine ⟨59878766185610820912948917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39919177457073880608632611 59878766185610820912948917)
                ·
                  refine ⟨5613634329901014460588961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59878766185610820912948917 5613634329901014460588961)
                  ·
                    refine ⟨4210225747425760845441721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5613634329901014460588961 4210225747425760845441721)
                    ·
                      refine ⟨3157669310569320634081291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210225747425760845441721 3157669310569320634081291)
                      ·
                        rfl

theorem cell23_6149539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_6149539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149539 prefixEnd_6149539 := by exact prefixLift 6149539
  have htrace : WordTrace (prefixWord ++ tailWord_6149539) baseStart_6149539 baseEnd_6149539 := by
    simpa [prefixWord, tailWord_6149539, baseEnd_6149539] using wordTrace_append hprefix tailTrace_6149539
  have hstable : (prefixWord ++ tailWord_6149539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149539).length < 2 ^ (prefixWord ++ tailWord_6149539).sum := by decide
  have hdescent : baseEnd_6149539 < baseStart_6149539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149549 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6149549 : Nat := 118140960795 + 6149549 * 2 ^ 59
def prefixEnd_6149549 : Nat := 4983230072969 + 3 ^ 40 * 6149549 * 2
def baseEnd_6149549 : Nat := 1052558148458621864985415

theorem tailTrace_6149549 : CollatzResearch.WordTrace tailWord_6149549 prefixEnd_6149549 1052558148458621864985415 := by
  unfold tailWord_6149549
  simp only [CollatzResearch.WordTrace]
  refine ⟨224292478398241707198891701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149528318932161138132594467 224292478398241707198891701)
  ·
    refine ⟨21027419849835160049896097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224292478398241707198891701 21027419849835160049896097)
    ·
      refine ⟨15770564887376370037422073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21027419849835160049896097 15770564887376370037422073)
      ·
        refine ⟨11827923665532277528066555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15770564887376370037422073 11827923665532277528066555)
        ·
          refine ⟨17741885498298416292099833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11827923665532277528066555 17741885498298416292099833)
          ·
            refine ⟨13306414123723812219074875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17741885498298416292099833 13306414123723812219074875)
            ·
              refine ⟨19959621185585718328612313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13306414123723812219074875 19959621185585718328612313)
              ·
                refine ⟨14969715889189288746459235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19959621185585718328612313 14969715889189288746459235)
                ·
                  refine ⟨22454573833783933119688853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14969715889189288746459235 22454573833783933119688853)
                  ·
                    refine ⟨1052558148458621864985415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22454573833783933119688853 1052558148458621864985415)
                    ·
                      rfl

theorem cell23_6149549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6149549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149549 prefixEnd_6149549 := by exact prefixLift 6149549
  have htrace : WordTrace (prefixWord ++ tailWord_6149549) baseStart_6149549 baseEnd_6149549 := by
    simpa [prefixWord, tailWord_6149549, baseEnd_6149549] using wordTrace_append hprefix tailTrace_6149549
  have hstable : (prefixWord ++ tailWord_6149549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149549).length < 2 ^ (prefixWord ++ tailWord_6149549).sum := by decide
  have hdescent : baseEnd_6149549 < baseStart_6149549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149575 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 9]
def baseStart_6149575 : Nat := 118140960795 + 6149575 * 2 ^ 59
def prefixEnd_6149575 : Nat := 4983230072969 + 3 ^ 40 * 6149575 * 2
def baseEnd_6149575 : Nat := 1052562598624294164410375

theorem tailTrace_6149575 : CollatzResearch.WordTrace tailWord_6149575 prefixEnd_6149575 1052562598624294164410375 := by
  unfold tailWord_6149575
  simp only [CollatzResearch.WordTrace]
  refine ⟨224293426696147513639338179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149528951130765009092892119 224293426696147513639338179)
  ·
    refine ⟨336440140044221270459007269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224293426696147513639338179 336440140044221270459007269)
    ·
      refine ⟨63082526258291488211063863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336440140044221270459007269 63082526258291488211063863)
      ·
        refine ⟨94623789387437232316595795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63082526258291488211063863 94623789387437232316595795)
        ·
          refine ⟨141935684081155848474893693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94623789387437232316595795 141935684081155848474893693)
          ·
            refine ⟨53225881530433443178085135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141935684081155848474893693 53225881530433443178085135)
            ·
              refine ⟨79838822295650164767127703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53225881530433443178085135 79838822295650164767127703)
              ·
                refine ⟨119758233443475247150691555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79838822295650164767127703 119758233443475247150691555)
                ·
                  refine ⟨179637350165212870726037333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119758233443475247150691555 179637350165212870726037333)
                  ·
                    refine ⟨1052562598624294164410375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 179637350165212870726037333 1052562598624294164410375)
                    ·
                      rfl

theorem cell23_6149575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_6149575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149575 prefixEnd_6149575 := by exact prefixLift 6149575
  have htrace : WordTrace (prefixWord ++ tailWord_6149575) baseStart_6149575 baseEnd_6149575 := by
    simpa [prefixWord, tailWord_6149575, baseEnd_6149575] using wordTrace_append hprefix tailTrace_6149575
  have hstable : (prefixWord ++ tailWord_6149575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149575).length < 2 ^ (prefixWord ++ tailWord_6149575).sum := by decide
  have hdescent : baseEnd_6149575 < baseStart_6149575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149585 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_6149585 : Nat := 118140960795 + 6149585 * 2 ^ 59
def prefixEnd_6149585 : Nat := 4983230072969 + 3 ^ 40 * 6149585 * 2
def baseEnd_6149585 : Nat := 3157692930679427454106079

theorem tailTrace_6149585 : CollatzResearch.WordTrace tailWord_6149585 prefixEnd_6149585 3157692930679427454106079 := by
  unfold tailWord_6149585
  simp only [CollatzResearch.WordTrace]
  refine ⟨224293791426111285347202209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149529194284074190231468139 224293791426111285347202209)
  ·
    refine ⟨168220343569583464010401657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224293791426111285347202209 168220343569583464010401657)
    ·
      refine ⟨126165257677187598007801243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168220343569583464010401657 126165257677187598007801243)
      ·
        refine ⟨189247886515781397011701865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126165257677187598007801243 189247886515781397011701865)
        ·
          refine ⟨141935914886836047758776399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189247886515781397011701865 141935914886836047758776399)
          ·
            refine ⟨212903872330254071638164599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141935914886836047758776399 212903872330254071638164599)
            ·
              refine ⟨319355808495381107457246899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212903872330254071638164599 319355808495381107457246899)
              ·
                refine ⟨479033712743071661185870349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319355808495381107457246899 479033712743071661185870349)
                ·
                  refine ⟨179637642278651872944701381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479033712743071661185870349 179637642278651872944701381)
                  ·
                    refine ⟨33682057927247226177131509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179637642278651872944701381 33682057927247226177131509)
                    ·
                      refine ⟨3157692930679427454106079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33682057927247226177131509 3157692930679427454106079)
                      ·
                        rfl

theorem cell23_6149585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_6149585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149585 prefixEnd_6149585 := by exact prefixLift 6149585
  have htrace : WordTrace (prefixWord ++ tailWord_6149585) baseStart_6149585 baseEnd_6149585 := by
    simpa [prefixWord, tailWord_6149585, baseEnd_6149585] using wordTrace_append hprefix tailTrace_6149585
  have hstable : (prefixWord ++ tailWord_6149585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149585).length < 2 ^ (prefixWord ++ tailWord_6149585).sum := by decide
  have hdescent : baseEnd_6149585 < baseStart_6149585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149589 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6149589 : Nat := 118140960795 + 6149589 * 2 ^ 59
def prefixEnd_6149589 : Nat := 4983230072969 + 3 ^ 40 * 6149589 * 2
def baseEnd_6149589 : Nat := 3157694984602045438456061

theorem tailTrace_6149589 : CollatzResearch.WordTrace tailWord_6149589 prefixEnd_6149589 3157694984602045438456061 := by
  unfold tailWord_6149589
  simp only [CollatzResearch.WordTrace]
  refine ⟨224293937318096794030347821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149529291545397862686898547 224293937318096794030347821)
  ·
    refine ⟨84110226494286297761380433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224293937318096794030347821 84110226494286297761380433)
    ·
      refine ⟨63082669870714723321035325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84110226494286297761380433 63082669870714723321035325)
      ·
        refine ⟨23656001201518021245388247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63082669870714723321035325 23656001201518021245388247)
        ·
          refine ⟨35484001802277031868082371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23656001201518021245388247 35484001802277031868082371)
          ·
            refine ⟨53226002703415547802123557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35484001802277031868082371 53226002703415547802123557)
            ·
              refine ⟨9979875506890415212898167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53226002703415547802123557 9979875506890415212898167)
              ·
                refine ⟨14969813260335622819347251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9979875506890415212898167 14969813260335622819347251)
                ·
                  refine ⟨22454719890503434229020877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14969813260335622819347251 22454719890503434229020877)
                  ·
                    refine ⟨8420519958938787835882829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22454719890503434229020877 8420519958938787835882829)
                    ·
                      refine ⟨3157694984602045438456061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8420519958938787835882829 3157694984602045438456061)
                      ·
                        rfl

theorem cell23_6149589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6149589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149589 prefixEnd_6149589 := by exact prefixLift 6149589
  have htrace : WordTrace (prefixWord ++ tailWord_6149589) baseStart_6149589 baseEnd_6149589 := by
    simpa [prefixWord, tailWord_6149589, baseEnd_6149589] using wordTrace_append hprefix tailTrace_6149589
  have hstable : (prefixWord ++ tailWord_6149589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149589).length < 2 ^ (prefixWord ++ tailWord_6149589).sum := by decide
  have hdescent : baseEnd_6149589 < baseStart_6149589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149599 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 3, 3, 2]
def baseStart_6149599 : Nat := 118140960795 + 6149599 * 2 ^ 59
def prefixEnd_6149599 : Nat := 4983230072969 + 3 ^ 40 * 6149599 * 2
def baseEnd_6149599 : Nat := 3157700119408590399331015

theorem tailTrace_6149599 : CollatzResearch.WordTrace tailWord_6149599 prefixEnd_6149599 3157700119408590399331015 := by
  unfold tailWord_6149599
  simp only [CollatzResearch.WordTrace]
  refine ⟨224294302048060565738211851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149529534698707043825474567 224294302048060565738211851)
  ·
    refine ⟨336441453072090848607317777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224294302048060565738211851 336441453072090848607317777)
    ·
      refine ⟨252331089804068136455488333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336441453072090848607317777 252331089804068136455488333)
      ·
        refine ⟨94624158676525551170808125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252331089804068136455488333 94624158676525551170808125)
        ·
          refine ⟨35484059503697081689053047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94624158676525551170808125 35484059503697081689053047)
          ·
            refine ⟨53226089255545622533579571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35484059503697081689053047 53226089255545622533579571)
            ·
              refine ⟨79839133883318433800369357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53226089255545622533579571 79839133883318433800369357)
              ·
                refine ⟨29939675206244412675138509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79839133883318433800369357 29939675206244412675138509)
                ·
                  refine ⟨11227378202341654753176941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29939675206244412675138509 11227378202341654753176941)
                  ·
                    refine ⟨4210266825878120532441353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11227378202341654753176941 4210266825878120532441353)
                    ·
                      refine ⟨3157700119408590399331015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210266825878120532441353 3157700119408590399331015)
                      ·
                        rfl

theorem cell23_6149599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_6149599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149599 prefixEnd_6149599 := by exact prefixLift 6149599
  have htrace : WordTrace (prefixWord ++ tailWord_6149599) baseStart_6149599 baseEnd_6149599 := by
    simpa [prefixWord, tailWord_6149599, baseEnd_6149599] using wordTrace_append hprefix tailTrace_6149599
  have hstable : (prefixWord ++ tailWord_6149599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149599).length < 2 ^ (prefixWord ++ tailWord_6149599).sum := by decide
  have hdescent : baseEnd_6149599 < baseStart_6149599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149610 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_6149610 : Nat := 118140960795 + 6149610 * 2 ^ 59
def prefixEnd_6149610 : Nat := 4983230072969 + 3 ^ 40 * 6149610 * 2
def baseEnd_6149610 : Nat := 3157705767695789856293465

theorem tailTrace_6149610 : CollatzResearch.WordTrace tailWord_6149610 prefixEnd_6149610 3157705767695789856293465 := by
  unfold tailWord_6149610
  simp only [CollatzResearch.WordTrace]
  refine ⟨56073675812755178654215571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149529802167347143077908189 56073675812755178654215571)
  ·
    refine ⟨84110513719132767981323357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56073675812755178654215571 84110513719132767981323357)
    ·
      refine ⟨31541442644674787992996259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84110513719132767981323357 31541442644674787992996259)
      ·
        refine ⟨47312163967012181989494389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31541442644674787992996259 47312163967012181989494389)
        ·
          refine ⟨4435515371907392061515099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47312163967012181989494389 4435515371907392061515099)
          ·
            refine ⟨6653273057861088092272649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435515371907392061515099 6653273057861088092272649)
            ·
              refine ⟨4989954793395816069204487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653273057861088092272649 4989954793395816069204487)
              ·
                refine ⟨7484932190093724103806731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989954793395816069204487 7484932190093724103806731)
                ·
                  refine ⟨11227398285140586155710097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484932190093724103806731 11227398285140586155710097)
                  ·
                    refine ⟨8420548713855439616782573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11227398285140586155710097 8420548713855439616782573)
                    ·
                      refine ⟨3157705767695789856293465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8420548713855439616782573 3157705767695789856293465)
                      ·
                        rfl

theorem cell23_6149610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_6149610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149610 prefixEnd_6149610 := by exact prefixLift 6149610
  have htrace : WordTrace (prefixWord ++ tailWord_6149610) baseStart_6149610 baseEnd_6149610 := by
    simpa [prefixWord, tailWord_6149610, baseEnd_6149610] using wordTrace_append hprefix tailTrace_6149610
  have hstable : (prefixWord ++ tailWord_6149610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149610).length < 2 ^ (prefixWord ++ tailWord_6149610).sum := by decide
  have hdescent : baseEnd_6149610 < baseStart_6149610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149616 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 1, 3, 2]
def baseStart_6149616 : Nat := 118140960795 + 6149616 * 2 ^ 59
def prefixEnd_6149616 : Nat := 4983230072969 + 3 ^ 40 * 6149616 * 2
def baseEnd_6149616 : Nat := 3157708848579716832818437

theorem tailTrace_6149616 : CollatzResearch.WordTrace tailWord_6149616 prefixEnd_6149616 3157708848579716832818437 := by
  unfold tailWord_6149616
  simp only [CollatzResearch.WordTrace]
  refine ⟨112147461044499488820790351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149529948059332651761053801 112147461044499488820790351)
  ·
    refine ⟨168221191566749233231185527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112147461044499488820790351 168221191566749233231185527)
    ·
      refine ⟨252331787350123849846778291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168221191566749233231185527 252331787350123849846778291)
      ·
        refine ⟨378497681025185774770167437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252331787350123849846778291 378497681025185774770167437)
        ·
          refine ⟨141936630384444665538812789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378497681025185774770167437 141936630384444665538812789)
          ·
            refine ⟨13306559098541687394263699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141936630384444665538812789 13306559098541687394263699)
            ·
              refine ⟨19959838647812531091395549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13306559098541687394263699 19959838647812531091395549)
              ·
                refine ⟨7484939492929699159273331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19959838647812531091395549 7484939492929699159273331)
                ·
                  refine ⟨11227409239394548738909997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7484939492929699159273331 11227409239394548738909997)
                  ·
                    refine ⟨4210278464772955777091249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11227409239394548738909997 4210278464772955777091249)
                    ·
                      refine ⟨3157708848579716832818437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210278464772955777091249 3157708848579716832818437)
                      ·
                        rfl

theorem cell23_6149616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 3, 2].length) (baseStart_6149616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149616 prefixEnd_6149616 := by exact prefixLift 6149616
  have htrace : WordTrace (prefixWord ++ tailWord_6149616) baseStart_6149616 baseEnd_6149616 := by
    simpa [prefixWord, tailWord_6149616, baseEnd_6149616] using wordTrace_append hprefix tailTrace_6149616
  have hstable : (prefixWord ++ tailWord_6149616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149616).length < 2 ^ (prefixWord ++ tailWord_6149616).sum := by decide
  have hdescent : baseEnd_6149616 < baseStart_6149616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149719 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_6149719 : Nat := 118140960795 + 6149719 * 2 ^ 59
def prefixEnd_6149719 : Nat := 4983230072969 + 3 ^ 40 * 6149719 * 2
def baseEnd_6149719 : Nat := 3157761737087129929830463

theorem tailTrace_6149719 : CollatzResearch.WordTrace tailWord_6149719 prefixEnd_6149719 3157761737087129929830463 := by
  unfold tailWord_6149719
  simp only [CollatzResearch.WordTrace]
  refine ⟨224298678807625826232580211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149532452538417217488386807 224298678807625826232580211)
  ·
    refine ⟨336448018211438739348870317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224298678807625826232580211 336448018211438739348870317)
    ·
      refine ⟨126168006829289527255826369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336448018211438739348870317 126168006829289527255826369)
      ·
        refine ⟨94626005121967145441869777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126168006829289527255826369 94626005121967145441869777)
        ·
          refine ⟨70969503841475359081402333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94626005121967145441869777 70969503841475359081402333)
          ·
            refine ⟨26613563940553259655525875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70969503841475359081402333 26613563940553259655525875)
            ·
              refine ⟨39920345910829889483288813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26613563940553259655525875 39920345910829889483288813)
              ·
                refine ⟨14970129716561208556233305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39920345910829889483288813 14970129716561208556233305)
                ·
                  refine ⟨11227597287420906417174979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14970129716561208556233305 11227597287420906417174979)
                  ·
                    refine ⟨16841395931131359625762469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11227597287420906417174979 16841395931131359625762469)
                    ·
                      refine ⟨3157761737087129929830463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16841395931131359625762469 3157761737087129929830463)
                      ·
                        rfl

theorem cell23_6149719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_6149719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149719 prefixEnd_6149719 := by exact prefixLift 6149719
  have htrace : WordTrace (prefixWord ++ tailWord_6149719) baseStart_6149719 baseEnd_6149719 := by
    simpa [prefixWord, tailWord_6149719, baseEnd_6149719] using wordTrace_append hprefix tailTrace_6149719
  have hstable : (prefixWord ++ tailWord_6149719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149719).length < 2 ^ (prefixWord ++ tailWord_6149719).sum := by decide
  have hdescent : baseEnd_6149719 < baseStart_6149719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149736 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6149736 : Nat := 118140960795 + 6149736 * 2 ^ 59
def prefixEnd_6149736 : Nat := 4983230072969 + 3 ^ 40 * 6149736 * 2
def baseEnd_6149736 : Nat := 3157770466258256363317885

theorem tailTrace_6149736 : CollatzResearch.WordTrace tailWord_6149736 prefixEnd_6149736 3157770466258256363317885 := by
  unfold tailWord_6149736
  simp only [CollatzResearch.WordTrace]
  refine ⟨112149649424282119067974531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149532865899042825423966041 112149649424282119067974531)
  ·
    refine ⟨168224474136423178601961797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112149649424282119067974531 168224474136423178601961797)
    ·
      refine ⟨31542088900579345987867837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168224474136423178601961797 31542088900579345987867837)
      ·
        refine ⟨11828283337717254745450439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31542088900579345987867837 11828283337717254745450439)
        ·
          refine ⟨17742425006575882118175659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11828283337717254745450439 17742425006575882118175659)
          ·
            refine ⟨26613637509863823177263489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17742425006575882118175659 26613637509863823177263489)
            ·
              refine ⟨19960228132397867382947617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26613637509863823177263489 19960228132397867382947617)
              ·
                refine ⟨14970171099298400537210713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19960228132397867382947617 14970171099298400537210713)
                ·
                  refine ⟨11227628324473800402908035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14970171099298400537210713 11227628324473800402908035)
                  ·
                    refine ⟨16841442486710700604362053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11227628324473800402908035 16841442486710700604362053)
                    ·
                      refine ⟨3157770466258256363317885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16841442486710700604362053 3157770466258256363317885)
                      ·
                        rfl

theorem cell23_6149736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6149736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149736 prefixEnd_6149736 := by exact prefixLift 6149736
  have htrace : WordTrace (prefixWord ++ tailWord_6149736) baseStart_6149736 baseEnd_6149736 := by
    simpa [prefixWord, tailWord_6149736, baseEnd_6149736] using wordTrace_append hprefix tailTrace_6149736
  have hstable : (prefixWord ++ tailWord_6149736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149736).length < 2 ^ (prefixWord ++ tailWord_6149736).sum := by decide
  have hdescent : baseEnd_6149736 < baseStart_6149736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149839 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_6149839 : Nat := 118140960795 + 6149839 * 2 ^ 59
def prefixEnd_6149839 : Nat := 4983230072969 + 3 ^ 40 * 6149839 * 2
def baseEnd_6149839 : Nat := 3157823354765669460329911

theorem tailTrace_6149839 : CollatzResearch.WordTrace tailWord_6149839 prefixEnd_6149839 3157823354765669460329911 := by
  unfold tailWord_6149839
  simp only [CollatzResearch.WordTrace]
  refine ⟨224303055567191086726948571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149535370378127391151299047 224303055567191086726948571)
  ·
    refine ⟨336454583350786630090422857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224303055567191086726948571 336454583350786630090422857)
    ·
      refine ⟨252340937513089972567817143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336454583350786630090422857 252340937513089972567817143)
      ·
        refine ⟨378511406269634958851725715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252340937513089972567817143 378511406269634958851725715)
        ·
          refine ⟨567767109404452438277588573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378511406269634958851725715 567767109404452438277588573)
          ·
            refine ⟨212912666026669664354095715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567767109404452438277588573 212912666026669664354095715)
            ·
              refine ⟨319368999040004496531143573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212912666026669664354095715 319368999040004496531143573)
              ·
                refine ⟨14970421830000210774897355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 319368999040004496531143573 14970421830000210774897355)
                ·
                  refine ⟨22455632745000316162346033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14970421830000210774897355 22455632745000316162346033)
                  ·
                    refine ⟨16841724558750237121759525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22455632745000316162346033 16841724558750237121759525)
                    ·
                      refine ⟨3157823354765669460329911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16841724558750237121759525 3157823354765669460329911)
                      ·
                        rfl

theorem cell23_6149839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_6149839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149839 prefixEnd_6149839 := by exact prefixLift 6149839
  have htrace : WordTrace (prefixWord ++ tailWord_6149839) baseStart_6149839 baseEnd_6149839 := by
    simpa [prefixWord, tailWord_6149839, baseEnd_6149839] using wordTrace_append hprefix tailTrace_6149839
  have hstable : (prefixWord ++ tailWord_6149839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149839).length < 2 ^ (prefixWord ++ tailWord_6149839).sum := by decide
  have hdescent : baseEnd_6149839 < baseStart_6149839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149849 : List Nat := [1, 2, 1, 2, 3, 5, 9]
def baseStart_6149849 : Nat := 118140960795 + 6149849 * 2 ^ 59
def prefixEnd_6149849 : Nat := 4983230072969 + 3 ^ 40 * 6149849 * 2
def baseEnd_6149849 : Nat := 38985536908298943471665

theorem tailTrace_6149849 : CollatzResearch.WordTrace tailWord_6149849 prefixEnd_6149849 38985536908298943471665 := by
  unfold tailWord_6149849
  simp only [CollatzResearch.WordTrace]
  refine ⟨224303420297154858434812601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149535613531436572289875067 224303420297154858434812601)
  ·
    refine ⟨168227565222866143826109451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224303420297154858434812601 168227565222866143826109451)
    ·
      refine ⟨252341347834299215739164177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168227565222866143826109451 252341347834299215739164177)
      ·
        refine ⟨189256010875724411804373133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252341347834299215739164177 189256010875724411804373133)
        ·
          refine ⟨70971004078396654426639925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189256010875724411804373133 70971004078396654426639925)
          ·
            refine ⟨6653531632349686352497493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70971004078396654426639925 6653531632349686352497493)
            ·
              refine ⟨38985536908298943471665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6653531632349686352497493 38985536908298943471665)
              ·
                rfl

theorem cell23_6149849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 9].length) (baseStart_6149849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149849 prefixEnd_6149849 := by exact prefixLift 6149849
  have htrace : WordTrace (prefixWord ++ tailWord_6149849) baseStart_6149849 baseEnd_6149849 := by
    simpa [prefixWord, tailWord_6149849, baseEnd_6149849] using wordTrace_append hprefix tailTrace_6149849
  have hstable : (prefixWord ++ tailWord_6149849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149849).length < 2 ^ (prefixWord ++ tailWord_6149849).sum := by decide
  have hdescent : baseEnd_6149849 < baseStart_6149849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149889 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_6149889 : Nat := 118140960795 + 6149889 * 2 ^ 59
def prefixEnd_6149889 : Nat := 4983230072969 + 3 ^ 40 * 6149889 * 2
def baseEnd_6149889 : Nat := 3157849028798394264704681

theorem tailTrace_6149889 : CollatzResearch.WordTrace tailWord_6149889 prefixEnd_6149889 3157849028798394264704681 := by
  unfold tailWord_6149889
  simp only [CollatzResearch.WordTrace]
  refine ⟨224304879217009945266268721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149536586144673296844179147 224304879217009945266268721)
  ·
    refine ⟨168228659412757458949701541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224304879217009945266268721 168228659412757458949701541)
    ·
      refine ⟨31542873639892023553069039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168228659412757458949701541 31542873639892023553069039)
      ·
        refine ⟨47314310459838035329603559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31542873639892023553069039 47314310459838035329603559)
        ·
          refine ⟨70971465689757052994405339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47314310459838035329603559 70971465689757052994405339)
          ·
            refine ⟨106457198534635579491608009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70971465689757052994405339 106457198534635579491608009)
            ·
              refine ⟨79842898900976684618706007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106457198534635579491608009 79842898900976684618706007)
              ·
                refine ⟨119764348351465026928059011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79842898900976684618706007 119764348351465026928059011)
                ·
                  refine ⟨179646522527197540392088517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119764348351465026928059011 179646522527197540392088517)
                  ·
                    refine ⟨33683722973849538823516597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179646522527197540392088517 33683722973849538823516597)
                    ·
                      refine ⟨3157849028798394264704681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33683722973849538823516597 3157849028798394264704681)
                      ·
                        rfl

theorem cell23_6149889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_6149889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149889 prefixEnd_6149889 := by exact prefixLift 6149889
  have htrace : WordTrace (prefixWord ++ tailWord_6149889) baseStart_6149889 baseEnd_6149889 := by
    simpa [prefixWord, tailWord_6149889, baseEnd_6149889] using wordTrace_append hprefix tailTrace_6149889
  have hstable : (prefixWord ++ tailWord_6149889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149889).length < 2 ^ (prefixWord ++ tailWord_6149889).sum := by decide
  have hdescent : baseEnd_6149889 < baseStart_6149889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149950 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_6149950 : Nat := 118140960795 + 6149950 * 2 ^ 59
def prefixEnd_6149950 : Nat := 4983230072969 + 3 ^ 40 * 6149950 * 2
def baseEnd_6149950 : Nat := 3157880351118318526041901

theorem tailTrace_6149950 : CollatzResearch.WordTrace tailWord_6149950 prefixEnd_6149950 3157880351118318526041901 := by
  unfold tailWord_6149950
  simp only [CollatzResearch.WordTrace]
  refine ⟨28038388008723619085529913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149538069379859301789492869 28038388008723619085529913)
  ·
    refine ⟨21028791006542714314147435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28038388008723619085529913 21028791006542714314147435)
    ·
      refine ⟨31543186509814071471221153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21028791006542714314147435 31543186509814071471221153)
      ·
        refine ⟨23657389882360553603415865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31543186509814071471221153 23657389882360553603415865)
        ·
          refine ⟨17743042411770415202561899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23657389882360553603415865 17743042411770415202561899)
          ·
            refine ⟨26614563617655622803842849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17743042411770415202561899 26614563617655622803842849)
            ·
              refine ⟨19960922713241717102882137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26614563617655622803842849 19960922713241717102882137)
              ·
                refine ⟨14970692034931287827161603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19960922713241717102882137 14970692034931287827161603)
                ·
                  refine ⟨22456038052396931740742405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14970692034931287827161603 22456038052396931740742405)
                  ·
                    refine ⟨4210507134824424701389201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22456038052396931740742405 4210507134824424701389201)
                    ·
                      refine ⟨3157880351118318526041901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210507134824424701389201 3157880351118318526041901)
                      ·
                        rfl

theorem cell23_6149950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_6149950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149950 prefixEnd_6149950 := by exact prefixLift 6149950
  have htrace : WordTrace (prefixWord ++ tailWord_6149950) baseStart_6149950 baseEnd_6149950 := by
    simpa [prefixWord, tailWord_6149950, baseEnd_6149950] using wordTrace_append hprefix tailTrace_6149950
  have hstable : (prefixWord ++ tailWord_6149950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149950).length < 2 ^ (prefixWord ++ tailWord_6149950).sum := by decide
  have hdescent : baseEnd_6149950 < baseStart_6149950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6149973 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 5]
def baseStart_6149973 : Nat := 118140960795 + 6149973 * 2 ^ 59
def prefixEnd_6149973 : Nat := 4983230072969 + 3 ^ 40 * 6149973 * 2
def baseEnd_6149973 : Nat := 350876906797041326228255

theorem tailTrace_6149973 : CollatzResearch.WordTrace tailWord_6149973 prefixEnd_6149973 350876906797041326228255 := by
  unfold tailWord_6149973
  simp only [CollatzResearch.WordTrace]
  refine ⟨224307942948705627612326573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149538628632470418408217715 224307942948705627612326573)
  ·
    refine ⟨84115478605764610354622465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224307942948705627612326573 84115478605764610354622465)
    ·
      refine ⟨63086608954323457765966849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84115478605764610354622465 63086608954323457765966849)
      ·
        refine ⟨47314956715742593324475137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63086608954323457765966849 47314956715742593324475137)
        ·
          refine ⟨35486217536806944993356353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47314956715742593324475137 35486217536806944993356353)
          ·
            refine ⟨26614663152605208745017265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35486217536806944993356353 26614663152605208745017265)
            ·
              refine ⟨19960997364453906558762949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26614663152605208745017265 19960997364453906558762949)
              ·
                refine ⟨3742687005835107479768053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19960997364453906558762949 3742687005835107479768053)
                ·
                  refine ⟨350876906797041326228255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3742687005835107479768053 350876906797041326228255)
                  ·
                    rfl

theorem cell23_6149973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_6149973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6149973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6149973 prefixEnd_6149973 := by exact prefixLift 6149973
  have htrace : WordTrace (prefixWord ++ tailWord_6149973) baseStart_6149973 baseEnd_6149973 := by
    simpa [prefixWord, tailWord_6149973, baseEnd_6149973] using wordTrace_append hprefix tailTrace_6149973
  have hstable : (prefixWord ++ tailWord_6149973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6149973).length < 2 ^ (prefixWord ++ tailWord_6149973).sum := by decide
  have hdescent : baseEnd_6149973 < baseStart_6149973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6149973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150030 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6150030 : Nat := 118140960795 + 6150030 * 2 ^ 59
def prefixEnd_6150030 : Nat := 4983230072969 + 3 ^ 40 * 6150030 * 2
def baseEnd_6150030 : Nat := 3157921429570678213041533

theorem tailTrace_6150030 : CollatzResearch.WordTrace tailWord_6150030 prefixEnd_6150030 3157921429570678213041533 := by
  unfold tailWord_6150030
  simp only [CollatzResearch.WordTrace]
  refine ⟨28038752738687390793393943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149540014606332750898101029 28038752738687390793393943)
  ·
    refine ⟨42058129108031086190090915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28038752738687390793393943 42058129108031086190090915)
    ·
      refine ⟨63087193662046629285136373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42058129108031086190090915 63087193662046629285136373)
      ·
        refine ⟨5914424405816871495481535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63087193662046629285136373 5914424405816871495481535)
        ·
          refine ⟨8871636608725307243222303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5914424405816871495481535 8871636608725307243222303)
          ·
            refine ⟨13307454913087960864833455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8871636608725307243222303 13307454913087960864833455)
            ·
              refine ⟨19961182369631941297250183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13307454913087960864833455 19961182369631941297250183)
              ·
                refine ⟨29941773554447911945875275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19961182369631941297250183 29941773554447911945875275)
                ·
                  refine ⟨44912660331671867918812913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29941773554447911945875275 44912660331671867918812913)
                  ·
                    refine ⟨33684495248753900939109685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44912660331671867918812913 33684495248753900939109685)
                    ·
                      refine ⟨3157921429570678213041533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33684495248753900939109685 3157921429570678213041533)
                      ·
                        rfl

theorem cell23_6150030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6150030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150030 prefixEnd_6150030 := by exact prefixLift 6150030
  have htrace : WordTrace (prefixWord ++ tailWord_6150030) baseStart_6150030 baseEnd_6150030 := by
    simpa [prefixWord, tailWord_6150030, baseEnd_6150030] using wordTrace_append hprefix tailTrace_6150030
  have hstable : (prefixWord ++ tailWord_6150030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150030).length < 2 ^ (prefixWord ++ tailWord_6150030).sum := by decide
  have hdescent : baseEnd_6150030 < baseStart_6150030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150033 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 3, 4]
def baseStart_6150033 : Nat := 118140960795 + 6150033 * 2 ^ 59
def prefixEnd_6150033 : Nat := 4983230072969 + 3 ^ 40 * 6150033 * 2
def baseEnd_6150033 : Nat := 1052640990004213900434673

theorem tailTrace_6150033 : CollatzResearch.WordTrace tailWord_6150033 prefixEnd_6150033 1052640990004213900434673 := by
  unfold tailWord_6150033
  simp only [CollatzResearch.WordTrace]
  refine ⟨224310131328488257859510753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149540087552325505239673835 224310131328488257859510753)
  ·
    refine ⟨168232598496366193394633065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224310131328488257859510753 168232598496366193394633065)
    ·
      refine ⟨126174448872274645045974799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168232598496366193394633065 126174448872274645045974799)
      ·
        refine ⟨189261673308411967568962199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126174448872274645045974799 189261673308411967568962199)
        ·
          refine ⟨283892509962617951353443299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189261673308411967568962199 283892509962617951353443299)
          ·
            refine ⟨425838764943926927030164949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283892509962617951353443299 425838764943926927030164949)
            ·
              refine ⟨9980596053373287352269491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 425838764943926927030164949 9980596053373287352269491)
              ·
                refine ⟨14970894080059931028404237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9980596053373287352269491 14970894080059931028404237)
                ·
                  refine ⟨5614085280022474135651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14970894080059931028404237 5614085280022474135651589)
                  ·
                    refine ⟨1052640990004213900434673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614085280022474135651589 1052640990004213900434673)
                    ·
                      rfl

theorem cell23_6150033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_6150033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150033 prefixEnd_6150033 := by exact prefixLift 6150033
  have htrace : WordTrace (prefixWord ++ tailWord_6150033) baseStart_6150033 baseEnd_6150033 := by
    simpa [prefixWord, tailWord_6150033, baseEnd_6150033] using wordTrace_append hprefix tailTrace_6150033
  have hstable : (prefixWord ++ tailWord_6150033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150033).length < 2 ^ (prefixWord ++ tailWord_6150033).sum := by decide
  have hdescent : baseEnd_6150033 < baseStart_6150033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150100 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6150100 : Nat := 118140960795 + 6150100 * 2 ^ 59
def prefixEnd_6150100 : Nat := 4983230072969 + 3 ^ 40 * 6150100 * 2
def baseEnd_6150100 : Nat := 3157957373216492939166211

theorem tailTrace_6150100 : CollatzResearch.WordTrace tailWord_6150100 prefixEnd_6150100 3157957373216492939166211 := by
  unfold tailWord_6150100
  simp only [CollatzResearch.WordTrace]
  refine ⟨112156287509622764151099877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149541716679497018868133169 112156287509622764151099877)
  ·
    refine ⟨21029303908054268278331227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112156287509622764151099877 21029303908054268278331227)
    ·
      refine ⟨31543955862081402417496841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21029303908054268278331227 31543955862081402417496841)
      ·
        refine ⟨23657966896561051813122631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31543955862081402417496841 23657966896561051813122631)
        ·
          refine ⟨35486950344841577719683947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23657966896561051813122631 35486950344841577719683947)
          ·
            refine ⟨53230425517262366579525921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35486950344841577719683947 53230425517262366579525921)
            ·
              refine ⟨39922819137946774934644441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53230425517262366579525921 39922819137946774934644441)
              ·
                refine ⟨29942114353460081200983331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39922819137946774934644441 29942114353460081200983331)
                ·
                  refine ⟨44913171530190121801474997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29942114353460081200983331 44913171530190121801474997)
                  ·
                    refine ⟨4210609830955323918888281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44913171530190121801474997 4210609830955323918888281)
                    ·
                      refine ⟨3157957373216492939166211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210609830955323918888281 3157957373216492939166211)
                      ·
                        rfl

theorem cell23_6150100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6150100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150100 prefixEnd_6150100 := by exact prefixLift 6150100
  have htrace : WordTrace (prefixWord ++ tailWord_6150100) baseStart_6150100 baseEnd_6150100 := by
    simpa [prefixWord, tailWord_6150100, baseEnd_6150100] using wordTrace_append hprefix tailTrace_6150100
  have hstable : (prefixWord ++ tailWord_6150100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150100).length < 2 ^ (prefixWord ++ tailWord_6150100).sum := by decide
  have hdescent : baseEnd_6150100 < baseStart_6150100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150113 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_6150113 : Nat := 118140960795 + 6150113 * 2 ^ 59
def prefixEnd_6150113 : Nat := 4983230072969 + 3 ^ 40 * 6150113 * 2
def baseEnd_6150113 : Nat := 3157964048465001388303651

theorem tailTrace_6150113 : CollatzResearch.WordTrace tailWord_6150113 prefixEnd_6150113 3157964048465001388303651 := by
  unfold tailWord_6150113
  simp only [CollatzResearch.WordTrace]
  refine ⟨224313049168198431522422993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149542032778798954348281995 224313049168198431522422993)
  ·
    refine ⟨168234786876148823641817245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224313049168198431522422993 168234786876148823641817245)
    ·
      refine ⟨63088045078555808865681467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168234786876148823641817245 63088045078555808865681467)
      ·
        refine ⟨94632067617833713298522201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63088045078555808865681467 94632067617833713298522201)
        ·
          refine ⟨70974050713375284973891651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94632067617833713298522201 70974050713375284973891651)
          ·
            refine ⟨106461076070062927460837477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70974050713375284973891651 106461076070062927460837477)
            ·
              refine ⟨19961451763136798898907027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106461076070062927460837477 19961451763136798898907027)
              ·
                refine ⟨29942177644705198348360541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19961451763136798898907027 29942177644705198348360541)
                ·
                  refine ⟨11228316616764449380635203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29942177644705198348360541 11228316616764449380635203)
                  ·
                    refine ⟨16842474925146674070952805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11228316616764449380635203 16842474925146674070952805)
                    ·
                      refine ⟨3157964048465001388303651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16842474925146674070952805 3157964048465001388303651)
                      ·
                        rfl

theorem cell23_6150113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_6150113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150113 prefixEnd_6150113 := by exact prefixLift 6150113
  have htrace : WordTrace (prefixWord ++ tailWord_6150113) baseStart_6150113 baseEnd_6150113 := by
    simpa [prefixWord, tailWord_6150113, baseEnd_6150113] using wordTrace_append hprefix tailTrace_6150113
  have hstable : (prefixWord ++ tailWord_6150113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150113).length < 2 ^ (prefixWord ++ tailWord_6150113).sum := by decide
  have hdescent : baseEnd_6150113 < baseStart_6150113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150170 : List Nat := [3, 1, 1, 3, 1, 5, 2, 7]
def baseStart_6150170 : Nat := 118140960795 + 6150170 * 2 ^ 59
def prefixEnd_6150170 : Nat := 4983230072969 + 3 ^ 40 * 6150170 * 2
def baseEnd_6150170 : Nat := 116962715439344728344107

theorem tailTrace_6150170 : CollatzResearch.WordTrace tailWord_6150170 prefixEnd_6150170 116962715439344728344107 := by
  unfold tailWord_6150170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56078782032247982564311991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149543418752661286838165309 56078782032247982564311991)
  ·
    refine ⟨84118173048371973846467987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56078782032247982564311991 84118173048371973846467987)
    ·
      refine ⟨126177259572557960769701981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84118173048371973846467987 126177259572557960769701981)
      ·
        refine ⟨47316472339709235288638243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126177259572557960769701981 47316472339709235288638243)
        ·
          refine ⟨70974708509563852932957365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47316472339709235288638243 70974708509563852932957365)
          ·
            refine ⟨6653878922771611212464753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70974708509563852932957365 6653878922771611212464753)
            ·
              refine ⟨4990409192078708409348565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653878922771611212464753 4990409192078708409348565)
              ·
                refine ⟨116962715439344728344107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4990409192078708409348565 116962715439344728344107)
                ·
                  rfl

theorem cell23_6150170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_6150170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150170 prefixEnd_6150170 := by exact prefixLift 6150170
  have htrace : WordTrace (prefixWord ++ tailWord_6150170) baseStart_6150170 baseEnd_6150170 := by
    simpa [prefixWord, tailWord_6150170, baseEnd_6150170] using wordTrace_append hprefix tailTrace_6150170
  have hstable : (prefixWord ++ tailWord_6150170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150170).length < 2 ^ (prefixWord ++ tailWord_6150170).sum := by decide
  have hdescent : baseEnd_6150170 < baseStart_6150170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150181 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 1, 2, 2]
def baseStart_6150181 : Nat := 118140960795 + 6150181 * 2 ^ 59
def prefixEnd_6150181 : Nat := 4983230072969 + 3 ^ 40 * 6150181 * 2
def baseEnd_6150181 : Nat := 3157998965149507122253339

theorem tailTrace_6150181 : CollatzResearch.WordTrace tailWord_6150181 prefixEnd_6150181 3157998965149507122253339 := by
  unfold tailWord_6150181
  simp only [CollatzResearch.WordTrace]
  refine ⟨224315529331952079135898397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149543686221301386090598931 224315529331952079135898397)
  ·
    refine ⟨84118323499482029675961899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224315529331952079135898397 84118323499482029675961899)
    ·
      refine ⟨126177485249223044513942849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84118323499482029675961899 126177485249223044513942849)
      ·
        refine ⟨94633113936917283385457137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126177485249223044513942849 94633113936917283385457137)
        ·
          refine ⟨70974835452687962539092853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94633113936917283385457137 70974835452687962539092853)
          ·
            refine ⟨6653890823689496488039955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70974835452687962539092853 6653890823689496488039955)
            ·
              refine ⟨9980836235534244732059933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6653890823689496488039955 9980836235534244732059933)
              ·
                refine ⟨3742813588325341774522475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9980836235534244732059933 3742813588325341774522475)
                ·
                  refine ⟨5614220382488012661783713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742813588325341774522475 5614220382488012661783713)
                  ·
                    refine ⟨4210665286866009496337785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5614220382488012661783713 4210665286866009496337785)
                    ·
                      refine ⟨3157998965149507122253339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210665286866009496337785 3157998965149507122253339)
                      ·
                        rfl

theorem cell23_6150181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_6150181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150181 prefixEnd_6150181 := by exact prefixLift 6150181
  have htrace : WordTrace (prefixWord ++ tailWord_6150181) baseStart_6150181 baseEnd_6150181 := by
    simpa [prefixWord, tailWord_6150181, baseEnd_6150181] using wordTrace_append hprefix tailTrace_6150181
  have hstable : (prefixWord ++ tailWord_6150181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150181).length < 2 ^ (prefixWord ++ tailWord_6150181).sum := by decide
  have hdescent : baseEnd_6150181 < baseStart_6150181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150198 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_6150198 : Nat := 118140960795 + 6150198 * 2 ^ 59
def prefixEnd_6150198 : Nat := 4983230072969 + 3 ^ 40 * 6150198 * 2
def baseEnd_6150198 : Nat := 3158007694320633555740761

theorem tailTrace_6150198 : CollatzResearch.WordTrace tailWord_6150198 prefixEnd_6150198 3158007694320633555740761 := by
  unfold tailWord_6150198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14019759335805655689954203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149544099581926994026178165 14019759335805655689954203)
  ·
    refine ⟨21029639003708483534931305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14019759335805655689954203 21029639003708483534931305)
    ·
      refine ⟨15772229252781362651198479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21029639003708483534931305 15772229252781362651198479)
      ·
        refine ⟨23658343879172043976797719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15772229252781362651198479 23658343879172043976797719)
        ·
          refine ⟨35487515818758065965196579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23658343879172043976797719 35487515818758065965196579)
          ·
            refine ⟨53231273728137098947794869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35487515818758065965196579 53231273728137098947794869)
            ·
              refine ⟨4990431912012853026355769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53231273728137098947794869 4990431912012853026355769)
              ·
                refine ⟨3742823934009639769766827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990431912012853026355769 3742823934009639769766827)
                ·
                  refine ⟨5614235901014459654650241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742823934009639769766827 5614235901014459654650241)
                  ·
                    refine ⟨4210676925760844740987681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5614235901014459654650241 4210676925760844740987681)
                    ·
                      refine ⟨3158007694320633555740761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210676925760844740987681 3158007694320633555740761)
                      ·
                        rfl

theorem cell23_6150198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_6150198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150198 prefixEnd_6150198 := by exact prefixLift 6150198
  have htrace : WordTrace (prefixWord ++ tailWord_6150198) baseStart_6150198 baseEnd_6150198 := by
    simpa [prefixWord, tailWord_6150198, baseEnd_6150198] using wordTrace_append hprefix tailTrace_6150198
  have hstable : (prefixWord ++ tailWord_6150198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150198).length < 2 ^ (prefixWord ++ tailWord_6150198).sum := by decide
  have hdescent : baseEnd_6150198 < baseStart_6150198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150223 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_6150223 : Nat := 118140960795 + 6150223 * 2 ^ 59
def prefixEnd_6150223 : Nat := 4983230072969 + 3 ^ 40 * 6150223 * 2
def baseEnd_6150223 : Nat := 3158020531336995957928145

theorem tailTrace_6150223 : CollatzResearch.WordTrace tailWord_6150223 prefixEnd_6150223 3158020531336995957928145 := by
  unfold tailWord_6150223
  simp only [CollatzResearch.WordTrace]
  refine ⟨224317061197799920308927323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149544707465199946872618215 224317061197799920308927323)
  ·
    refine ⟨336475591796699880463390985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224317061197799920308927323 336475591796699880463390985)
    ·
      refine ⟨252356693847524910347543239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336475591796699880463390985 252356693847524910347543239)
      ·
        refine ⟨378535040771287365521314859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252356693847524910347543239 378535040771287365521314859)
        ·
          refine ⟨567802561156931048281972289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378535040771287365521314859 567802561156931048281972289)
          ·
            refine ⟨425851920867698286211479217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567802561156931048281972289 425851920867698286211479217)
            ·
              refine ⟨319388940650773714658609413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425851920867698286211479217 319388940650773714658609413)
              ·
                refine ⟨59885426372020071498489265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319388940650773714658609413 59885426372020071498489265)
                ·
                  refine ⟨44914069779015053623866949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59885426372020071498489265 44914069779015053623866949)
                  ·
                    refine ⟨8421388083565322554475053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44914069779015053623866949 8421388083565322554475053)
                    ·
                      refine ⟨3158020531336995957928145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8421388083565322554475053 3158020531336995957928145)
                      ·
                        rfl

theorem cell23_6150223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_6150223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150223 prefixEnd_6150223 := by exact prefixLift 6150223
  have htrace : WordTrace (prefixWord ++ tailWord_6150223) baseStart_6150223 baseEnd_6150223 := by
    simpa [prefixWord, tailWord_6150223, baseEnd_6150223] using wordTrace_append hprefix tailTrace_6150223
  have hstable : (prefixWord ++ tailWord_6150223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150223).length < 2 ^ (prefixWord ++ tailWord_6150223).sum := by decide
  have hdescent : baseEnd_6150223 < baseStart_6150223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150290 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_6150290 : Nat := 118140960795 + 6150290 * 2 ^ 59
def prefixEnd_6150290 : Nat := 4983230072969 + 3 ^ 40 * 6150290 * 2
def baseEnd_6150290 : Nat := 1052684978180282398596779

theorem tailTrace_6150290 : CollatzResearch.WordTrace tailWord_6150290 prefixEnd_6150290 1052684978180282398596779 := by
  unfold tailWord_6150290
  simp only [CollatzResearch.WordTrace]
  refine ⟨56079876222139297687904081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149546336592371460501077549 56079876222139297687904081)
  ·
    refine ⟨42059907166604473265928061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56079876222139297687904081 42059907166604473265928061)
    ·
      refine ⟨15772465187476677474723023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42059907166604473265928061 15772465187476677474723023)
      ·
        refine ⟨23658697781215016212084535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15772465187476677474723023 23658697781215016212084535)
        ·
          refine ⟨35488046671822524318126803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23658697781215016212084535 35488046671822524318126803)
          ·
            refine ⟨53232070007733786477190205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35488046671822524318126803 53232070007733786477190205)
            ·
              refine ⟨19962026252900169928946327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53232070007733786477190205 19962026252900169928946327)
              ·
                refine ⟨29943039379350254893419491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19962026252900169928946327 29943039379350254893419491)
                ·
                  refine ⟨44914559069025382340129237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29943039379350254893419491 44914559069025382340129237)
                  ·
                    refine ⟨1052684978180282398596779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44914559069025382340129237 1052684978180282398596779)
                    ·
                      rfl

theorem cell23_6150290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_6150290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150290 prefixEnd_6150290 := by exact prefixLift 6150290
  have htrace : WordTrace (prefixWord ++ tailWord_6150290) baseStart_6150290 baseEnd_6150290 := by
    simpa [prefixWord, tailWord_6150290, baseEnd_6150290] using wordTrace_append hprefix tailTrace_6150290
  have hstable : (prefixWord ++ tailWord_6150290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150290).length < 2 ^ (prefixWord ++ tailWord_6150290).sum := by decide
  have hdescent : baseEnd_6150290 < baseStart_6150290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150323 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_6150323 : Nat := 118140960795 + 6150323 * 2 ^ 59
def prefixEnd_6150323 : Nat := 4983230072969 + 3 ^ 40 * 6150323 * 2
def baseEnd_6150323 : Nat := 3158071879402445566677685

theorem tailTrace_6150323 : CollatzResearch.WordTrace tailWord_6150323 prefixEnd_6150323 3158071879402445566677685 := by
  unfold tailWord_6150323
  simp only [CollatzResearch.WordTrace]
  refine ⟨224320708497437637387567623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149547138998291758258378415 224320708497437637387567623)
  ·
    refine ⟨336481062746156456081351435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224320708497437637387567623 336481062746156456081351435)
    ·
      refine ⟨504721594119234684122027153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336481062746156456081351435 504721594119234684122027153)
      ·
        refine ⟨378541195589426013091520365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504721594119234684122027153 378541195589426013091520365)
        ·
          refine ⟨141952948346034754909320137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378541195589426013091520365 141952948346034754909320137)
          ·
            refine ⟨106464711259526066181990103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141952948346034754909320137 106464711259526066181990103)
            ·
              refine ⟨159697066889289099272985155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106464711259526066181990103 159697066889289099272985155)
              ·
                refine ⟨239545600333933648909477733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159697066889289099272985155 239545600333933648909477733)
                ·
                  refine ⟨44914800062612559170527075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 239545600333933648909477733 44914800062612559170527075)
                  ·
                    refine ⟨67372200093918838755790613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44914800062612559170527075 67372200093918838755790613)
                    ·
                      refine ⟨3158071879402445566677685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67372200093918838755790613 3158071879402445566677685)
                      ·
                        rfl

theorem cell23_6150323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_6150323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150323 prefixEnd_6150323 := by exact prefixLift 6150323
  have htrace : WordTrace (prefixWord ++ tailWord_6150323) baseStart_6150323 baseEnd_6150323 := by
    simpa [prefixWord, tailWord_6150323, baseEnd_6150323] using wordTrace_append hprefix tailTrace_6150323
  have hstable : (prefixWord ++ tailWord_6150323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150323).length < 2 ^ (prefixWord ++ tailWord_6150323).sum := by decide
  have hdescent : baseEnd_6150323 < baseStart_6150323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150327 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 2, 4, 2]
def baseStart_6150327 : Nat := 118140960795 + 6150327 * 2 ^ 59
def prefixEnd_6150327 : Nat := 4983230072969 + 3 ^ 40 * 6150327 * 2
def baseEnd_6150327 : Nat := 3158073933325063551027667

theorem tailTrace_6150327 : CollatzResearch.WordTrace tailWord_6150327 prefixEnd_6150327 3158073933325063551027667 := by
  unfold tailWord_6150327
  simp only [CollatzResearch.WordTrace]
  refine ⟨224320854389423146070713235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149547236259615430713808823 224320854389423146070713235)
  ·
    refine ⟨336481281584134719106069853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224320854389423146070713235 336481281584134719106069853)
    ·
      refine ⟨126180480594050519664776195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336481281584134719106069853 126180480594050519664776195)
      ·
        refine ⟨189270720891075779497164293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126180480594050519664776195 189270720891075779497164293)
        ·
          refine ⟨35488260167076708655718305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189270720891075779497164293 35488260167076708655718305)
          ·
            refine ⟨26616195125307531491788729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35488260167076708655718305 26616195125307531491788729)
            ·
              refine ⟨19962146343980648618841547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26616195125307531491788729 19962146343980648618841547)
              ·
                refine ⟨29943219515970972928262321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19962146343980648618841547 29943219515970972928262321)
                ·
                  refine ⟨22457414636978229696196741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29943219515970972928262321 22457414636978229696196741)
                  ·
                    refine ⟨4210765244433418068036889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22457414636978229696196741 4210765244433418068036889)
                    ·
                      refine ⟨3158073933325063551027667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210765244433418068036889 3158073933325063551027667)
                      ·
                        rfl

theorem cell23_6150327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_6150327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150327 prefixEnd_6150327 := by exact prefixLift 6150327
  have htrace : WordTrace (prefixWord ++ tailWord_6150327) baseStart_6150327 baseEnd_6150327 := by
    simpa [prefixWord, tailWord_6150327, baseEnd_6150327] using wordTrace_append hprefix tailTrace_6150327
  have hstable : (prefixWord ++ tailWord_6150327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150327).length < 2 ^ (prefixWord ++ tailWord_6150327).sum := by decide
  have hdescent : baseEnd_6150327 < baseStart_6150327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150330 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3]
def baseStart_6150330 : Nat := 118140960795 + 6150330 * 2 ^ 59
def prefixEnd_6150330 : Nat := 4983230072969 + 3 ^ 40 * 6150330 * 2
def baseEnd_6150330 : Nat := 3158075473767027039290153

theorem tailTrace_6150330 : CollatzResearch.WordTrace tailWord_6150330 prefixEnd_6150330 3158075473767027039290153 := by
  unfold tailWord_6150330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56080240952103069395768111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149547309205608185055381629 56080240952103069395768111)
  ·
    refine ⟨84120361428154604093652167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56080240952103069395768111 84120361428154604093652167)
    ·
      refine ⟨126180542142231906140478251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84120361428154604093652167 126180542142231906140478251)
      ·
        refine ⟨189270813213347859210717377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126180542142231906140478251 189270813213347859210717377)
        ·
          refine ⟨141953109910010894408038033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189270813213347859210717377 141953109910010894408038033)
          ·
            refine ⟨106464832432508170806028525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141953109910010894408038033 106464832432508170806028525)
            ·
              refine ⟨39924312162190564052260697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106464832432508170806028525 39924312162190564052260697)
              ·
                refine ⟨29943234121642923039195523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39924312162190564052260697 29943234121642923039195523)
                ·
                  refine ⟨44914851182464384558793285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29943234121642923039195523 44914851182464384558793285)
                  ·
                    refine ⟨8421534596712072104773741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44914851182464384558793285 8421534596712072104773741)
                    ·
                      refine ⟨3158075473767027039290153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8421534596712072104773741 3158075473767027039290153)
                      ·
                        rfl

theorem cell23_6150330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_6150330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150330 prefixEnd_6150330 := by exact prefixLift 6150330
  have htrace : WordTrace (prefixWord ++ tailWord_6150330) baseStart_6150330 baseEnd_6150330 := by
    simpa [prefixWord, tailWord_6150330, baseEnd_6150330] using wordTrace_append hprefix tailTrace_6150330
  have hstable : (prefixWord ++ tailWord_6150330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150330).length < 2 ^ (prefixWord ++ tailWord_6150330).sum := by decide
  have hdescent : baseEnd_6150330 < baseStart_6150330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150343 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_6150343 : Nat := 118140960795 + 6150343 * 2 ^ 59
def prefixEnd_6150343 : Nat := 4983230072969 + 3 ^ 40 * 6150343 * 2
def baseEnd_6150343 : Nat := 3158082149015535488427593

theorem tailTrace_6150343 : CollatzResearch.WordTrace tailWord_6150343 prefixEnd_6150343 3158082149015535488427593 := by
  unfold tailWord_6150343
  simp only [CollatzResearch.WordTrace]
  refine ⟨224321437957365180803295683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149547625304910120535530455 224321437957365180803295683)
  ·
    refine ⟨336482156936047771204943525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224321437957365180803295683 336482156936047771204943525)
    ·
      refine ⟨63090404425508957100926911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336482156936047771204943525 63090404425508957100926911)
      ·
        refine ⟨94635606638263435651390367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63090404425508957100926911 94635606638263435651390367)
        ·
          refine ⟨141953409957395153477085551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94635606638263435651390367 141953409957395153477085551)
          ·
            refine ⟨212930114936092730215628327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141953409957395153477085551 212930114936092730215628327)
            ·
              refine ⟨319395172404139095323442491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212930114936092730215628327 319395172404139095323442491)
              ·
                refine ⟨479092758606208642985163737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319395172404139095323442491 479092758606208642985163737)
                ·
                  refine ⟨359319568954656482238872803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 479092758606208642985163737 359319568954656482238872803)
                  ·
                    refine ⟨538979353431984723358309205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359319568954656482238872803 538979353431984723358309205)
                    ·
                      refine ⟨3158082149015535488427593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 538979353431984723358309205 3158082149015535488427593)
                      ·
                        rfl

theorem cell23_6150343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_6150343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150343 prefixEnd_6150343 := by exact prefixLift 6150343
  have htrace : WordTrace (prefixWord ++ tailWord_6150343) baseStart_6150343 baseEnd_6150343 := by
    simpa [prefixWord, tailWord_6150343, baseEnd_6150343] using wordTrace_append hprefix tailTrace_6150343
  have hstable : (prefixWord ++ tailWord_6150343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150343).length < 2 ^ (prefixWord ++ tailWord_6150343).sum := by decide
  have hdescent : baseEnd_6150343 < baseStart_6150343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150350 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 8]
def baseStart_6150350 : Nat := 118140960795 + 6150350 * 2 ^ 59
def prefixEnd_6150350 : Nat := 4983230072969 + 3 ^ 40 * 6150350 * 2
def baseEnd_6150350 : Nat := 350898415931124106782229

theorem tailTrace_6150350 : CollatzResearch.WordTrace tailWord_6150350 prefixEnd_6150350 350898415931124106782229 := by
  unfold tailWord_6150350
  simp only [CollatzResearch.WordTrace]
  refine ⟨28040211658542477624850063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149547795512226547332533669 28040211658542477624850063)
  ·
    refine ⟨42060317487813716437275095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28040211658542477624850063 42060317487813716437275095)
    ·
      refine ⟨63090476231720574655912643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42060317487813716437275095 63090476231720574655912643)
      ·
        refine ⟨94635714347580861983868965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63090476231720574655912643 94635714347580861983868965)
        ·
          refine ⟨17744196440171411621975431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94635714347580861983868965 17744196440171411621975431)
          ·
            refine ⟨26616294660257117432963147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17744196440171411621975431 26616294660257117432963147)
            ·
              refine ⟨39924441990385676149444721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26616294660257117432963147 39924441990385676149444721)
              ·
                refine ⟨29943331492789257112083541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39924441990385676149444721 29943331492789257112083541)
                ·
                  refine ⟨350898415931124106782229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29943331492789257112083541 350898415931124106782229)
                  ·
                    rfl

theorem cell23_6150350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_6150350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150350 prefixEnd_6150350 := by exact prefixLift 6150350
  have htrace : WordTrace (prefixWord ++ tailWord_6150350) baseStart_6150350 baseEnd_6150350 := by
    simpa [prefixWord, tailWord_6150350, baseEnd_6150350] using wordTrace_append hprefix tailTrace_6150350
  have hstable : (prefixWord ++ tailWord_6150350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150350).length < 2 ^ (prefixWord ++ tailWord_6150350).sum := by decide
  have hdescent : baseEnd_6150350 < baseStart_6150350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150371 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 3, 4]
def baseStart_6150371 : Nat := 118140960795 + 6150371 * 2 ^ 59
def prefixEnd_6150371 : Nat := 4983230072969 + 3 ^ 40 * 6150371 * 2
def baseEnd_6150371 : Nat := 1052698842157953792959155

theorem tailTrace_6150371 : CollatzResearch.WordTrace tailWord_6150371 prefixEnd_6150371 1052698842157953792959155 := by
  unfold tailWord_6150371
  simp only [CollatzResearch.WordTrace]
  refine ⟨224322459201263741585314967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149548306134175827723543311 224322459201263741585314967)
  ·
    refine ⟨336483688801895612377972451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224322459201263741585314967 336483688801895612377972451)
    ·
      refine ⟨504725533202843418566958677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336483688801895612377972451 504725533202843418566958677)
      ·
        refine ⟨5914752342220821311331547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 504725533202843418566958677 5914752342220821311331547)
        ·
          refine ⟨8872128513331231966997321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5914752342220821311331547 8872128513331231966997321)
          ·
            refine ⟨6654096384998423975247991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8872128513331231966997321 6654096384998423975247991)
            ·
              refine ⟨9981144577497635962871987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654096384998423975247991 9981144577497635962871987)
              ·
                refine ⟨14971716866246453944307981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9981144577497635962871987 14971716866246453944307981)
                ·
                  refine ⟨5614393824842420229115493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14971716866246453944307981 5614393824842420229115493)
                  ·
                    refine ⟨1052698842157953792959155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614393824842420229115493 1052698842157953792959155)
                    ·
                      rfl

theorem cell23_6150371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 4].length) (baseStart_6150371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150371 prefixEnd_6150371 := by exact prefixLift 6150371
  have htrace : WordTrace (prefixWord ++ tailWord_6150371) baseStart_6150371 baseEnd_6150371 := by
    simpa [prefixWord, tailWord_6150371, baseEnd_6150371] using wordTrace_append hprefix tailTrace_6150371
  have hstable : (prefixWord ++ tailWord_6150371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150371).length < 2 ^ (prefixWord ++ tailWord_6150371).sum := by decide
  have hdescent : baseEnd_6150371 < baseStart_6150371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150380 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_6150380 : Nat := 118140960795 + 6150380 * 2 ^ 59
def prefixEnd_6150380 : Nat := 4983230072969 + 3 ^ 40 * 6150380 * 2
def baseEnd_6150380 : Nat := 1052700382599917281221641

theorem tailTrace_6150380 : CollatzResearch.WordTrace tailWord_6150380 prefixEnd_6150380 1052700382599917281221641 := by
  unfold tailWord_6150380
  simp only [CollatzResearch.WordTrace]
  refine ⟨112161393729115568061196297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149548524972154090748261729 112161393729115568061196297)
  ·
    refine ⟨84121045296836676045897223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112161393729115568061196297 84121045296836676045897223)
    ·
      refine ⟨126181567945255014068845835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84121045296836676045897223 126181567945255014068845835)
      ·
        refine ⟨189272351917882521103268753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126181567945255014068845835 189272351917882521103268753)
        ·
          refine ⟨141954263938411890827451565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189272351917882521103268753 141954263938411890827451565)
          ·
            refine ⟨53232848976904459060294337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141954263938411890827451565 53232848976904459060294337)
            ·
              refine ⟨39924636732678344295220753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53232848976904459060294337 39924636732678344295220753)
              ·
                refine ⟨29943477549508758221415565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39924636732678344295220753 29943477549508758221415565)
                ·
                  refine ⟨11228804081065784333030837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29943477549508758221415565 11228804081065784333030837)
                  ·
                    refine ⟨1052700382599917281221641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11228804081065784333030837 1052700382599917281221641)
                    ·
                      rfl

theorem cell23_6150380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_6150380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150380 prefixEnd_6150380 := by exact prefixLift 6150380
  have htrace : WordTrace (prefixWord ++ tailWord_6150380) baseStart_6150380 baseEnd_6150380 := by
    simpa [prefixWord, tailWord_6150380, baseEnd_6150380] using wordTrace_append hprefix tailTrace_6150380
  have hstable : (prefixWord ++ tailWord_6150380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150380).length < 2 ^ (prefixWord ++ tailWord_6150380).sum := by decide
  have hdescent : baseEnd_6150380 < baseStart_6150380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150387 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 4, 3, 2]
def baseStart_6150387 : Nat := 118140960795 + 6150387 * 2 ^ 59
def prefixEnd_6150387 : Nat := 4983230072969 + 3 ^ 40 * 6150387 * 2
def baseEnd_6150387 : Nat := 3158104742164333316277391

theorem tailTrace_6150387 : CollatzResearch.WordTrace tailWord_6150387 prefixEnd_6150387 3158104742164333316277391 := by
  unfold tailWord_6150387
  simp only [CollatzResearch.WordTrace]
  refine ⟨224323042769205776317897415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149548695179470517545264943 224323042769205776317897415)
  ·
    refine ⟨336484564153808664476846123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224323042769205776317897415 336484564153808664476846123)
    ·
      refine ⟨504726846230712996715269185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336484564153808664476846123 504726846230712996715269185)
      ·
        refine ⟨378545134673034747536451889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504726846230712996715269185 378545134673034747536451889)
        ·
          refine ⟨283908851004776060652338917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378545134673034747536451889 283908851004776060652338917)
          ·
            refine ⟨53232909563395511372313547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283908851004776060652338917 53232909563395511372313547)
            ·
              refine ⟨79849364345093267058470321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53232909563395511372313547 79849364345093267058470321)
              ·
                refine ⟨59887023258819950293852741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79849364345093267058470321 59887023258819950293852741)
                ·
                  refine ⟨11228816861028740680097389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59887023258819950293852741 11228816861028740680097389)
                  ·
                    refine ⟨4210806322885777755036521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11228816861028740680097389 4210806322885777755036521)
                    ·
                      refine ⟨3158104742164333316277391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4210806322885777755036521 3158104742164333316277391)
                      ·
                        rfl

theorem cell23_6150387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 3, 2].length) (baseStart_6150387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150387 prefixEnd_6150387 := by exact prefixLift 6150387
  have htrace : WordTrace (prefixWord ++ tailWord_6150387) baseStart_6150387 baseEnd_6150387 := by
    simpa [prefixWord, tailWord_6150387, baseEnd_6150387] using wordTrace_append hprefix tailTrace_6150387
  have hstable : (prefixWord ++ tailWord_6150387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150387).length < 2 ^ (prefixWord ++ tailWord_6150387).sum := by decide
  have hdescent : baseEnd_6150387 < baseStart_6150387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150410 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 3, 6]
def baseStart_6150410 : Nat := 118140960795 + 6150410 * 2 ^ 59
def prefixEnd_6150410 : Nat := 4983230072969 + 3 ^ 40 * 6150410 * 2
def baseEnd_6150410 : Nat := 1052705517406462242096595

theorem tailTrace_6150410 : CollatzResearch.WordTrace tailWord_6150410 prefixEnd_6150410 1052705517406462242096595 := by
  unfold tailWord_6150410
  simp only [CollatzResearch.WordTrace]
  refine ⟨56080970412030612811496171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149549254432081634163989789 56080970412030612811496171)
  ·
    refine ⟨84121455618045919217244257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56080970412030612811496171 84121455618045919217244257)
    ·
      refine ⟨63091091713534439412933193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84121455618045919217244257 63091091713534439412933193)
      ·
        refine ⟨47318318785150829559699895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63091091713534439412933193 47318318785150829559699895)
        ·
          refine ⟨70977478177726244339549843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47318318785150829559699895 70977478177726244339549843)
          ·
            refine ⟨106466217266589366509324765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70977478177726244339549843 106466217266589366509324765)
            ·
              refine ⟨39924831474971012440996787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106466217266589366509324765 39924831474971012440996787)
              ·
                refine ⟨59887247212456518661495181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39924831474971012440996787 59887247212456518661495181)
                ·
                  refine ⟨22457717704671194498060693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59887247212456518661495181 22457717704671194498060693)
                  ·
                    refine ⟨1052705517406462242096595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22457717704671194498060693 1052705517406462242096595)
                    ·
                      rfl

theorem cell23_6150410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_6150410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150410 prefixEnd_6150410 := by exact prefixLift 6150410
  have htrace : WordTrace (prefixWord ++ tailWord_6150410) baseStart_6150410 baseEnd_6150410 := by
    simpa [prefixWord, tailWord_6150410, baseEnd_6150410] using wordTrace_append hprefix tailTrace_6150410
  have hstable : (prefixWord ++ tailWord_6150410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150410).length < 2 ^ (prefixWord ++ tailWord_6150410).sum := by decide
  have hdescent : baseEnd_6150410 < baseStart_6150410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150414 : List Nat := [4, 1, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_6150414 : Nat := 118140960795 + 6150414 * 2 ^ 59
def prefixEnd_6150414 : Nat := 4983230072969 + 3 ^ 40 * 6150414 * 2
def baseEnd_6150414 : Nat := 1052706202047334903546589

theorem tailTrace_6150414 : CollatzResearch.WordTrace tailWord_6150414 prefixEnd_6150414 1052706202047334903546589 := by
  unfold tailWord_6150414
  simp only [CollatzResearch.WordTrace]
  refine ⟨28040503442513494991141287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149549351693405306619420197 28040503442513494991141287)
  ·
    refine ⟨42060755163770242486711931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28040503442513494991141287 42060755163770242486711931)
    ·
      refine ⟨63091132745655363730067897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42060755163770242486711931 63091132745655363730067897)
      ·
        refine ⟨47318349559241522797550923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63091132745655363730067897 47318349559241522797550923)
        ·
          refine ⟨70977524338862284196326385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47318349559241522797550923 70977524338862284196326385)
          ·
            refine ⟨53233143254146713147244789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70977524338862284196326385 53233143254146713147244789)
            ·
              refine ⟨4990607180076254357554199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53233143254146713147244789 4990607180076254357554199)
              ·
                refine ⟨7485910770114381536331299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4990607180076254357554199 7485910770114381536331299)
                ·
                  refine ⟨11228866155171572304496949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7485910770114381536331299 11228866155171572304496949)
                  ·
                    refine ⟨1052706202047334903546589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11228866155171572304496949 1052706202047334903546589)
                    ·
                      rfl

theorem cell23_6150414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_6150414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150414 prefixEnd_6150414 := by exact prefixLift 6150414
  have htrace : WordTrace (prefixWord ++ tailWord_6150414) baseStart_6150414 baseEnd_6150414 := by
    simpa [prefixWord, tailWord_6150414, baseEnd_6150414] using wordTrace_append hprefix tailTrace_6150414
  have hstable : (prefixWord ++ tailWord_6150414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150414).length < 2 ^ (prefixWord ++ tailWord_6150414).sum := by decide
  have hdescent : baseEnd_6150414 < baseStart_6150414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150427 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 2, 4]
def baseStart_6150427 : Nat := 118140960795 + 6150427 * 2 ^ 59
def prefixEnd_6150427 : Nat := 4983230072969 + 3 ^ 40 * 6150427 * 2
def baseEnd_6150427 : Nat := 1052708427130171053259069

theorem tailTrace_6150427 : CollatzResearch.WordTrace tailWord_6150427 prefixEnd_6150427 1052708427130171053259069 := by
  unfold tailWord_6150427
  simp only [CollatzResearch.WordTrace]
  refine ⟨224324501689060863149353535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149549667792707242099569023 224324501689060863149353535)
  ·
    refine ⟨336486752533591294724030303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224324501689060863149353535 336486752533591294724030303)
    ·
      refine ⟨504730128800386942086045455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336486752533591294724030303 504730128800386942086045455)
      ·
        refine ⟨757095193200580413129068183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504730128800386942086045455 757095193200580413129068183)
        ·
          refine ⟨1135642789800870619693602275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757095193200580413129068183 1135642789800870619693602275)
          ·
            refine ⟨1703464184701305929540403413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135642789800870619693602275 1703464184701305929540403413)
            ·
              refine ⟨39924941828936857723603205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1703464184701305929540403413 39924941828936857723603205)
              ·
                refine ⟨7485926592925660823175601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39924941828936857723603205 7485926592925660823175601)
                ·
                  refine ⟨5614444944694245617381701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7485926592925660823175601 5614444944694245617381701)
                  ·
                    refine ⟨1052708427130171053259069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614444944694245617381701 1052708427130171053259069)
                    ·
                      rfl

theorem cell23_6150427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 4].length) (baseStart_6150427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150427 prefixEnd_6150427 := by exact prefixLift 6150427
  have htrace : WordTrace (prefixWord ++ tailWord_6150427) baseStart_6150427 baseEnd_6150427 := by
    simpa [prefixWord, tailWord_6150427, baseEnd_6150427] using wordTrace_append hprefix tailTrace_6150427
  have hstable : (prefixWord ++ tailWord_6150427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150427).length < 2 ^ (prefixWord ++ tailWord_6150427).sum := by decide
  have hdescent : baseEnd_6150427 < baseStart_6150427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150467 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 3]
def baseStart_6150467 : Nat := 118140960795 + 6150467 * 2 ^ 59
def prefixEnd_6150467 : Nat := 4983230072969 + 3 ^ 40 * 6150467 * 2
def baseEnd_6150467 : Nat := 3158145820616693003277023

theorem tailTrace_6150467 : CollatzResearch.WordTrace tailWord_6150467 prefixEnd_6150467 3158145820616693003277023 := by
  unfold tailWord_6150467
  simp only [CollatzResearch.WordTrace]
  refine ⟨224325960608915949980809655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149550640405943966653873103 224325960608915949980809655)
  ·
    refine ⟨336488940913373924971214483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224325960608915949980809655 336488940913373924971214483)
    ·
      refine ⟨504733411370060887456821725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336488940913373924971214483 504733411370060887456821725)
      ·
        refine ⟨189275029263772832796308147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 504733411370060887456821725 189275029263772832796308147)
        ·
          refine ⟨283912543895659249194462221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189275029263772832796308147 283912543895659249194462221)
          ·
            refine ⟨106467203960872218447923333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283912543895659249194462221 106467203960872218447923333)
            ·
              refine ⟨19962600742663540958985625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106467203960872218447923333 19962600742663540958985625)
              ·
                refine ⟨14971950556997655719239219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19962600742663540958985625 14971950556997655719239219)
                ·
                  refine ⟨22457925835496483578858829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14971950556997655719239219 22457925835496483578858829)
                  ·
                    refine ⟨8421722188311181342072061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22457925835496483578858829 8421722188311181342072061)
                    ·
                      refine ⟨3158145820616693003277023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8421722188311181342072061 3158145820616693003277023)
                      ·
                        rfl

theorem cell23_6150467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_6150467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150467 prefixEnd_6150467 := by exact prefixLift 6150467
  have htrace : WordTrace (prefixWord ++ tailWord_6150467) baseStart_6150467 baseEnd_6150467 := by
    simpa [prefixWord, tailWord_6150467, baseEnd_6150467] using wordTrace_append hprefix tailTrace_6150467
  have hstable : (prefixWord ++ tailWord_6150467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150467).length < 2 ^ (prefixWord ++ tailWord_6150467).sum := by decide
  have hdescent : baseEnd_6150467 < baseStart_6150467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150624 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 3, 4]
def baseStart_6150624 : Nat := 118140960795 + 6150624 * 2 ^ 59
def prefixEnd_6150624 : Nat := 4983230072969 + 3 ^ 40 * 6150624 * 2
def baseEnd_6150624 : Nat := 1052742145693149629671267

theorem tailTrace_6150624 : CollatzResearch.WordTrace tailWord_6150624 prefixEnd_6150624 1052742145693149629671267 := by
  unfold tailWord_6150624
  simp only [CollatzResearch.WordTrace]
  refine ⟨112165843434673582897137463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149554457912898110529516617 112165843434673582897137463)
  ·
    refine ⟨168248765152010374345706195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112165843434673582897137463 168248765152010374345706195)
    ·
      refine ⟨252373147728015561518559293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168248765152010374345706195 252373147728015561518559293)
      ·
        refine ⟨94639930398005835569459735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252373147728015561518559293 94639930398005835569459735)
        ·
          refine ⟨141959895597008753354189603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94639930398005835569459735 141959895597008753354189603)
          ·
            refine ⟨212939843395513130031284405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141959895597008753354189603 212939843395513130031284405)
            ·
              refine ⟨19963110318329355940432913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212939843395513130031284405 19963110318329355940432913)
              ·
                refine ⟨14972332738747016955324685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19963110318329355940432913 14972332738747016955324685)
                ·
                  refine ⟨5614624777030131358246757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14972332738747016955324685 5614624777030131358246757)
                  ·
                    refine ⟨1052742145693149629671267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614624777030131358246757 1052742145693149629671267)
                    ·
                      rfl

theorem cell23_6150624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_6150624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150624 prefixEnd_6150624 := by exact prefixLift 6150624
  have htrace : WordTrace (prefixWord ++ tailWord_6150624) baseStart_6150624 baseEnd_6150624 := by
    simpa [prefixWord, tailWord_6150624, baseEnd_6150624] using wordTrace_append hprefix tailTrace_6150624
  have hstable : (prefixWord ++ tailWord_6150624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150624).length < 2 ^ (prefixWord ++ tailWord_6150624).sum := by decide
  have hdescent : baseEnd_6150624 < baseStart_6150624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150691 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 1, 5, 2]
def baseStart_6150691 : Nat := 118140960795 + 6150691 * 2 ^ 59
def prefixEnd_6150691 : Nat := 4983230072969 + 3 ^ 40 * 6150691 * 2
def baseEnd_6150691 : Nat := 3158260840283300126875993

theorem tailTrace_6150691 : CollatzResearch.WordTrace tailWord_6150691 prefixEnd_6150691 3158260840283300126875993 := by
  unfold tailWord_6150691
  simp only [CollatzResearch.WordTrace]
  refine ⟨224334130560104436236963927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149556087040069624157975951 224334130560104436236963927)
  ·
    refine ⟨336501195840156654355445891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224334130560104436236963927 336501195840156654355445891)
    ·
      refine ⟨504751793760234981533168837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336501195840156654355445891 504751793760234981533168837)
      ·
        refine ⟨94640961330044059037469157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 504751793760234981533168837 94640961330044059037469157)
        ·
          refine ⟨17745180249383261069525467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94640961330044059037469157 17745180249383261069525467)
          ·
            refine ⟨26617770374074891604288201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17745180249383261069525467 26617770374074891604288201)
            ·
              refine ⟨19963327780556168703216151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26617770374074891604288201 19963327780556168703216151)
              ·
                refine ⟨29944991670834253054824227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19963327780556168703216151 29944991670834253054824227)
                ·
                  refine ⟨44917487506251379582236341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29944991670834253054824227 44917487506251379582236341)
                  ·
                    refine ⟨4211014453711066835834657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44917487506251379582236341 4211014453711066835834657)
                    ·
                      refine ⟨3158260840283300126875993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211014453711066835834657 3158260840283300126875993)
                      ·
                        rfl

theorem cell23_6150691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_6150691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150691 prefixEnd_6150691 := by exact prefixLift 6150691
  have htrace : WordTrace (prefixWord ++ tailWord_6150691) baseStart_6150691 baseEnd_6150691 := by
    simpa [prefixWord, tailWord_6150691, baseEnd_6150691] using wordTrace_append hprefix tailTrace_6150691
  have hstable : (prefixWord ++ tailWord_6150691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150691).length < 2 ^ (prefixWord ++ tailWord_6150691).sum := by decide
  have hdescent : baseEnd_6150691 < baseStart_6150691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150692 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_6150692 : Nat := 118140960795 + 6150692 * 2 ^ 59
def prefixEnd_6150692 : Nat := 4983230072969 + 3 ^ 40 * 6150692 * 2
def baseEnd_6150692 : Nat := 1052753784587984874321163

theorem tailTrace_6150692 : CollatzResearch.WordTrace tailWord_6150692 prefixEnd_6150692 1052753784587984874321163 := by
  unfold tailWord_6150692
  simp only [CollatzResearch.WordTrace]
  refine ⟨112167083516550406703875165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149556111355400542271833553 112167083516550406703875165)
  ·
    refine ⟨42062656318706402513953187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112167083516550406703875165 42062656318706402513953187)
    ·
      refine ⟨63093984478059603770929781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42062656318706402513953187 63093984478059603770929781)
      ·
        refine ⟨5915061044818087853524667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63093984478059603770929781 5915061044818087853524667)
        ·
          refine ⟨8872591567227131780287001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915061044818087853524667 8872591567227131780287001)
          ·
            refine ⟨6654443675420348835215251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8872591567227131780287001 6654443675420348835215251)
            ·
              refine ⟨9981665513130523252822877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654443675420348835215251 9981665513130523252822877)
              ·
                refine ⟨3743124567423946219808579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9981665513130523252822877 3743124567423946219808579)
                ·
                  refine ⟨5614686851135919329712869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743124567423946219808579 5614686851135919329712869)
                  ·
                    refine ⟨1052753784587984874321163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614686851135919329712869 1052753784587984874321163)
                    ·
                      rfl

theorem cell23_6150692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_6150692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150692 prefixEnd_6150692 := by exact prefixLift 6150692
  have htrace : WordTrace (prefixWord ++ tailWord_6150692) baseStart_6150692 baseEnd_6150692 := by
    simpa [prefixWord, tailWord_6150692, baseEnd_6150692] using wordTrace_append hprefix tailTrace_6150692
  have hstable : (prefixWord ++ tailWord_6150692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150692).length < 2 ^ (prefixWord ++ tailWord_6150692).sum := by decide
  have hdescent : baseEnd_6150692 < baseStart_6150692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150734 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_6150734 : Nat := 118140960795 + 6150734 * 2 ^ 59
def prefixEnd_6150734 : Nat := 4983230072969 + 3 ^ 40 * 6150734 * 2
def baseEnd_6150734 : Nat := 3158282919951443458638295

theorem tailTrace_6150734 : CollatzResearch.WordTrace tailWord_6150734 prefixEnd_6150734 3158282919951443458638295 := by
  unfold tailWord_6150734
  simp only [CollatzResearch.WordTrace]
  refine ⟨28041962362368581822597407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149557132599299103053852837 28041962362368581822597407)
  ·
    refine ⟨42062943543552872733896111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28041962362368581822597407 42062943543552872733896111)
    ·
      refine ⟨63094415315329309100844167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42062943543552872733896111 63094415315329309100844167)
      ·
        refine ⟨94641622972993963651266251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63094415315329309100844167 94641622972993963651266251)
        ·
          refine ⟨141962434459490945476899377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94641622972993963651266251 141962434459490945476899377)
          ·
            refine ⟨106471825844618209107674533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141962434459490945476899377 106471825844618209107674533)
            ·
              refine ⟨19963467345865914207688975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106471825844618209107674533 19963467345865914207688975)
              ·
                refine ⟨29945201018798871311533463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19963467345865914207688975 29945201018798871311533463)
                ·
                  refine ⟨44917801528198306967300195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29945201018798871311533463 44917801528198306967300195)
                  ·
                    refine ⟨67376702292297460450950293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44917801528198306967300195 67376702292297460450950293)
                    ·
                      refine ⟨3158282919951443458638295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67376702292297460450950293 3158282919951443458638295)
                      ·
                        rfl

theorem cell23_6150734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_6150734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150734 prefixEnd_6150734 := by exact prefixLift 6150734
  have htrace : WordTrace (prefixWord ++ tailWord_6150734) baseStart_6150734 baseEnd_6150734 := by
    simpa [prefixWord, tailWord_6150734, baseEnd_6150734] using wordTrace_append hprefix tailTrace_6150734
  have hstable : (prefixWord ++ tailWord_6150734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150734).length < 2 ^ (prefixWord ++ tailWord_6150734).sum := by decide
  have hdescent : baseEnd_6150734 < baseStart_6150734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150738 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_6150738 : Nat := 118140960795 + 6150738 * 2 ^ 59
def prefixEnd_6150738 : Nat := 4983230072969 + 3 ^ 40 * 6150738 * 2
def baseEnd_6150738 : Nat := 3158284973874061442988277

theorem tailTrace_6150738 : CollatzResearch.WordTrace tailWord_6150738 prefixEnd_6150738 3158284973874061442988277 := by
  unfold tailWord_6150738
  simp only [CollatzResearch.WordTrace]
  refine ⟨56083961197733540815981217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149557229860622775509283245 56083961197733540815981217)
  ·
    refine ⟨42062970898300155611985913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56083961197733540815981217 42062970898300155611985913)
    ·
      refine ⟨31547228173725116708989435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42062970898300155611985913 31547228173725116708989435)
      ·
        refine ⟨47320842260587675063484153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31547228173725116708989435 47320842260587675063484153)
        ·
          refine ⟨35490631695440756297613115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47320842260587675063484153 35490631695440756297613115)
          ·
            refine ⟨53235947543161134446419673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35490631695440756297613115 53235947543161134446419673)
            ·
              refine ⟨39926960657370850834814755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53235947543161134446419673 39926960657370850834814755)
              ·
                refine ⟨59890440986056276252222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39926960657370850834814755 59890440986056276252222133)
                ·
                  refine ⟨5614728842442775898645825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59890440986056276252222133 5614728842442775898645825)
                  ·
                    refine ⟨4211046631832081923984369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5614728842442775898645825 4211046631832081923984369)
                    ·
                      refine ⟨3158284973874061442988277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211046631832081923984369 3158284973874061442988277)
                      ·
                        rfl

theorem cell23_6150738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_6150738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150738 prefixEnd_6150738 := by exact prefixLift 6150738
  have htrace : WordTrace (prefixWord ++ tailWord_6150738) baseStart_6150738 baseEnd_6150738 := by
    simpa [prefixWord, tailWord_6150738, baseEnd_6150738] using wordTrace_append hprefix tailTrace_6150738
  have hstable : (prefixWord ++ tailWord_6150738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150738).length < 2 ^ (prefixWord ++ tailWord_6150738).sum := by decide
  have hdescent : baseEnd_6150738 < baseStart_6150738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150755 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 1, 2, 2]
def baseStart_6150755 : Nat := 118140960795 + 6150755 * 2 ^ 59
def prefixEnd_6150755 : Nat := 4983230072969 + 3 ^ 40 * 6150755 * 2
def baseEnd_6150755 : Nat := 3158293703045187876475699

theorem tailTrace_6150755 : CollatzResearch.WordTrace tailWord_6150755 prefixEnd_6150755 3158293703045187876475699 := by
  unfold tailWord_6150755
  simp only [CollatzResearch.WordTrace]
  refine ⟨224336464831872575167293719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149557643221248383444862479 224336464831872575167293719)
  ·
    refine ⟨336504697247808862750940579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224336464831872575167293719 336504697247808862750940579)
    ·
      refine ⟨504757045871713294126410869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336504697247808862750940579 504757045871713294126410869)
      ·
        refine ⟨47320973050473121324351019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 504757045871713294126410869 47320973050473121324351019)
        ·
          refine ⟨70981459575709681986526529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47320973050473121324351019 70981459575709681986526529)
          ·
            refine ⟨53236094681782261489894897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70981459575709681986526529 53236094681782261489894897)
            ·
              refine ⟨39927071011336696117421173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53236094681782261489894897 39927071011336696117421173)
              ·
                refine ⟨3743162907312815261008235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39927071011336696117421173 3743162907312815261008235)
                ·
                  refine ⟨5614744360969222891512353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743162907312815261008235 5614744360969222891512353)
                  ·
                    refine ⟨4211058270726917168634265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5614744360969222891512353 4211058270726917168634265)
                    ·
                      refine ⟨3158293703045187876475699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211058270726917168634265 3158293703045187876475699)
                      ·
                        rfl

theorem cell23_6150755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_6150755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150755 prefixEnd_6150755 := by exact prefixLift 6150755
  have htrace : WordTrace (prefixWord ++ tailWord_6150755) baseStart_6150755 baseEnd_6150755 := by
    simpa [prefixWord, tailWord_6150755, baseEnd_6150755] using wordTrace_append hprefix tailTrace_6150755
  have hstable : (prefixWord ++ tailWord_6150755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150755).length < 2 ^ (prefixWord ++ tailWord_6150755).sum := by decide
  have hdescent : baseEnd_6150755 < baseStart_6150755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150788 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_6150788 : Nat := 118140960795 + 6150788 * 2 ^ 59
def prefixEnd_6150788 : Nat := 4983230072969 + 3 ^ 40 * 6150788 * 2
def baseEnd_6150788 : Nat := 3158310647906786247363047

theorem tailTrace_6150788 : CollatzResearch.WordTrace tailWord_6150788 prefixEnd_6150788 3158310647906786247363047 := by
  unfold tailWord_6150788
  simp only [CollatzResearch.WordTrace]
  refine ⟨112168834220376510901622509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149558445627168681202163345 112168834220376510901622509)
  ·
    refine ⟨42063312832641191588108441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112168834220376510901622509 42063312832641191588108441)
    ·
      refine ⟨31547484624480893691081331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42063312832641191588108441 31547484624480893691081331)
      ·
        refine ⟨47321226936721340536621997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31547484624480893691081331 47321226936721340536621997)
        ·
          refine ⟨17745460101270502701233249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47321226936721340536621997 17745460101270502701233249)
          ·
            refine ⟨13309095075952877025924937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17745460101270502701233249 13309095075952877025924937)
            ·
              refine ⟨9981821306964657769443703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13309095075952877025924937 9981821306964657769443703)
              ·
                refine ⟨14972731960446986654165555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9981821306964657769443703 14972731960446986654165555)
                ·
                  refine ⟨22459097940670479981248333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14972731960446986654165555 22459097940670479981248333)
                  ·
                    refine ⟨8422161727751429992968125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22459097940670479981248333 8422161727751429992968125)
                    ·
                      refine ⟨3158310647906786247363047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8422161727751429992968125 3158310647906786247363047)
                      ·
                        rfl

theorem cell23_6150788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_6150788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150788 prefixEnd_6150788 := by exact prefixLift 6150788
  have htrace : WordTrace (prefixWord ++ tailWord_6150788) baseStart_6150788 baseEnd_6150788 := by
    simpa [prefixWord, tailWord_6150788, baseEnd_6150788] using wordTrace_append hprefix tailTrace_6150788
  have hstable : (prefixWord ++ tailWord_6150788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150788).length < 2 ^ (prefixWord ++ tailWord_6150788).sum := by decide
  have hdescent : baseEnd_6150788 < baseStart_6150788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150798 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6150798 : Nat := 118140960795 + 6150798 * 2 ^ 59
def prefixEnd_6150798 : Nat := 4983230072969 + 3 ^ 40 * 6150798 * 2
def baseEnd_6150798 : Nat := 3158315782713331208238001

theorem tailTrace_6150798 : CollatzResearch.WordTrace tailWord_6150798 prefixEnd_6150798 3158315782713331208238001 := by
  unfold tailWord_6150798
  simp only [CollatzResearch.WordTrace]
  refine ⟨28042254146339599188888631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149558688780477862340739365 28042254146339599188888631)
  ·
    refine ⟨42063381219509398783332947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28042254146339599188888631 42063381219509398783332947)
    ·
      refine ⟨63095071829264098174999421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42063381219509398783332947 63095071829264098174999421)
      ·
        refine ⟨23660651935974036815624783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63095071829264098174999421 23660651935974036815624783)
        ·
          refine ⟨35490977903961055223437175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23660651935974036815624783 35490977903961055223437175)
          ·
            refine ⟨53236466855941582835155763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35490977903961055223437175 53236466855941582835155763)
            ·
              refine ⟨79854700283912374252733645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53236466855941582835155763 79854700283912374252733645)
              ·
                refine ⟨29945512606467140344775117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79854700283912374252733645 29945512606467140344775117)
                ·
                  refine ⟨11229567227425177629290669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29945512606467140344775117 11229567227425177629290669)
                  ·
                    refine ⟨4211087710284441610984001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11229567227425177629290669 4211087710284441610984001)
                    ·
                      refine ⟨3158315782713331208238001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211087710284441610984001 3158315782713331208238001)
                      ·
                        rfl

theorem cell23_6150798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6150798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150798 prefixEnd_6150798 := by exact prefixLift 6150798
  have htrace : WordTrace (prefixWord ++ tailWord_6150798) baseStart_6150798 baseEnd_6150798 := by
    simpa [prefixWord, tailWord_6150798, baseEnd_6150798] using wordTrace_append hprefix tailTrace_6150798
  have hstable : (prefixWord ++ tailWord_6150798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150798).length < 2 ^ (prefixWord ++ tailWord_6150798).sum := by decide
  have hdescent : baseEnd_6150798 < baseStart_6150798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150845 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_6150845 : Nat := 118140960795 + 6150845 * 2 ^ 59
def prefixEnd_6150845 : Nat := 4983230072969 + 3 ^ 40 * 6150845 * 2
def baseEnd_6150845 : Nat := 3158339916304092524350285

theorem tailTrace_6150845 : CollatzResearch.WordTrace tailWord_6150845 prefixEnd_6150845 3158339916304092524350285 := by
  unfold tailWord_6150845
  simp only [CollatzResearch.WordTrace]
  refine ⟨224339747401546520538069989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149559831601031013692046659 224339747401546520538069989)
  ·
    refine ⟨42063702637789972600888123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224339747401546520538069989 42063702637789972600888123)
    ·
      refine ⟨63095553956684958901332185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42063702637789972600888123 63095553956684958901332185)
      ·
        refine ⟨47321665467513719175999139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63095553956684958901332185 47321665467513719175999139)
        ·
          refine ⟨70982498201270578763998709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47321665467513719175999139 70982498201270578763998709)
          ·
            refine ⟨6654609206369116759124879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70982498201270578763998709 6654609206369116759124879)
            ·
              refine ⟨9981913809553675138687319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654609206369116759124879 9981913809553675138687319)
              ·
                refine ⟨14972870714330512708030979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9981913809553675138687319 14972870714330512708030979)
                ·
                  refine ⟨22459306071495769062046469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14972870714330512708030979 22459306071495769062046469)
                  ·
                    refine ⟨4211119888405456699133713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22459306071495769062046469 4211119888405456699133713)
                    ·
                      refine ⟨3158339916304092524350285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211119888405456699133713 3158339916304092524350285)
                      ·
                        rfl

theorem cell23_6150845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_6150845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150845 prefixEnd_6150845 := by exact prefixLift 6150845
  have htrace : WordTrace (prefixWord ++ tailWord_6150845) baseStart_6150845 baseEnd_6150845 := by
    simpa [prefixWord, tailWord_6150845, baseEnd_6150845] using wordTrace_append hprefix tailTrace_6150845
  have hstable : (prefixWord ++ tailWord_6150845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150845).length < 2 ^ (prefixWord ++ tailWord_6150845).sum := by decide
  have hdescent : baseEnd_6150845 < baseStart_6150845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150849 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6150849 : Nat := 118140960795 + 6150849 * 2 ^ 59
def prefixEnd_6150849 : Nat := 4983230072969 + 3 ^ 40 * 6150849 * 2
def baseEnd_6150849 : Nat := 3158341970226710508700267

theorem tailTrace_6150849 : CollatzResearch.WordTrace tailWord_6150849 prefixEnd_6150849 3158341970226710508700267 := by
  unfold tailWord_6150849
  simp only [CollatzResearch.WordTrace]
  refine ⟨224339893293532029221215601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149559928862354686147477067 224339893293532029221215601)
  ·
    refine ⟨168254919970149021915911701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224339893293532029221215601 168254919970149021915911701)
    ·
      refine ⟨7886949373600735402308361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168254919970149021915911701 7886949373600735402308361)
      ·
        refine ⟨5915212030200551551731271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7886949373600735402308361 5915212030200551551731271)
        ·
          refine ⟨8872818045300827327596907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915212030200551551731271 8872818045300827327596907)
          ·
            refine ⟨13309227067951240991395361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8872818045300827327596907 13309227067951240991395361)
            ·
              refine ⟨9981920300963430743546521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13309227067951240991395361 9981920300963430743546521)
              ·
                refine ⟨7486440225722573057659891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9981920300963430743546521 7486440225722573057659891)
                ·
                  refine ⟨11229660338583859586489837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486440225722573057659891 11229660338583859586489837)
                  ·
                    refine ⟨4211122626968947344933689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11229660338583859586489837 4211122626968947344933689)
                    ·
                      refine ⟨3158341970226710508700267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211122626968947344933689 3158341970226710508700267)
                      ·
                        rfl

theorem cell23_6150849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6150849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150849 prefixEnd_6150849 := by exact prefixLift 6150849
  have htrace : WordTrace (prefixWord ++ tailWord_6150849) baseStart_6150849 baseEnd_6150849 := by
    simpa [prefixWord, tailWord_6150849, baseEnd_6150849] using wordTrace_append hprefix tailTrace_6150849
  have hstable : (prefixWord ++ tailWord_6150849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150849).length < 2 ^ (prefixWord ++ tailWord_6150849).sum := by decide
  have hdescent : baseEnd_6150849 < baseStart_6150849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150881 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_6150881 : Nat := 118140960795 + 6150881 * 2 ^ 59
def prefixEnd_6150881 : Nat := 4983230072969 + 3 ^ 40 * 6150881 * 2
def baseEnd_6150881 : Nat := 1052786133869218127833373

theorem tailTrace_6150881 : CollatzResearch.WordTrace tailWord_6150881 prefixEnd_6150881 1052786133869218127833373 := by
  unfold tailWord_6150881
  simp only [CollatzResearch.WordTrace]
  refine ⟨224341060429416098686380497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149560706952944065790920331 224341060429416098686380497)
  ·
    refine ⟨168255795322062074014785373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224341060429416098686380497 168255795322062074014785373)
    ·
      refine ⟨63095923245773277755544515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168255795322062074014785373 63095923245773277755544515)
      ·
        refine ⟨94643884868659916633316773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63095923245773277755544515 94643884868659916633316773)
        ·
          refine ⟨17745728412873734368746895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94643884868659916633316773 17745728412873734368746895)
          ·
            refine ⟨26618592619310601553120343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17745728412873734368746895 26618592619310601553120343)
            ·
              refine ⟨39927888928965902329680515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26618592619310601553120343 39927888928965902329680515)
              ·
                refine ⟨59891833393448853494520773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39927888928965902329680515 59891833393448853494520773)
                ·
                  refine ⟨11229718761271660030222645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59891833393448853494520773 11229718761271660030222645)
                  ·
                    refine ⟨1052786133869218127833373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11229718761271660030222645 1052786133869218127833373)
                    ·
                      rfl

theorem cell23_6150881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_6150881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150881 prefixEnd_6150881 := by exact prefixLift 6150881
  have htrace : WordTrace (prefixWord ++ tailWord_6150881) baseStart_6150881 baseEnd_6150881 := by
    simpa [prefixWord, tailWord_6150881, baseEnd_6150881] using wordTrace_append hprefix tailTrace_6150881
  have hstable : (prefixWord ++ tailWord_6150881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150881).length < 2 ^ (prefixWord ++ tailWord_6150881).sum := by decide
  have hdescent : baseEnd_6150881 < baseStart_6150881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150885 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 5]
def baseStart_6150885 : Nat := 118140960795 + 6150885 * 2 ^ 59
def prefixEnd_6150885 : Nat := 4983230072969 + 3 ^ 40 * 6150885 * 2
def baseEnd_6150885 : Nat := 350928939503363596427789

theorem tailTrace_6150885 : CollatzResearch.WordTrace tailWord_6150885 prefixEnd_6150885 350928939503363596427789 := by
  unfold tailWord_6150885
  simp only [CollatzResearch.WordTrace]
  refine ⟨224341206321401607369526109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149560804214267738246350739 224341206321401607369526109)
  ·
    refine ⟨84127952370525602763572291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224341206321401607369526109 84127952370525602763572291)
    ·
      refine ⟨126191928555788404145358437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84127952370525602763572291 126191928555788404145358437)
      ·
        refine ⟨23660986604210325777254707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126191928555788404145358437 23660986604210325777254707)
        ·
          refine ⟨35491479906315488665882061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23660986604210325777254707 35491479906315488665882061)
          ·
            refine ⟨13309304964868308249705773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35491479906315488665882061 13309304964868308249705773)
            ·
              refine ⟨4990989361825615593639665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13309304964868308249705773 4990989361825615593639665)
              ·
                refine ⟨3743242021369211695229749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990989361825615593639665 3743242021369211695229749)
                ·
                  refine ⟨350928939503363596427789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743242021369211695229749 350928939503363596427789)
                  ·
                    rfl

theorem cell23_6150885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_6150885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150885 prefixEnd_6150885 := by exact prefixLift 6150885
  have htrace : WordTrace (prefixWord ++ tailWord_6150885) baseStart_6150885 baseEnd_6150885 := by
    simpa [prefixWord, tailWord_6150885, baseEnd_6150885] using wordTrace_append hprefix tailTrace_6150885
  have hstable : (prefixWord ++ tailWord_6150885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150885).length < 2 ^ (prefixWord ++ tailWord_6150885).sum := by decide
  have hdescent : baseEnd_6150885 < baseStart_6150885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150911 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 5, 4]
def baseStart_6150911 : Nat := 118140960795 + 6150911 * 2 ^ 59
def prefixEnd_6150911 : Nat := 4983230072969 + 3 ^ 40 * 6150911 * 2
def baseEnd_6150911 : Nat := 1052791268675763088708327

theorem tailTrace_6150911 : CollatzResearch.WordTrace tailWord_6150911 prefixEnd_6150911 1052791268675763088708327 := by
  unfold tailWord_6150911
  simp only [CollatzResearch.WordTrace]
  refine ⟨224342154619307413809972587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149561436412871609206648391 224342154619307413809972587)
  ·
    refine ⟨336513231928961120714958881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224342154619307413809972587 336513231928961120714958881)
    ·
      refine ⟨252384923946720840536219161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336513231928961120714958881 252384923946720840536219161)
      ·
        refine ⟨189288692960040630402164371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252384923946720840536219161 189288692960040630402164371)
        ·
          refine ⟨283933039440060945603246557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189288692960040630402164371 283933039440060945603246557)
          ·
            refine ⟨106474889790022854601217459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283933039440060945603246557 106474889790022854601217459)
            ·
              refine ⟨159712334685034281901826189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106474889790022854601217459 159712334685034281901826189)
              ·
                refine ⟨59892125506887855713184821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159712334685034281901826189 59892125506887855713184821)
                ·
                  refine ⟨5614886766270736473111077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59892125506887855713184821 5614886766270736473111077)
                  ·
                    refine ⟨1052791268675763088708327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614886766270736473111077 1052791268675763088708327)
                    ·
                      rfl

theorem cell23_6150911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_6150911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150911 prefixEnd_6150911 := by exact prefixLift 6150911
  have htrace : WordTrace (prefixWord ++ tailWord_6150911) baseStart_6150911 baseEnd_6150911 := by
    simpa [prefixWord, tailWord_6150911, baseEnd_6150911] using wordTrace_append hprefix tailTrace_6150911
  have hstable : (prefixWord ++ tailWord_6150911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150911).length < 2 ^ (prefixWord ++ tailWord_6150911).sum := by decide
  have hdescent : baseEnd_6150911 < baseStart_6150911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150921 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_6150921 : Nat := 118140960795 + 6150921 * 2 ^ 59
def prefixEnd_6150921 : Nat := 4983230072969 + 3 ^ 40 * 6150921 * 2
def baseEnd_6150921 : Nat := 3158378940833834226999935

theorem tailTrace_6150921 : CollatzResearch.WordTrace tailWord_6150921 prefixEnd_6150921 3158378940833834226999935 := by
  unfold tailWord_6150921
  simp only [CollatzResearch.WordTrace]
  refine ⟨224342519349271185517836617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149561679566180790345224411 224342519349271185517836617)
  ·
    refine ⟨168256889511953389138377463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224342519349271185517836617 168256889511953389138377463)
    ·
      refine ⟨252385334267930083707566195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168256889511953389138377463 252385334267930083707566195)
      ·
        refine ⟨378578001401895125561349293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252385334267930083707566195 378578001401895125561349293)
        ·
          refine ⟨141966750525710672085505985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378578001401895125561349293 141966750525710672085505985)
          ·
            refine ⟨106475062894283004064129489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141966750525710672085505985 106475062894283004064129489)
            ·
              refine ⟨79856297170712253048097117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106475062894283004064129489 79856297170712253048097117)
              ·
                refine ⟨29946111439017094893036419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79856297170712253048097117 29946111439017094893036419)
                ·
                  refine ⟨44919167158525642339554629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29946111439017094893036419 44919167158525642339554629)
                  ·
                    refine ⟨8422343842223557938666493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44919167158525642339554629 8422343842223557938666493)
                    ·
                      refine ⟨3158378940833834226999935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8422343842223557938666493 3158378940833834226999935)
                      ·
                        rfl

theorem cell23_6150921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_6150921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150921 prefixEnd_6150921 := by exact prefixLift 6150921
  have htrace : WordTrace (prefixWord ++ tailWord_6150921) baseStart_6150921 baseEnd_6150921 := by
    simpa [prefixWord, tailWord_6150921, baseEnd_6150921] using wordTrace_append hprefix tailTrace_6150921
  have hstable : (prefixWord ++ tailWord_6150921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150921).length < 2 ^ (prefixWord ++ tailWord_6150921).sum := by decide
  have hdescent : baseEnd_6150921 < baseStart_6150921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150938 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3]
def baseStart_6150938 : Nat := 118140960795 + 6150938 * 2 ^ 59
def prefixEnd_6150938 : Nat := 4983230072969 + 3 ^ 40 * 6150938 * 2
def baseEnd_6150938 : Nat := 3158387670004960660487357

theorem tailTrace_6150938 : CollatzResearch.WordTrace tailWord_6150938 prefixEnd_6150938 3158387670004960660487357 := by
  unfold tailWord_6150938
  simp only [CollatzResearch.WordTrace]
  refine ⟨56085784847552399355301367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149562092926806398280803645 56085784847552399355301367)
  ·
    refine ⟨84128677271328599032952051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56085784847552399355301367 84128677271328599032952051)
    ·
      refine ⟨126193015906992898549428077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84128677271328599032952051 126193015906992898549428077)
      ·
        refine ⟨47322380965122336956035529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126193015906992898549428077 47322380965122336956035529)
        ·
          refine ⟨35491785723841752717026647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47322380965122336956035529 35491785723841752717026647)
          ·
            refine ⟨53237678585762629075539971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35491785723841752717026647 53237678585762629075539971)
            ·
              refine ⟨79856517878643943613309957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53237678585762629075539971 79856517878643943613309957)
              ·
                refine ⟨14973097102245739427495617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79856517878643943613309957 14973097102245739427495617)
                ·
                  refine ⟨11229822826684304570621713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14973097102245739427495617 11229822826684304570621713)
                  ·
                    refine ⟨8422367120013228427966285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11229822826684304570621713 8422367120013228427966285)
                    ·
                      refine ⟨3158387670004960660487357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8422367120013228427966285 3158387670004960660487357)
                      ·
                        rfl

theorem cell23_6150938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_6150938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150938 prefixEnd_6150938 := by exact prefixLift 6150938
  have htrace : WordTrace (prefixWord ++ tailWord_6150938) baseStart_6150938 baseEnd_6150938 := by
    simpa [prefixWord, tailWord_6150938, baseEnd_6150938] using wordTrace_append hprefix tailTrace_6150938
  have hstable : (prefixWord ++ tailWord_6150938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150938).length < 2 ^ (prefixWord ++ tailWord_6150938).sum := by decide
  have hdescent : baseEnd_6150938 < baseStart_6150938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6150945 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 1, 4]
def baseStart_6150945 : Nat := 118140960795 + 6150945 * 2 ^ 59
def prefixEnd_6150945 : Nat := 4983230072969 + 3 ^ 40 * 6150945 * 2
def baseEnd_6150945 : Nat := 1052797088123180711033275

theorem tailTrace_6150945 : CollatzResearch.WordTrace tailWord_6150945 prefixEnd_6150945 1052797088123180711033275 := by
  unfold tailWord_6150945
  simp only [CollatzResearch.WordTrace]
  refine ⟨224343394701184237616710289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149562263134122825077806859 224343394701184237616710289)
  ·
    refine ⟨168257546025888178212532717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224343394701184237616710289 168257546025888178212532717)
    ·
      refine ⟨63096579759708066829699769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168257546025888178212532717 63096579759708066829699769)
      ·
        refine ⟨47322434819781050122274827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63096579759708066829699769 47322434819781050122274827)
        ·
          refine ⟨70983652229671575183412241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47322434819781050122274827 70983652229671575183412241)
          ·
            refine ⟨53237739172253681387559181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70983652229671575183412241 53237739172253681387559181)
            ·
              refine ⟨19964152189595130520334693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53237739172253681387559181 19964152189595130520334693)
              ·
                refine ⟨3743278535549086972562755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19964152189595130520334693 3743278535549086972562755)
                ·
                  refine ⟨5614917803323630458844133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743278535549086972562755 5614917803323630458844133)
                  ·
                    refine ⟨1052797088123180711033275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5614917803323630458844133 1052797088123180711033275)
                    ·
                      rfl

theorem cell23_6150945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_6150945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6150945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6150945 prefixEnd_6150945 := by exact prefixLift 6150945
  have htrace : WordTrace (prefixWord ++ tailWord_6150945) baseStart_6150945 baseEnd_6150945 := by
    simpa [prefixWord, tailWord_6150945, baseEnd_6150945] using wordTrace_append hprefix tailTrace_6150945
  have hstable : (prefixWord ++ tailWord_6150945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6150945).length < 2 ^ (prefixWord ++ tailWord_6150945).sum := by decide
  have hdescent : baseEnd_6150945 < baseStart_6150945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6150945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151002 : List Nat := [3, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3]
def baseStart_6151002 : Nat := 118140960795 + 6151002 * 2 ^ 59
def prefixEnd_6151002 : Nat := 4983230072969 + 3 ^ 40 * 6151002 * 2
def baseEnd_6151002 : Nat := 3158420532766848410087063

theorem tailTrace_6151002 : CollatzResearch.WordTrace tailWord_6151002 prefixEnd_6151002 3158420532766848410087063 := by
  unfold tailWord_6151002
  simp only [CollatzResearch.WordTrace]
  refine ⟨56086368415494434087883815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149563649107985157567690173 56086368415494434087883815)
  ·
    refine ⟨84129552623241651131825723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56086368415494434087883815 84129552623241651131825723)
    ·
      refine ⟨126194328934862476697738585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84129552623241651131825723 126194328934862476697738585)
      ·
        refine ⟨94645746701146857523303939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126194328934862476697738585 94645746701146857523303939)
        ·
          refine ⟨141968620051720286284955909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94645746701146857523303939 141968620051720286284955909)
          ·
            refine ⟨26619116259697553678429233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141968620051720286284955909 26619116259697553678429233)
            ·
              refine ⟨19964337194773165258821925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26619116259697553678429233 19964337194773165258821925)
              ·
                refine ⟨3743313224019968486029111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19964337194773165258821925 3743313224019968486029111)
                ·
                  refine ⟨5614969836029952729043667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3743313224019968486029111 5614969836029952729043667)
                  ·
                    refine ⟨8422454754044929093565501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5614969836029952729043667 8422454754044929093565501)
                    ·
                      refine ⟨3158420532766848410087063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8422454754044929093565501 3158420532766848410087063)
                      ·
                        rfl

theorem cell23_6151002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_6151002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151002 prefixEnd_6151002 := by exact prefixLift 6151002
  have htrace : WordTrace (prefixWord ++ tailWord_6151002) baseStart_6151002 baseEnd_6151002 := by
    simpa [prefixWord, tailWord_6151002, baseEnd_6151002] using wordTrace_append hprefix tailTrace_6151002
  have hstable : (prefixWord ++ tailWord_6151002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151002).length < 2 ^ (prefixWord ++ tailWord_6151002).sum := by decide
  have hdescent : baseEnd_6151002 < baseStart_6151002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151022 : List Nat := [4, 1, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_6151022 : Nat := 118140960795 + 6151022 * 2 ^ 59
def prefixEnd_6151022 : Nat := 4983230072969 + 3 ^ 40 * 6151022 * 2
def baseEnd_6151022 : Nat := 1052810267459979443945657

theorem tailTrace_6151022 : CollatzResearch.WordTrace tailWord_6151022 prefixEnd_6151022 1052810267459979443945657 := by
  unfold tailWord_6151022
  simp only [CollatzResearch.WordTrace]
  refine ⟨28043275390238159970907915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149564135414603519844842213 28043275390238159970907915)
  ·
    refine ⟨42064913085357239956361873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28043275390238159970907915 42064913085357239956361873)
    ·
      refine ⟨31548684814017929967271405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42064913085357239956361873 31548684814017929967271405)
      ·
        refine ⟨11830756805256723737726777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31548684814017929967271405 11830756805256723737726777)
        ·
          refine ⟨8873067603942542803295083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11830756805256723737726777 8873067603942542803295083)
          ·
            refine ⟨13309601405913814204942625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8873067603942542803295083 13309601405913814204942625)
            ·
              refine ⟨9982201054435360653706969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13309601405913814204942625 9982201054435360653706969)
              ·
                refine ⟨7486650790826520490280227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9982201054435360653706969 7486650790826520490280227)
                ·
                  refine ⟨11229976186239780735420341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486650790826520490280227 11229976186239780735420341)
                  ·
                    refine ⟨1052810267459979443945657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11229976186239780735420341 1052810267459979443945657)
                    ·
                      rfl

theorem cell23_6151022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_6151022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151022 prefixEnd_6151022 := by exact prefixLift 6151022
  have htrace : WordTrace (prefixWord ++ tailWord_6151022) baseStart_6151022 baseEnd_6151022 := by
    simpa [prefixWord, tailWord_6151022, baseEnd_6151022] using wordTrace_append hprefix tailTrace_6151022
  have hstable : (prefixWord ++ tailWord_6151022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151022).length < 2 ^ (prefixWord ++ tailWord_6151022).sum := by decide
  have hdescent : baseEnd_6151022 < baseStart_6151022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151025 : List Nat := [1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_6151025 : Nat := 118140960795 + 6151025 * 2 ^ 59
def prefixEnd_6151025 : Nat := 4983230072969 + 3 ^ 40 * 6151025 * 2
def baseEnd_6151025 : Nat := 3158432342821901820099457

theorem tailTrace_6151025 : CollatzResearch.WordTrace tailWord_6151025 prefixEnd_6151025 3158432342821901820099457 := by
  unfold tailWord_6151025
  simp only [CollatzResearch.WordTrace]
  refine ⟨224346312540894411279622529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149564208360596274186415019 224346312540894411279622529)
  ·
    refine ⟨168259734405670808459716897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224346312540894411279622529 168259734405670808459716897)
    ·
      refine ⟨126194800804253106344787673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168259734405670808459716897 126194800804253106344787673)
      ·
        refine ⟨94646100603189829758590755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126194800804253106344787673 94646100603189829758590755)
        ·
          refine ⟨141969150904784744637886133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94646100603189829758590755 141969150904784744637886133)
          ·
            refine ⟨13309607897323569809801825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141969150904784744637886133 13309607897323569809801825)
            ·
              refine ⟨9982205922992677357351369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13309607897323569809801825 9982205922992677357351369)
              ·
                refine ⟨7486654442244508018013527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9982205922992677357351369 7486654442244508018013527)
                ·
                  refine ⟨11229981663366762027020291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486654442244508018013527 11229981663366762027020291)
                  ·
                    refine ⟨16844972495050143040530437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11229981663366762027020291 16844972495050143040530437)
                    ·
                      refine ⟨3158432342821901820099457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16844972495050143040530437 3158432342821901820099457)
                      ·
                        rfl

theorem cell23_6151025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_6151025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151025 prefixEnd_6151025 := by exact prefixLift 6151025
  have htrace : WordTrace (prefixWord ++ tailWord_6151025) baseStart_6151025 baseEnd_6151025 := by
    simpa [prefixWord, tailWord_6151025, baseEnd_6151025] using wordTrace_append hprefix tailTrace_6151025
  have hstable : (prefixWord ++ tailWord_6151025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151025).length < 2 ^ (prefixWord ++ tailWord_6151025).sum := by decide
  have hdescent : baseEnd_6151025 < baseStart_6151025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151045 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_6151045 : Nat := 118140960795 + 6151045 * 2 ^ 59
def prefixEnd_6151045 : Nat := 4983230072969 + 3 ^ 40 * 6151045 * 2
def baseEnd_6151045 : Nat := 3158442612434991741849365

theorem tailTrace_6151045 : CollatzResearch.WordTrace tailWord_6151045 prefixEnd_6151045 3158442612434991741849365 := by
  unfold tailWord_6151045
  simp only [CollatzResearch.WordTrace]
  refine ⟨224347042000821954695350589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149564694667214636463567059 224347042000821954695350589)
  ·
    refine ⟨84130140750308233010756471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224347042000821954695350589 84130140750308233010756471)
    ·
      refine ⟨126195211125462349516134707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84130140750308233010756471 126195211125462349516134707)
      ·
        refine ⟨189292816688193524274202061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126195211125462349516134707 189292816688193524274202061)
        ·
          refine ⟨70984806258072571602825773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189292816688193524274202061 70984806258072571602825773)
          ·
            refine ⟨26619302346777214351059665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70984806258072571602825773 26619302346777214351059665)
            ·
              refine ⟨19964476760082910763294749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26619302346777214351059665 19964476760082910763294749)
              ·
                refine ⟨7486678785031091536235531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19964476760082910763294749 7486678785031091536235531)
                ·
                  refine ⟨11230018177546637304353297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486678785031091536235531 11230018177546637304353297)
                  ·
                    refine ⟨8422513633159977978264973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11230018177546637304353297 8422513633159977978264973)
                    ·
                      refine ⟨3158442612434991741849365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8422513633159977978264973 3158442612434991741849365)
                      ·
                        rfl

theorem cell23_6151045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_6151045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151045 prefixEnd_6151045 := by exact prefixLift 6151045
  have htrace : WordTrace (prefixWord ++ tailWord_6151045) baseStart_6151045 baseEnd_6151045 := by
    simpa [prefixWord, tailWord_6151045, baseEnd_6151045] using wordTrace_append hprefix tailTrace_6151045
  have hstable : (prefixWord ++ tailWord_6151045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151045).length < 2 ^ (prefixWord ++ tailWord_6151045).sum := by decide
  have hdescent : baseEnd_6151045 < baseStart_6151045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151048 : List Nat := [2, 1, 3, 3, 2, 3, 9]
def baseStart_6151048 : Nat := 118140960795 + 6151048 * 2 ^ 59
def prefixEnd_6151048 : Nat := 4983230072969 + 3 ^ 40 * 6151048 * 2
def baseEnd_6151048 : Nat := 38993137689838953458171

theorem tailTrace_6151048 : CollatzResearch.WordTrace tailWord_6151048 prefixEnd_6151048 38993137689838953458171 := by
  unfold tailWord_6151048
  simp only [CollatzResearch.WordTrace]
  refine ⟨112173575709905543103854899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149564767613207390805139865 112173575709905543103854899)
  ·
    refine ⟨168260363564858314655782349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112173575709905543103854899 168260363564858314655782349)
    ·
      refine ⟨63097636336821867995918381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168260363564858314655782349 63097636336821867995918381)
      ·
        refine ⟨23661613626308200498469393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63097636336821867995918381 23661613626308200498469393)
        ·
          refine ⟨17746210219731150373852045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23661613626308200498469393 17746210219731150373852045)
          ·
            refine ⟨6654828832399181390194517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17746210219731150373852045 6654828832399181390194517)
            ·
              refine ⟨38993137689838953458171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6654828832399181390194517 38993137689838953458171)
              ·
                rfl

theorem cell23_6151048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 9].length) (baseStart_6151048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151048 prefixEnd_6151048 := by exact prefixLift 6151048
  have htrace : WordTrace (prefixWord ++ tailWord_6151048) baseStart_6151048 baseEnd_6151048 := by
    simpa [prefixWord, tailWord_6151048, baseEnd_6151048] using wordTrace_append hprefix tailTrace_6151048
  have hstable : (prefixWord ++ tailWord_6151048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151048).length < 2 ^ (prefixWord ++ tailWord_6151048).sum := by decide
  have hdescent : baseEnd_6151048 < baseStart_6151048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151079 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_6151079 : Nat := 118140960795 + 6151079 * 2 ^ 59
def prefixEnd_6151079 : Nat := 4983230072969 + 3 ^ 40 * 6151079 * 2
def baseEnd_6151079 : Nat := 3158460070777244608824209

theorem tailTrace_6151079 : CollatzResearch.WordTrace tailWord_6151079 prefixEnd_6151079 3158460070777244608824209 := by
  unfold tailWord_6151079
  simp only [CollatzResearch.WordTrace]
  refine ⟨224348282082698778502088291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149565521388465852334725527 224348282082698778502088291)
  ·
    refine ⟨336522423124048167753132437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224348282082698778502088291 336522423124048167753132437)
    ·
      refine ⟨15774488583939757863428083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 336522423124048167753132437 15774488583939757863428083)
      ·
        refine ⟨23661732875909636795142125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15774488583939757863428083 23661732875909636795142125)
        ·
          refine ⟨8873149828466113798178297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23661732875909636795142125 8873149828466113798178297)
          ·
            refine ⟨6654862371349585348633723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8873149828466113798178297 6654862371349585348633723)
            ·
              refine ⟨9982293557024378022950585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6654862371349585348633723 9982293557024378022950585)
              ·
                refine ⟨7486720167768283517212939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9982293557024378022950585 7486720167768283517212939)
                ·
                  refine ⟨11230080251652425275819409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7486720167768283517212939 11230080251652425275819409)
                  ·
                    refine ⟨8422560188739318956864557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11230080251652425275819409 8422560188739318956864557)
                    ·
                      refine ⟨3158460070777244608824209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8422560188739318956864557 3158460070777244608824209)
                      ·
                        rfl

theorem cell23_6151079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_6151079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151079 prefixEnd_6151079 := by exact prefixLift 6151079
  have htrace : WordTrace (prefixWord ++ tailWord_6151079) baseStart_6151079 baseEnd_6151079 := by
    simpa [prefixWord, tailWord_6151079, baseEnd_6151079] using wordTrace_append hprefix tailTrace_6151079
  have hstable : (prefixWord ++ tailWord_6151079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151079).length < 2 ^ (prefixWord ++ tailWord_6151079).sum := by decide
  have hdescent : baseEnd_6151079 < baseStart_6151079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151091 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 3, 8]
def baseStart_6151091 : Nat := 118140960795 + 6151091 * 2 ^ 59
def prefixEnd_6151091 : Nat := 4983230072969 + 3 ^ 40 * 6151091 * 2
def baseEnd_6151091 : Nat := 1052822077515032853958051

theorem tailTrace_6151091 : CollatzResearch.WordTrace tailWord_6151091 prefixEnd_6151091 1052822077515032853958051 := by
  unfold tailWord_6151091
  simp only [CollatzResearch.WordTrace]
  refine ⟨224348719758655304551525127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149565813172436869701016751 224348719758655304551525127)
  ·
    refine ⟨336523079637982956827287691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224348719758655304551525127 336523079637982956827287691)
    ·
      refine ⟨504784619456974435240931537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336523079637982956827287691 504784619456974435240931537)
      ·
        refine ⟨378588464592730826430698653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504784619456974435240931537 378588464592730826430698653)
        ·
          refine ⟨141970674222274059911511995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378588464592730826430698653 141970674222274059911511995)
          ·
            refine ⟨212956011333411089867267993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141970674222274059911511995 212956011333411089867267993)
            ·
              refine ⟨159717008500058317400450995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212956011333411089867267993 159717008500058317400450995)
              ·
                refine ⟨239575512750087476100676493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159717008500058317400450995 239575512750087476100676493)
                ·
                  refine ⟨89840817281282803537753685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239575512750087476100676493 89840817281282803537753685)
                  ·
                    refine ⟨1052822077515032853958051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89840817281282803537753685 1052822077515032853958051)
                    ·
                      rfl

theorem cell23_6151091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 8].length) (baseStart_6151091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151091 prefixEnd_6151091 := by exact prefixLift 6151091
  have htrace : WordTrace (prefixWord ++ tailWord_6151091) baseStart_6151091 baseEnd_6151091 := by
    simpa [prefixWord, tailWord_6151091, baseEnd_6151091] using wordTrace_append hprefix tailTrace_6151091
  have hstable : (prefixWord ++ tailWord_6151091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151091).length < 2 ^ (prefixWord ++ tailWord_6151091).sum := by decide
  have hdescent : baseEnd_6151091 < baseStart_6151091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151092 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6151092 : Nat := 118140960795 + 6151092 * 2 ^ 59
def prefixEnd_6151092 : Nat := 4983230072969 + 3 ^ 40 * 6151092 * 2
def baseEnd_6151092 : Nat := 3158466746025753057961649

theorem tailTrace_6151092 : CollatzResearch.WordTrace tailWord_6151092 prefixEnd_6151092 3158466746025753057961649 := by
  unfold tailWord_6151092
  simp only [CollatzResearch.WordTrace]
  refine ⟨112174378115825840861155765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149565837487767787814874353 112174378115825840861155765)
  ·
    refine ⟨10516347948358672580733353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112174378115825840861155765 10516347948358672580733353)
    ·
      refine ⟨7887260961269004435550015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10516347948358672580733353 7887260961269004435550015)
      ·
        refine ⟨11830891441903506653325023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7887260961269004435550015 11830891441903506653325023)
        ·
          refine ⟨17746337162855259979987535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11830891441903506653325023 17746337162855259979987535)
          ·
            refine ⟨26619505744282889969981303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17746337162855259979987535 26619505744282889969981303)
            ·
              refine ⟨39929258616424334954971955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26619505744282889969981303 39929258616424334954971955)
              ·
                refine ⟨59893887924636502432457933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39929258616424334954971955 59893887924636502432457933)
                ·
                  refine ⟨22460207971738688412171725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59893887924636502432457933 22460207971738688412171725)
                  ·
                    refine ⟨8422577989402008154564397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22460207971738688412171725 8422577989402008154564397)
                    ·
                      refine ⟨3158466746025753057961649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8422577989402008154564397 3158466746025753057961649)
                      ·
                        rfl

theorem cell23_6151092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6151092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151092 prefixEnd_6151092 := by exact prefixLift 6151092
  have htrace : WordTrace (prefixWord ++ tailWord_6151092) baseStart_6151092 baseEnd_6151092 := by
    simpa [prefixWord, tailWord_6151092, baseEnd_6151092] using wordTrace_append hprefix tailTrace_6151092
  have hstable : (prefixWord ++ tailWord_6151092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151092).length < 2 ^ (prefixWord ++ tailWord_6151092).sum := by decide
  have hdescent : baseEnd_6151092 < baseStart_6151092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151125 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_6151125 : Nat := 118140960795 + 6151125 * 2 ^ 59
def prefixEnd_6151125 : Nat := 4983230072969 + 3 ^ 40 * 6151125 * 2
def baseEnd_6151125 : Nat := 1052827896962450476282999

theorem tailTrace_6151125 : CollatzResearch.WordTrace tailWord_6151125 prefixEnd_6151125 1052827896962450476282999 := by
  unfold tailWord_6151125
  simp only [CollatzResearch.WordTrace]
  refine ⟨224349959840532128358262829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149566639893688085572175219 224349959840532128358262829)
  ·
    refine ⟨84131234940199548134348561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224349959840532128358262829 84131234940199548134348561)
    ·
      refine ⟨63098426205149661100761421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84131234940199548134348561 63098426205149661100761421)
      ·
        refine ⟨23661909826931122912785533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63098426205149661100761421 23661909826931122912785533)
        ·
          refine ⟨8873216185099171092294575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23661909826931122912785533 8873216185099171092294575)
          ·
            refine ⟨13309824277648756638441863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8873216185099171092294575 13309824277648756638441863)
            ·
              refine ⟨19964736416473134957662795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13309824277648756638441863 19964736416473134957662795)
              ·
                refine ⟨29947104624709702436494193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19964736416473134957662795 29947104624709702436494193)
                ·
                  refine ⟨22460328468532276827370645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29947104624709702436494193 22460328468532276827370645)
                  ·
                    refine ⟨1052827896962450476282999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22460328468532276827370645 1052827896962450476282999)
                    ·
                      rfl

theorem cell23_6151125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_6151125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151125 prefixEnd_6151125 := by exact prefixLift 6151125
  have htrace : WordTrace (prefixWord ++ tailWord_6151125) baseStart_6151125 baseEnd_6151125 := by
    simpa [prefixWord, tailWord_6151125, baseEnd_6151125] using wordTrace_append hprefix tailTrace_6151125
  have hstable : (prefixWord ++ tailWord_6151125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151125).length < 2 ^ (prefixWord ++ tailWord_6151125).sum := by decide
  have hdescent : baseEnd_6151125 < baseStart_6151125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151128 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6151128 : Nat := 118140960795 + 6151128 * 2 ^ 59
def prefixEnd_6151128 : Nat := 4983230072969 + 3 ^ 40 * 6151128 * 2
def baseEnd_6151128 : Nat := 3158485231329314917111483

theorem tailTrace_6151128 : CollatzResearch.WordTrace tailWord_6151128 prefixEnd_6151128 3158485231329314917111483 := by
  unfold tailWord_6151128
  simp only [CollatzResearch.WordTrace]
  refine ⟨112175034629760629935311019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149566712839680839913748025 112175034629760629935311019)
  ·
    refine ⟨168262551944640944902966529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112175034629760629935311019 168262551944640944902966529)
    ·
      refine ⟨126196913958480708677224897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168262551944640944902966529 126196913958480708677224897)
      ·
        refine ⟨94647685468860531507918673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126196913958480708677224897 94647685468860531507918673)
        ·
          refine ⟨70985764101645398630939005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94647685468860531507918673 70985764101645398630939005)
          ·
            refine ⟨26619661538117024486602127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70985764101645398630939005 26619661538117024486602127)
            ·
              refine ⟨39929492307175536729903191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26619661538117024486602127 39929492307175536729903191)
              ·
                refine ⟨59894238460763305094854787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39929492307175536729903191 59894238460763305094854787)
                ·
                  refine ⟨89841357691144957642282181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59894238460763305094854787 89841357691144957642282181)
                  ·
                    refine ⟨16845254567089679557927909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89841357691144957642282181 16845254567089679557927909)
                    ·
                      refine ⟨3158485231329314917111483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16845254567089679557927909 3158485231329314917111483)
                      ·
                        rfl

theorem cell23_6151128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6151128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151128 prefixEnd_6151128 := by exact prefixLift 6151128
  have htrace : WordTrace (prefixWord ++ tailWord_6151128) baseStart_6151128 baseEnd_6151128 := by
    simpa [prefixWord, tailWord_6151128, baseEnd_6151128] using wordTrace_append hprefix tailTrace_6151128
  have hstable : (prefixWord ++ tailWord_6151128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151128).length < 2 ^ (prefixWord ++ tailWord_6151128).sum := by decide
  have hdescent : baseEnd_6151128 < baseStart_6151128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151166 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6151166 : Nat := 118140960795 + 6151166 * 2 ^ 59
def prefixEnd_6151166 : Nat := 4983230072969 + 3 ^ 40 * 6151166 * 2
def baseEnd_6151166 : Nat := 3158504743594185768436309

theorem tailTrace_6151166 : CollatzResearch.WordTrace tailWord_6151166 prefixEnd_6151166 3158504743594185768436309 := by
  unfold tailWord_6151166
  simp only [CollatzResearch.WordTrace]
  refine ⟨28043931904172949045063169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149567636822255728240336901 28043931904172949045063169)
  ·
    refine ⟨21032948928129711783797377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28043931904172949045063169 21032948928129711783797377)
    ·
      refine ⟨15774711696097283837848033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21032948928129711783797377 15774711696097283837848033)
      ·
        refine ⟨11831033772072962878386025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15774711696097283837848033 11831033772072962878386025)
        ·
          refine ⟨8873275329054722158789519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11831033772072962878386025 8873275329054722158789519)
          ·
            refine ⟨13309912993582083238184279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8873275329054722158789519 13309912993582083238184279)
            ·
              refine ⟨19964869490373124857276419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13309912993582083238184279 19964869490373124857276419)
              ·
                refine ⟨29947304235559687285914629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19964869490373124857276419 29947304235559687285914629)
                ·
                  refine ⟨5615119544167441366108993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29947304235559687285914629 5615119544167441366108993)
                  ·
                    refine ⟨4211339658125581024581745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5615119544167441366108993 4211339658125581024581745)
                    ·
                      refine ⟨3158504743594185768436309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211339658125581024581745 3158504743594185768436309)
                      ·
                        rfl

theorem cell23_6151166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6151166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151166 prefixEnd_6151166 := by exact prefixLift 6151166
  have htrace : WordTrace (prefixWord ++ tailWord_6151166) baseStart_6151166 baseEnd_6151166 := by
    simpa [prefixWord, tailWord_6151166, baseEnd_6151166] using wordTrace_append hprefix tailTrace_6151166
  have hstable : (prefixWord ++ tailWord_6151166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151166).length < 2 ^ (prefixWord ++ tailWord_6151166).sum := by decide
  have hdescent : baseEnd_6151166 < baseStart_6151166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151205 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_6151205 : Nat := 118140960795 + 6151205 * 2 ^ 59
def prefixEnd_6151205 : Nat := 4983230072969 + 3 ^ 40 * 6151205 * 2
def baseEnd_6151205 : Nat := 3158524769339711115848629

theorem tailTrace_6151205 : CollatzResearch.WordTrace tailWord_6151205 prefixEnd_6151205 3158524769339711115848629 := by
  unfold tailWord_6151205
  simp only [CollatzResearch.WordTrace]
  refine ⟨224352877680242302021175069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149568585120161534680783379 224352877680242302021175069)
  ·
    refine ⟨84132329130090863257940651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224352877680242302021175069 84132329130090863257940651)
    ·
      refine ⟨126198493695136294886910977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84132329130090863257940651 126198493695136294886910977)
      ·
        refine ⟨94648870271352221165183233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126198493695136294886910977 94648870271352221165183233)
        ·
          refine ⟨70986652703514165873887425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94648870271352221165183233 70986652703514165873887425)
          ·
            refine ⟨53239989527635624405415569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70986652703514165873887425 53239989527635624405415569)
            ·
              refine ⟨39929992145726718304061677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53239989527635624405415569 39929992145726718304061677)
              ·
                refine ⟨14973747054647519364023129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39929992145726718304061677 14973747054647519364023129)
                ·
                  refine ⟨11230310290985639523017347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14973747054647519364023129 11230310290985639523017347)
                  ·
                    refine ⟨16845465436478459284526021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11230310290985639523017347 16845465436478459284526021)
                    ·
                      refine ⟨3158524769339711115848629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16845465436478459284526021 3158524769339711115848629)
                      ·
                        rfl

theorem cell23_6151205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_6151205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151205 prefixEnd_6151205 := by exact prefixLift 6151205
  have htrace : WordTrace (prefixWord ++ tailWord_6151205) baseStart_6151205 baseEnd_6151205 := by
    simpa [prefixWord, tailWord_6151205, baseEnd_6151205] using wordTrace_append hprefix tailTrace_6151205
  have hstable : (prefixWord ++ tailWord_6151205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151205).length < 2 ^ (prefixWord ++ tailWord_6151205).sum := by decide
  have hdescent : baseEnd_6151205 < baseStart_6151205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151222 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_6151222 : Nat := 118140960795 + 6151222 * 2 ^ 59
def prefixEnd_6151222 : Nat := 4983230072969 + 3 ^ 40 * 6151222 * 2
def baseEnd_6151222 : Nat := 3158533498510837549336051

theorem tailTrace_6151222 : CollatzResearch.WordTrace tailWord_6151222 prefixEnd_6151222 3158533498510837549336051 := by
  unfold tailWord_6151222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14022093607573794620283995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149568998480787142616362613 14022093607573794620283995)
  ·
    refine ⟨21033140411360691930425993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14022093607573794620283995 21033140411360691930425993)
    ·
      refine ⟨15774855308520518947819495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21033140411360691930425993 15774855308520518947819495)
      ·
        refine ⟨23662282962780778421729243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15774855308520518947819495 23662282962780778421729243)
        ·
          refine ⟨35493424444171167632593865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23662282962780778421729243 35493424444171167632593865)
          ·
            refine ⟨26620068333128375724445399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35493424444171167632593865 26620068333128375724445399)
            ·
              refine ⟨39930102499692563586668099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26620068333128375724445399 39930102499692563586668099)
              ·
                refine ⟨59895153749538845380002149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39930102499692563586668099 59895153749538845380002149)
                ·
                  refine ⟨11230341328038533508750403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59895153749538845380002149 11230341328038533508750403)
                  ·
                    refine ⟨16845511992057800263125605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11230341328038533508750403 16845511992057800263125605)
                    ·
                      refine ⟨3158533498510837549336051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16845511992057800263125605 3158533498510837549336051)
                      ·
                        rfl

theorem cell23_6151222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_6151222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151222 prefixEnd_6151222 := by exact prefixLift 6151222
  have htrace : WordTrace (prefixWord ++ tailWord_6151222) baseStart_6151222 baseEnd_6151222 := by
    simpa [prefixWord, tailWord_6151222, baseEnd_6151222] using wordTrace_append hprefix tailTrace_6151222
  have hstable : (prefixWord ++ tailWord_6151222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151222).length < 2 ^ (prefixWord ++ tailWord_6151222).sum := by decide
  have hdescent : baseEnd_6151222 < baseStart_6151222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151248 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_6151248 : Nat := 118140960795 + 6151248 * 2 ^ 59
def prefixEnd_6151248 : Nat := 4983230072969 + 3 ^ 40 * 6151248 * 2
def baseEnd_6151248 : Nat := 3158546849007854447610931

theorem tailTrace_6151248 : CollatzResearch.WordTrace tailWord_6151248 prefixEnd_6151248 3158546849007854447610931 := by
  unfold tailWord_6151248
  simp only [CollatzResearch.WordTrace]
  refine ⟨112177223009543260182495199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149569630679391013576660265 112177223009543260182495199)
  ·
    refine ⟨168265834514314890273742799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112177223009543260182495199 168265834514314890273742799)
    ·
      refine ⟨252398751771472335410614199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168265834514314890273742799 252398751771472335410614199)
      ·
        refine ⟨378598127657208503115921299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252398751771472335410614199 378598127657208503115921299)
        ·
          refine ⟨567897191485812754673881949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378598127657208503115921299 567897191485812754673881949)
          ·
            refine ⟨212961446807179783002705731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567897191485812754673881949 212961446807179783002705731)
            ·
              refine ⟨319442170210769674504058597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212961446807179783002705731 319442170210769674504058597)
              ·
                refine ⟨59895406914519313969510987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319442170210769674504058597 59895406914519313969510987)
                ·
                  refine ⟨89843110371778970954266481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59895406914519313969510987 89843110371778970954266481)
                  ·
                    refine ⟨67382332778834228215699861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89843110371778970954266481 67382332778834228215699861)
                    ·
                      refine ⟨3158546849007854447610931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67382332778834228215699861 3158546849007854447610931)
                      ·
                        rfl

theorem cell23_6151248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_6151248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151248 prefixEnd_6151248 := by exact prefixLift 6151248
  have htrace : WordTrace (prefixWord ++ tailWord_6151248) baseStart_6151248 baseEnd_6151248 := by
    simpa [prefixWord, tailWord_6151248, baseEnd_6151248] using wordTrace_append hprefix tailTrace_6151248
  have hstable : (prefixWord ++ tailWord_6151248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151248).length < 2 ^ (prefixWord ++ tailWord_6151248).sum := by decide
  have hdescent : baseEnd_6151248 < baseStart_6151248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151305 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_6151305 : Nat := 118140960795 + 6151305 * 2 ^ 59
def prefixEnd_6151305 : Nat := 4983230072969 + 3 ^ 40 * 6151305 * 2
def baseEnd_6151305 : Nat := 1052858705801720241532723

theorem tailTrace_6151305 : CollatzResearch.WordTrace tailWord_6151305 prefixEnd_6151305 1052858705801720241532723 := by
  unfold tailWord_6151305
  simp only [CollatzResearch.WordTrace]
  refine ⟨224356524979880019099815369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149571016653253346066543579 224356524979880019099815369)
  ·
    refine ⟨168267393734910014324861527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224356524979880019099815369 168267393734910014324861527)
    ·
      refine ⟨252401090602365021487292291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168267393734910014324861527 252401090602365021487292291)
      ·
        refine ⟨378601635903547532230938437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252401090602365021487292291 378601635903547532230938437)
        ·
          refine ⟨70987806731915162293300957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378601635903547532230938437 70987806731915162293300957)
          ·
            refine ⟨26620427524468185859987859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70987806731915162293300957 26620427524468185859987859)
            ·
              refine ⟨39930641286702278789981789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26620427524468185859987859 39930641286702278789981789)
              ·
                refine ⟨14973990482513354546243171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39930641286702278789981789 14973990482513354546243171)
                ·
                  refine ⟨22460985723770031819364757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14973990482513354546243171 22460985723770031819364757)
                  ·
                    refine ⟨1052858705801720241532723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22460985723770031819364757 1052858705801720241532723)
                    ·
                      rfl

theorem cell23_6151305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_6151305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151305 prefixEnd_6151305 := by exact prefixLift 6151305
  have htrace : WordTrace (prefixWord ++ tailWord_6151305) baseStart_6151305 baseEnd_6151305 := by
    simpa [prefixWord, tailWord_6151305, baseEnd_6151305] using wordTrace_append hprefix tailTrace_6151305
  have hstable : (prefixWord ++ tailWord_6151305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151305).length < 2 ^ (prefixWord ++ tailWord_6151305).sum := by decide
  have hdescent : baseEnd_6151305 < baseStart_6151305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151322 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 1, 6]
def baseStart_6151322 : Nat := 118140960795 + 6151322 * 2 ^ 59
def prefixEnd_6151322 : Nat := 4983230072969 + 3 ^ 40 * 6151322 * 2
def baseEnd_6151322 : Nat := 1052861615525429052695197

theorem tailTrace_6151322 : CollatzResearch.WordTrace tailWord_6151322 prefixEnd_6151322 1052861615525429052695197 := by
  unfold tailWord_6151322
  simp only [CollatzResearch.WordTrace]
  refine ⟨56089286255204607750796055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149571430013878954002122813 56089286255204607750796055)
  ·
    refine ⟨84133929382806911626194083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56089286255204607750796055 84133929382806911626194083)
    ·
      refine ⟨126200894074210367439291125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84133929382806911626194083 126200894074210367439291125)
      ·
        refine ⟨11831333819457221947433543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126200894074210367439291125 11831333819457221947433543)
        ·
          refine ⟨17747000729185832921150315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11831333819457221947433543 17747000729185832921150315)
          ·
            refine ⟨26620501093778749381725473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17747000729185832921150315 26620501093778749381725473)
            ·
              refine ⟨19965375820334062036294105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26620501093778749381725473 19965375820334062036294105)
              ·
                refine ⟨14974031865250546527220579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19965375820334062036294105 14974031865250546527220579)
                ·
                  refine ⟨22461047797875819790830869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14974031865250546527220579 22461047797875819790830869)
                  ·
                    refine ⟨1052861615525429052695197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22461047797875819790830869 1052861615525429052695197)
                    ·
                      rfl

theorem cell23_6151322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_6151322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151322 prefixEnd_6151322 := by exact prefixLift 6151322
  have htrace : WordTrace (prefixWord ++ tailWord_6151322) baseStart_6151322 baseEnd_6151322 := by
    simpa [prefixWord, tailWord_6151322, baseEnd_6151322] using wordTrace_append hprefix tailTrace_6151322
  have hstable : (prefixWord ++ tailWord_6151322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151322).length < 2 ^ (prefixWord ++ tailWord_6151322).sum := by decide
  have hdescent : baseEnd_6151322 < baseStart_6151322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151326 : List Nat := [4, 3, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_6151326 : Nat := 118140960795 + 6151326 * 2 ^ 59
def prefixEnd_6151326 : Nat := 4983230072969 + 3 ^ 40 * 6151326 * 2
def baseEnd_6151326 : Nat := 1052862300166301714145191

theorem tailTrace_6151326 : CollatzResearch.WordTrace tailWord_6151326 prefixEnd_6151326 1052862300166301714145191 := by
  unfold tailWord_6151326
  simp only [CollatzResearch.WordTrace]
  refine ⟨28044661364100492460791229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149571527275202626457553221 28044661364100492460791229)
  ·
    refine ⟨10516748011537684672796711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28044661364100492460791229 10516748011537684672796711)
    ·
      refine ⟨15775122017306527009195067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10516748011537684672796711 15775122017306527009195067)
      ·
        refine ⟨23662683025959790513792601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15775122017306527009195067 23662683025959790513792601)
        ·
          refine ⟨17747012269469842885344451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23662683025959790513792601 17747012269469842885344451)
          ·
            refine ⟨26620518404204764328016677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17747012269469842885344451 26620518404204764328016677)
            ·
              refine ⟨4991347200788393311503127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26620518404204764328016677 4991347200788393311503127)
              ·
                refine ⟨7487020801182589967254691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991347200788393311503127 7487020801182589967254691)
                ·
                  refine ⟨11230531201773884950882037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7487020801182589967254691 11230531201773884950882037)
                  ·
                    refine ⟨1052862300166301714145191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11230531201773884950882037 1052862300166301714145191)
                    ·
                      rfl

theorem cell23_6151326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_6151326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151326 prefixEnd_6151326 := by exact prefixLift 6151326
  have htrace : WordTrace (prefixWord ++ tailWord_6151326) baseStart_6151326 baseEnd_6151326 := by
    simpa [prefixWord, tailWord_6151326, baseEnd_6151326] using wordTrace_append hprefix tailTrace_6151326
  have hstable : (prefixWord ++ tailWord_6151326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151326).length < 2 ^ (prefixWord ++ tailWord_6151326).sum := by decide
  have hdescent : baseEnd_6151326 < baseStart_6151326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151329 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6151329 : Nat := 118140960795 + 6151329 * 2 ^ 59
def prefixEnd_6151329 : Nat := 4983230072969 + 3 ^ 40 * 6151329 * 2
def baseEnd_6151329 : Nat := 3158588440940868630698059

theorem tailTrace_6151329 : CollatzResearch.WordTrace tailWord_6151329 prefixEnd_6151329 3158588440940868630698059 := by
  unfold tailWord_6151329
  simp only [CollatzResearch.WordTrace]
  refine ⟨224357400331793071198689041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149571600221195380799126027 224357400331793071198689041)
  ·
    refine ⟨168268050248844803399016781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224357400331793071198689041 168268050248844803399016781)
    ·
      refine ⟨63100518843316801274631293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168268050248844803399016781 63100518843316801274631293)
      ·
        refine ⟨23662694566243800477986735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63100518843316801274631293 23662694566243800477986735)
        ·
          refine ⟨35494041849365700716980103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23662694566243800477986735 35494041849365700716980103)
          ·
            refine ⟨53241062774048551075470155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35494041849365700716980103 53241062774048551075470155)
            ·
              refine ⟨79861594161072826613205233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53241062774048551075470155 79861594161072826613205233)
              ·
                refine ⟨59896195620804619959903925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79861594161072826613205233 59896195620804619959903925)
                ·
                  refine ⟨5615268339450433121240993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59896195620804619959903925 5615268339450433121240993)
                  ·
                    refine ⟨4211451254587824840930745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5615268339450433121240993 4211451254587824840930745)
                    ·
                      refine ⟨3158588440940868630698059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211451254587824840930745 3158588440940868630698059)
                      ·
                        rfl

theorem cell23_6151329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6151329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151329 prefixEnd_6151329 := by exact prefixLift 6151329
  have htrace : WordTrace (prefixWord ++ tailWord_6151329) baseStart_6151329 baseEnd_6151329 := by
    simpa [prefixWord, tailWord_6151329, baseEnd_6151329] using wordTrace_append hprefix tailTrace_6151329
  have hstable : (prefixWord ++ tailWord_6151329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151329).length < 2 ^ (prefixWord ++ tailWord_6151329).sum := by decide
  have hdescent : baseEnd_6151329 < baseStart_6151329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151346 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_6151346 : Nat := 118140960795 + 6151346 * 2 ^ 59
def prefixEnd_6151346 : Nat := 4983230072969 + 3 ^ 40 * 6151346 * 2
def baseEnd_6151346 : Nat := 3158597170111995064185481

theorem tailTrace_6151346 : CollatzResearch.WordTrace tailWord_6151346 prefixEnd_6151346 3158597170111995064185481 := by
  unfold tailWord_6151346
  simp only [CollatzResearch.WordTrace]
  refine ⟨56089505093182870775514473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149572013581820988734705261 56089505093182870775514473)
  ·
    refine ⟨42067128819887153081635855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56089505093182870775514473 42067128819887153081635855)
    ·
      refine ⟨63100693229830729622453783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42067128819887153081635855 63100693229830729622453783)
      ·
        refine ⟨94651039844746094433680675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63100693229830729622453783 94651039844746094433680675)
        ·
          refine ⟨141976559767119141650521013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94651039844746094433680675 141976559767119141650521013)
          ·
            refine ⟨13310302478167419529736345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141976559767119141650521013 13310302478167419529736345)
            ·
              refine ⟨9982726858625564647302259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13310302478167419529736345 9982726858625564647302259)
              ·
                refine ⟨14974090287938346970953389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9982726858625564647302259 14974090287938346970953389)
                ·
                  refine ⟨5615283857976880114107521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14974090287938346970953389 5615283857976880114107521)
                  ·
                    refine ⟨4211462893482660085580641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5615283857976880114107521 4211462893482660085580641)
                    ·
                      refine ⟨3158597170111995064185481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211462893482660085580641 3158597170111995064185481)
                      ·
                        rfl

theorem cell23_6151346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_6151346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151346 prefixEnd_6151346 := by exact prefixLift 6151346
  have htrace : WordTrace (prefixWord ++ tailWord_6151346) baseStart_6151346 baseEnd_6151346 := by
    simpa [prefixWord, tailWord_6151346, baseEnd_6151346] using wordTrace_append hprefix tailTrace_6151346
  have hstable : (prefixWord ++ tailWord_6151346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151346).length < 2 ^ (prefixWord ++ tailWord_6151346).sum := by decide
  have hdescent : baseEnd_6151346 < baseStart_6151346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151356 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_6151356 : Nat := 118140960795 + 6151356 * 2 ^ 59
def prefixEnd_6151356 : Nat := 4983230072969 + 3 ^ 40 * 6151356 * 2
def baseEnd_6151356 : Nat := 1052867434972846675020145

theorem tailTrace_6151356 : CollatzResearch.WordTrace tailWord_6151356 prefixEnd_6151356 1052867434972846675020145 := by
  unfold tailWord_6151356
  simp only [CollatzResearch.WordTrace]
  refine ⟨112179192551347627404960961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149572256735130169873281281 112179192551347627404960961)
  ·
    refine ⟨84134394413510720553720721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112179192551347627404960961 84134394413510720553720721)
    ·
      refine ⟨63100795810133040415290541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84134394413510720553720721 63100795810133040415290541)
      ·
        refine ⟨23662798428799890155733953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63100795810133040415290541 23662798428799890155733953)
        ·
          refine ⟨17747098821599917616800465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23662798428799890155733953 17747098821599917616800465)
          ·
            refine ⟨13310324116199938212600349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17747098821599917616800465 13310324116199938212600349)
            ·
              refine ⟨4991371543574976829725131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13310324116199938212600349 4991371543574976829725131)
              ·
                refine ⟨7487057315362465244587697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991371543574976829725131 7487057315362465244587697)
                ·
                  refine ⟨5615292986521848933440773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7487057315362465244587697 5615292986521848933440773)
                  ·
                    refine ⟨1052867434972846675020145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5615292986521848933440773 1052867434972846675020145)
                    ·
                      rfl

theorem cell23_6151356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_6151356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151356 prefixEnd_6151356 := by exact prefixLift 6151356
  have htrace : WordTrace (prefixWord ++ tailWord_6151356) baseStart_6151356 baseEnd_6151356 := by
    simpa [prefixWord, tailWord_6151356, baseEnd_6151356] using wordTrace_append hprefix tailTrace_6151356
  have hstable : (prefixWord ++ tailWord_6151356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151356).length < 2 ^ (prefixWord ++ tailWord_6151356).sum := by decide
  have hdescent : baseEnd_6151356 < baseStart_6151356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151385 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_6151385 : Nat := 118140960795 + 6151385 * 2 ^ 59
def prefixEnd_6151385 : Nat := 4983230072969 + 3 ^ 40 * 6151385 * 2
def baseEnd_6151385 : Nat := 3158617195857520411597801

theorem tailTrace_6151385 : CollatzResearch.WordTrace tailWord_6151385 prefixEnd_6151385 3158617195857520411597801 := by
  unfold tailWord_6151385
  simp only [CollatzResearch.WordTrace]
  refine ⟨224359442819590192762727609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149572961879726795175151739 224359442819590192762727609)
  ·
    refine ⟨168269582114692644572045707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224359442819590192762727609 168269582114692644572045707)
    ·
      refine ⟨252404373172038966858068561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168269582114692644572045707 252404373172038966858068561)
      ·
        refine ⟨189303279879029225143551421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252404373172038966858068561 189303279879029225143551421)
        ·
          refine ⟨70988729954635959428831783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189303279879029225143551421 70988729954635959428831783)
          ·
            refine ⟨106483094931953939143247675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70988729954635959428831783 106483094931953939143247675)
            ·
              refine ⟨159724642397930908714871513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106483094931953939143247675 159724642397930908714871513)
              ·
                refine ⟨119793481798448181536153635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159724642397930908714871513 119793481798448181536153635)
                ·
                  refine ⟨179690222697672272304230453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119793481798448181536153635 179690222697672272304230453)
                  ·
                    refine ⟨16845958377906775528521605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 179690222697672272304230453 16845958377906775528521605)
                    ·
                      refine ⟨3158617195857520411597801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16845958377906775528521605 3158617195857520411597801)
                      ·
                        rfl

theorem cell23_6151385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_6151385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151385 prefixEnd_6151385 := by exact prefixLift 6151385
  have htrace : WordTrace (prefixWord ++ tailWord_6151385) baseStart_6151385 baseEnd_6151385 := by
    simpa [prefixWord, tailWord_6151385, baseEnd_6151385] using wordTrace_append hprefix tailTrace_6151385
  have hstable : (prefixWord ++ tailWord_6151385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151385).length < 2 ^ (prefixWord ++ tailWord_6151385).sum := by decide
  have hdescent : baseEnd_6151385 < baseStart_6151385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151453 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_6151453 : Nat := 118140960795 + 6151453 * 2 ^ 59
def prefixEnd_6151453 : Nat := 4983230072969 + 3 ^ 40 * 6151453 * 2
def baseEnd_6151453 : Nat := 3158652112542026145547489

theorem tailTrace_6151453 : CollatzResearch.WordTrace tailWord_6151453 prefixEnd_6151453 3158652112542026145547489 := by
  unfold tailWord_6151453
  simp only [CollatzResearch.WordTrace]
  refine ⟨224361922983343840376203013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149574615322229226917468675 224361922983343840376203013)
  ·
    refine ⟨42067860559376970070538065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224361922983343840376203013 42067860559376970070538065)
    ·
      refine ⟨31550895419532727552903549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42067860559376970070538065 31550895419532727552903549)
      ·
        refine ⟨11831585782324772832338831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31550895419532727552903549 11831585782324772832338831)
        ·
          refine ⟨17747378673487159248508247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11831585782324772832338831 17747378673487159248508247)
          ·
            refine ⟨26621068010230738872762371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17747378673487159248508247 26621068010230738872762371)
            ·
              refine ⟨39931602015346108309143557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26621068010230738872762371 39931602015346108309143557)
              ·
                refine ⟨7487175377877395307964417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39931602015346108309143557 7487175377877395307964417)
                ·
                  refine ⟨5615381533408046480973313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7487175377877395307964417 5615381533408046480973313)
                  ·
                    refine ⟨4211536150056034860729985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5615381533408046480973313 4211536150056034860729985)
                    ·
                      refine ⟨3158652112542026145547489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4211536150056034860729985 3158652112542026145547489)
                      ·
                        rfl

theorem cell23_6151453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_6151453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151453 prefixEnd_6151453 := by exact prefixLift 6151453
  have htrace : WordTrace (prefixWord ++ tailWord_6151453) baseStart_6151453 baseEnd_6151453 := by
    simpa [prefixWord, tailWord_6151453, baseEnd_6151453] using wordTrace_append hprefix tailTrace_6151453
  have hstable : (prefixWord ++ tailWord_6151453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151453).length < 2 ^ (prefixWord ++ tailWord_6151453).sum := by decide
  have hdescent : baseEnd_6151453 < baseStart_6151453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151459 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 5]
def baseStart_6151459 : Nat := 118140960795 + 6151459 * 2 ^ 59
def prefixEnd_6151459 : Nat := 4983230072969 + 3 ^ 40 * 6151459 * 2
def baseEnd_6151459 : Nat := 350961688158439235785829

theorem tailTrace_6151459 : CollatzResearch.WordTrace tailWord_6151459 prefixEnd_6151459 350961688158439235785829 := by
  unfold tailWord_6151459
  simp only [CollatzResearch.WordTrace]
  refine ⟨224362141821322103400921431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149574761214214735600614287 224362141821322103400921431)
  ·
    refine ⟨336543212731983155101382147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224362141821322103400921431 336543212731983155101382147)
    ·
      refine ⟨504814819097974732652073221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336543212731983155101382147 504814819097974732652073221)
      ·
        refine ⟨94652778580870262372263729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 504814819097974732652073221 94652778580870262372263729)
        ·
          refine ⟨70989583935652696779197797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94652778580870262372263729 70989583935652696779197797)
          ·
            refine ⟨13310546987934880646099587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70989583935652696779197797 13310546987934880646099587)
            ·
              refine ⟨19965820481902320969149381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13310546987934880646099587 19965820481902320969149381)
              ·
                refine ⟨3743591340356685181715509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19965820481902320969149381 3743591340356685181715509)
                ·
                  refine ⟨350961688158439235785829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3743591340356685181715509 350961688158439235785829)
                  ·
                    rfl

theorem cell23_6151459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 5].length) (baseStart_6151459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151459 prefixEnd_6151459 := by exact prefixLift 6151459
  have htrace : WordTrace (prefixWord ++ tailWord_6151459) baseStart_6151459 baseEnd_6151459 := by
    simpa [prefixWord, tailWord_6151459, baseEnd_6151459] using wordTrace_append hprefix tailTrace_6151459
  have hstable : (prefixWord ++ tailWord_6151459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151459).length < 2 ^ (prefixWord ++ tailWord_6151459).sum := by decide
  have hdescent : baseEnd_6151459 < baseStart_6151459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6151465 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_6151465 : Nat := 118140960795 + 6151465 * 2 ^ 59
def prefixEnd_6151465 : Nat := 4983230072969 + 3 ^ 40 * 6151465 * 2
def baseEnd_6151465 : Nat := 3158658274309880098597433

theorem tailTrace_6151465 : CollatzResearch.WordTrace tailWord_6151465 prefixEnd_6151465 3158658274309880098597433 := by
  unfold tailWord_6151465
  simp only [CollatzResearch.WordTrace]
  refine ⟨224362360659300366425639849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149574907106200244283759899 224362360659300366425639849)
  ·
    refine ⟨168271770494475274819229887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224362360659300366425639849 168271770494475274819229887)
    ·
      refine ⟨252407655741712912228844831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168271770494475274819229887 252407655741712912228844831)
      ·
        refine ⟨378611483612569368343267247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252407655741712912228844831 378611483612569368343267247)
        ·
          refine ⟨567917225418854052514900871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378611483612569368343267247 567917225418854052514900871)
          ·
            refine ⟨851875838128281078772351307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567917225418854052514900871 851875838128281078772351307)
            ·
              refine ⟨1277813757192421618158526961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851875838128281078772351307 1277813757192421618158526961)
              ·
                refine ⟨958360317894316213618895221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277813757192421618158526961 958360317894316213618895221)
                ·
                  refine ⟨89846279802592145026771427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 958360317894316213618895221 89846279802592145026771427)
                  ·
                    refine ⟨134769419703888217540157141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89846279802592145026771427 134769419703888217540157141)
                    ·
                      refine ⟨3158658274309880098597433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134769419703888217540157141 3158658274309880098597433)
                      ·
                        rfl

theorem cell23_6151465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_6151465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6151465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6151465 prefixEnd_6151465 := by exact prefixLift 6151465
  have htrace : WordTrace (prefixWord ++ tailWord_6151465) baseStart_6151465 baseEnd_6151465 := by
    simpa [prefixWord, tailWord_6151465, baseEnd_6151465] using wordTrace_append hprefix tailTrace_6151465
  have hstable : (prefixWord ++ tailWord_6151465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6151465).length < 2 ^ (prefixWord ++ tailWord_6151465).sum := by decide
  have hdescent : baseEnd_6151465 < baseStart_6151465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6151465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
