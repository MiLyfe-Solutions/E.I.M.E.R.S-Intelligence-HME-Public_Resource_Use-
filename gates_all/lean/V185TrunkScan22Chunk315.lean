import V185TrunkScan22Chunk314

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2810467 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 2, 3]
def baseStart_2810467 : Nat := 118140960795 + 2810467 * 2 ^ 59
def prefixEnd_2810467 : Nat := 4983230072969 + 3 ^ 40 * 2810467 * 2
def baseEnd_2810467 : Nat := 962080289733173845758269

theorem tailTrace_2810467 : CollatzResearch.WordTrace tailWord_2810467 prefixEnd_2810467 962080289733173845758269 := by
  unfold tailWord_2810467
  simp only [CollatzResearch.WordTrace]
  refine ⟨102506152709165523394789655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68337435139443682263193103 102506152709165523394789655)
  ·
    refine ⟨153759229063748285092184483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102506152709165523394789655 153759229063748285092184483)
    ·
      refine ⟨230638843595622427638276725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153759229063748285092184483 230638843595622427638276725)
      ·
        refine ⟨21622391587089602591088443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230638843595622427638276725 21622391587089602591088443)
        ·
          refine ⟨32433587380634403886632665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21622391587089602591088443 32433587380634403886632665)
          ·
            refine ⟨24325190535475802914974499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32433587380634403886632665 24325190535475802914974499)
            ·
              refine ⟨36487785803213704372461749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24325190535475802914974499 36487785803213704372461749)
              ·
                refine ⟨3420729919051284784918289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36487785803213704372461749 3420729919051284784918289)
                ·
                  refine ⟨2565547439288463588688717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3420729919051284784918289 2565547439288463588688717)
                  ·
                    refine ⟨962080289733173845758269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565547439288463588688717 962080289733173845758269)
                    ·
                      rfl

theorem cell22_2810467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 3].length) (baseStart_2810467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810467 prefixEnd_2810467 := by exact prefixLift 2810467
  have htrace : WordTrace (prefixWord ++ tailWord_2810467) baseStart_2810467 baseEnd_2810467 := by
    simpa [prefixWord, tailWord_2810467, baseEnd_2810467] using wordTrace_append hprefix tailTrace_2810467
  have hstable : (prefixWord ++ tailWord_2810467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810467).length < 2 ^ (prefixWord ++ tailWord_2810467).sum := by decide
  have hdescent : baseEnd_2810467 < baseStart_2810467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810482 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_2810482 : Nat := 118140960795 + 2810482 * 2 ^ 59
def prefixEnd_2810482 : Nat := 4983230072969 + 3 ^ 40 * 2810482 * 2
def baseEnd_2810482 : Nat := 962085424539718806633223

theorem tailTrace_2810482 : CollatzResearch.WordTrace tailWord_2810482 prefixEnd_2810482 962085424539718806633223 := by
  unfold tailWord_2810482
  simp only [CollatzResearch.WordTrace]
  refine ⟨25626674951027795239146425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68337799869407453971057133 25626674951027795239146425)
  ·
    refine ⟨19220006213270846429359819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25626674951027795239146425 19220006213270846429359819)
    ·
      refine ⟨28830009319906269644039729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19220006213270846429359819 28830009319906269644039729)
      ·
        refine ⟨21622506989929702233029797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28830009319906269644039729 21622506989929702233029797)
        ·
          refine ⟨4054220060611819168693087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21622506989929702233029797 4054220060611819168693087)
          ·
            refine ⟨6081330090917728753039631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054220060611819168693087 6081330090917728753039631)
            ·
              refine ⟨9121995136376593129559447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081330090917728753039631 9121995136376593129559447)
              ·
                refine ⟨13682992704564889694339171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9121995136376593129559447 13682992704564889694339171)
                ·
                  refine ⟨20524489056847334541508757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13682992704564889694339171 20524489056847334541508757)
                  ·
                    refine ⟨962085424539718806633223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20524489056847334541508757 962085424539718806633223)
                    ·
                      rfl

theorem cell22_2810482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_2810482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810482 prefixEnd_2810482 := by exact prefixLift 2810482
  have htrace : WordTrace (prefixWord ++ tailWord_2810482) baseStart_2810482 baseEnd_2810482 := by
    simpa [prefixWord, tailWord_2810482, baseEnd_2810482] using wordTrace_append hprefix tailTrace_2810482
  have hstable : (prefixWord ++ tailWord_2810482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810482).length < 2 ^ (prefixWord ++ tailWord_2810482).sum := by decide
  have hdescent : baseEnd_2810482 < baseStart_2810482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810486 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2810486 : Nat := 118140960795 + 2810486 * 2 ^ 59
def prefixEnd_2810486 : Nat := 4983230072969 + 3 ^ 40 * 2810486 * 2
def baseEnd_2810486 : Nat := 320695597940488043177737

theorem tailTrace_2810486 : CollatzResearch.WordTrace tailWord_2810486 prefixEnd_2810486 320695597940488043177737 := by
  unfold tailWord_2810486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6406677856006043102483207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68337897130731126426487541 6406677856006043102483207)
  ·
    refine ⟨9610016784009064653724811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6406677856006043102483207 9610016784009064653724811)
    ·
      refine ⟨14415025176013596980587217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9610016784009064653724811 14415025176013596980587217)
      ·
        refine ⟨10811268882010197735440413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14415025176013596980587217 10811268882010197735440413)
        ·
          refine ⟨4054225830753824150790155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10811268882010197735440413 4054225830753824150790155)
          ·
            refine ⟨6081338746130736226185233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054225830753824150790155 6081338746130736226185233)
            ·
              refine ⟨4561004059598052169638925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6081338746130736226185233 4561004059598052169638925)
              ·
                refine ⟨1710376522349269563614597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4561004059598052169638925 1710376522349269563614597)
                ·
                  refine ⟨320695597940488043177737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710376522349269563614597 320695597940488043177737)
                  ·
                    rfl

theorem cell22_2810486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2810486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810486 prefixEnd_2810486 := by exact prefixLift 2810486
  have htrace : WordTrace (prefixWord ++ tailWord_2810486) baseStart_2810486 baseEnd_2810486 := by
    simpa [prefixWord, tailWord_2810486, baseEnd_2810486] using wordTrace_append hprefix tailTrace_2810486
  have hstable : (prefixWord ++ tailWord_2810486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810486).length < 2 ^ (prefixWord ++ tailWord_2810486).sum := by decide
  have hdescent : baseEnd_2810486 < baseStart_2810486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810555 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 7, 4]
def baseStart_2810555 : Nat := 118140960795 + 2810555 * 2 ^ 59
def prefixEnd_2810555 : Nat := 4983230072969 + 3 ^ 40 * 2810555 * 2
def baseEnd_2810555 : Nat := 962110413931570949557999

theorem tailTrace_2810555 : CollatzResearch.WordTrace tailWord_2810555 prefixEnd_2810555 962110413931570949557999 := by
  unfold tailWord_2810555
  simp only [CollatzResearch.WordTrace]
  refine ⟨102509362332846714423993119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68339574888564476282662079 102509362332846714423993119)
  ·
    refine ⟨153764043499270071635989679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102509362332846714423993119 153764043499270071635989679)
    ·
      refine ⟨230646065248905107453984519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153764043499270071635989679 230646065248905107453984519)
      ·
        refine ⟨345969097873357661180976779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230646065248905107453984519 345969097873357661180976779)
        ·
          refine ⟨518953646810036491771465169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345969097873357661180976779 518953646810036491771465169)
          ·
            refine ⟨389215235107527368828598877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518953646810036491771465169 389215235107527368828598877)
            ·
              refine ⟨145955713165322763310724579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389215235107527368828598877 145955713165322763310724579)
              ·
                refine ⟨218933569747984144966086869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145955713165322763310724579 218933569747984144966086869)
                ·
                  refine ⟨5131255540968378397642661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 218933569747984144966086869 5131255540968378397642661)
                  ·
                    refine ⟨962110413931570949557999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131255540968378397642661 962110413931570949557999)
                    ·
                      rfl

theorem cell22_2810555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 4].length) (baseStart_2810555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810555 prefixEnd_2810555 := by exact prefixLift 2810555
  have htrace : WordTrace (prefixWord ++ tailWord_2810555) baseStart_2810555 baseEnd_2810555 := by
    simpa [prefixWord, tailWord_2810555, baseEnd_2810555] using wordTrace_append hprefix tailTrace_2810555
  have hstable : (prefixWord ++ tailWord_2810555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810555).length < 2 ^ (prefixWord ++ tailWord_2810555).sum := by decide
  have hdescent : baseEnd_2810555 < baseStart_2810555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810606 : List Nat := [4, 1, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_2810606 : Nat := 118140960795 + 2810606 * 2 ^ 59
def prefixEnd_2810606 : Nat := 4983230072969 + 3 ^ 40 * 2810606 * 2
def baseEnd_2810606 : Nat := 962127872273823816532843

theorem tailTrace_2810606 : CollatzResearch.WordTrace tailWord_2810606 prefixEnd_2810606 962127872273823816532843 := by
  unfold tailWord_2810606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12813902806957743766762459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68340814970441300089399781 12813902806957743766762459)
  ·
    refine ⟨19220854210436615650143689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12813902806957743766762459 19220854210436615650143689)
    ·
      refine ⟨14415640657827461737607767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19220854210436615650143689 14415640657827461737607767)
      ·
        refine ⟨21623460986741192606411651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14415640657827461737607767 21623460986741192606411651)
        ·
          refine ⟨32435191480111788909617477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21623460986741192606411651 32435191480111788909617477)
          ·
            refine ⟨6081598402520960420553277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32435191480111788909617477 6081598402520960420553277)
            ·
              refine ⟨2280599400945360157707479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6081598402520960420553277 2280599400945360157707479)
              ·
                refine ⟨3420899101418040236561219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280599400945360157707479 3420899101418040236561219)
                ·
                  refine ⟨5131348652127060354841829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3420899101418040236561219 5131348652127060354841829)
                  ·
                    refine ⟨962127872273823816532843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131348652127060354841829 962127872273823816532843)
                    ·
                      rfl

theorem cell22_2810606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_2810606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810606 prefixEnd_2810606 := by exact prefixLift 2810606
  have htrace : WordTrace (prefixWord ++ tailWord_2810606) baseStart_2810606 baseEnd_2810606 := by
    simpa [prefixWord, tailWord_2810606, baseEnd_2810606] using wordTrace_append hprefix tailTrace_2810606
  have hstable : (prefixWord ++ tailWord_2810606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810606).length < 2 ^ (prefixWord ++ tailWord_2810606).sum := by decide
  have hdescent : baseEnd_2810606 < baseStart_2810606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810632 : List Nat := [2, 1, 3, 2, 2, 2, 3, 7]
def baseStart_2810632 : Nat := 118140960795 + 2810632 * 2 ^ 59
def prefixEnd_2810632 : Nat := 4983230072969 + 3 ^ 40 * 2810632 * 2
def baseEnd_2810632 : Nat := 106904085845018712820307

theorem tailTrace_2810632 : CollatzResearch.WordTrace tailWord_2810632 prefixEnd_2810632 106904085845018712820307 := by
  unfold tailWord_2810632
  simp only [CollatzResearch.WordTrace]
  refine ⟨51256085376783878287273075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68341447169045171049697433 51256085376783878287273075)
  ·
    refine ⟨76884128065175817430909613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51256085376783878287273075 76884128065175817430909613)
    ·
      refine ⟨28831548024440931536591105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76884128065175817430909613 28831548024440931536591105)
      ·
        refine ⟨21623661018330698652443329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28831548024440931536591105 21623661018330698652443329)
        ·
          refine ⟨16217745763748023989332497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21623661018330698652443329 16217745763748023989332497)
          ·
            refine ⟨12163309322811017991999373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16217745763748023989332497 12163309322811017991999373)
            ·
              refine ⟨4561240996054131746999765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12163309322811017991999373 4561240996054131746999765)
              ·
                refine ⟨106904085845018712820307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4561240996054131746999765 106904085845018712820307)
                ·
                  rfl

theorem cell22_2810632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_2810632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810632 prefixEnd_2810632 := by exact prefixLift 2810632
  have htrace : WordTrace (prefixWord ++ tailWord_2810632) baseStart_2810632 baseEnd_2810632 := by
    simpa [prefixWord, tailWord_2810632, baseEnd_2810632] using wordTrace_append hprefix tailTrace_2810632
  have hstable : (prefixWord ++ tailWord_2810632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810632).length < 2 ^ (prefixWord ++ tailWord_2810632).sum := by decide
  have hdescent : baseEnd_2810632 < baseStart_2810632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810664 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2810664 : Nat := 118140960795 + 2810664 * 2 ^ 59
def prefixEnd_2810664 : Nat := 4983230072969 + 3 ^ 40 * 2810664 * 2
def baseEnd_2810664 : Nat := 962147726859130998582665

theorem tailTrace_2810664 : CollatzResearch.WordTrace tailWord_2810664 prefixEnd_2810664 962147726859130998582665 := by
  unfold tailWord_2810664
  simp only [CollatzResearch.WordTrace]
  refine ⟨51256668944725913019855523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68342225259634550693140697 51256668944725913019855523)
  ·
    refine ⟨76885003417088869529783285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51256668944725913019855523 76885003417088869529783285)
    ·
      refine ⟨7207969070352081518417183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76885003417088869529783285 7207969070352081518417183)
      ·
        refine ⟨10811953605528122277625775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7207969070352081518417183 10811953605528122277625775)
        ·
          refine ⟨16217930408292183416438663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10811953605528122277625775 16217930408292183416438663)
          ·
            refine ⟨24326895612438275124657995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16217930408292183416438663 24326895612438275124657995)
            ·
              refine ⟨36490343418657412686986993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24326895612438275124657995 36490343418657412686986993)
              ·
                refine ⟨27367757563993059515240245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36490343418657412686986993 27367757563993059515240245)
                ·
                  refine ⟨2565727271624349329553773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27367757563993059515240245 2565727271624349329553773)
                  ·
                    refine ⟨962147726859130998582665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565727271624349329553773 962147726859130998582665)
                    ·
                      rfl

theorem cell22_2810664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2810664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810664 prefixEnd_2810664 := by exact prefixLift 2810664
  have htrace : WordTrace (prefixWord ++ tailWord_2810664) baseStart_2810664 baseEnd_2810664 := by
    simpa [prefixWord, tailWord_2810664, baseEnd_2810664] using wordTrace_append hprefix tailTrace_2810664
  have hstable : (prefixWord ++ tailWord_2810664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810664).length < 2 ^ (prefixWord ++ tailWord_2810664).sum := by decide
  have hdescent : baseEnd_2810664 < baseStart_2810664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810707 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 3, 4]
def baseStart_2810707 : Nat := 118140960795 + 2810707 * 2 ^ 59
def prefixEnd_2810707 : Nat := 4983230072969 + 3 ^ 40 * 2810707 * 2
def baseEnd_2810707 : Nat := 962162446637893219757533

theorem tailTrace_2810707 : CollatzResearch.WordTrace tailWord_2810707 prefixEnd_2810707 962162446637893219757533 := by
  unfold tailWord_2810707
  simp only [CollatzResearch.WordTrace]
  refine ⟨102514906228296044383526375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68343270818864029589017583 102514906228296044383526375)
  ·
    refine ⟨153772359342444066575289563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102514906228296044383526375 153772359342444066575289563)
    ·
      refine ⟨230658539013666099862934345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153772359342444066575289563 230658539013666099862934345)
      ·
        refine ⟨172993904260249574897200759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230658539013666099862934345 172993904260249574897200759)
        ·
          refine ⟨259490856390374362345801139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172993904260249574897200759 259490856390374362345801139)
          ·
            refine ⟨389236284585561543518701709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259490856390374362345801139 389236284585561543518701709)
            ·
              refine ⟨145963606719585578819513141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389236284585561543518701709 145963606719585578819513141)
              ·
                refine ⟨13684088129961148014329357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145963606719585578819513141 13684088129961148014329357)
                ·
                  refine ⟨5131533048735430505373509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13684088129961148014329357 5131533048735430505373509)
                  ·
                    refine ⟨962162446637893219757533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131533048735430505373509 962162446637893219757533)
                    ·
                      rfl

theorem cell22_2810707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 4].length) (baseStart_2810707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810707 prefixEnd_2810707 := by exact prefixLift 2810707
  have htrace : WordTrace (prefixWord ++ tailWord_2810707) baseStart_2810707 baseEnd_2810707 := by
    simpa [prefixWord, tailWord_2810707, baseEnd_2810707] using wordTrace_append hprefix tailTrace_2810707
  have hstable : (prefixWord ++ tailWord_2810707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810707).length < 2 ^ (prefixWord ++ tailWord_2810707).sum := by decide
  have hdescent : baseEnd_2810707 < baseStart_2810707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810739 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 4]
def baseStart_2810739 : Nat := 118140960795 + 2810739 * 2 ^ 59
def prefixEnd_2810739 : Nat := 4983230072969 + 3 ^ 40 * 2810739 * 2
def baseEnd_2810739 : Nat := 320724466963951934319145

theorem tailTrace_2810739 : CollatzResearch.WordTrace tailWord_2810739 prefixEnd_2810739 320724466963951934319145 := by
  unfold tailWord_2810739
  simp only [CollatzResearch.WordTrace]
  refine ⟨102516073364180113848691271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68344048909453409232460847 102516073364180113848691271)
  ·
    refine ⟨153774110046270170773036907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102516073364180113848691271 153774110046270170773036907)
    ·
      refine ⟨230661165069405256159555361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153774110046270170773036907 230661165069405256159555361)
      ·
        refine ⟨172995873802053942119666521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230661165069405256159555361 172995873802053942119666521)
        ·
          refine ⟨129746905351540456589749891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172995873802053942119666521 129746905351540456589749891)
          ·
            refine ⟨194620358027310684884624837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129746905351540456589749891 194620358027310684884624837)
            ·
              refine ⟨36491317130120753415867157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194620358027310684884624837 36491317130120753415867157)
              ·
                refine ⟨1710530490474410316368773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36491317130120753415867157 1710530490474410316368773)
                ·
                  refine ⟨320724466963951934319145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710530490474410316368773 320724466963951934319145)
                  ·
                    rfl

theorem cell22_2810739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 4].length) (baseStart_2810739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810739 prefixEnd_2810739 := by exact prefixLift 2810739
  have htrace : WordTrace (prefixWord ++ tailWord_2810739) baseStart_2810739 baseEnd_2810739 := by
    simpa [prefixWord, tailWord_2810739, baseEnd_2810739] using wordTrace_append hprefix tailTrace_2810739
  have hstable : (prefixWord ++ tailWord_2810739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810739).length < 2 ^ (prefixWord ++ tailWord_2810739).sum := by decide
  have hdescent : baseEnd_2810739 < baseStart_2810739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810752 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_2810752 : Nat := 118140960795 + 2810752 * 2 ^ 59
def prefixEnd_2810752 : Nat := 4983230072969 + 3 ^ 40 * 2810752 * 2
def baseEnd_2810752 : Nat := 962177851057528102382395

theorem tailTrace_2810752 : CollatzResearch.WordTrace tailWord_2810752 prefixEnd_2810752 962177851057528102382395 := by
  unfold tailWord_2810752
  simp only [CollatzResearch.WordTrace]
  refine ⟨51258273756566508534457255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68344365008755344712609673 51258273756566508534457255)
  ·
    refine ⟨76887410634849762801685883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51258273756566508534457255 76887410634849762801685883)
    ·
      refine ⟨115331115952274644202528825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76887410634849762801685883 115331115952274644202528825)
      ·
        refine ⟨86498336964205983151896619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115331115952274644202528825 86498336964205983151896619)
        ·
          refine ⟨129747505446308974727844929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86498336964205983151896619 129747505446308974727844929)
          ·
            refine ⟨97310629084731731045883697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129747505446308974727844929 97310629084731731045883697)
            ·
              refine ⟨72982971813548798284412773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97310629084731731045883697 72982971813548798284412773)
              ·
                refine ⟨13684307215040399678327395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72982971813548798284412773 13684307215040399678327395)
                ·
                  refine ⟨20526460822560599517491093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13684307215040399678327395 20526460822560599517491093)
                  ·
                    refine ⟨962177851057528102382395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20526460822560599517491093 962177851057528102382395)
                    ·
                      rfl

theorem cell22_2810752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_2810752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810752 prefixEnd_2810752 := by exact prefixLift 2810752
  have htrace : WordTrace (prefixWord ++ tailWord_2810752) baseStart_2810752 baseEnd_2810752 := by
    simpa [prefixWord, tailWord_2810752, baseEnd_2810752] using wordTrace_append hprefix tailTrace_2810752
  have hstable : (prefixWord ++ tailWord_2810752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810752).length < 2 ^ (prefixWord ++ tailWord_2810752).sum := by decide
  have hdescent : baseEnd_2810752 < baseStart_2810752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810786 : List Nat := [3, 3, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2810786 : Nat := 118140960795 + 2810786 * 2 ^ 59
def prefixEnd_2810786 : Nat := 4983230072969 + 3 ^ 40 * 2810786 * 2
def baseEnd_2810786 : Nat := 962189489952363347032291

theorem tailTrace_2810786 : CollatzResearch.WordTrace tailWord_2810786 prefixEnd_2810786 962189489952363347032291 := by
  unfold tailWord_2810786
  simp only [CollatzResearch.WordTrace]
  refine ⟨25629446898752460218913053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68345191730006560583768141 25629446898752460218913053)
  ·
    refine ⟨9611042587032172582092395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25629446898752460218913053 9611042587032172582092395)
    ·
      refine ⟨14416563880548258873138593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9611042587032172582092395 14416563880548258873138593)
      ·
        refine ⟨10812422910411194154853945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14416563880548258873138593 10812422910411194154853945)
        ·
          refine ⟨8109317182808395616140459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10812422910411194154853945 8109317182808395616140459)
          ·
            refine ⟨12163975774212593424210689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8109317182808395616140459 12163975774212593424210689)
            ·
              refine ⟨9122981830659445068158017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12163975774212593424210689 9122981830659445068158017)
              ·
                refine ⟨6842236372994583801118513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9122981830659445068158017 6842236372994583801118513)
                ·
                  refine ⟨5131677279745937850838885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842236372994583801118513 5131677279745937850838885)
                  ·
                    refine ⟨962189489952363347032291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131677279745937850838885 962189489952363347032291)
                    ·
                      rfl

theorem cell22_2810786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2810786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810786 prefixEnd_2810786 := by exact prefixLift 2810786
  have htrace : WordTrace (prefixWord ++ tailWord_2810786) baseStart_2810786 baseEnd_2810786 := by
    simpa [prefixWord, tailWord_2810786, baseEnd_2810786] using wordTrace_append hprefix tailTrace_2810786
  have hstable : (prefixWord ++ tailWord_2810786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810786).length < 2 ^ (prefixWord ++ tailWord_2810786).sum := by decide
  have hdescent : baseEnd_2810786 < baseStart_2810786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810801 : List Nat := [1, 2, 2, 4, 3, 2, 1, 7]
def baseStart_2810801 : Nat := 118140960795 + 2810801 * 2 ^ 59
def prefixEnd_2810801 : Nat := 4983230072969 + 3 ^ 40 * 2810801 * 2
def baseEnd_2810801 : Nat := 106910513862100923100805

theorem tailTrace_2810801 : CollatzResearch.WordTrace tailWord_2810801 prefixEnd_2810801 106910513862100923100805 := by
  unfold tailWord_2810801
  simp only [CollatzResearch.WordTrace]
  refine ⟨102518334689955498437448257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68345556459970332291632171 102518334689955498437448257)
  ·
    refine ⟨76888751017466623828086193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102518334689955498437448257 76888751017466623828086193)
    ·
      refine ⟨57666563263099967871064645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76888751017466623828086193 57666563263099967871064645)
      ·
        refine ⟨10812480611831243975824621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57666563263099967871064645 10812480611831243975824621)
        ·
          refine ⟨4054680229436716490934233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10812480611831243975824621 4054680229436716490934233)
          ·
            refine ⟨3041010172077537368200675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4054680229436716490934233 3041010172077537368200675)
            ·
              refine ⟨4561515258116306052301013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041010172077537368200675 4561515258116306052301013)
              ·
                refine ⟨106910513862100923100805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4561515258116306052301013 106910513862100923100805)
                ·
                  rfl

theorem cell22_2810801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 7].length) (baseStart_2810801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810801 prefixEnd_2810801 := by exact prefixLift 2810801
  have htrace : WordTrace (prefixWord ++ tailWord_2810801) baseStart_2810801 baseEnd_2810801 := by
    simpa [prefixWord, tailWord_2810801, baseEnd_2810801] using wordTrace_append hprefix tailTrace_2810801
  have hstable : (prefixWord ++ tailWord_2810801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810801).length < 2 ^ (prefixWord ++ tailWord_2810801).sum := by decide
  have hdescent : baseEnd_2810801 < baseStart_2810801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810814 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2810814 : Nat := 118140960795 + 2810814 * 2 ^ 59
def prefixEnd_2810814 : Nat := 4983230072969 + 3 ^ 40 * 2810814 * 2
def baseEnd_2810814 : Nat := 962199074924580607332205

theorem tailTrace_2810814 : CollatzResearch.WordTrace tailWord_2810814 prefixEnd_2810814 962199074924580607332205 := by
  unfold tailWord_2810814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12814851104863550207208937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68345872559272267771780997 12814851104863550207208937)
  ·
    refine ⟨9611138328647662655406703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12814851104863550207208937 9611138328647662655406703)
    ·
      refine ⟨14416707492971493983110055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9611138328647662655406703 14416707492971493983110055)
      ·
        refine ⟨21625061239457240974665083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14416707492971493983110055 21625061239457240974665083)
        ·
          refine ⟨32437591859185861461997625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21625061239457240974665083 32437591859185861461997625)
          ·
            refine ⟨24328193894389396096498219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32437591859185861461997625 24328193894389396096498219)
            ·
              refine ⟨36492290841584094144747329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24328193894389396096498219 36492290841584094144747329)
              ·
                refine ⟨27369218131188070608560497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36492290841584094144747329 27369218131188070608560497)
                ·
                  refine ⟨20526913598391052956420373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27369218131188070608560497 20526913598391052956420373)
                  ·
                    refine ⟨962199074924580607332205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20526913598391052956420373 962199074924580607332205)
                    ·
                      rfl

theorem cell22_2810814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2810814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810814 prefixEnd_2810814 := by exact prefixLift 2810814
  have htrace : WordTrace (prefixWord ++ tailWord_2810814) baseStart_2810814 baseEnd_2810814 := by
    simpa [prefixWord, tailWord_2810814, baseEnd_2810814] using wordTrace_append hprefix tailTrace_2810814
  have hstable : (prefixWord ++ tailWord_2810814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810814).length < 2 ^ (prefixWord ++ tailWord_2810814).sum := by decide
  have hdescent : baseEnd_2810814 < baseStart_2810814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810816 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_2810816 : Nat := 118140960795 + 2810816 * 2 ^ 59
def prefixEnd_2810816 : Nat := 4983230072969 + 3 ^ 40 * 2810816 * 2
def baseEnd_2810816 : Nat := 962199759565453268782199

theorem tailTrace_2810816 : CollatzResearch.WordTrace tailWord_2810816 prefixEnd_2810816 962199759565453268782199 := by
  unfold tailWord_2810816
  simp only [CollatzResearch.WordTrace]
  refine ⟨51259440892450577999622151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68345921189934103999496201 51259440892450577999622151)
  ·
    refine ⟨76889161338675866999433227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51259440892450577999622151 76889161338675866999433227)
    ·
      refine ⟨115333742008013800499149841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76889161338675866999433227 115333742008013800499149841)
      ·
        refine ⟨86500306506010350374362381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115333742008013800499149841 86500306506010350374362381)
        ·
          refine ⟨32437614939753881390385893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86500306506010350374362381 32437614939753881390385893)
          ·
            refine ⟨6082052801203852760697355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32437614939753881390385893 6082052801203852760697355)
            ·
              refine ⟨9123079201805779141046033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082052801203852760697355 9123079201805779141046033)
              ·
                refine ⟨6842309401354334355784525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9123079201805779141046033 6842309401354334355784525)
                ·
                  refine ⟨2565866025507875383419197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6842309401354334355784525 2565866025507875383419197)
                  ·
                    refine ⟨962199759565453268782199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565866025507875383419197 962199759565453268782199)
                    ·
                      rfl

theorem cell22_2810816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_2810816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810816 prefixEnd_2810816 := by exact prefixLift 2810816
  have htrace : WordTrace (prefixWord ++ tailWord_2810816) baseStart_2810816 baseEnd_2810816 := by
    simpa [prefixWord, tailWord_2810816, baseEnd_2810816] using wordTrace_append hprefix tailTrace_2810816
  have hstable : (prefixWord ++ tailWord_2810816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810816).length < 2 ^ (prefixWord ++ tailWord_2810816).sum := by decide
  have hdescent : baseEnd_2810816 < baseStart_2810816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810820 : List Nat := [2, 3, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2810820 : Nat := 118140960795 + 2810820 * 2 ^ 59
def prefixEnd_2810820 : Nat := 4983230072969 + 3 ^ 40 * 2810820 * 2
def baseEnd_2810820 : Nat := 962201128847198591682187

theorem tailTrace_2810820 : CollatzResearch.WordTrace tailWord_2810820 prefixEnd_2810820 962201128847198591682187 := by
  unfold tailWord_2810820
  simp only [CollatzResearch.WordTrace]
  refine ⟨51259513838443332341194957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68346018451257776454926609 51259513838443332341194957)
  ·
    refine ⟨19222317689416249627948109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51259513838443332341194957 19222317689416249627948109)
    ·
      refine ⟨7208369133531093610480541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19222317689416249627948109 7208369133531093610480541)
      ·
        refine ⟨2703138425074160103930203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7208369133531093610480541 2703138425074160103930203)
        ·
          refine ⟨4054707637611240155895305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703138425074160103930203 4054707637611240155895305)
          ·
            refine ⟨3041030728208430116921479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4054707637611240155895305 3041030728208430116921479)
            ·
              refine ⟨4561546092312645175382219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041030728208430116921479 4561546092312645175382219)
              ·
                refine ⟨6842319138468967763073329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561546092312645175382219 6842319138468967763073329)
                ·
                  refine ⟨5131739353851725822304997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6842319138468967763073329 5131739353851725822304997)
                  ·
                    refine ⟨962201128847198591682187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131739353851725822304997 962201128847198591682187)
                    ·
                      rfl

theorem cell22_2810820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2810820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810820 prefixEnd_2810820 := by exact prefixLift 2810820
  have htrace : WordTrace (prefixWord ++ tailWord_2810820) baseStart_2810820 baseEnd_2810820 := by
    simpa [prefixWord, tailWord_2810820, baseEnd_2810820] using wordTrace_append hprefix tailTrace_2810820
  have hstable : (prefixWord ++ tailWord_2810820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810820).length < 2 ^ (prefixWord ++ tailWord_2810820).sum := by decide
  have hdescent : baseEnd_2810820 < baseStart_2810820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810833 : List Nat := [1, 2, 2, 1, 2, 1, 6, 3, 1, 3]
def baseStart_2810833 : Nat := 118140960795 + 2810833 * 2 ^ 59
def prefixEnd_2810833 : Nat := 4983230072969 + 3 ^ 40 * 2810833 * 2
def baseEnd_2810833 : Nat := 962205579012870891107147

theorem tailTrace_2810833 : CollatzResearch.WordTrace tailWord_2810833 prefixEnd_2810833 962205579012870891107147 := by
  unfold tailWord_2810833
  simp only [CollatzResearch.WordTrace]
  refine ⟨102519501825839567902613153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68346334550559711935075435 102519501825839567902613153)
  ·
    refine ⟨76889626369379675926959865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102519501825839567902613153 76889626369379675926959865)
    ·
      refine ⟨57667219777034756945219899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76889626369379675926959865 57667219777034756945219899)
      ·
        refine ⟨86500829665552135417829849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57667219777034756945219899 86500829665552135417829849)
        ·
          refine ⟨64875622249164101563372387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86500829665552135417829849 64875622249164101563372387)
          ·
            refine ⟨97313433373746152345058581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64875622249164101563372387 97313433373746152345058581)
            ·
              refine ⟨4561567189394350891174621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97313433373746152345058581 4561567189394350891174621)
              ·
                refine ⟨1710587696022881584190483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4561567189394350891174621 1710587696022881584190483)
                ·
                  refine ⟨2565881544034322376285725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710587696022881584190483 2565881544034322376285725)
                  ·
                    refine ⟨962205579012870891107147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565881544034322376285725 962205579012870891107147)
                    ·
                      rfl

theorem cell22_2810833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_2810833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810833 prefixEnd_2810833 := by exact prefixLift 2810833
  have htrace : WordTrace (prefixWord ++ tailWord_2810833) baseStart_2810833 baseEnd_2810833 := by
    simpa [prefixWord, tailWord_2810833, baseEnd_2810833] using wordTrace_append hprefix tailTrace_2810833
  have hstable : (prefixWord ++ tailWord_2810833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810833).length < 2 ^ (prefixWord ++ tailWord_2810833).sum := by decide
  have hdescent : baseEnd_2810833 < baseStart_2810833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810850 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2810850 : Nat := 118140960795 + 2810850 * 2 ^ 59
def prefixEnd_2810850 : Nat := 4983230072969 + 3 ^ 40 * 2810850 * 2
def baseEnd_2810850 : Nat := 962211398460288513432095

theorem tailTrace_2810850 : CollatzResearch.WordTrace tailWord_2810850 prefixEnd_2810850 962211398460288513432095 := by
  unfold tailWord_2810850
  simp only [CollatzResearch.WordTrace]
  refine ⟨25630030466694494951495501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68346747911185319870654669 25630030466694494951495501)
  ·
    refine ⟨9611261425010435606810813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25630030466694494951495501 9611261425010435606810813)
    ·
      refine ⟨3604223034378913352554055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9611261425010435606810813 3604223034378913352554055)
      ·
        refine ⟨5406334551568370028831083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3604223034378913352554055 5406334551568370028831083)
        ·
          refine ⟨8109501827352555043246625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5406334551568370028831083 8109501827352555043246625)
          ·
            refine ⟨6082126370514416282434969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8109501827352555043246625 6082126370514416282434969)
            ·
              refine ⟨4561594777885812211826227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6082126370514416282434969 4561594777885812211826227)
              ·
                refine ⟨6842392166828718317739341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561594777885812211826227 6842392166828718317739341)
                ·
                  refine ⟨2565897062560769369152253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6842392166828718317739341 2565897062560769369152253)
                  ·
                    refine ⟨962211398460288513432095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565897062560769369152253 962211398460288513432095)
                    ·
                      rfl

theorem cell22_2810850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2810850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810850 prefixEnd_2810850 := by exact prefixLift 2810850
  have htrace : WordTrace (prefixWord ++ tailWord_2810850) baseStart_2810850 baseEnd_2810850 := by
    simpa [prefixWord, tailWord_2810850, baseEnd_2810850] using wordTrace_append hprefix tailTrace_2810850
  have hstable : (prefixWord ++ tailWord_2810850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810850).length < 2 ^ (prefixWord ++ tailWord_2810850).sum := by decide
  have hdescent : baseEnd_2810850 < baseStart_2810850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810876 : List Nat := [2, 2, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_2810876 : Nat := 118140960795 + 2810876 * 2 ^ 59
def prefixEnd_2810876 : Nat := 4983230072969 + 3 ^ 40 * 2810876 * 2
def baseEnd_2810876 : Nat := 962220298791633112282015

theorem tailTrace_2810876 : CollatzResearch.WordTrace tailWord_2810876 prefixEnd_2810876 962220298791633112282015 := by
  unfold tailWord_2810876
  simp only [CollatzResearch.WordTrace]
  refine ⟨51260535082341893123214241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68347380109789190830952321 51260535082341893123214241)
  ·
    refine ⟨38445401311756419842410681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51260535082341893123214241 38445401311756419842410681)
    ·
      refine ⟨28834050983817314881808011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38445401311756419842410681 28834050983817314881808011)
      ·
        refine ⟨43251076475725972322712017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28834050983817314881808011 43251076475725972322712017)
        ·
          refine ⟨32438307356794479242034013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43251076475725972322712017 32438307356794479242034013)
          ·
            refine ⟨12164365258797929715762755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32438307356794479242034013 12164365258797929715762755)
            ·
              refine ⟨18246547888196894573644133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12164365258797929715762755 18246547888196894573644133)
              ·
                refine ⟨3421227729036917732558275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18246547888196894573644133 3421227729036917732558275)
                ·
                  refine ⟨5131841593555376598837413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421227729036917732558275 5131841593555376598837413)
                  ·
                    refine ⟨962220298791633112282015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5131841593555376598837413 962220298791633112282015)
                    ·
                      rfl

theorem cell22_2810876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_2810876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810876 prefixEnd_2810876 := by exact prefixLift 2810876
  have htrace : WordTrace (prefixWord ++ tailWord_2810876) baseStart_2810876 baseEnd_2810876 := by
    simpa [prefixWord, tailWord_2810876, baseEnd_2810876] using wordTrace_append hprefix tailTrace_2810876
  have hstable : (prefixWord ++ tailWord_2810876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810876).length < 2 ^ (prefixWord ++ tailWord_2810876).sum := by decide
  have hdescent : baseEnd_2810876 < baseStart_2810876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810889 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_2810889 : Nat := 118140960795 + 2810889 * 2 ^ 59
def prefixEnd_2810889 : Nat := 4983230072969 + 3 ^ 40 * 2810889 * 2
def baseEnd_2810889 : Nat := 962224748957305411706975

theorem tailTrace_2810889 : CollatzResearch.WordTrace tailWord_2810889 prefixEnd_2810889 962224748957305411706975 := by
  unfold tailWord_2810889
  simp only [CollatzResearch.WordTrace]
  refine ⟨102521544313636689466651721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68347696209091126311101147 102521544313636689466651721)
  ·
    refine ⟨76891158235227517099988791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102521544313636689466651721 76891158235227517099988791)
    ·
      refine ⟨115336737352841275649983187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76891158235227517099988791 115336737352841275649983187)
      ·
        refine ⟨173005106029261913474974781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115336737352841275649983187 173005106029261913474974781)
        ·
          refine ⟨64876914760973217553115543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173005106029261913474974781 64876914760973217553115543)
          ·
            refine ⟨97315372141459826329673315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64876914760973217553115543 97315372141459826329673315)
            ·
              refine ⟨145973058212189739494509973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97315372141459826329673315 145973058212189739494509973)
              ·
                refine ⟨6842487103696394038805155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 145973058212189739494509973 6842487103696394038805155)
                ·
                  refine ⟨10263730655544591058207733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6842487103696394038805155 10263730655544591058207733)
                  ·
                    refine ⟨962224748957305411706975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10263730655544591058207733 962224748957305411706975)
                    ·
                      rfl

theorem cell22_2810889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_2810889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810889 prefixEnd_2810889 := by exact prefixLift 2810889
  have htrace : WordTrace (prefixWord ++ tailWord_2810889) baseStart_2810889 baseEnd_2810889 := by
    simpa [prefixWord, tailWord_2810889, baseEnd_2810889] using wordTrace_append hprefix tailTrace_2810889
  have hstable : (prefixWord ++ tailWord_2810889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810889).length < 2 ^ (prefixWord ++ tailWord_2810889).sum := by decide
  have hdescent : baseEnd_2810889 < baseStart_2810889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810906 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 4, 3]
def baseStart_2810906 : Nat := 118140960795 + 2810906 * 2 ^ 59
def prefixEnd_2810906 : Nat := 4983230072969 + 3 ^ 40 * 2810906 * 2
def baseEnd_2810906 : Nat := 962230568404723034031923

theorem tailTrace_2810906 : CollatzResearch.WordTrace tailWord_2810906 prefixEnd_2810906 962230568404723034031923 := by
  unfold tailWord_2810906
  simp only [CollatzResearch.WordTrace]
  refine ⟨25630541088643775342505143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68348109569716734246680381 25630541088643775342505143)
  ·
    refine ⟨38445811632965663013757715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25630541088643775342505143 38445811632965663013757715)
    ·
      refine ⟨57668717449448494520636573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38445811632965663013757715 57668717449448494520636573)
      ·
        refine ⟨21625769043543185445238715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57668717449448494520636573 21625769043543185445238715)
        ·
          refine ⟨32438653565314778167858073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21625769043543185445238715 32438653565314778167858073)
          ·
            refine ⟨24328990173986083625893555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32438653565314778167858073 24328990173986083625893555)
            ·
              refine ⟨36493485260979125438840333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24328990173986083625893555 36493485260979125438840333)
              ·
                refine ⟨13685056972867172039565125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36493485260979125438840333 13685056972867172039565125)
                ·
                  refine ⟨2565948182412594757418461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13685056972867172039565125 2565948182412594757418461)
                  ·
                    refine ⟨962230568404723034031923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2565948182412594757418461 962230568404723034031923)
                    ·
                      rfl

theorem cell22_2810906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_2810906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810906 prefixEnd_2810906 := by exact prefixLift 2810906
  have htrace : WordTrace (prefixWord ++ tailWord_2810906) baseStart_2810906 baseEnd_2810906 := by
    simpa [prefixWord, tailWord_2810906, baseEnd_2810906] using wordTrace_append hprefix tailTrace_2810906
  have hstable : (prefixWord ++ tailWord_2810906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810906).length < 2 ^ (prefixWord ++ tailWord_2810906).sum := by decide
  have hdescent : baseEnd_2810906 < baseStart_2810906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810908 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 6]
def baseStart_2810908 : Nat := 118140960795 + 2810908 * 2 ^ 59
def prefixEnd_2810908 : Nat := 4983230072969 + 3 ^ 40 * 2810908 * 2
def baseEnd_2810908 : Nat := 320743751015198565160639

theorem tailTrace_2810908 : CollatzResearch.WordTrace tailWord_2810908 prefixEnd_2810908 320743751015198565160639 := by
  unfold tailWord_2810908
  simp only [CollatzResearch.WordTrace]
  refine ⟨51261118650283927855796689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68348158200378570474395585 51261118650283927855796689)
  ·
    refine ⟨38445838987712945891847517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51261118650283927855796689 38445838987712945891847517)
    ·
      refine ⟨14417189620392354709442819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38445838987712945891847517 14417189620392354709442819)
      ·
        refine ⟨21625784430588532064164229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14417189620392354709442819 21625784430588532064164229)
        ·
          refine ⟨4054834580735349762030793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21625784430588532064164229 4054834580735349762030793)
          ·
            refine ⟨3041125935551512321523095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4054834580735349762030793 3041125935551512321523095)
            ·
              refine ⟨4561688903327268482284643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041125935551512321523095 4561688903327268482284643)
              ·
                refine ⟨6842533354990902723426965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4561688903327268482284643 6842533354990902723426965)
                ·
                  refine ⟨320743751015198565160639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6842533354990902723426965 320743751015198565160639)
                  ·
                    rfl

theorem cell22_2810908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_2810908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810908 prefixEnd_2810908 := by exact prefixLift 2810908
  have htrace : WordTrace (prefixWord ++ tailWord_2810908) baseStart_2810908 baseEnd_2810908 := by
    simpa [prefixWord, tailWord_2810908, baseEnd_2810908] using wordTrace_append hprefix tailTrace_2810908
  have hstable : (prefixWord ++ tailWord_2810908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810908).length < 2 ^ (prefixWord ++ tailWord_2810908).sum := by decide
  have hdescent : baseEnd_2810908 < baseStart_2810908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2810981 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 5]
def baseStart_2810981 : Nat := 118140960795 + 2810981 * 2 ^ 59
def prefixEnd_2810981 : Nat := 4983230072969 + 3 ^ 40 * 2810981 * 2
def baseEnd_2810981 : Nat := 320752080812482612802231

theorem tailTrace_2810981 : CollatzResearch.WordTrace tailWord_2810981 prefixEnd_2810981 320752080812482612802231 := by
  unfold tailWord_2810981
  simp only [CollatzResearch.WordTrace]
  refine ⟨102524899829303389179000797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68349933219535592786000531 102524899829303389179000797)
  ·
    refine ⟨38446837435988770942125299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102524899829303389179000797 38446837435988770942125299)
    ·
      refine ⟨57670256153983156413187949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38446837435988770942125299 57670256153983156413187949)
      ·
        refine ⟨21626346057743683654945481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57670256153983156413187949 21626346057743683654945481)
        ·
          refine ⟨16219759543307762741209111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21626346057743683654945481 16219759543307762741209111)
          ·
            refine ⟨24329639314961644111813667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16219759543307762741209111 24329639314961644111813667)
            ·
              refine ⟨36494458972442466167720501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24329639314961644111813667 36494458972442466167720501)
              ·
                refine ⟨3421355528666481203223797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36494458972442466167720501 3421355528666481203223797)
                ·
                  refine ⟨320752080812482612802231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3421355528666481203223797 320752080812482612802231)
                  ·
                    rfl

theorem cell22_2810981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_2810981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2810981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2810981 prefixEnd_2810981 := by exact prefixLift 2810981
  have htrace : WordTrace (prefixWord ++ tailWord_2810981) baseStart_2810981 baseEnd_2810981 := by
    simpa [prefixWord, tailWord_2810981, baseEnd_2810981] using wordTrace_append hprefix tailTrace_2810981
  have hstable : (prefixWord ++ tailWord_2810981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2810981).length < 2 ^ (prefixWord ++ tailWord_2810981).sum := by decide
  have hdescent : baseEnd_2810981 < baseStart_2810981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2810981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811058 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_2811058 : Nat := 118140960795 + 2811058 * 2 ^ 59
def prefixEnd_2811058 : Nat := 4983230072969 + 3 ^ 40 * 2811058 * 2
def baseEnd_2811058 : Nat := 962282601111045304231457

theorem tailTrace_2811058 : CollatzResearch.WordTrace tailWord_2811058 prefixEnd_2811058 962282601111045304231457 := by
  unfold tailWord_2811058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25631927062506107832388457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68351805500016287553035885 25631927062506107832388457)
  ·
    refine ⟨19223945296879580874291343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25631927062506107832388457 19223945296879580874291343)
    ·
      refine ⟨28835917945319371311437015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19223945296879580874291343 28835917945319371311437015)
      ·
        refine ⟨43253876917979056967155523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28835917945319371311437015 43253876917979056967155523)
        ·
          refine ⟨64880815376968585450733285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43253876917979056967155523 64880815376968585450733285)
          ·
            refine ⟨12165152883181609772012491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64880815376968585450733285 12165152883181609772012491)
            ·
              refine ⟨18247729324772414658018737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12165152883181609772012491 18247729324772414658018737)
              ·
                refine ⟨13685796993579310993514053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18247729324772414658018737 13685796993579310993514053)
                ·
                  refine ⟨2566086936296120811283885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13685796993579310993514053 2566086936296120811283885)
                  ·
                    refine ⟨962282601111045304231457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566086936296120811283885 962282601111045304231457)
                    ·
                      rfl

theorem cell22_2811058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_2811058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811058 prefixEnd_2811058 := by exact prefixLift 2811058
  have htrace : WordTrace (prefixWord ++ tailWord_2811058) baseStart_2811058 baseEnd_2811058 := by
    simpa [prefixWord, tailWord_2811058, baseEnd_2811058] using wordTrace_append hprefix tailTrace_2811058
  have hstable : (prefixWord ++ tailWord_2811058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811058).length < 2 ^ (prefixWord ++ tailWord_2811058).sum := by decide
  have hdescent : baseEnd_2811058 < baseStart_2811058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811103 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 3, 3]
def baseStart_2811103 : Nat := 118140960795 + 2811103 * 2 ^ 59
def prefixEnd_2811103 : Nat := 4983230072969 + 3 ^ 40 * 2811103 * 2
def baseEnd_2811103 : Nat := 962298005530680186856319

theorem tailTrace_2811103 : CollatzResearch.WordTrace tailWord_2811103 prefixEnd_2811103 962298005530680186856319 := by
  unfold tailWord_2811103
  simp only [CollatzResearch.WordTrace]
  refine ⟨102529349534861404014941963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68352899689907602676627975 102529349534861404014941963)
  ·
    refine ⟨153794024302292106022412945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102529349534861404014941963 153794024302292106022412945)
    ·
      refine ⟨115345518226719079516809709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153794024302292106022412945 115345518226719079516809709)
      ·
        refine ⟨43254569335019654818803641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115345518226719079516809709 43254569335019654818803641)
        ·
          refine ⟨32440927001264741114102731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43254569335019654818803641 32440927001264741114102731)
          ·
            refine ⟨48661390501897111671154097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32440927001264741114102731 48661390501897111671154097)
            ·
              refine ⟨36496042876422833753365573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48661390501897111671154097 36496042876422833753365573)
              ·
                refine ⟨6843008039329281328756045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36496042876422833753365573 6843008039329281328756045)
                ·
                  refine ⟨2566128014748480498283517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6843008039329281328756045 2566128014748480498283517)
                  ·
                    refine ⟨962298005530680186856319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566128014748480498283517 962298005530680186856319)
                    ·
                      rfl

theorem cell22_2811103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 3].length) (baseStart_2811103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811103 prefixEnd_2811103 := by exact prefixLift 2811103
  have htrace : WordTrace (prefixWord ++ tailWord_2811103) baseStart_2811103 baseEnd_2811103 := by
    simpa [prefixWord, tailWord_2811103, baseEnd_2811103] using wordTrace_append hprefix tailTrace_2811103
  have hstable : (prefixWord ++ tailWord_2811103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811103).length < 2 ^ (prefixWord ++ tailWord_2811103).sum := by decide
  have hdescent : baseEnd_2811103 < baseStart_2811103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811137 : List Nat := [1, 2, 4, 1, 1, 4, 1, 4, 1, 3]
def baseStart_2811137 : Nat := 118140960795 + 2811137 * 2 ^ 59
def prefixEnd_2811137 : Nat := 4983230072969 + 3 ^ 40 * 2811137 * 2
def baseEnd_2811137 : Nat := 962309644425515431506215

theorem tailTrace_2811137 : CollatzResearch.WordTrace tailWord_2811137 prefixEnd_2811137 962309644425515431506215 := by
  unfold tailWord_2811137
  simp only [CollatzResearch.WordTrace]
  refine ⟨102530589616738227821679665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68353726411158818547786443 102530589616738227821679665)
  ·
    refine ⟨76897942212553670866259749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102530589616738227821679665 76897942212553670866259749)
    ·
      refine ⟨14418364164853813287423703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76897942212553670866259749 14418364164853813287423703)
      ·
        refine ⟨21627546247280719931135555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14418364164853813287423703 21627546247280719931135555)
        ·
          refine ⟨32441319370921079896703333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21627546247280719931135555 32441319370921079896703333)
          ·
            refine ⟨6082747382047702480631875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32441319370921079896703333 6082747382047702480631875)
            ·
              refine ⟨9124121073071553720947813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082747382047702480631875 9124121073071553720947813)
              ·
                refine ⟨1710772701200916322677715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9124121073071553720947813 1710772701200916322677715)
                ·
                  refine ⟨2566159051801374484016573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710772701200916322677715 2566159051801374484016573)
                  ·
                    refine ⟨962309644425515431506215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566159051801374484016573 962309644425515431506215)
                    ·
                      rfl

theorem cell22_2811137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_2811137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811137 prefixEnd_2811137 := by exact prefixLift 2811137
  have htrace : WordTrace (prefixWord ++ tailWord_2811137) baseStart_2811137 baseEnd_2811137 := by
    simpa [prefixWord, tailWord_2811137, baseEnd_2811137] using wordTrace_append hprefix tailTrace_2811137
  have hstable : (prefixWord ++ tailWord_2811137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811137).length < 2 ^ (prefixWord ++ tailWord_2811137).sum := by decide
  have hdescent : baseEnd_2811137 < baseStart_2811137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811148 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_2811148 : Nat := 118140960795 + 2811148 * 2 ^ 59
def prefixEnd_2811148 : Nat := 4983230072969 + 3 ^ 40 * 2811148 * 2
def baseEnd_2811148 : Nat := 962313409950315069481181

theorem tailTrace_2811148 : CollatzResearch.WordTrace tailWord_2811148 prefixEnd_2811148 962313409950315069481181 := by
  unfold tailWord_2811148
  simp only [CollatzResearch.WordTrace]
  refine ⟨51265495409849188350165049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68353993879798917800220065 51265495409849188350165049)
  ·
    refine ⟨38449121557386891262623787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51265495409849188350165049 38449121557386891262623787)
    ·
      refine ⟨57673682336080336893935681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38449121557386891262623787 57673682336080336893935681)
      ·
        refine ⟨43255261752060252670451761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57673682336080336893935681 43255261752060252670451761)
        ·
          refine ⟨32441446314045189502838821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43255261752060252670451761 32441446314045189502838821)
          ·
            refine ⟨6082771183883473031782279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32441446314045189502838821 6082771183883473031782279)
            ·
              refine ⟨9124156775825209547673419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082771183883473031782279 9124156775825209547673419)
              ·
                refine ⟨13686235163737814321510129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9124156775825209547673419 13686235163737814321510129)
                ·
                  refine ⟨10264676372803360741132597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13686235163737814321510129 10264676372803360741132597)
                  ·
                    refine ⟨962313409950315069481181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10264676372803360741132597 962313409950315069481181)
                    ·
                      rfl

theorem cell22_2811148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_2811148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811148 prefixEnd_2811148 := by exact prefixLift 2811148
  have htrace : WordTrace (prefixWord ++ tailWord_2811148) baseStart_2811148 baseEnd_2811148 := by
    simpa [prefixWord, tailWord_2811148, baseEnd_2811148] using wordTrace_append hprefix tailTrace_2811148
  have hstable : (prefixWord ++ tailWord_2811148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811148).length < 2 ^ (prefixWord ++ tailWord_2811148).sum := by decide
  have hdescent : baseEnd_2811148 < baseStart_2811148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811154 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2811154 : Nat := 118140960795 + 2811154 * 2 ^ 59
def prefixEnd_2811154 : Nat := 4983230072969 + 3 ^ 40 * 2811154 * 2
def baseEnd_2811154 : Nat := 962315463872933053831163

theorem tailTrace_2811154 : CollatzResearch.WordTrace tailWord_2811154 prefixEnd_2811154 962315463872933053831163 := by
  unfold tailWord_2811154
  simp only [CollatzResearch.WordTrace]
  refine ⟨25632802414419159931262129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68354139771784426483365677 25632802414419159931262129)
  ·
    refine ⟨19224601810814369948446597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25632802414419159931262129 19224601810814369948446597)
    ·
      refine ⟨3604612839527694365333737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19224601810814369948446597 3604612839527694365333737)
      ·
        refine ⟨2703459629645770774000303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3604612839527694365333737 2703459629645770774000303)
        ·
          refine ⟨4055189444468656161000455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703459629645770774000303 4055189444468656161000455)
          ·
            refine ⟨6082784166702984241500683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055189444468656161000455 6082784166702984241500683)
            ·
              refine ⟨9124176250054476362251025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082784166702984241500683 9124176250054476362251025)
              ·
                refine ⟨6843132187540857271688269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9124176250054476362251025 6843132187540857271688269)
                ·
                  refine ⟨2566174570327821476883101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6843132187540857271688269 2566174570327821476883101)
                  ·
                    refine ⟨962315463872933053831163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566174570327821476883101 962315463872933053831163)
                    ·
                      rfl

theorem cell22_2811154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2811154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811154 prefixEnd_2811154 := by exact prefixLift 2811154
  have htrace : WordTrace (prefixWord ++ tailWord_2811154) baseStart_2811154 baseEnd_2811154 := by
    simpa [prefixWord, tailWord_2811154, baseEnd_2811154] using wordTrace_append hprefix tailTrace_2811154
  have hstable : (prefixWord ++ tailWord_2811154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811154).length < 2 ^ (prefixWord ++ tailWord_2811154).sum := by decide
  have hdescent : baseEnd_2811154 < baseStart_2811154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811163 : List Nat := [1, 1, 1, 1, 1, 1, 5, 6, 1, 4]
def baseStart_2811163 : Nat := 118140960795 + 2811163 * 2 ^ 59
def prefixEnd_2811163 : Nat := 4983230072969 + 3 ^ 40 * 2811163 * 2
def baseEnd_2811163 : Nat := 962318544756860030356135

theorem tailTrace_2811163 : CollatzResearch.WordTrace tailWord_2811163 prefixEnd_2811163 962318544756860030356135 := by
  unfold tailWord_2811163
  simp only [CollatzResearch.WordTrace]
  refine ⟨102531537914644034262126143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68354358609762689508084095 102531537914644034262126143)
  ·
    refine ⟨153797306871966051393189215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102531537914644034262126143 153797306871966051393189215)
    ·
      refine ⟨230695960307949077089783823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153797306871966051393189215 230695960307949077089783823)
      ·
        refine ⟨346043940461923615634675735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230695960307949077089783823 346043940461923615634675735)
        ·
          refine ⟨519065910692885423452013603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346043940461923615634675735 519065910692885423452013603)
          ·
            refine ⟨778598866039328135178020405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519065910692885423452013603 778598866039328135178020405)
            ·
              refine ⟨72993643691187012672939413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 778598866039328135178020405 72993643691187012672939413)
              ·
                refine ⟨3421577048024391219044035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72993643691187012672939413 3421577048024391219044035)
                ·
                  refine ⟨5132365572036586828566053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3421577048024391219044035 5132365572036586828566053)
                  ·
                    refine ⟨962318544756860030356135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5132365572036586828566053 962318544756860030356135)
                    ·
                      rfl

theorem cell22_2811163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 4].length) (baseStart_2811163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811163 prefixEnd_2811163 := by exact prefixLift 2811163
  have htrace : WordTrace (prefixWord ++ tailWord_2811163) baseStart_2811163 baseEnd_2811163 := by
    simpa [prefixWord, tailWord_2811163, baseEnd_2811163] using wordTrace_append hprefix tailTrace_2811163
  have hstable : (prefixWord ++ tailWord_2811163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811163).length < 2 ^ (prefixWord ++ tailWord_2811163).sum := by decide
  have hdescent : baseEnd_2811163 < baseStart_2811163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811210 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_2811210 : Nat := 118140960795 + 2811210 * 2 ^ 59
def prefixEnd_2811210 : Nat := 4983230072969 + 3 ^ 40 * 2811210 * 2
def baseEnd_2811210 : Nat := 962334633817367574430991

theorem tailTrace_2811210 : CollatzResearch.WordTrace tailWord_2811210 prefixEnd_2811210 962334633817367574430991 := by
  unfold tailWord_2811210
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633313036368440322271771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68355501430315840859391389 25633313036368440322271771)
  ·
    refine ⟨38449969554552660483407657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25633313036368440322271771 38449969554552660483407657)
    ·
      refine ⟨28837477165914495362555743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38449969554552660483407657 28837477165914495362555743)
      ·
        refine ⟨43256215748871743043833615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28837477165914495362555743 43256215748871743043833615)
        ·
          refine ⟨64884323623307614565750423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43256215748871743043833615 64884323623307614565750423)
          ·
            refine ⟨97326485434961421848625635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64884323623307614565750423 97326485434961421848625635)
            ·
              refine ⟨145989728152442132772938453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97326485434961421848625635 145989728152442132772938453)
              ·
                refine ⟨3421634253572862486865745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 145989728152442132772938453 3421634253572862486865745)
                ·
                  refine ⟨2566225690179646865149309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3421634253572862486865745 2566225690179646865149309)
                  ·
                    refine ⟨962334633817367574430991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566225690179646865149309 962334633817367574430991)
                    ·
                      rfl

theorem cell22_2811210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_2811210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811210 prefixEnd_2811210 := by exact prefixLift 2811210
  have htrace : WordTrace (prefixWord ++ tailWord_2811210) baseStart_2811210 baseEnd_2811210 := by
    simpa [prefixWord, tailWord_2811210, baseEnd_2811210] using wordTrace_append hprefix tailTrace_2811210
  have hstable : (prefixWord ++ tailWord_2811210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811210).length < 2 ^ (prefixWord ++ tailWord_2811210).sum := by decide
  have hdescent : baseEnd_2811210 < baseStart_2811210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811222 : List Nat := [5, 2, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2811222 : Nat := 118140960795 + 2811222 * 2 ^ 59
def prefixEnd_2811222 : Nat := 4983230072969 + 3 ^ 40 * 2811222 * 2
def baseEnd_2811222 : Nat := 962338741662603543130955

theorem tailTrace_2811222 : CollatzResearch.WordTrace tailWord_2811222 prefixEnd_2811222 962338741662603543130955 := by
  unfold tailWord_2811222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6408355613839392958657745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68355793214286858225682613 6408355613839392958657745)
  ·
    refine ⟨4806266710379544718993309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6408355613839392958657745 4806266710379544718993309)
    ·
      refine ⟨1802350016392329269622491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4806266710379544718993309 1802350016392329269622491)
      ·
        refine ⟨2703525024588493904433737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802350016392329269622491 2703525024588493904433737)
        ·
          refine ⟨2027643768441370428325303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2703525024588493904433737 2027643768441370428325303)
          ·
            refine ⟨3041465652662055642487955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027643768441370428325303 3041465652662055642487955)
            ·
              refine ⟨4562198478993083463731933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041465652662055642487955 4562198478993083463731933)
              ·
                refine ⟨1710824429622406298899475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4562198478993083463731933 1710824429622406298899475)
                ·
                  refine ⟨2566236644433609448349213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1710824429622406298899475 2566236644433609448349213)
                  ·
                    refine ⟨962338741662603543130955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566236644433609448349213 962338741662603543130955)
                    ·
                      rfl

theorem cell22_2811222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2811222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811222 prefixEnd_2811222 := by exact prefixLift 2811222
  have htrace : WordTrace (prefixWord ++ tailWord_2811222) baseStart_2811222 baseEnd_2811222 := by
    simpa [prefixWord, tailWord_2811222, baseEnd_2811222] using wordTrace_append hprefix tailTrace_2811222
  have hstable : (prefixWord ++ tailWord_2811222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811222).length < 2 ^ (prefixWord ++ tailWord_2811222).sum := by decide
  have hdescent : baseEnd_2811222 < baseStart_2811222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811223 : List Nat := [1, 1, 3, 2, 3, 3, 1, 8]
def baseStart_2811223 : Nat := 118140960795 + 2811223 * 2 ^ 59
def prefixEnd_2811223 : Nat := 4983230072969 + 3 ^ 40 * 2811223 * 2
def baseEnd_2811223 : Nat := 106926564887004430428439

theorem tailTrace_2811223 : CollatzResearch.WordTrace tailWord_2811223 prefixEnd_2811223 106926564887004430428439 := by
  unfold tailWord_2811223
  simp only [CollatzResearch.WordTrace]
  refine ⟨102533726294426664509310323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68355817529617776339540215 102533726294426664509310323)
  ·
    refine ⟨153800589441639996763965485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102533726294426664509310323 153800589441639996763965485)
    ·
      refine ⟨57675221040614998786487057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153800589441639996763965485 57675221040614998786487057)
      ·
        refine ⟨43256415780461249089865293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57675221040614998786487057 43256415780461249089865293)
        ·
          refine ⟨16221155917672968408699485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43256415780461249089865293 16221155917672968408699485)
          ·
            refine ⟨6082933469127363153262307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16221155917672968408699485 6082933469127363153262307)
            ·
              refine ⟨9124400203691044729893461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082933469127363153262307 9124400203691044729893461)
              ·
                refine ⟨106926564887004430428439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9124400203691044729893461 106926564887004430428439)
                ·
                  rfl

theorem cell22_2811223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 8].length) (baseStart_2811223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811223 prefixEnd_2811223 := by exact prefixLift 2811223
  have htrace : WordTrace (prefixWord ++ tailWord_2811223) baseStart_2811223 baseEnd_2811223 := by
    simpa [prefixWord, tailWord_2811223, baseEnd_2811223] using wordTrace_append hprefix tailTrace_2811223
  have hstable : (prefixWord ++ tailWord_2811223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811223).length < 2 ^ (prefixWord ++ tailWord_2811223).sum := by decide
  have hdescent : baseEnd_2811223 < baseStart_2811223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811240 : List Nat := [2, 1, 4, 2, 3, 2, 8]
def baseStart_2811240 : Nat := 118140960795 + 2811240 * 2 ^ 59
def prefixEnd_2811240 : Nat := 4983230072969 + 3 ^ 40 * 2811240 * 2
def baseEnd_2811240 : Nat := 35642403830757685043737

theorem tailTrace_2811240 : CollatzResearch.WordTrace tailWord_2811240 prefixEnd_2811240 35642403830757685043737 := by
  unfold tailWord_2811240
  simp only [CollatzResearch.WordTrace]
  refine ⟨51267173167682538206339587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68356230890243384275119449 51267173167682538206339587)
  ·
    refine ⟨76900759751523807309509381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51267173167682538206339587 76900759751523807309509381)
    ·
      refine ⟨14418892453410713870533009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76900759751523807309509381 14418892453410713870533009)
      ·
        refine ⟨10814169340058035402899757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14418892453410713870533009 10814169340058035402899757)
        ·
          refine ⟨4055313502521763276087409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10814169340058035402899757 4055313502521763276087409)
          ·
            refine ⟨3041485126891322457065557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4055313502521763276087409 3041485126891322457065557)
            ·
              refine ⟨35642403830757685043737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3041485126891322457065557 35642403830757685043737)
              ·
                rfl

theorem cell22_2811240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 8].length) (baseStart_2811240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811240 prefixEnd_2811240 := by exact prefixLift 2811240
  have htrace : WordTrace (prefixWord ++ tailWord_2811240) baseStart_2811240 baseEnd_2811240 := by
    simpa [prefixWord, tailWord_2811240, baseEnd_2811240] using wordTrace_append hprefix tailTrace_2811240
  have hstable : (prefixWord ++ tailWord_2811240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811240).length < 2 ^ (prefixWord ++ tailWord_2811240).sum := by decide
  have hdescent : baseEnd_2811240 < baseStart_2811240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811242 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2811242 : Nat := 118140960795 + 2811242 * 2 ^ 59
def prefixEnd_2811242 : Nat := 4983230072969 + 3 ^ 40 * 2811242 * 2
def baseEnd_2811242 : Nat := 962345588071330157630893

theorem tailTrace_2811242 : CollatzResearch.WordTrace tailWord_2811242 prefixEnd_2811242 962345588071330157630893 := by
  unfold tailWord_2811242
  simp only [CollatzResearch.WordTrace]
  refine ⟨25633604820339457688562995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68356279520905220502834653 25633604820339457688562995)
  ·
    refine ⟨38450407230509186532844493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25633604820339457688562995 38450407230509186532844493)
    ·
      refine ⟨14418902711440944949816685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38450407230509186532844493 14418902711440944949816685)
      ·
        refine ⟨5407088516790354356181257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14418902711440944949816685 5407088516790354356181257)
        ·
          refine ⟨4055316387592765767135943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5407088516790354356181257 4055316387592765767135943)
          ·
            refine ⟨6082974581389148650703915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055316387592765767135943 6082974581389148650703915)
            ·
              refine ⟨9124461872083722976055873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6082974581389148650703915 9124461872083722976055873)
              ·
                refine ⟨6843346404062792232041905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9124461872083722976055873 6843346404062792232041905)
                ·
                  refine ⟨5132509803047094174031429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6843346404062792232041905 5132509803047094174031429)
                  ·
                    refine ⟨962345588071330157630893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5132509803047094174031429 962345588071330157630893)
                    ·
                      rfl

theorem cell22_2811242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2811242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811242 prefixEnd_2811242 := by exact prefixLift 2811242
  have htrace : WordTrace (prefixWord ++ tailWord_2811242) baseStart_2811242 baseEnd_2811242 := by
    simpa [prefixWord, tailWord_2811242, baseEnd_2811242] using wordTrace_append hprefix tailTrace_2811242
  have hstable : (prefixWord ++ tailWord_2811242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811242).length < 2 ^ (prefixWord ++ tailWord_2811242).sum := by decide
  have hdescent : baseEnd_2811242 < baseStart_2811242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811246 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_2811246 : Nat := 118140960795 + 2811246 * 2 ^ 59
def prefixEnd_2811246 : Nat := 4983230072969 + 3 ^ 40 * 2811246 * 2
def baseEnd_2811246 : Nat := 320782319117691826843627

theorem tailTrace_2811246 : CollatzResearch.WordTrace tailWord_2811246 prefixEnd_2811246 320782319117691826843627 := by
  unfold tailWord_2811246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12816820646667917429674699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68356376782228892958265061 12816820646667917429674699)
  ·
    refine ⟨19225230970001876144512049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12816820646667917429674699 19225230970001876144512049)
    ·
      refine ⟨14418923227501407108384037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19225230970001876144512049 14418923227501407108384037)
      ·
        refine ⟨2703548105156513832822007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14418923227501407108384037 2703548105156513832822007)
        ·
          refine ⟨4055322157734770749233011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703548105156513832822007 4055322157734770749233011)
          ·
            refine ⟨6082983236602156123849517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055322157734770749233011 6082983236602156123849517)
            ·
              refine ⟨2281118713725808546443569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6082983236602156123849517 2281118713725808546443569)
              ·
                refine ⟨1710839035294356409832677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281118713725808546443569 1710839035294356409832677)
                ·
                  refine ⟨320782319117691826843627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1710839035294356409832677 320782319117691826843627)
                  ·
                    rfl

theorem cell22_2811246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_2811246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811246 prefixEnd_2811246 := by exact prefixLift 2811246
  have htrace : WordTrace (prefixWord ++ tailWord_2811246) baseStart_2811246 baseEnd_2811246 := by
    simpa [prefixWord, tailWord_2811246, baseEnd_2811246] using wordTrace_append hprefix tailTrace_2811246
  have hstable : (prefixWord ++ tailWord_2811246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811246).length < 2 ^ (prefixWord ++ tailWord_2811246).sum := by decide
  have hdescent : baseEnd_2811246 < baseStart_2811246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811332 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2811332 : Nat := 118140960795 + 2811332 * 2 ^ 59
def prefixEnd_2811332 : Nat := 4983230072969 + 3 ^ 40 * 2811332 * 2
def baseEnd_2811332 : Nat := 962376396910599922880617

theorem tailTrace_2811332 : CollatzResearch.WordTrace tailWord_2811332 prefixEnd_2811332 962376396910599922880617 := by
  unfold tailWord_2811332
  simp only [CollatzResearch.WordTrace]
  refine ⟨51268850925515888062514125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68358467900687850750018833 51268850925515888062514125)
  ·
    refine ⟨19225819097068458023442797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51268850925515888062514125 19225819097068458023442797)
    ·
      refine ⟨7209682161400671758791049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19225819097068458023442797 7209682161400671758791049)
      ·
        refine ⟨5407261621050503819093287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7209682161400671758791049 5407261621050503819093287)
        ·
          refine ⟨8110892431575755728639931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407261621050503819093287 8110892431575755728639931)
          ·
            refine ⟨12166338647363633592959897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8110892431575755728639931 12166338647363633592959897)
            ·
              refine ⟨9124753985522725194719923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12166338647363633592959897 9124753985522725194719923)
              ·
                refine ⟨13687130978284087792079885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9124753985522725194719923 13687130978284087792079885)
                ·
                  refine ⟨5132674116856532922029957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13687130978284087792079885 5132674116856532922029957)
                  ·
                    refine ⟨962376396910599922880617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5132674116856532922029957 962376396910599922880617)
                    ·
                      rfl

theorem cell22_2811332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2811332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811332 prefixEnd_2811332 := by exact prefixLift 2811332
  have htrace : WordTrace (prefixWord ++ tailWord_2811332) baseStart_2811332 baseEnd_2811332 := by
    simpa [prefixWord, tailWord_2811332, baseEnd_2811332] using wordTrace_append hprefix tailTrace_2811332
  have hstable : (prefixWord ++ tailWord_2811332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811332).length < 2 ^ (prefixWord ++ tailWord_2811332).sum := by decide
  have hdescent : baseEnd_2811332 < baseStart_2811332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811420 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_2811420 : Nat := 118140960795 + 2811420 * 2 ^ 59
def prefixEnd_2811420 : Nat := 4983230072969 + 3 ^ 40 * 2811420 * 2
def baseEnd_2811420 : Nat := 320802173702999008893449

theorem tailTrace_2811420 : CollatzResearch.WordTrace tailWord_2811420 prefixEnd_2811420 320802173702999008893449 := by
  unfold tailWord_2811420
  simp only [CollatzResearch.WordTrace]
  refine ⟨51270455737356483577115857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68360607649808644769487809 51270455737356483577115857)
  ·
    refine ⟨38452841803017362682836893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51270455737356483577115857 38452841803017362682836893)
    ·
      refine ⟨14419815676131511006063835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38452841803017362682836893 14419815676131511006063835)
      ·
        refine ⟨21629723514197266509095753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14419815676131511006063835 21629723514197266509095753)
        ·
          refine ⟨16222292635647949881821815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21629723514197266509095753 16222292635647949881821815)
          ·
            refine ⟨24333438953471924822732723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16222292635647949881821815 24333438953471924822732723)
            ·
              refine ⟨36500158430207887234099085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24333438953471924822732723 36500158430207887234099085)
              ·
                refine ⟨13687559411327957712787157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36500158430207887234099085 13687559411327957712787157)
                ·
                  refine ⟨320802173702999008893449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13687559411327957712787157 320802173702999008893449)
                  ·
                    rfl

theorem cell22_2811420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_2811420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811420 prefixEnd_2811420 := by exact prefixLift 2811420
  have htrace : WordTrace (prefixWord ++ tailWord_2811420) baseStart_2811420 baseEnd_2811420 := by
    simpa [prefixWord, tailWord_2811420, baseEnd_2811420] using wordTrace_append hprefix tailTrace_2811420
  have hstable : (prefixWord ++ tailWord_2811420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811420).length < 2 ^ (prefixWord ++ tailWord_2811420).sum := by decide
  have hdescent : baseEnd_2811420 < baseStart_2811420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811424 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_2811424 : Nat := 118140960795 + 2811424 * 2 ^ 59
def prefixEnd_2811424 : Nat := 4983230072969 + 3 ^ 40 * 2811424 * 2
def baseEnd_2811424 : Nat := 962407890390742349580335

theorem tailTrace_2811424 : CollatzResearch.WordTrace tailWord_2811424 prefixEnd_2811424 962407890390742349580335 := by
  unfold tailWord_2811424
  simp only [CollatzResearch.WordTrace]
  refine ⟨51270528683349237918688663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68360704911132317224918217 51270528683349237918688663)
  ·
    refine ⟨76905793025023856878032995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51270528683349237918688663 76905793025023856878032995)
    ·
      refine ⟨115358689537535785317049493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76905793025023856878032995 115358689537535785317049493)
      ·
        refine ⟨5407438572071989936736695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115358689537535785317049493 5407438572071989936736695)
        ·
          refine ⟨8111157858107984905105043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407438572071989936736695 8111157858107984905105043)
          ·
            refine ⟨12166736787161977357657565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8111157858107984905105043 12166736787161977357657565)
            ·
              refine ⟨4562526295185741509121587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12166736787161977357657565 4562526295185741509121587)
              ·
                refine ⟨6843789442778612263682381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562526295185741509121587 6843789442778612263682381)
                ·
                  refine ⟨2566421041041979598880893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6843789442778612263682381 2566421041041979598880893)
                  ·
                    refine ⟨962407890390742349580335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566421041041979598880893 962407890390742349580335)
                    ·
                      rfl

theorem cell22_2811424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_2811424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811424 prefixEnd_2811424 := by exact prefixLift 2811424
  have htrace : WordTrace (prefixWord ++ tailWord_2811424) baseStart_2811424 baseEnd_2811424 := by
    simpa [prefixWord, tailWord_2811424, baseEnd_2811424] using wordTrace_append hprefix tailTrace_2811424
  have hstable : (prefixWord ++ tailWord_2811424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811424).length < 2 ^ (prefixWord ++ tailWord_2811424).sum := by decide
  have hdescent : baseEnd_2811424 < baseStart_2811424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811480 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_2811480 : Nat := 118140960795 + 2811480 * 2 ^ 59
def prefixEnd_2811480 : Nat := 4983230072969 + 3 ^ 40 * 2811480 * 2
def baseEnd_2811480 : Nat := 962427060335176870180163

theorem tailTrace_2811480 : CollatzResearch.WordTrace tailWord_2811480 prefixEnd_2811480 962427060335176870180163 := by
  unfold tailWord_2811480
  simp only [CollatzResearch.WordTrace]
  refine ⟨51271549927247798700707947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68362066569663731600943929 51271549927247798700707947)
  ·
    refine ⟨76907324890871698051061921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51271549927247798700707947 76907324890871698051061921)
    ·
      refine ⟨57680493668153773538296441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76907324890871698051061921 57680493668153773538296441)
      ·
        refine ⟨43260370251115330153722331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57680493668153773538296441 43260370251115330153722331)
        ·
          refine ⟨64890555376672995230583497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43260370251115330153722331 64890555376672995230583497)
          ·
            refine ⟨48667916532504746422937623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64890555376672995230583497 48667916532504746422937623)
            ·
              refine ⟨73001874798757119634406435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48667916532504746422937623 73001874798757119634406435)
              ·
                refine ⟨109502812198135679451609653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73001874798757119634406435 109502812198135679451609653)
                ·
                  refine ⟨10265888643575219948588405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109502812198135679451609653 10265888643575219948588405)
                  ·
                    refine ⟨962427060335176870180163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10265888643575219948588405 962427060335176870180163)
                    ·
                      rfl

theorem cell22_2811480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_2811480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811480 prefixEnd_2811480 := by exact prefixLift 2811480
  have htrace : WordTrace (prefixWord ++ tailWord_2811480) baseStart_2811480 baseEnd_2811480 := by
    simpa [prefixWord, tailWord_2811480, baseEnd_2811480] using wordTrace_append hprefix tailTrace_2811480
  have hstable : (prefixWord ++ tailWord_2811480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811480).length < 2 ^ (prefixWord ++ tailWord_2811480).sum := by decide
  have hdescent : baseEnd_2811480 < baseStart_2811480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811548 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2811548 : Nat := 118140960795 + 2811548 * 2 ^ 59
def prefixEnd_2811548 : Nat := 4983230072969 + 3 ^ 40 * 2811548 * 2
def baseEnd_2811548 : Nat := 962450338124847359479955

theorem tailTrace_2811548 : CollatzResearch.WordTrace tailWord_2811548 prefixEnd_2811548 962450338124847359479955 := by
  unfold tailWord_2811548
  simp only [CollatzResearch.WordTrace]
  refine ⟨51272790009124622507445649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68363720012166163343260865 51272790009124622507445649)
  ·
    refine ⟨38454592506843466880584237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51272790009124622507445649 38454592506843466880584237)
    ·
      refine ⟨14420472190066300080219089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38454592506843466880584237 14420472190066300080219089)
      ·
        refine ⟨10815354142549725060164317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14420472190066300080219089 10815354142549725060164317)
        ·
          refine ⟨4055757803456146897561619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10815354142549725060164317 4055757803456146897561619)
          ·
            refine ⟨6083636705184220346342429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055757803456146897561619 6083636705184220346342429)
            ·
              refine ⟨2281363764444082629878411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6083636705184220346342429 2281363764444082629878411)
              ·
                refine ⟨3422045646666123944817617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281363764444082629878411 3422045646666123944817617)
                ·
                  refine ⟨2566534234999592958613213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422045646666123944817617 2566534234999592958613213)
                  ·
                    refine ⟨962450338124847359479955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566534234999592958613213 962450338124847359479955)
                    ·
                      rfl

theorem cell22_2811548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2811548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811548 prefixEnd_2811548 := by exact prefixLift 2811548
  have htrace : WordTrace (prefixWord ++ tailWord_2811548) baseStart_2811548 baseEnd_2811548 := by
    simpa [prefixWord, tailWord_2811548, baseEnd_2811548] using wordTrace_append hprefix tailTrace_2811548
  have hstable : (prefixWord ++ tailWord_2811548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811548).length < 2 ^ (prefixWord ++ tailWord_2811548).sum := by decide
  have hdescent : baseEnd_2811548 < baseStart_2811548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811649 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2811649 : Nat := 118140960795 + 2811649 * 2 ^ 59
def prefixEnd_2811649 : Nat := 4983230072969 + 3 ^ 40 * 2811649 * 2
def baseEnd_2811649 : Nat := 962484912488916762704645

theorem tailTrace_2811649 : CollatzResearch.WordTrace tailWord_2811649 prefixEnd_2811649 962484912488916762704645 := by
  unfold tailWord_2811649
  simp only [CollatzResearch.WordTrace]
  refine ⟨102549263790883339264318001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68366175860588892842878667 102549263790883339264318001)
  ·
    refine ⟨76911947843162504448238501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102549263790883339264318001 76911947843162504448238501)
    ·
      refine ⟨14420990220592969584044719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76911947843162504448238501 14420990220592969584044719)
      ·
        refine ⟨21631485330889454376067079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14420990220592969584044719 21631485330889454376067079)
        ·
          refine ⟨32447227996334181564100619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21631485330889454376067079 32447227996334181564100619)
          ·
            refine ⟨48670841994501272346150929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32447227996334181564100619 48670841994501272346150929)
            ·
              refine ⟨36503131495875954259613197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48670841994501272346150929 36503131495875954259613197)
              ·
                refine ⟨13688674310953482847354949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36503131495875954259613197 13688674310953482847354949)
                ·
                  refine ⟨2566626433303778033879053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13688674310953482847354949 2566626433303778033879053)
                  ·
                    refine ⟨962484912488916762704645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566626433303778033879053 962484912488916762704645)
                    ·
                      rfl

theorem cell22_2811649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2811649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811649 prefixEnd_2811649 := by exact prefixLift 2811649
  have htrace : WordTrace (prefixWord ++ tailWord_2811649) baseStart_2811649 baseEnd_2811649 := by
    simpa [prefixWord, tailWord_2811649, baseEnd_2811649] using wordTrace_append hprefix tailTrace_2811649
  have hstable : (prefixWord ++ tailWord_2811649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811649).length < 2 ^ (prefixWord ++ tailWord_2811649).sum := by decide
  have hdescent : baseEnd_2811649 < baseStart_2811649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811651 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 4]
def baseStart_2811651 : Nat := 118140960795 + 2811651 * 2 ^ 59
def prefixEnd_2811651 : Nat := 4983230072969 + 3 ^ 40 * 2811651 * 2
def baseEnd_2811651 : Nat := 320828532376596474718213

theorem tailTrace_2811651 : CollatzResearch.WordTrace tailWord_2811651 prefixEnd_2811651 320828532376596474718213 := by
  unfold tailWord_2811651
  simp only [CollatzResearch.WordTrace]
  refine ⟨102549336736876093605890807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68366224491250729070593871 102549336736876093605890807)
  ·
    refine ⟨153824005105314140408836211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102549336736876093605890807 153824005105314140408836211)
    ·
      refine ⟨230736007657971210613254317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153824005105314140408836211 230736007657971210613254317)
      ·
        refine ⟨86526002871739203979970369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230736007657971210613254317 86526002871739203979970369)
        ·
          refine ⟨64894502153804402984977777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86526002871739203979970369 64894502153804402984977777)
          ·
            refine ⟨48670876615353302238733333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64894502153804402984977777 48670876615353302238733333)
            ·
              refine ⟨2281447341344686042440625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48670876615353302238733333 2281447341344686042440625)
              ·
                refine ⟨1711085506008514531830469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2281447341344686042440625 1711085506008514531830469)
                ·
                  refine ⟨320828532376596474718213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711085506008514531830469 320828532376596474718213)
                  ·
                    rfl

theorem cell22_2811651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 4].length) (baseStart_2811651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811651 prefixEnd_2811651 := by exact prefixLift 2811651
  have htrace : WordTrace (prefixWord ++ tailWord_2811651) baseStart_2811651 baseEnd_2811651 := by
    simpa [prefixWord, tailWord_2811651, baseEnd_2811651] using wordTrace_append hprefix tailTrace_2811651
  have hstable : (prefixWord ++ tailWord_2811651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811651).length < 2 ^ (prefixWord ++ tailWord_2811651).sum := by decide
  have hdescent : baseEnd_2811651 < baseStart_2811651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811666 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2811666 : Nat := 118140960795 + 2811666 * 2 ^ 59
def prefixEnd_2811666 : Nat := 4983230072969 + 3 ^ 40 * 2811666 * 2
def baseEnd_2811666 : Nat := 962490731936334385029593

theorem tailTrace_2811666 : CollatzResearch.WordTrace tailWord_2811666 prefixEnd_2811666 962490731936334385029593 := by
  unfold tailWord_2811666
  simp only [CollatzResearch.WordTrace]
  refine ⟨25637470957955437791921713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68366589221214500778457901 25637470957955437791921713)
  ·
    refine ⟨19228103218466578343941285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25637470957955437791921713 19228103218466578343941285)
    ·
      refine ⟨3605269353462483439488991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19228103218466578343941285 3605269353462483439488991)
      ·
        refine ⟨5407904030193725159233487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605269353462483439488991 5407904030193725159233487)
        ·
          refine ⟨8111856045290587738850231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407904030193725159233487 8111856045290587738850231)
          ·
            refine ⟨12167784067935881608275347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8111856045290587738850231 12167784067935881608275347)
            ·
              refine ⟨18251676101903822412413021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12167784067935881608275347 18251676101903822412413021)
              ·
                refine ⟨6844378538213933404654883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18251676101903822412413021 6844378538213933404654883)
                ·
                  refine ⟨10266567807320900106982325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844378538213933404654883 10266567807320900106982325)
                  ·
                    refine ⟨962490731936334385029593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10266567807320900106982325 962490731936334385029593)
                    ·
                      rfl

theorem cell22_2811666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2811666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811666 prefixEnd_2811666 := by exact prefixLift 2811666
  have htrace : WordTrace (prefixWord ++ tailWord_2811666) baseStart_2811666 baseEnd_2811666 := by
    simpa [prefixWord, tailWord_2811666, baseEnd_2811666] using wordTrace_append hprefix tailTrace_2811666
  have hstable : (prefixWord ++ tailWord_2811666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811666).length < 2 ^ (prefixWord ++ tailWord_2811666).sum := by decide
  have hdescent : baseEnd_2811666 < baseStart_2811666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811679 : List Nat := [1, 1, 2, 4, 2, 1, 5, 6]
def baseStart_2811679 : Nat := 118140960795 + 2811679 * 2 ^ 59
def prefixEnd_2811679 : Nat := 4983230072969 + 3 ^ 40 * 2811679 * 2
def baseEnd_2811679 : Nat := 106943909122445187161617

theorem tailTrace_2811679 : CollatzResearch.WordTrace tailWord_2811679 prefixEnd_2811679 106943909122445187161617 := by
  unfold tailWord_2811679
  simp only [CollatzResearch.WordTrace]
  refine ⟨102550357980774654387910091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68366905320516436258606727 102550357980774654387910091)
  ·
    refine ⟨153825536971161981581865137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102550357980774654387910091 153825536971161981581865137)
    ·
      refine ⟨115369152728371486186398853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153825536971161981581865137 115369152728371486186398853)
      ·
        refine ⟨21631716136569653659949785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115369152728371486186398853 21631716136569653659949785)
        ·
          refine ⟨16223787102427240244962339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21631716136569653659949785 16223787102427240244962339)
          ·
            refine ⟨24335680653640860367443509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16223787102427240244962339 24335680653640860367443509)
            ·
              refine ⟨2281470061278830659447829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24335680653640860367443509 2281470061278830659447829)
              ·
                refine ⟨106943909122445187161617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2281470061278830659447829 106943909122445187161617)
                ·
                  rfl

theorem cell22_2811679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 6].length) (baseStart_2811679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811679 prefixEnd_2811679 := by exact prefixLift 2811679
  have htrace : WordTrace (prefixWord ++ tailWord_2811679) baseStart_2811679 baseEnd_2811679 := by
    simpa [prefixWord, tailWord_2811679, baseEnd_2811679] using wordTrace_append hprefix tailTrace_2811679
  have hstable : (prefixWord ++ tailWord_2811679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811679).length < 2 ^ (prefixWord ++ tailWord_2811679).sum := by decide
  have hdescent : baseEnd_2811679 < baseStart_2811679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811681 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2811681 : Nat := 118140960795 + 2811681 * 2 ^ 59
def prefixEnd_2811681 : Nat := 4983230072969 + 3 ^ 40 * 2811681 * 2
def baseEnd_2811681 : Nat := 962495866742879345904547

theorem tailTrace_2811681 : CollatzResearch.WordTrace tailWord_2811681 prefixEnd_2811681 962495866742879345904547 := by
  unfold tailWord_2811681
  simp only [CollatzResearch.WordTrace]
  refine ⟨102550430926767408729482897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68366953951178272486321931 102550430926767408729482897)
  ·
    refine ⟨76912823195075556547112173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102550430926767408729482897 76912823195075556547112173)
    ·
      refine ⟨28842308698153333705167065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76912823195075556547112173 28842308698153333705167065)
      ·
        refine ⟨21631731523615000278875299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28842308698153333705167065 21631731523615000278875299)
        ·
          refine ⟨32447597285422500418312949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21631731523615000278875299 32447597285422500418312949)
          ·
            refine ⟨3041962245508359414216839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32447597285422500418312949 3041962245508359414216839)
            ·
              refine ⟨4562943368262539121325259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041962245508359414216839 4562943368262539121325259)
              ·
                refine ⟨6844415052393808681987889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4562943368262539121325259 6844415052393808681987889)
                ·
                  refine ⟨5133311289295356511490917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844415052393808681987889 5133311289295356511490917)
                  ·
                    refine ⟨962495866742879345904547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133311289295356511490917 962495866742879345904547)
                    ·
                      rfl

theorem cell22_2811681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2811681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811681 prefixEnd_2811681 := by exact prefixLift 2811681
  have htrace : WordTrace (prefixWord ++ tailWord_2811681) baseStart_2811681 baseEnd_2811681 := by
    simpa [prefixWord, tailWord_2811681, baseEnd_2811681] using wordTrace_append hprefix tailTrace_2811681
  have hstable : (prefixWord ++ tailWord_2811681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811681).length < 2 ^ (prefixWord ++ tailWord_2811681).sum := by decide
  have hdescent : baseEnd_2811681 < baseStart_2811681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811700 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_2811700 : Nat := 118140960795 + 2811700 * 2 ^ 59
def prefixEnd_2811700 : Nat := 4983230072969 + 3 ^ 40 * 2811700 * 2
def baseEnd_2811700 : Nat := 962502370831169629679489

theorem tailTrace_2811700 : CollatzResearch.WordTrace tailWord_2811700 prefixEnd_2811700 962502370831169629679489 := by
  unfold tailWord_2811700
  simp only [CollatzResearch.WordTrace]
  refine ⟨51275561956849287487212277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68367415942465716649616369 51275561956849287487212277)
  ·
    refine ⟨4807083933454620701926151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51275561956849287487212277 4807083933454620701926151)
    ·
      refine ⟨7210625900181931052889227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4807083933454620701926151 7210625900181931052889227)
      ·
        refine ⟨10815938850272896579333841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7210625900181931052889227 10815938850272896579333841)
        ·
          refine ⟨8111954137704672434500381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10815938850272896579333841 8111954137704672434500381)
          ·
            refine ⟨3041982801639252162937643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8111954137704672434500381 3041982801639252162937643)
            ·
              refine ⟨4562974202458878244406465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3041982801639252162937643 4562974202458878244406465)
              ·
                refine ⟨3422230651844158683304849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4562974202458878244406465 3422230651844158683304849)
                ·
                  refine ⟨2566672988883119012478637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422230651844158683304849 2566672988883119012478637)
                  ·
                    refine ⟨962502370831169629679489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566672988883119012478637 962502370831169629679489)
                    ·
                      rfl

theorem cell22_2811700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_2811700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811700 prefixEnd_2811700 := by exact prefixLift 2811700
  have htrace : WordTrace (prefixWord ++ tailWord_2811700) baseStart_2811700 baseEnd_2811700 := by
    simpa [prefixWord, tailWord_2811700, baseEnd_2811700] using wordTrace_append hprefix tailTrace_2811700
  have hstable : (prefixWord ++ tailWord_2811700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811700).length < 2 ^ (prefixWord ++ tailWord_2811700).sum := by decide
  have hdescent : baseEnd_2811700 < baseStart_2811700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811904 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_2811904 : Nat := 118140960795 + 2811904 * 2 ^ 59
def prefixEnd_2811904 : Nat := 4983230072969 + 3 ^ 40 * 2811904 * 2
def baseEnd_2811904 : Nat := 320857401400060365859621

theorem tailTrace_2811904 : CollatzResearch.WordTrace tailWord_2811904 prefixEnd_2811904 320857401400060365859621 := by
  unfold tailWord_2811904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51279282202479758907425383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68372376269973011876567177 51279282202479758907425383)
  ·
    refine ⟨76918923303719638361138075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51279282202479758907425383 76918923303719638361138075)
    ·
      refine ⟨115378384955579457541707113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76918923303719638361138075 115378384955579457541707113)
      ·
        refine ⟨86533788716684593156280335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115378384955579457541707113 86533788716684593156280335)
        ·
          refine ⟨129800683075026889734420503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86533788716684593156280335 129800683075026889734420503)
          ·
            refine ⟨194701024612540334601630755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129800683075026889734420503 194701024612540334601630755)
            ·
              refine ⟨292051536918810501902446133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194701024612540334601630755 292051536918810501902446133)
              ·
                refine ⟨27379831586138484553354325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292051536918810501902446133 27379831586138484553354325)
                ·
                  refine ⟨320857401400060365859621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27379831586138484553354325 320857401400060365859621)
                  ·
                    rfl

theorem cell22_2811904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_2811904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811904 prefixEnd_2811904 := by exact prefixLift 2811904
  have htrace : WordTrace (prefixWord ++ tailWord_2811904) baseStart_2811904 baseEnd_2811904 := by
    simpa [prefixWord, tailWord_2811904, baseEnd_2811904] using wordTrace_append hprefix tailTrace_2811904
  have hstable : (prefixWord ++ tailWord_2811904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811904).length < 2 ^ (prefixWord ++ tailWord_2811904).sum := by decide
  have hdescent : baseEnd_2811904 < baseStart_2811904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811914 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 1, 3]
def baseStart_2811914 : Nat := 118140960795 + 2811914 * 2 ^ 59
def prefixEnd_2811914 : Nat := 4983230072969 + 3 ^ 40 * 2811914 * 2
def baseEnd_2811914 : Nat := 962575627404544404828833

theorem tailTrace_2811914 : CollatzResearch.WordTrace tailWord_2811914 prefixEnd_2811914 962575627404544404828833 := by
  unfold tailWord_2811914
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639732283730822380678699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68372619423282193015143197 25639732283730822380678699)
  ·
    refine ⟨38459598425596233571018049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25639732283730822380678699 38459598425596233571018049)
    ·
      refine ⟨28844698819197175178263537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38459598425596233571018049 28844698819197175178263537)
      ·
        refine ⟨21633524114397881383697653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28844698819197175178263537 21633524114397881383697653)
        ·
          refine ⟨2028142885724801379721655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21633524114397881383697653 2028142885724801379721655)
          ·
            refine ⟨3042214328587202069582483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028142885724801379721655 3042214328587202069582483)
            ·
              refine ⟨4563321492880803104373725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3042214328587202069582483 4563321492880803104373725)
              ·
                refine ⟨1711245559830301164140147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4563321492880803104373725 1711245559830301164140147)
                ·
                  refine ⟨2566868339745451746210221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711245559830301164140147 2566868339745451746210221)
                  ·
                    refine ⟨962575627404544404828833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2566868339745451746210221 962575627404544404828833)
                    ·
                      rfl

theorem cell22_2811914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_2811914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811914 prefixEnd_2811914 := by exact prefixLift 2811914
  have htrace : WordTrace (prefixWord ++ tailWord_2811914) baseStart_2811914 baseEnd_2811914 := by
    simpa [prefixWord, tailWord_2811914, baseEnd_2811914] using wordTrace_append hprefix tailTrace_2811914
  have hstable : (prefixWord ++ tailWord_2811914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811914).length < 2 ^ (prefixWord ++ tailWord_2811914).sum := by decide
  have hdescent : baseEnd_2811914 < baseStart_2811914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811944 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 5]
def baseStart_2811944 : Nat := 118140960795 + 2811944 * 2 ^ 59
def prefixEnd_2811944 : Nat := 4983230072969 + 3 ^ 40 * 2811944 * 2
def baseEnd_2811944 : Nat := 320861965672544775526247

theorem tailTrace_2811944 : CollatzResearch.WordTrace tailWord_2811944 prefixEnd_2811944 320861965672544775526247 := by
  unfold tailWord_2811944
  simp only [CollatzResearch.WordTrace]
  refine ⟨51280011662407302323153443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68373348883209736430871257 51280011662407302323153443)
  ·
    refine ⟨76920017493610953484730165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51280011662407302323153443 76920017493610953484730165)
    ·
      refine ⟨7211251640026026889193453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76920017493610953484730165 7211251640026026889193453)
      ·
        refine ⟨2704219365009760083447545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7211251640026026889193453 2704219365009760083447545)
        ·
          refine ⟨2028164523757320062585659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2704219365009760083447545 2028164523757320062585659)
          ·
            refine ⟨3042246785635980093878489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2028164523757320062585659 3042246785635980093878489)
            ·
              refine ⟨2281685089226985070408867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042246785635980093878489 2281685089226985070408867)
              ·
                refine ⟨3422527633840477605613301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281685089226985070408867 3422527633840477605613301)
                ·
                  refine ⟨320861965672544775526247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3422527633840477605613301 320861965672544775526247)
                  ·
                    rfl

theorem cell22_2811944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_2811944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811944 prefixEnd_2811944 := by exact prefixLift 2811944
  have htrace : WordTrace (prefixWord ++ tailWord_2811944) baseStart_2811944 baseEnd_2811944 := by
    simpa [prefixWord, tailWord_2811944, baseEnd_2811944] using wordTrace_append hprefix tailTrace_2811944
  have hstable : (prefixWord ++ tailWord_2811944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811944).length < 2 ^ (prefixWord ++ tailWord_2811944).sum := by decide
  have hdescent : baseEnd_2811944 < baseStart_2811944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2811968 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_2811968 : Nat := 118140960795 + 2811968 * 2 ^ 59
def prefixEnd_2811968 : Nat := 4983230072969 + 3 ^ 40 * 2811968 * 2
def baseEnd_2811968 : Nat := 962594112708106263978667

theorem tailTrace_2811968 : CollatzResearch.WordTrace tailWord_2811968 prefixEnd_2811968 962594112708106263978667 := by
  unfold tailWord_2811968
  simp only [CollatzResearch.WordTrace]
  refine ⟨51280449338363828372590279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68373932451151771163453705 51280449338363828372590279)
  ·
    refine ⟨76920674007545742558885419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51280449338363828372590279 76920674007545742558885419)
    ·
      refine ⟨115381011011318613838328129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76920674007545742558885419 115381011011318613838328129)
      ·
        refine ⟨86535758258488960378746097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115381011011318613838328129 86535758258488960378746097)
        ·
          refine ⟨64901818693866720284059573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86535758258488960378746097 64901818693866720284059573)
          ·
            refine ⟨6084545502550005026630585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64901818693866720284059573 6084545502550005026630585)
            ·
              refine ⟨4563409126912503769972939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6084545502550005026630585 4563409126912503769972939)
              ·
                refine ⟨6845113690368755654959409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4563409126912503769972939 6845113690368755654959409)
                ·
                  refine ⟨5133835267776566741219557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6845113690368755654959409 5133835267776566741219557)
                  ·
                    refine ⟨962594112708106263978667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133835267776566741219557 962594112708106263978667)
                    ·
                      rfl

theorem cell22_2811968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_2811968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2811968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2811968 prefixEnd_2811968 := by exact prefixLift 2811968
  have htrace : WordTrace (prefixWord ++ tailWord_2811968) baseStart_2811968 baseEnd_2811968 := by
    simpa [prefixWord, tailWord_2811968, baseEnd_2811968] using wordTrace_append hprefix tailTrace_2811968
  have hstable : (prefixWord ++ tailWord_2811968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2811968).length < 2 ^ (prefixWord ++ tailWord_2811968).sum := by decide
  have hdescent : baseEnd_2811968 < baseStart_2811968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2811968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812088 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_2812088 : Nat := 118140960795 + 2812088 * 2 ^ 59
def prefixEnd_2812088 : Nat := 4983230072969 + 3 ^ 40 * 2812088 * 2
def baseEnd_2812088 : Nat := 962635191160465950978299

theorem tailTrace_2812088 : CollatzResearch.WordTrace tailWord_2812088 prefixEnd_2812088 962635191160465950978299 := by
  unfold tailWord_2812088
  simp only [CollatzResearch.WordTrace]
  refine ⟨51282637718146458619774459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68376850290861944826365945 51282637718146458619774459)
  ·
    refine ⟨76923956577219687929661689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51282637718146458619774459 76923956577219687929661689)
    ·
      refine ⟨57692967432914765947246267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76923956577219687929661689 57692967432914765947246267)
      ·
        refine ⟨86539451149372148920869401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57692967432914765947246267 86539451149372148920869401)
        ·
          refine ⟨64904588362029111690652051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86539451149372148920869401 64904588362029111690652051)
          ·
            refine ⟨97356882543043667535978077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64904588362029111690652051 97356882543043667535978077)
            ·
              refine ⟨36508830953641375325991779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97356882543043667535978077 36508830953641375325991779)
              ·
                refine ⟨54763246430462062988987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36508830953641375325991779 54763246430462062988987669)
                ·
                  refine ⟨2567027176427909202608797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54763246430462062988987669 2567027176427909202608797)
                  ·
                    refine ⟨962635191160465950978299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567027176427909202608797 962635191160465950978299)
                    ·
                      rfl

theorem cell22_2812088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_2812088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812088 prefixEnd_2812088 := by exact prefixLift 2812088
  have htrace : WordTrace (prefixWord ++ tailWord_2812088) baseStart_2812088 baseEnd_2812088 := by
    simpa [prefixWord, tailWord_2812088, baseEnd_2812088] using wordTrace_append hprefix tailTrace_2812088
  have hstable : (prefixWord ++ tailWord_2812088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812088).length < 2 ^ (prefixWord ++ tailWord_2812088).sum := by decide
  have hdescent : baseEnd_2812088 < baseStart_2812088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812090 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_2812090 : Nat := 118140960795 + 2812090 * 2 ^ 59
def prefixEnd_2812090 : Nat := 4983230072969 + 3 ^ 40 * 2812090 * 2
def baseEnd_2812090 : Nat := 320878625267112870809431

theorem tailTrace_2812090 : CollatzResearch.WordTrace tailWord_2812090 prefixEnd_2812090 320878625267112870809431 := by
  unfold tailWord_2812090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25641337095571417895280431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68376898921523781054081149 25641337095571417895280431)
  ·
    refine ⟨38462005643357126842920647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25641337095571417895280431 38462005643357126842920647)
    ·
      refine ⟨57693008465035690264380971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38462005643357126842920647 57693008465035690264380971)
      ·
        refine ⟨86539512697553535396571457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57693008465035690264380971 86539512697553535396571457)
        ·
          refine ⟨64904634523165151547428593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86539512697553535396571457 64904634523165151547428593)
          ·
            refine ⟨48678475892373863660571445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64904634523165151547428593 48678475892373863660571445)
            ·
              refine ⟨4563607114910049718178573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48678475892373863660571445 4563607114910049718178573)
              ·
                refine ⟨1711352668091268644316965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4563607114910049718178573 1711352668091268644316965)
                ·
                  refine ⟨320878625267112870809431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711352668091268644316965 320878625267112870809431)
                  ·
                    rfl

theorem cell22_2812090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_2812090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812090 prefixEnd_2812090 := by exact prefixLift 2812090
  have htrace : WordTrace (prefixWord ++ tailWord_2812090) baseStart_2812090 baseEnd_2812090 := by
    simpa [prefixWord, tailWord_2812090, baseEnd_2812090] using wordTrace_append hprefix tailTrace_2812090
  have hstable : (prefixWord ++ tailWord_2812090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812090).length < 2 ^ (prefixWord ++ tailWord_2812090).sum := by decide
  have hdescent : baseEnd_2812090 < baseStart_2812090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812101 : List Nat := [1, 3, 1, 1, 1, 1, 14]
def baseStart_2812101 : Nat := 118140960795 + 2812101 * 2 ^ 59
def prefixEnd_2812101 : Nat := 4983230072969 + 3 ^ 40 * 2812101 * 2
def baseEnd_2812101 : Nat := 35653320049116231496417

theorem tailTrace_2812101 : CollatzResearch.WordTrace tailWord_2812101 prefixEnd_2812101 35653320049116231496417 := by
  unfold tailWord_2812101
  simp only [CollatzResearch.WordTrace]
  refine ⟨102565749585245820459772157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68377166390163880306514771 102565749585245820459772157)
  ·
    refine ⟨38462156094467182672414559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102565749585245820459772157 38462156094467182672414559)
    ·
      refine ⟨57693234141700774008621839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38462156094467182672414559 57693234141700774008621839)
      ·
        refine ⟨86539851212551161012932759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57693234141700774008621839 86539851212551161012932759)
        ·
          refine ⟨129809776818826741519399139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86539851212551161012932759 129809776818826741519399139)
          ·
            refine ⟨194714665228240112279098709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129809776818826741519399139 194714665228240112279098709)
            ·
              refine ⟨35653320049116231496417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 194714665228240112279098709 35653320049116231496417)
              ·
                rfl

theorem cell22_2812101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 14].length) (baseStart_2812101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812101 prefixEnd_2812101 := by exact prefixLift 2812101
  have htrace : WordTrace (prefixWord ++ tailWord_2812101) baseStart_2812101 baseEnd_2812101 := by
    simpa [prefixWord, tailWord_2812101, baseEnd_2812101] using wordTrace_append hprefix tailTrace_2812101
  have hstable : (prefixWord ++ tailWord_2812101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812101).length < 2 ^ (prefixWord ++ tailWord_2812101).sum := by decide
  have hdescent : baseEnd_2812101 < baseStart_2812101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812122 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_2812122 : Nat := 118140960795 + 2812122 * 2 ^ 59
def prefixEnd_2812122 : Nat := 4983230072969 + 3 ^ 40 * 2812122 * 2
def baseEnd_2812122 : Nat := 962646830055301195628195

theorem tailTrace_2812122 : CollatzResearch.WordTrace tailWord_2812122 prefixEnd_2812122 962646830055301195628195 := by
  unfold tailWord_2812122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25641628879542435261571655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68377677012113160697524413 25641628879542435261571655)
  ·
    refine ⟨38462443319313652892357483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25641628879542435261571655 38462443319313652892357483)
    ·
      refine ⟨57693664978970479338536225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38462443319313652892357483 57693664978970479338536225)
      ·
        refine ⟨43270248734227859503902169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57693664978970479338536225 43270248734227859503902169)
        ·
          refine ⟨32452686550670894627926627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43270248734227859503902169 32452686550670894627926627)
          ·
            refine ⟨48679029826006341941889941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32452686550670894627926627 48679029826006341941889941)
            ·
              refine ⟨2281829523094047278526091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48679029826006341941889941 2281829523094047278526091)
              ·
                refine ⟨3422744284641070917789137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281829523094047278526091 3422744284641070917789137)
                ·
                  refine ⟨2567058213480803188341853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422744284641070917789137 2567058213480803188341853)
                  ·
                    refine ⟨962646830055301195628195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567058213480803188341853 962646830055301195628195)
                    ·
                      rfl

theorem cell22_2812122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_2812122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812122 prefixEnd_2812122 := by exact prefixLift 2812122
  have htrace : WordTrace (prefixWord ++ tailWord_2812122) baseStart_2812122 baseEnd_2812122 := by
    simpa [prefixWord, tailWord_2812122, baseEnd_2812122] using wordTrace_append hprefix tailTrace_2812122
  have hstable : (prefixWord ++ tailWord_2812122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812122).length < 2 ^ (prefixWord ++ tailWord_2812122).sum := by decide
  have hdescent : baseEnd_2812122 < baseStart_2812122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812240 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_2812240 : Nat := 118140960795 + 2812240 * 2 ^ 59
def prefixEnd_2812240 : Nat := 4983230072969 + 3 ^ 40 * 2812240 * 2
def baseEnd_2812240 : Nat := 962687223866788221177833

theorem tailTrace_2812240 : CollatzResearch.WordTrace tailWord_2812240 prefixEnd_2812240 962687223866788221177833 := by
  unfold tailWord_2812240
  simp only [CollatzResearch.WordTrace]
  refine ⟨51285409665871123599541087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68380546221161498132721449 51285409665871123599541087)
  ·
    refine ⟨76928114498806685399311631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51285409665871123599541087 76928114498806685399311631)
    ·
      refine ⟨115392171748210028098967447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76928114498806685399311631 115392171748210028098967447)
      ·
        refine ⟨173088257622315042148451171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115392171748210028098967447 173088257622315042148451171)
        ·
          refine ⟨259632386433472563222676757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173088257622315042148451171 259632386433472563222676757)
          ·
            refine ⟨12170268114069026401062973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 259632386433472563222676757 12170268114069026401062973)
            ·
              refine ⟨4563850542775884900398615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12170268114069026401062973 4563850542775884900398615)
              ·
                refine ⟨6845775814163827350597923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4563850542775884900398615 6845775814163827350597923)
                ·
                  refine ⟨10268663721245741025896885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6845775814163827350597923 10268663721245741025896885)
                  ·
                    refine ⟨962687223866788221177833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10268663721245741025896885 962687223866788221177833)
                    ·
                      rfl

theorem cell22_2812240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_2812240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812240 prefixEnd_2812240 := by exact prefixLift 2812240
  have htrace : WordTrace (prefixWord ++ tailWord_2812240) baseStart_2812240 baseEnd_2812240 := by
    simpa [prefixWord, tailWord_2812240, baseEnd_2812240] using wordTrace_append hprefix tailTrace_2812240
  have hstable : (prefixWord ++ tailWord_2812240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812240).length < 2 ^ (prefixWord ++ tailWord_2812240).sum := by decide
  have hdescent : baseEnd_2812240 < baseStart_2812240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812291 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 2, 3]
def baseStart_2812291 : Nat := 118140960795 + 2812291 * 2 ^ 59
def prefixEnd_2812291 : Nat := 4983230072969 + 3 ^ 40 * 2812291 * 2
def baseEnd_2812291 : Nat := 962704682209041088152677

theorem tailTrace_2812291 : CollatzResearch.WordTrace tailWord_2812291 prefixEnd_2812291 962704682209041088152677 := by
  unfold tailWord_2812291
  simp only [CollatzResearch.WordTrace]
  refine ⟨102572679454557482909188727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68381786303038321939459151 102572679454557482909188727)
  ·
    refine ⟨153859019181836224363783091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102572679454557482909188727 153859019181836224363783091)
    ·
      refine ⟨230788528772754336545674637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153859019181836224363783091 230788528772754336545674637)
      ·
        refine ⟨86545698289782876204627989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230788528772754336545674637 86545698289782876204627989)
        ·
          refine ⟨4056829607333572322091937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86545698289782876204627989 4056829607333572322091937)
          ·
            refine ⟨3042622205500179241568953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4056829607333572322091937 3042622205500179241568953)
            ·
              refine ⟨2281966654125134431176715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042622205500179241568953 2281966654125134431176715)
              ·
                refine ⟨3422949981187701646765073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2281966654125134431176715 3422949981187701646765073)
                ·
                  refine ⟨2567212485890776235073805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3422949981187701646765073 2567212485890776235073805)
                  ·
                    refine ⟨962704682209041088152677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567212485890776235073805 962704682209041088152677)
                    ·
                      rfl

theorem cell22_2812291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 3].length) (baseStart_2812291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812291 prefixEnd_2812291 := by exact prefixLift 2812291
  have htrace : WordTrace (prefixWord ++ tailWord_2812291) baseStart_2812291 baseEnd_2812291 := by
    simpa [prefixWord, tailWord_2812291, baseEnd_2812291] using wordTrace_append hprefix tailTrace_2812291
  have hstable : (prefixWord ++ tailWord_2812291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812291).length < 2 ^ (prefixWord ++ tailWord_2812291).sum := by decide
  have hdescent : baseEnd_2812291 < baseStart_2812291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812319 : List Nat := [1, 1, 2, 5, 1, 1, 2, 5, 1, 3]
def baseStart_2812319 : Nat := 118140960795 + 2812319 * 2 ^ 59
def prefixEnd_2812319 : Nat := 4983230072969 + 3 ^ 40 * 2812319 * 2
def baseEnd_2812319 : Nat := 962714267181258348452591

theorem tailTrace_2812319 : CollatzResearch.WordTrace tailWord_2812319 prefixEnd_2812319 962714267181258348452591 := by
  unfold tailWord_2812319
  simp only [CollatzResearch.WordTrace]
  refine ⟨102573700698456043691208011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68382467132304029127472007 102573700698456043691208011)
  ·
    refine ⟨153860551047684065536812017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102573700698456043691208011 153860551047684065536812017)
    ·
      refine ⟨115395413285763049152609013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153860551047684065536812017 115395413285763049152609013)
      ·
        refine ⟨10818319995540285858057095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115395413285763049152609013 10818319995540285858057095)
        ·
          refine ⟨16227479993310428787085643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10818319995540285858057095 16227479993310428787085643)
          ·
            refine ⟨24341219989965643180628465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16227479993310428787085643 24341219989965643180628465)
            ·
              refine ⟨18255914992474232385471349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24341219989965643180628465 18255914992474232385471349)
              ·
                refine ⟨1711492030544459286137939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18255914992474232385471349 1711492030544459286137939)
                ·
                  refine ⟨2567238045816688929206909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711492030544459286137939 2567238045816688929206909)
                  ·
                    refine ⟨962714267181258348452591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567238045816688929206909 962714267181258348452591)
                    ·
                      rfl

theorem cell22_2812319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_2812319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812319 prefixEnd_2812319 := by exact prefixLift 2812319
  have htrace : WordTrace (prefixWord ++ tailWord_2812319) baseStart_2812319 baseEnd_2812319 := by
    simpa [prefixWord, tailWord_2812319, baseEnd_2812319] using wordTrace_append hprefix tailTrace_2812319
  have hstable : (prefixWord ++ tailWord_2812319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812319).length < 2 ^ (prefixWord ++ tailWord_2812319).sum := by decide
  have hdescent : baseEnd_2812319 < baseStart_2812319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812353 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2812353 : Nat := 118140960795 + 2812353 * 2 ^ 59
def prefixEnd_2812353 : Nat := 4983230072969 + 3 ^ 40 * 2812353 * 2
def baseEnd_2812353 : Nat := 962725906076093593102487

theorem tailTrace_2812353 : CollatzResearch.WordTrace tailWord_2812353 prefixEnd_2812353 962725906076093593102487 := by
  unfold tailWord_2812353
  simp only [CollatzResearch.WordTrace]
  refine ⟨102574940780332867497945713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68383293853555244998630475 102574940780332867497945713)
  ·
    refine ⟨76931205585249650623459285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102574940780332867497945713 76931205585249650623459285)
    ·
      refine ⟨1803075130904288686487327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 76931205585249650623459285 1803075130904288686487327)
      ·
        refine ⟨2704612696356433029730991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803075130904288686487327 2704612696356433029730991)
        ·
          refine ⟨4056919044534649544596487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704612696356433029730991 4056919044534649544596487)
          ·
            refine ⟨6085378566801974316894731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056919044534649544596487 6085378566801974316894731)
            ·
              refine ⟨9128067850202961475342097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085378566801974316894731 9128067850202961475342097)
              ·
                refine ⟨6846050887652221106506573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9128067850202961475342097 6846050887652221106506573)
                ·
                  refine ⟨2567269082869582914939965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6846050887652221106506573 2567269082869582914939965)
                  ·
                    refine ⟨962725906076093593102487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567269082869582914939965 962725906076093593102487)
                    ·
                      rfl

theorem cell22_2812353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2812353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812353 prefixEnd_2812353 := by exact prefixLift 2812353
  have htrace : WordTrace (prefixWord ++ tailWord_2812353) baseStart_2812353 baseEnd_2812353 := by
    simpa [prefixWord, tailWord_2812353, baseEnd_2812353] using wordTrace_append hprefix tailTrace_2812353
  have hstable : (prefixWord ++ tailWord_2812353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812353).length < 2 ^ (prefixWord ++ tailWord_2812353).sum := by decide
  have hdescent : baseEnd_2812353 < baseStart_2812353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812360 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_2812360 : Nat := 118140960795 + 2812360 * 2 ^ 59
def prefixEnd_2812360 : Nat := 4983230072969 + 3 ^ 40 * 2812360 * 2
def baseEnd_2812360 : Nat := 320909434106382636059155

theorem tailTrace_2812360 : CollatzResearch.WordTrace tailWord_2812360 prefixEnd_2812360 320909434106382636059155 := by
  unfold tailWord_2812360
  simp only [CollatzResearch.WordTrace]
  refine ⟨51287598045653753846725267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68383464060871671795633689 51287598045653753846725267)
  ·
    refine ⟨76931397068480630770087901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51287598045653753846725267 76931397068480630770087901)
    ·
      refine ⟨28849273900680236538782963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76931397068480630770087901 28849273900680236538782963)
      ·
        refine ⟨43273910851020354808174445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28849273900680236538782963 43273910851020354808174445)
        ·
          refine ⟨16227716569132633053065417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43273910851020354808174445 16227716569132633053065417)
          ·
            refine ⟨12170787426849474789799063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16227716569132633053065417 12170787426849474789799063)
            ·
              refine ⟨18256181140274212184698595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12170787426849474789799063 18256181140274212184698595)
              ·
                refine ⟨27384271710411318277047893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18256181140274212184698595 27384271710411318277047893)
                ·
                  refine ⟨320909434106382636059155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27384271710411318277047893 320909434106382636059155)
                  ·
                    rfl

theorem cell22_2812360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_2812360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812360 prefixEnd_2812360 := by exact prefixLift 2812360
  have htrace : WordTrace (prefixWord ++ tailWord_2812360) baseStart_2812360 baseEnd_2812360 := by
    simpa [prefixWord, tailWord_2812360, baseEnd_2812360] using wordTrace_append hprefix tailTrace_2812360
  have hstable : (prefixWord ++ tailWord_2812360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812360).length < 2 ^ (prefixWord ++ tailWord_2812360).sum := by decide
  have hdescent : baseEnd_2812360 < baseStart_2812360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812362 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_2812362 : Nat := 118140960795 + 2812362 * 2 ^ 59
def prefixEnd_2812362 : Nat := 4983230072969 + 3 ^ 40 * 2812362 * 2
def baseEnd_2812362 : Nat := 962728986960020569627459

theorem tailTrace_2812362 : CollatzResearch.WordTrace tailWord_2812362 prefixEnd_2812362 962728986960020569627459 := by
  unfold tailWord_2812362
  simp only [CollatzResearch.WordTrace]
  refine ⟨25643817259325065508755835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68383512691533508023348893 25643817259325065508755835)
  ·
    refine ⟨38465725888987598263133753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25643817259325065508755835 38465725888987598263133753)
    ·
      refine ⟨28849294416740698697350315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38465725888987598263133753 28849294416740698697350315)
      ·
        refine ⟨43273941625111048046025473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28849294416740698697350315 43273941625111048046025473)
        ·
          refine ⟨32455456218833286034519105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43273941625111048046025473 32455456218833286034519105)
          ·
            refine ⟨24341592164124964525889329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32455456218833286034519105 24341592164124964525889329)
            ·
              refine ⟨18256194123093723394416997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24341592164124964525889329 18256194123093723394416997)
              ·
                refine ⟨3423036398080073136453187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18256194123093723394416997 3423036398080073136453187)
                ·
                  refine ⟨5134554597120109704679781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423036398080073136453187 5134554597120109704679781)
                  ·
                    refine ⟨962728986960020569627459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134554597120109704679781 962728986960020569627459)
                    ·
                      rfl

theorem cell22_2812362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_2812362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812362 prefixEnd_2812362 := by exact prefixLift 2812362
  have htrace : WordTrace (prefixWord ++ tailWord_2812362) baseStart_2812362 baseEnd_2812362 := by
    simpa [prefixWord, tailWord_2812362, baseEnd_2812362] using wordTrace_append hprefix tailTrace_2812362
  have hstable : (prefixWord ++ tailWord_2812362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812362).length < 2 ^ (prefixWord ++ tailWord_2812362).sum := by decide
  have hdescent : baseEnd_2812362 < baseStart_2812362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812394 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 4]
def baseStart_2812394 : Nat := 118140960795 + 2812394 * 2 ^ 59
def prefixEnd_2812394 : Nat := 4983230072969 + 3 ^ 40 * 2812394 * 2
def baseEnd_2812394 : Nat := 320913313737994384275787

theorem tailTrace_2812394 : CollatzResearch.WordTrace tailWord_2812394 prefixEnd_2812394 320913313737994384275787 := by
  unfold tailWord_2812394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25644109043296082875047059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68384290782122887666792157 25644109043296082875047059)
  ·
    refine ⟨38466163564944124312570589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25644109043296082875047059 38466163564944124312570589)
    ·
      refine ⟨14424811336854046617213971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38466163564944124312570589 14424811336854046617213971)
      ·
        refine ⟨21637217005281069925820957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14424811336854046617213971 21637217005281069925820957)
        ·
          refine ⟨8113956376980401222182859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21637217005281069925820957 8113956376980401222182859)
          ·
            refine ⟨12170934565470601833274289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8113956376980401222182859 12170934565470601833274289)
            ·
              refine ⟨9128200924102951374955717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12170934565470601833274289 9128200924102951374955717)
              ·
                refine ⟨1711537673269303382804197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9128200924102951374955717 1711537673269303382804197)
                ·
                  refine ⟨320913313737994384275787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1711537673269303382804197 320913313737994384275787)
                  ·
                    rfl

theorem cell22_2812394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 4].length) (baseStart_2812394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812394 prefixEnd_2812394 := by exact prefixLift 2812394
  have htrace : WordTrace (prefixWord ++ tailWord_2812394) baseStart_2812394 baseEnd_2812394 := by
    simpa [prefixWord, tailWord_2812394, baseEnd_2812394] using wordTrace_append hprefix tailTrace_2812394
  have hstable : (prefixWord ++ tailWord_2812394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812394).length < 2 ^ (prefixWord ++ tailWord_2812394).sum := by decide
  have hdescent : baseEnd_2812394 < baseStart_2812394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812439 : List Nat := [1, 1, 3, 6, 1, 2, 8]
def baseStart_2812439 : Nat := 118140960795 + 2812439 * 2 ^ 59
def prefixEnd_2812439 : Nat := 4983230072969 + 3 ^ 40 * 2812439 * 2
def baseEnd_2812439 : Nat := 35657605393837705016749

theorem tailTrace_2812439 : CollatzResearch.WordTrace tailWord_2812439 prefixEnd_2812439 35657605393837705016749 := by
  unfold tailWord_2812439
  simp only [CollatzResearch.WordTrace]
  refine ⟨102578077458021304185576371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68385384972014202790384247 102578077458021304185576371)
  ·
    refine ⟨153867116187031956278364557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102578077458021304185576371 153867116187031956278364557)
    ·
      refine ⟨57700168570136983604386709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153867116187031956278364557 57700168570136983604386709)
      ·
        refine ⟨2704695401725171106455627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57700168570136983604386709 2704695401725171106455627)
        ·
          refine ⟨4057043102587756659683441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704695401725171106455627 4057043102587756659683441)
          ·
            refine ⟨3042782326940817494762581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4057043102587756659683441 3042782326940817494762581)
            ·
              refine ⟨35657605393837705016749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3042782326940817494762581 35657605393837705016749)
              ·
                rfl

theorem cell22_2812439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 8].length) (baseStart_2812439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812439 prefixEnd_2812439 := by exact prefixLift 2812439
  have htrace : WordTrace (prefixWord ++ tailWord_2812439) baseStart_2812439 baseEnd_2812439 := by
    simpa [prefixWord, tailWord_2812439, baseEnd_2812439] using wordTrace_append hprefix tailTrace_2812439
  have hstable : (prefixWord ++ tailWord_2812439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812439).length < 2 ^ (prefixWord ++ tailWord_2812439).sum := by decide
  have hdescent : baseEnd_2812439 < baseStart_2812439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812467 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 5]
def baseStart_2812467 : Nat := 118140960795 + 2812467 * 2 ^ 59
def prefixEnd_2812467 : Nat := 4983230072969 + 3 ^ 40 * 2812467 * 2
def baseEnd_2812467 : Nat := 320921643535278431917379

theorem tailTrace_2812467 : CollatzResearch.WordTrace tailWord_2812467 prefixEnd_2812467 320921643535278431917379 := by
  unfold tailWord_2812467
  simp only [CollatzResearch.WordTrace]
  refine ⟨102579098701919864967595655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68386065801279909978397103 102579098701919864967595655)
  ·
    refine ⟨153868648052879797451393483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102579098701919864967595655 153868648052879797451393483)
    ·
      refine ⟨230802972079319696177090225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153868648052879797451393483 230802972079319696177090225)
      ·
        refine ⟨173102229059489772132817669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230802972079319696177090225 173102229059489772132817669)
        ·
          refine ⟨32456667948654332274903313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173102229059489772132817669 32456667948654332274903313)
          ·
            refine ⟨24342500961490749206177485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32456667948654332274903313 24342500961490749206177485)
            ·
              refine ⟨9128437860559030952316557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24342500961490749206177485 9128437860559030952316557)
              ·
                refine ⟨3423164197709636607118709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9128437860559030952316557 3423164197709636607118709)
                ·
                  refine ⟨320921643535278431917379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3423164197709636607118709 320921643535278431917379)
                  ·
                    rfl

theorem cell22_2812467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 5].length) (baseStart_2812467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812467 prefixEnd_2812467 := by exact prefixLift 2812467
  have htrace : WordTrace (prefixWord ++ tailWord_2812467) baseStart_2812467 baseEnd_2812467 := by
    simpa [prefixWord, tailWord_2812467, baseEnd_2812467] using wordTrace_append hprefix tailTrace_2812467
  have hstable : (prefixWord ++ tailWord_2812467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812467).length < 2 ^ (prefixWord ++ tailWord_2812467).sum := by decide
  have hdescent : baseEnd_2812467 < baseStart_2812467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812527 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 1, 5]
def baseStart_2812527 : Nat := 118140960795 + 2812527 * 2 ^ 59
def prefixEnd_2812527 : Nat := 4983230072969 + 3 ^ 40 * 2812527 * 2
def baseEnd_2812527 : Nat := 962785469832015139251953

theorem tailTrace_2812527 : CollatzResearch.WordTrace tailWord_2812527 prefixEnd_2812527 962785469832015139251953 := by
  unfold tailWord_2812527
  simp only [CollatzResearch.WordTrace]
  refine ⟨102581287081702495214779835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68387524721134996809853223 102581287081702495214779835)
  ·
    refine ⟨153871930622553742822169753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102581287081702495214779835 153871930622553742822169753)
    ·
      refine ⟨115403947966915307116627315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153871930622553742822169753 115403947966915307116627315)
      ·
        refine ⟨173105921950372960674940973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115403947966915307116627315 173105921950372960674940973)
        ·
          refine ⟨64914720731389860253102865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173105921950372960674940973 64914720731389860253102865)
          ·
            refine ⟨48686040548542395189827149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64914720731389860253102865 48686040548542395189827149)
            ·
              refine ⟨18257265205703398196185181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48686040548542395189827149 18257265205703398196185181)
              ·
                refine ⟨6846474452138774323569443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18257265205703398196185181 6846474452138774323569443)
                ·
                  refine ⟨10269711678208161485354165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6846474452138774323569443 10269711678208161485354165)
                  ·
                    refine ⟨962785469832015139251953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10269711678208161485354165 962785469832015139251953)
                    ·
                      rfl

theorem cell22_2812527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_2812527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812527 prefixEnd_2812527 := by exact prefixLift 2812527
  have htrace : WordTrace (prefixWord ++ tailWord_2812527) baseStart_2812527 baseEnd_2812527 := by
    simpa [prefixWord, tailWord_2812527, baseEnd_2812527] using wordTrace_append hprefix tailTrace_2812527
  have hstable : (prefixWord ++ tailWord_2812527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812527).length < 2 ^ (prefixWord ++ tailWord_2812527).sum := by decide
  have hdescent : baseEnd_2812527 < baseStart_2812527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812548 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_2812548 : Nat := 118140960795 + 2812548 * 2 ^ 59
def prefixEnd_2812548 : Nat := 4983230072969 + 3 ^ 40 * 2812548 * 2
def baseEnd_2812548 : Nat := 962792658561178084476889

theorem tailTrace_2812548 : CollatzResearch.WordTrace tailWord_2812548 prefixEnd_2812548 962792658561178084476889 := by
  unfold tailWord_2812548
  simp only [CollatzResearch.WordTrace]
  refine ⟨51291026507313207900647149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68388035343084277200862865 51291026507313207900647149)
  ·
    refine ⟨19234134940242452962742681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51291026507313207900647149 19234134940242452962742681)
    ·
      refine ⟨14425601205181839722057011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19234134940242452962742681 14425601205181839722057011)
      ·
        refine ⟨21638401807772759583085517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14425601205181839722057011 21638401807772759583085517)
        ·
          refine ⟨8114400677914784843657069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21638401807772759583085517 8114400677914784843657069)
          ·
            refine ⟨3042900254218044316371401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8114400677914784843657069 3042900254218044316371401)
            ·
              refine ⟨2282175190663533237278551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3042900254218044316371401 2282175190663533237278551)
              ·
                refine ⟨3423262785995299855917827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282175190663533237278551 3423262785995299855917827)
                ·
                  refine ⟨5134894178992949783876741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423262785995299855917827 5134894178992949783876741)
                  ·
                    refine ⟨962792658561178084476889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134894178992949783876741 962792658561178084476889)
                    ·
                      rfl

theorem cell22_2812548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_2812548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812548 prefixEnd_2812548 := by exact prefixLift 2812548
  have htrace : WordTrace (prefixWord ++ tailWord_2812548) baseStart_2812548 baseEnd_2812548 := by
    simpa [prefixWord, tailWord_2812548, baseEnd_2812548] using wordTrace_append hprefix tailTrace_2812548
  have hstable : (prefixWord ++ tailWord_2812548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812548).length < 2 ^ (prefixWord ++ tailWord_2812548).sum := by decide
  have hdescent : baseEnd_2812548 < baseStart_2812548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812574 : List Nat := [4, 3, 1, 1, 1, 1, 2, 9]
def baseStart_2812574 : Nat := 118140960795 + 2812574 * 2 ^ 59
def prefixEnd_2812574 : Nat := 4983230072969 + 3 ^ 40 * 2812574 * 2
def baseEnd_2812574 : Nat := 106977950988058075925201

theorem tailTrace_2812574 : CollatzResearch.WordTrace tailWord_2812574 prefixEnd_2812574 106977950988058075925201 := by
  unfold tailWord_2812574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822875164066527780217597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68388667541688148161160517 12822875164066527780217597)
  ·
    refine ⟨4808578186524947917581599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12822875164066527780217597 4808578186524947917581599)
    ·
      refine ⟨7212867279787421876372399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808578186524947917581599 7212867279787421876372399)
      ·
        refine ⟨10819300919681132814558599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7212867279787421876372399 10819300919681132814558599)
        ·
          refine ⟨16228951379521699221837899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10819300919681132814558599 16228951379521699221837899)
          ·
            refine ⟨24343427069282548832756849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16228951379521699221837899 24343427069282548832756849)
            ·
              refine ⟨18257570301961911624567637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24343427069282548832756849 18257570301961911624567637)
              ·
                refine ⟨106977950988058075925201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18257570301961911624567637 106977950988058075925201)
                ·
                  rfl

theorem cell22_2812574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_2812574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812574 prefixEnd_2812574 := by exact prefixLift 2812574
  have htrace : WordTrace (prefixWord ++ tailWord_2812574) baseStart_2812574 baseEnd_2812574 := by
    simpa [prefixWord, tailWord_2812574, baseEnd_2812574] using wordTrace_append hprefix tailTrace_2812574
  have hstable : (prefixWord ++ tailWord_2812574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812574).length < 2 ^ (prefixWord ++ tailWord_2812574).sum := by decide
  have hdescent : baseEnd_2812574 < baseStart_2812574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812602 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_2812602 : Nat := 118140960795 + 2812602 * 2 ^ 59
def prefixEnd_2812602 : Nat := 4983230072969 + 3 ^ 40 * 2812602 * 2
def baseEnd_2812602 : Nat := 320937047954913314542241

theorem tailTrace_2812602 : CollatzResearch.WordTrace tailWord_2812602 prefixEnd_2812602 320937047954913314542241 := by
  unfold tailWord_2812602
  simp only [CollatzResearch.WordTrace]
  refine ⟨25646005639107695755940015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68389348370953855349173373 25646005639107695755940015)
  ·
    refine ⟨38469008458661543633910023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25646005639107695755940015 38469008458661543633910023)
    ·
      refine ⟨57703512687992315450865035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38469008458661543633910023 57703512687992315450865035)
      ·
        refine ⟨86555269031988473176297553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57703512687992315450865035 86555269031988473176297553)
        ·
          refine ⟨64916451773991354882223165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86555269031988473176297553 64916451773991354882223165)
          ·
            refine ⟨24343669415246758080833687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64916451773991354882223165 24343669415246758080833687)
            ·
              refine ⟨36515504122870137121250531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24343669415246758080833687 36515504122870137121250531)
              ·
                refine ⟨54773256184305205681875797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36515504122870137121250531 54773256184305205681875797)
                ·
                  refine ⟨320937047954913314542241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54773256184305205681875797 320937047954913314542241)
                  ·
                    rfl

theorem cell22_2812602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_2812602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812602 prefixEnd_2812602 := by exact prefixLift 2812602
  have htrace : WordTrace (prefixWord ++ tailWord_2812602) baseStart_2812602 baseEnd_2812602 := by
    simpa [prefixWord, tailWord_2812602, baseEnd_2812602] using wordTrace_append hprefix tailTrace_2812602
  have hstable : (prefixWord ++ tailWord_2812602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812602).length < 2 ^ (prefixWord ++ tailWord_2812602).sum := by decide
  have hdescent : baseEnd_2812602 < baseStart_2812602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812730 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 2, 3]
def baseStart_2812730 : Nat := 118140960795 + 2812730 * 2 ^ 59
def prefixEnd_2812730 : Nat := 4983230072969 + 3 ^ 40 * 2812730 * 2
def baseEnd_2812730 : Nat := 962854960880590276426331

theorem tailTrace_2812730 : CollatzResearch.WordTrace tailWord_2812730 prefixEnd_2812730 962854960880590276426331 := by
  unfold tailWord_2812730
  simp only [CollatzResearch.WordTrace]
  refine ⟨25647172774991765221104911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68392460733311373922946429 25647172774991765221104911)
  ·
    refine ⟨38470759162487647831657367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25647172774991765221104911 38470759162487647831657367)
    ·
      refine ⟨57706138743731471747486051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38470759162487647831657367 57706138743731471747486051)
      ·
        refine ⟨86559208115597207621229077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57706138743731471747486051 86559208115597207621229077)
        ·
          refine ⟨4057462880418619107245113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86559208115597207621229077 4057462880418619107245113)
          ·
            refine ⟨3043097160313964330433835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4057462880418619107245113 3043097160313964330433835)
            ·
              refine ⟨4564645740470946495650753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043097160313964330433835 4564645740470946495650753)
              ·
                refine ⟨3423484305353209871738065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4564645740470946495650753 3423484305353209871738065)
                ·
                  refine ⟨2567613229014907403803549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3423484305353209871738065 2567613229014907403803549)
                  ·
                    refine ⟨962854960880590276426331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567613229014907403803549 962854960880590276426331)
                    ·
                      rfl

theorem cell22_2812730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_2812730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812730 prefixEnd_2812730 := by exact prefixLift 2812730
  have htrace : WordTrace (prefixWord ++ tailWord_2812730) baseStart_2812730 baseEnd_2812730 := by
    simpa [prefixWord, tailWord_2812730, baseEnd_2812730] using wordTrace_append hprefix tailTrace_2812730
  have hstable : (prefixWord ++ tailWord_2812730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812730).length < 2 ^ (prefixWord ++ tailWord_2812730).sum := by decide
  have hdescent : baseEnd_2812730 < baseStart_2812730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812769 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2812769 : Nat := 118140960795 + 2812769 * 2 ^ 59
def prefixEnd_2812769 : Nat := 4983230072969 + 3 ^ 40 * 2812769 * 2
def baseEnd_2812769 : Nat := 962868311377607174701211

theorem tailTrace_2812769 : CollatzResearch.WordTrace tailWord_2812769 prefixEnd_2812769 962868311377607174701211 := by
  unfold tailWord_2812769
  simp only [CollatzResearch.WordTrace]
  refine ⟨102590113546825770545089361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68393409031217180363392907 102590113546825770545089361)
  ·
    refine ⟨76942585160119327908817021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102590113546825770545089361 76942585160119327908817021)
    ·
      refine ⟨28853469435044747965806383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76942585160119327908817021 28853469435044747965806383)
      ·
        refine ⟨43280204152567121948709575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28853469435044747965806383 43280204152567121948709575)
        ·
          refine ⟨64920306228850682923064363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43280204152567121948709575 64920306228850682923064363)
          ·
            refine ⟨97380459343276024384596545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64920306228850682923064363 97380459343276024384596545)
            ·
              refine ⟨73035344507457018288447409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97380459343276024384596545 73035344507457018288447409)
              ·
                refine ⟨54776508380592763716335557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73035344507457018288447409 54776508380592763716335557)
                ·
                  refine ⟨10270595321361143196812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54776508380592763716335557 10270595321361143196812917)
                  ·
                    refine ⟨962868311377607174701211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10270595321361143196812917 962868311377607174701211)
                    ·
                      rfl

theorem cell22_2812769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2812769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812769 prefixEnd_2812769 := by exact prefixLift 2812769
  have htrace : WordTrace (prefixWord ++ tailWord_2812769) baseStart_2812769 baseEnd_2812769 := by
    simpa [prefixWord, tailWord_2812769, baseEnd_2812769] using wordTrace_append hprefix tailTrace_2812769
  have hstable : (prefixWord ++ tailWord_2812769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812769).length < 2 ^ (prefixWord ++ tailWord_2812769).sum := by decide
  have hdescent : baseEnd_2812769 < baseStart_2812769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812775 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2812775 : Nat := 118140960795 + 2812775 * 2 ^ 59
def prefixEnd_2812775 : Nat := 4983230072969 + 3 ^ 40 * 2812775 * 2
def baseEnd_2812775 : Nat := 962870365300225159051193

theorem tailTrace_2812775 : CollatzResearch.WordTrace tailWord_2812775 prefixEnd_2812775 962870365300225159051193 := by
  unfold tailWord_2812775
  simp only [CollatzResearch.WordTrace]
  refine ⟨102590332384804033569807779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68393554923202689046538519 102590332384804033569807779)
  ·
    refine ⟨153885498577206050354711669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102590332384804033569807779 153885498577206050354711669)
    ·
      refine ⟨14426765491613067220754219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153885498577206050354711669 14426765491613067220754219)
      ·
        refine ⟨21640148237419600831131329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14426765491613067220754219 21640148237419600831131329)
        ·
          refine ⟨16230111178064700623348497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21640148237419600831131329 16230111178064700623348497)
          ·
            refine ⟨12172583383548525467511373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16230111178064700623348497 12172583383548525467511373)
            ·
              refine ⟨4564718768830697050316765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12172583383548525467511373 4564718768830697050316765)
              ·
                refine ⟨1711769538311511393868787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4564718768830697050316765 1711769538311511393868787)
                ·
                  refine ⟨2567654307467267090803181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1711769538311511393868787 2567654307467267090803181)
                  ·
                    refine ⟨962870365300225159051193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567654307467267090803181 962870365300225159051193)
                    ·
                      rfl

theorem cell22_2812775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2812775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812775 prefixEnd_2812775 := by exact prefixLift 2812775
  have htrace : WordTrace (prefixWord ++ tailWord_2812775) baseStart_2812775 baseEnd_2812775 := by
    simpa [prefixWord, tailWord_2812775, baseEnd_2812775] using wordTrace_append hprefix tailTrace_2812775
  have hstable : (prefixWord ++ tailWord_2812775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812775).length < 2 ^ (prefixWord ++ tailWord_2812775).sum := by decide
  have hdescent : baseEnd_2812775 < baseStart_2812775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812831 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 3, 5]
def baseStart_2812831 : Nat := 118140960795 + 2812831 * 2 ^ 59
def prefixEnd_2812831 : Nat := 4983230072969 + 3 ^ 40 * 2812831 * 2
def baseEnd_2812831 : Nat := 962889535244659679651021

theorem tailTrace_2812831 : CollatzResearch.WordTrace tailWord_2812831 prefixEnd_2812831 962889535244659679651021 := by
  unfold tailWord_2812831
  simp only [CollatzResearch.WordTrace]
  refine ⟨102592374872601155133846347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68394916581734103422564231 102592374872601155133846347)
  ·
    refine ⟨153888562308901732700769521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102592374872601155133846347 153888562308901732700769521)
    ·
      refine ⟨115416421731676299525577141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153888562308901732700769521 115416421731676299525577141)
      ·
        refine ⟨10820289537344653080522857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115416421731676299525577141 10820289537344653080522857)
        ·
          refine ⟨8115217153008489810392143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10820289537344653080522857 8115217153008489810392143)
          ·
            refine ⟨12172825729512734715588215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115217153008489810392143 12172825729512734715588215)
            ·
              refine ⟨18259238594269102073382323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12172825729512734715588215 18259238594269102073382323)
              ·
                refine ⟨27388857891403653110073485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18259238594269102073382323 27388857891403653110073485)
                ·
                  refine ⟨10270821709276369916277557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27388857891403653110073485 10270821709276369916277557)
                  ·
                    refine ⟨962889535244659679651021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10270821709276369916277557 962889535244659679651021)
                    ·
                      rfl

theorem cell22_2812831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_2812831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812831 prefixEnd_2812831 := by exact prefixLift 2812831
  have htrace : WordTrace (prefixWord ++ tailWord_2812831) baseStart_2812831 baseEnd_2812831 := by
    simpa [prefixWord, tailWord_2812831, baseEnd_2812831] using wordTrace_append hprefix tailTrace_2812831
  have hstable : (prefixWord ++ tailWord_2812831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812831).length < 2 ^ (prefixWord ++ tailWord_2812831).sum := by decide
  have hdescent : baseEnd_2812831 < baseStart_2812831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812878 : List Nat := [4, 1, 1, 1, 2, 4, 3, 6]
def baseStart_2812878 : Nat := 118140960795 + 2812878 * 2 ^ 59
def prefixEnd_2812878 : Nat := 4983230072969 + 3 ^ 40 * 2812878 * 2
def baseEnd_2812878 : Nat := 106989513811685247080653

theorem tailTrace_2812878 : CollatzResearch.WordTrace tailWord_2812878 prefixEnd_2812878 106989513811685247080653 := by
  unfold tailWord_2812878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12824261137928860270100911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68396059402287254773871525 12824261137928860270100911)
  ·
    refine ⟨19236391706893290405151367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12824261137928860270100911 19236391706893290405151367)
    ·
      refine ⟨28854587560339935607727051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19236391706893290405151367 28854587560339935607727051)
      ·
        refine ⟨43281881340509903411590577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28854587560339935607727051 43281881340509903411590577)
        ·
          refine ⟨32461411005382427558692933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43281881340509903411590577 32461411005382427558692933)
          ·
            refine ⟨6086514563509205167254925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32461411005382427558692933 6086514563509205167254925)
            ·
              refine ⟨2282442961315951937720597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086514563509205167254925 2282442961315951937720597)
              ·
                refine ⟨106989513811685247080653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2282442961315951937720597 106989513811685247080653)
                ·
                  rfl

theorem cell22_2812878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_2812878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812878 prefixEnd_2812878 := by exact prefixLift 2812878
  have htrace : WordTrace (prefixWord ++ tailWord_2812878) baseStart_2812878 baseEnd_2812878 := by
    simpa [prefixWord, tailWord_2812878, baseEnd_2812878] using wordTrace_append hprefix tailTrace_2812878
  have hstable : (prefixWord ++ tailWord_2812878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812878).length < 2 ^ (prefixWord ++ tailWord_2812878).sum := by decide
  have hdescent : baseEnd_2812878 < baseStart_2812878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812916 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2812916 : Nat := 118140960795 + 2812916 * 2 ^ 59
def prefixEnd_2812916 : Nat := 4983230072969 + 3 ^ 40 * 2812916 * 2
def baseEnd_2812916 : Nat := 962918632481747791275761

theorem tailTrace_2812916 : CollatzResearch.WordTrace tailWord_2812916 prefixEnd_2812916 962918632481747791275761 := by
  unfold tailWord_2812916
  simp only [CollatzResearch.WordTrace]
  refine ⟨51297737538646607325345301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68396983384862143100460401 51297737538646607325345301)
  ·
    refine ⟨2404581447124059718375561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51297737538646607325345301 2404581447124059718375561)
    ·
      refine ⟨1803436085343044788781671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2404581447124059718375561 1803436085343044788781671)
      ·
        refine ⟨2705154128014567183172507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803436085343044788781671 2705154128014567183172507)
        ·
          refine ⟨4057731192021850774758761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2705154128014567183172507 4057731192021850774758761)
          ·
            refine ⟨3043298394016388081069071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4057731192021850774758761 3043298394016388081069071)
            ·
              refine ⟨4564947591024582121603607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043298394016388081069071 4564947591024582121603607)
              ·
                refine ⟨6847421386536873182405411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4564947591024582121603607 6847421386536873182405411)
                ·
                  refine ⟨10271132079805309773608117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6847421386536873182405411 10271132079805309773608117)
                  ·
                    refine ⟨962918632481747791275761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10271132079805309773608117 962918632481747791275761)
                    ·
                      rfl

theorem cell22_2812916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2812916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812916 prefixEnd_2812916 := by exact prefixLift 2812916
  have htrace : WordTrace (prefixWord ++ tailWord_2812916) baseStart_2812916 baseEnd_2812916 := by
    simpa [prefixWord, tailWord_2812916, baseEnd_2812916] using wordTrace_append hprefix tailTrace_2812916
  have hstable : (prefixWord ++ tailWord_2812916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812916).length < 2 ^ (prefixWord ++ tailWord_2812916).sum := by decide
  have hdescent : baseEnd_2812916 < baseStart_2812916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812921 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_2812921 : Nat := 118140960795 + 2812921 * 2 ^ 59
def prefixEnd_2812921 : Nat := 4983230072969 + 3 ^ 40 * 2812921 * 2
def baseEnd_2812921 : Nat := 962920344083929444900745

theorem tailTrace_2812921 : CollatzResearch.WordTrace tailWord_2812921 prefixEnd_2812921 962920344083929444900745 := by
  unfold tailWord_2812921
  simp only [CollatzResearch.WordTrace]
  refine ⟨102595657442275100504622617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68397104961516733669748411 102595657442275100504622617)
  ·
    refine ⟨76946743081706325378466963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102595657442275100504622617 76946743081706325378466963)
    ·
      refine ⟨115420114622559488067700445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76946743081706325378466963 115420114622559488067700445)
      ·
        refine ⟨43282542983459808025387667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115420114622559488067700445 43282542983459808025387667)
        ·
          refine ⟨64923814475189712038081501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43282542983459808025387667 64923814475189712038081501)
          ·
            refine ⟨24346430428196142014280563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64923814475189712038081501 24346430428196142014280563)
            ·
              refine ⟨36519645642294213021420845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24346430428196142014280563 36519645642294213021420845)
              ·
                refine ⟨13694867115860329883032817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36519645642294213021420845 13694867115860329883032817)
                ·
                  refine ⟨10271150336895247412274613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13694867115860329883032817 10271150336895247412274613)
                  ·
                    refine ⟨962920344083929444900745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10271150336895247412274613 962920344083929444900745)
                    ·
                      rfl

theorem cell22_2812921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_2812921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812921 prefixEnd_2812921 := by exact prefixLift 2812921
  have htrace : WordTrace (prefixWord ++ tailWord_2812921) baseStart_2812921 baseEnd_2812921 := by
    simpa [prefixWord, tailWord_2812921, baseEnd_2812921] using wordTrace_append hprefix tailTrace_2812921
  have hstable : (prefixWord ++ tailWord_2812921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812921).length < 2 ^ (prefixWord ++ tailWord_2812921).sum := by decide
  have hdescent : baseEnd_2812921 < baseStart_2812921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2812953 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_2812953 : Nat := 118140960795 + 2812953 * 2 ^ 59
def prefixEnd_2812953 : Nat := 4983230072969 + 3 ^ 40 * 2812953 * 2
def baseEnd_2812953 : Nat := 962931298337892028100647

theorem tailTrace_2812953 : CollatzResearch.WordTrace tailWord_2812953 prefixEnd_2812953 962931298337892028100647 := by
  unfold tailWord_2812953
  simp only [CollatzResearch.WordTrace]
  refine ⟨102596824578159169969787513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68397883052106113313191675 102596824578159169969787513)
  ·
    refine ⟨76947618433619377477340635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102596824578159169969787513 76947618433619377477340635)
    ·
      refine ⟨115421427650429066216010953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76947618433619377477340635 115421427650429066216010953)
      ·
        refine ⟨86566070737821799662008215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115421427650429066216010953 86566070737821799662008215)
        ·
          refine ⟨129849106106732699493012323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86566070737821799662008215 129849106106732699493012323)
          ·
            refine ⟨194773659160099049239518485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129849106106732699493012323 194773659160099049239518485)
            ·
              refine ⟨9130015273129642933102429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194773659160099049239518485 9130015273129642933102429)
              ·
                refine ⟨3423755727423616099913411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9130015273129642933102429 3423755727423616099913411)
                ·
                  refine ⟨5135633591135424149870117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423755727423616099913411 5135633591135424149870117)
                  ·
                    refine ⟨962931298337892028100647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5135633591135424149870117 962931298337892028100647)
                    ·
                      rfl

theorem cell22_2812953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_2812953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2812953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2812953 prefixEnd_2812953 := by exact prefixLift 2812953
  have htrace : WordTrace (prefixWord ++ tailWord_2812953) baseStart_2812953 baseEnd_2812953 := by
    simpa [prefixWord, tailWord_2812953, baseEnd_2812953] using wordTrace_append hprefix tailTrace_2812953
  have hstable : (prefixWord ++ tailWord_2812953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2812953).length < 2 ^ (prefixWord ++ tailWord_2812953).sum := by decide
  have hdescent : baseEnd_2812953 < baseStart_2812953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2812953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813092 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 5]
def baseStart_2813092 : Nat := 118140960795 + 2813092 * 2 ^ 59
def prefixEnd_2813092 : Nat := 4983230072969 + 3 ^ 40 * 2813092 * 2
def baseEnd_2813092 : Nat := 320992960292847332958407

theorem tailTrace_2813092 : CollatzResearch.WordTrace tailWord_2813092 prefixEnd_2813092 320992960292847332958407 := by
  unfold tailWord_2813092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51300947162327798354548765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68401262883103731139398353 51300947162327798354548765)
  ·
    refine ⟨19237855185872924382955787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51300947162327798354548765 19237855185872924382955787)
    ·
      refine ⟨28856782778809386574433681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19237855185872924382955787 28856782778809386574433681)
      ·
        refine ⟨21642587084107039930825261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28856782778809386574433681 21642587084107039930825261)
        ·
          refine ⟨8115970156540139974059473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21642587084107039930825261 8115970156540139974059473)
          ·
            refine ⟨6086977617405104980544605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8115970156540139974059473 6086977617405104980544605)
            ·
              refine ⟨2282616606526914367704227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6086977617405104980544605 2282616606526914367704227)
              ·
                refine ⟨3423924909790371551556341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2282616606526914367704227 3423924909790371551556341)
                ·
                  refine ⟨320992960292847332958407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3423924909790371551556341 320992960292847332958407)
                  ·
                    rfl

theorem cell22_2813092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_2813092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813092 prefixEnd_2813092 := by exact prefixLift 2813092
  have htrace : WordTrace (prefixWord ++ tailWord_2813092) baseStart_2813092 baseEnd_2813092 := by
    simpa [prefixWord, tailWord_2813092, baseEnd_2813092] using wordTrace_append hprefix tailTrace_2813092
  have hstable : (prefixWord ++ tailWord_2813092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813092).length < 2 ^ (prefixWord ++ tailWord_2813092).sum := by decide
  have hdescent : baseEnd_2813092 < baseStart_2813092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813103 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 6]
def baseStart_2813103 : Nat := 118140960795 + 2813103 * 2 ^ 59
def prefixEnd_2813103 : Nat := 4983230072969 + 3 ^ 40 * 2813103 * 2
def baseEnd_2813103 : Nat := 320994215467780545616729

theorem tailTrace_2813103 : CollatzResearch.WordTrace tailWord_2813103 prefixEnd_2813103 320994215467780545616729 := by
  unfold tailWord_2813103
  simp only [CollatzResearch.WordTrace]
  refine ⟨102602295527615745587747963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68401530351743830391831975 102602295527615745587747963)
  ·
    refine ⟨153903443291423618381621945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102602295527615745587747963 153903443291423618381621945)
    ·
      refine ⟨115427582468567713786216459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153903443291423618381621945 115427582468567713786216459)
      ·
        refine ⟨173141373702851570679324689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115427582468567713786216459 173141373702851570679324689)
        ·
          refine ⟨129856030277138678009493517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173141373702851570679324689 129856030277138678009493517)
          ·
            refine ⟨48696011353927004253560069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129856030277138678009493517 48696011353927004253560069)
            ·
              refine ⟨9130502128861313297542513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48696011353927004253560069 9130502128861313297542513)
              ·
                refine ⟨6847876596645984973156885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9130502128861313297542513 6847876596645984973156885)
                ·
                  refine ⟨320994215467780545616729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6847876596645984973156885 320994215467780545616729)
                  ·
                    rfl

theorem cell22_2813103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 6].length) (baseStart_2813103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813103 prefixEnd_2813103 := by exact prefixLift 2813103
  have htrace : WordTrace (prefixWord ++ tailWord_2813103) baseStart_2813103 baseEnd_2813103 := by
    simpa [prefixWord, tailWord_2813103, baseEnd_2813103] using wordTrace_append hprefix tailTrace_2813103
  have hstable : (prefixWord ++ tailWord_2813103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813103).length < 2 ^ (prefixWord ++ tailWord_2813103).sum := by decide
  have hdescent : baseEnd_2813103 < baseStart_2813103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813152 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_2813152 : Nat := 118140960795 + 2813152 * 2 ^ 59
def prefixEnd_2813152 : Nat := 4983230072969 + 3 ^ 40 * 2813152 * 2
def baseEnd_2813152 : Nat := 962999420104721842375037

theorem tailTrace_2813152 : CollatzResearch.WordTrace tailWord_2813152 prefixEnd_2813152 962999420104721842375037 := by
  unfold tailWord_2813152
  simp only [CollatzResearch.WordTrace]
  refine ⟨51302041352219113478140855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68402721802958817970854473 51302041352219113478140855)
  ·
    refine ⟨76953062028328670217211283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51302041352219113478140855 76953062028328670217211283)
    ·
      refine ⟨115429593042493005325816925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76953062028328670217211283 115429593042493005325816925)
      ·
        refine ⟨43286097390934876997181347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115429593042493005325816925 43286097390934876997181347)
        ·
          refine ⟨64929146086402315495772021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43286097390934876997181347 64929146086402315495772021)
          ·
            refine ⟨6087107445600217077728627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64929146086402315495772021 6087107445600217077728627)
            ·
              refine ⟨9130661168400325616592941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6087107445600217077728627 9130661168400325616592941)
              ·
                refine ⟨3423997938150122106222353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9130661168400325616592941 3423997938150122106222353)
                ·
                  refine ⟨2567998453612591579666765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3423997938150122106222353 2567998453612591579666765)
                  ·
                    refine ⟨962999420104721842375037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2567998453612591579666765 962999420104721842375037)
                    ·
                      rfl

theorem cell22_2813152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_2813152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813152 prefixEnd_2813152 := by exact prefixLift 2813152
  have htrace : WordTrace (prefixWord ++ tailWord_2813152) baseStart_2813152 baseEnd_2813152 := by
    simpa [prefixWord, tailWord_2813152, baseEnd_2813152] using wordTrace_append hprefix tailTrace_2813152
  have hstable : (prefixWord ++ tailWord_2813152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813152).length < 2 ^ (prefixWord ++ tailWord_2813152).sum := by decide
  have hdescent : baseEnd_2813152 < baseStart_2813152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813165 : List Nat := [1, 5, 1, 2, 2, 1, 2, 8]
def baseStart_2813165 : Nat := 118140960795 + 2813165 * 2 ^ 59
def prefixEnd_2813165 : Nat := 4983230072969 + 3 ^ 40 * 2813165 * 2
def baseEnd_2813165 : Nat := 107000430030043793533333

theorem tailTrace_2813165 : CollatzResearch.WordTrace tailWord_2813165 prefixEnd_2813165 107000430030043793533333 := by
  unfold tailWord_2813165
  simp only [CollatzResearch.WordTrace]
  refine ⟨102604556853391130176504949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68403037902260753451003299 102604556853391130176504949)
  ·
    refine ⟨9619177205005418454047339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102604556853391130176504949 9619177205005418454047339)
    ·
      refine ⟨14428765807508127681071009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9619177205005418454047339 14428765807508127681071009)
      ·
        refine ⟨10821574355631095760803257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14428765807508127681071009 10821574355631095760803257)
        ·
          refine ⟨8116180766723321820602443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10821574355631095760803257 8116180766723321820602443)
          ·
            refine ⟨12174271150084982730903665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8116180766723321820602443 12174271150084982730903665)
            ·
              refine ⟨9130703362563737048177749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12174271150084982730903665 9130703362563737048177749)
              ·
                refine ⟨107000430030043793533333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9130703362563737048177749 107000430030043793533333)
                ·
                  rfl

theorem cell22_2813165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 8].length) (baseStart_2813165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813165 prefixEnd_2813165 := by exact prefixLift 2813165
  have htrace : WordTrace (prefixWord ++ tailWord_2813165) baseStart_2813165 baseEnd_2813165 := by
    simpa [prefixWord, tailWord_2813165, baseEnd_2813165] using wordTrace_append hprefix tailTrace_2813165
  have hstable : (prefixWord ++ tailWord_2813165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813165).length < 2 ^ (prefixWord ++ tailWord_2813165).sum := by decide
  have hdescent : baseEnd_2813165 < baseStart_2813165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813167 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 2, 4]
def baseStart_2813167 : Nat := 118140960795 + 2813167 * 2 ^ 59
def prefixEnd_2813167 : Nat := 4983230072969 + 3 ^ 40 * 2813167 * 2
def baseEnd_2813167 : Nat := 963004554911266803249991

theorem tailTrace_2813167 : CollatzResearch.WordTrace tailWord_2813167 prefixEnd_2813167 963004554911266803249991 := by
  unfold tailWord_2813167
  simp only [CollatzResearch.WordTrace]
  refine ⟨102604629799383884518077755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68403086532922589678718503 102604629799383884518077755)
  ·
    refine ⟨153906944699075826777116633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102604629799383884518077755 153906944699075826777116633)
    ·
      refine ⟨115430208524306870082837475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153906944699075826777116633 115430208524306870082837475)
      ·
        refine ⟨173145312786460305124256213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115430208524306870082837475 173145312786460305124256213)
        ·
          refine ⟨4058093268432663401349755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173145312786460305124256213 4058093268432663401349755)
          ·
            refine ⟨6087139902648995102024633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058093268432663401349755 6087139902648995102024633)
            ·
              refine ⟨4565354926986746326518475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087139902648995102024633 4565354926986746326518475)
              ·
                refine ⟨6848032390480119489777713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565354926986746326518475 6848032390480119489777713)
                ·
                  refine ⟨5136024292860089617333285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6848032390480119489777713 5136024292860089617333285)
                  ·
                    refine ⟨963004554911266803249991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136024292860089617333285 963004554911266803249991)
                    ·
                      rfl

theorem cell22_2813167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_2813167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813167 prefixEnd_2813167 := by exact prefixLift 2813167
  have htrace : WordTrace (prefixWord ++ tailWord_2813167) baseStart_2813167 baseEnd_2813167 := by
    simpa [prefixWord, tailWord_2813167, baseEnd_2813167] using wordTrace_append hprefix tailTrace_2813167
  have hstable : (prefixWord ++ tailWord_2813167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813167).length < 2 ^ (prefixWord ++ tailWord_2813167).sum := by decide
  have hdescent : baseEnd_2813167 < baseStart_2813167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813186 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_2813186 : Nat := 118140960795 + 2813186 * 2 ^ 59
def prefixEnd_2813186 : Nat := 4983230072969 + 3 ^ 40 * 2813186 * 2
def baseEnd_2813186 : Nat := 963011058999557087024933

theorem tailTrace_2813186 : CollatzResearch.WordTrace tailWord_2813186 prefixEnd_2813186 963011058999557087024933 := by
  unfold tailWord_2813186
  simp only [CollatzResearch.WordTrace]
  refine ⟨25651330696578762690754853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68403548524210033842012941 25651330696578762690754853)
  ·
    refine ⟨4809624505608518004516535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25651330696578762690754853 4809624505608518004516535)
    ·
      refine ⟨7214436758412777006774803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4809624505608518004516535 7214436758412777006774803)
      ·
        refine ⟨10821655137619165510162205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7214436758412777006774803 10821655137619165510162205)
        ·
          refine ⟨4058120676607187066310827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10821655137619165510162205 4058120676607187066310827)
          ·
            refine ⟨6087181014910780599466241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058120676607187066310827 6087181014910780599466241)
            ·
              refine ⟨4565385761183085449599681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087181014910780599466241 4565385761183085449599681)
              ·
                refine ⟨3424039320887314087199761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565385761183085449599681 3424039320887314087199761)
                ·
                  refine ⟨2568029490665485565399821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3424039320887314087199761 2568029490665485565399821)
                  ·
                    refine ⟨963011058999557087024933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568029490665485565399821 963011058999557087024933)
                    ·
                      rfl

theorem cell22_2813186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_2813186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813186 prefixEnd_2813186 := by exact prefixLift 2813186
  have htrace : WordTrace (prefixWord ++ tailWord_2813186) baseStart_2813186 baseEnd_2813186 := by
    simpa [prefixWord, tailWord_2813186, baseEnd_2813186] using wordTrace_append hprefix tailTrace_2813186
  have hstable : (prefixWord ++ tailWord_2813186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813186).length < 2 ^ (prefixWord ++ tailWord_2813186).sum := by decide
  have hdescent : baseEnd_2813186 < baseStart_2813186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813255 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 6]
def baseStart_2813255 : Nat := 118140960795 + 2813255 * 2 ^ 59
def prefixEnd_2813255 : Nat := 4983230072969 + 3 ^ 40 * 2813255 * 2
def baseEnd_2813255 : Nat := 321011559703221302349907

theorem tailTrace_2813255 : CollatzResearch.WordTrace tailWord_2813255 prefixEnd_2813255 321011559703221302349907 := by
  unfold tailWord_2813255
  simp only [CollatzResearch.WordTrace]
  refine ⟨102607839423065075547281219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68405226282043383698187479 102607839423065075547281219)
  ·
    refine ⟨153911759134597613320921829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102607839423065075547281219 153911759134597613320921829)
    ·
      refine ⟨28858454837737052497672843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153911759134597613320921829 28858454837737052497672843)
      ·
        refine ⟨43287682256605578746509265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28858454837737052497672843 43287682256605578746509265)
        ·
          refine ⟨32465761692454184059881949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43287682256605578746509265 32465761692454184059881949)
          ·
            refine ⟨12174660634670319022455731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32465761692454184059881949 12174660634670319022455731)
            ·
              refine ⟨18261990952005478533683597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12174660634670319022455731 18261990952005478533683597)
              ·
                refine ⟨6848246607002054450131349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18261990952005478533683597 6848246607002054450131349)
                ·
                  refine ⟨321011559703221302349907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6848246607002054450131349 321011559703221302349907)
                  ·
                    rfl

theorem cell22_2813255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 6].length) (baseStart_2813255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813255 prefixEnd_2813255 := by exact prefixLift 2813255
  have htrace : WordTrace (prefixWord ++ tailWord_2813255) baseStart_2813255 baseEnd_2813255 := by
    simpa [prefixWord, tailWord_2813255, baseEnd_2813255] using wordTrace_append hprefix tailTrace_2813255
  have hstable : (prefixWord ++ tailWord_2813255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813255).length < 2 ^ (prefixWord ++ tailWord_2813255).sum := by decide
  have hdescent : baseEnd_2813255 < baseStart_2813255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813285 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_2813285 : Nat := 118140960795 + 2813285 * 2 ^ 59
def prefixEnd_2813285 : Nat := 4983230072969 + 3 ^ 40 * 2813285 * 2
def baseEnd_2813285 : Nat := 963044948722753828799629

theorem tailTrace_2813285 : CollatzResearch.WordTrace tailWord_2813285 prefixEnd_2813285 963044948722753828799629 := by
  unfold tailWord_2813285
  simp only [CollatzResearch.WordTrace]
  refine ⟨102608933612956390670873309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68405955741970927113915539 102608933612956390670873309)
  ·
    refine ⟨38478350104858646501577491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102608933612956390670873309 38478350104858646501577491)
    ·
      refine ⟨57717525157287969752366237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38478350104858646501577491 57717525157287969752366237)
      ·
        refine ⟨21644071933982988657137339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57717525157287969752366237 21644071933982988657137339)
        ·
          refine ⟨32466107900974482985706009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21644071933982988657137339 32466107900974482985706009)
          ·
            refine ⟨24349580925730862239279507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32466107900974482985706009 24349580925730862239279507)
            ·
              refine ⟨36524371388596293358919261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24349580925730862239279507 36524371388596293358919261)
              ·
                refine ⟨13696639270723610009594723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36524371388596293358919261 13696639270723610009594723)
                ·
                  refine ⟨20544958906085415014392085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13696639270723610009594723 20544958906085415014392085)
                  ·
                    refine ⟨963044948722753828799629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20544958906085415014392085 963044948722753828799629)
                    ·
                      rfl

theorem cell22_2813285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_2813285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813285 prefixEnd_2813285 := by exact prefixLift 2813285
  have htrace : WordTrace (prefixWord ++ tailWord_2813285) baseStart_2813285 baseEnd_2813285 := by
    simpa [prefixWord, tailWord_2813285, baseEnd_2813285] using wordTrace_append hprefix tailTrace_2813285
  have hstable : (prefixWord ++ tailWord_2813285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813285).length < 2 ^ (prefixWord ++ tailWord_2813285).sum := by decide
  have hdescent : baseEnd_2813285 < baseStart_2813285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813409 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2813409 : Nat := 118140960795 + 2813409 * 2 ^ 59
def prefixEnd_2813409 : Nat := 4983230072969 + 3 ^ 40 * 2813409 * 2
def baseEnd_2813409 : Nat := 963087396456858838699249

theorem tailTrace_2813409 : CollatzResearch.WordTrace tailWord_2813409 prefixEnd_2813409 963087396456858838699249 := by
  unfold tailWord_2813409
  simp only [CollatzResearch.WordTrace]
  refine ⟨102613456264507159848387281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68408970843004773232258187 102613456264507159848387281)
  ·
    refine ⟨76960092198380369886290461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102613456264507159848387281 76960092198380369886290461)
    ·
      refine ⟨28860034574392638707358923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76960092198380369886290461 28860034574392638707358923)
      ·
        refine ⟨43290051861588958061038385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28860034574392638707358923 43290051861588958061038385)
        ·
          refine ⟨32467538896191718545778789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43290051861588958061038385 32467538896191718545778789)
          ·
            refine ⟨6087663543035947227333523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32467538896191718545778789 6087663543035947227333523)
            ·
              refine ⟨9131495314553920841000285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6087663543035947227333523 9131495314553920841000285)
              ·
                refine ⟨3424310742957720315375107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9131495314553920841000285 3424310742957720315375107)
                ·
                  refine ⟨5136466114436580473062661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424310742957720315375107 5136466114436580473062661)
                  ·
                    refine ⟨963087396456858838699249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136466114436580473062661 963087396456858838699249)
                    ·
                      rfl

theorem cell22_2813409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2813409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813409 prefixEnd_2813409 := by exact prefixLift 2813409
  have htrace : WordTrace (prefixWord ++ tailWord_2813409) baseStart_2813409 baseEnd_2813409 := by
    simpa [prefixWord, tailWord_2813409, baseEnd_2813409] using wordTrace_append hprefix tailTrace_2813409
  have hstable : (prefixWord ++ tailWord_2813409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813409).length < 2 ^ (prefixWord ++ tailWord_2813409).sum := by decide
  have hdescent : baseEnd_2813409 < baseStart_2813409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813424 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 4]
def baseStart_2813424 : Nat := 118140960795 + 2813424 * 2 ^ 59
def prefixEnd_2813424 : Nat := 4983230072969 + 3 ^ 40 * 2813424 * 2
def baseEnd_2813424 : Nat := 321030843754467933191401

theorem tailTrace_2813424 : CollatzResearch.WordTrace tailWord_2813424 prefixEnd_2813424 321030843754467933191401 := by
  unfold tailWord_2813424
  simp only [CollatzResearch.WordTrace]
  refine ⟨51307001679726408705091663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68409335572968544940122217 51307001679726408705091663)
  ·
    refine ⟨76960502519589613057637495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51307001679726408705091663 76960502519589613057637495)
    ·
      refine ⟨115440753779384419586456243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76960502519589613057637495 115440753779384419586456243)
      ·
        refine ⟨173161130669076629379684365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115440753779384419586456243 173161130669076629379684365)
        ·
          refine ⟨64935424000903736017381637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173161130669076629379684365 64935424000903736017381637)
          ·
            refine ⟨12175392000169450503259057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64935424000903736017381637 12175392000169450503259057)
            ·
              refine ⟨9131544000127087877444293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12175392000169450503259057 9131544000127087877444293)
              ·
                refine ⟨1712164500023828977020805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9131544000127087877444293 1712164500023828977020805)
                ·
                  refine ⟨321030843754467933191401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712164500023828977020805 321030843754467933191401)
                  ·
                    rfl

theorem cell22_2813424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_2813424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813424 prefixEnd_2813424 := by exact prefixLift 2813424
  have htrace : WordTrace (prefixWord ++ tailWord_2813424) baseStart_2813424 baseEnd_2813424 := by
    simpa [prefixWord, tailWord_2813424, baseEnd_2813424] using wordTrace_append hprefix tailTrace_2813424
  have hstable : (prefixWord ++ tailWord_2813424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813424).length < 2 ^ (prefixWord ++ tailWord_2813424).sum := by decide
  have hdescent : baseEnd_2813424 < baseStart_2813424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813437 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2813437 : Nat := 118140960795 + 2813437 * 2 ^ 59
def prefixEnd_2813437 : Nat := 4983230072969 + 3 ^ 40 * 2813437 * 2
def baseEnd_2813437 : Nat := 963096981429076098999163

theorem tailTrace_2813437 : CollatzResearch.WordTrace tailWord_2813437 prefixEnd_2813437 963096981429076098999163 := by
  unfold tailWord_2813437
  simp only [CollatzResearch.WordTrace]
  refine ⟨102614477508405720630406565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68409651672270480420271043 102614477508405720630406565)
  ·
    refine ⟨19240214532826072618201231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102614477508405720630406565 19240214532826072618201231)
    ·
      refine ⟨28860321799239108927301847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19240214532826072618201231 28860321799239108927301847)
      ·
        refine ⟨43290482698858663390952771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28860321799239108927301847 43290482698858663390952771)
        ·
          refine ⟨64935724048287995086429157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43290482698858663390952771 64935724048287995086429157)
          ·
            refine ⟨12175448259053999078705467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64935724048287995086429157 12175448259053999078705467)
            ·
              refine ⟨18263172388580998618058201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12175448259053999078705467 18263172388580998618058201)
              ·
                refine ⟨13697379291435748963543651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18263172388580998618058201 13697379291435748963543651)
                ·
                  refine ⟨20546068937153623445315477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13697379291435748963543651 20546068937153623445315477)
                  ·
                    refine ⟨963096981429076098999163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20546068937153623445315477 963096981429076098999163)
                    ·
                      rfl

theorem cell22_2813437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2813437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813437 prefixEnd_2813437 := by exact prefixLift 2813437
  have htrace : WordTrace (prefixWord ++ tailWord_2813437) baseStart_2813437 baseEnd_2813437 := by
    simpa [prefixWord, tailWord_2813437, baseEnd_2813437] using wordTrace_append hprefix tailTrace_2813437
  have hstable : (prefixWord ++ tailWord_2813437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813437).length < 2 ^ (prefixWord ++ tailWord_2813437).sum := by decide
  have hdescent : baseEnd_2813437 < baseStart_2813437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813512 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_2813512 : Nat := 118140960795 + 2813512 * 2 ^ 59
def prefixEnd_2813512 : Nat := 4983230072969 + 3 ^ 40 * 2813512 * 2
def baseEnd_2813512 : Nat := 963122655461800903373933

theorem tailTrace_2813512 : CollatzResearch.WordTrace tailWord_2813512 prefixEnd_2813512 963122655461800903373933 := by
  unfold tailWord_2813512
  simp only [CollatzResearch.WordTrace]
  refine ⟨51308606491567004219693395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68411475322089338959591193 51308606491567004219693395)
  ·
    refine ⟨76962909737350506329540093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51308606491567004219693395 76962909737350506329540093)
    ·
      refine ⟨28861091151506439873577535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76962909737350506329540093 28861091151506439873577535)
      ·
        refine ⟨43291636727259659810366303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28861091151506439873577535 43291636727259659810366303)
        ·
          refine ⟨64937455090889489715549455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43291636727259659810366303 64937455090889489715549455)
          ·
            refine ⟨97406182636334234573324183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64937455090889489715549455 97406182636334234573324183)
            ·
              refine ⟨146109273954501351859986275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97406182636334234573324183 146109273954501351859986275)
              ·
                refine ⟨219163910931752027789979413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146109273954501351859986275 219163910931752027789979413)
                ·
                  refine ⟨10273308324925876302655285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219163910931752027789979413 10273308324925876302655285)
                  ·
                    refine ⟨963122655461800903373933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10273308324925876302655285 963122655461800903373933)
                    ·
                      rfl

theorem cell22_2813512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_2813512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813512 prefixEnd_2813512 := by exact prefixLift 2813512
  have htrace : WordTrace (prefixWord ++ tailWord_2813512) baseStart_2813512 baseEnd_2813512 := by
    simpa [prefixWord, tailWord_2813512, baseEnd_2813512] using wordTrace_append hprefix tailTrace_2813512
  have hstable : (prefixWord ++ tailWord_2813512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813512).length < 2 ^ (prefixWord ++ tailWord_2813512).sum := by decide
  have hdescent : baseEnd_2813512 < baseStart_2813512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813578 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_2813578 : Nat := 118140960795 + 2813578 * 2 ^ 59
def prefixEnd_2813578 : Nat := 4983230072969 + 3 ^ 40 * 2813578 * 2
def baseEnd_2813578 : Nat := 963145248610598731223731

theorem tailTrace_2813578 : CollatzResearch.WordTrace tailWord_2813578 prefixEnd_2813578 963145248610598731223731 := by
  unfold tailWord_2813578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25654905050223725427822347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68413080133929934474192925 25654905050223725427822347)
  ·
    refine ⟨38482357575335588141733521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25654905050223725427822347 38482357575335588141733521)
    ·
      refine ⟨28861768181501691106300141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38482357575335588141733521 28861768181501691106300141)
      ·
        refine ⟨10823163068063134164862553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28861768181501691106300141 10823163068063134164862553)
        ·
          refine ⟨8117372301047350623646915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10823163068063134164862553 8117372301047350623646915)
          ·
            refine ⟨12176058451571025935470373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8117372301047350623646915 12176058451571025935470373)
            ·
              refine ⟨2283010959669567362900695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12176058451571025935470373 2283010959669567362900695)
              ·
                refine ⟨3424516439504351044351043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283010959669567362900695 3424516439504351044351043)
                ·
                  refine ⟨5136774659256526566526565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424516439504351044351043 5136774659256526566526565)
                  ·
                    refine ⟨963145248610598731223731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136774659256526566526565 963145248610598731223731)
                    ·
                      rfl

theorem cell22_2813578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_2813578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813578 prefixEnd_2813578 := by exact prefixLift 2813578
  have htrace : WordTrace (prefixWord ++ tailWord_2813578) baseStart_2813578 baseEnd_2813578 := by
    simpa [prefixWord, tailWord_2813578, baseEnd_2813578] using wordTrace_append hprefix tailTrace_2813578
  have hstable : (prefixWord ++ tailWord_2813578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813578).length < 2 ^ (prefixWord ++ tailWord_2813578).sum := by decide
  have hdescent : baseEnd_2813578 < baseStart_2813578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813589 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2813589 : Nat := 118140960795 + 2813589 * 2 ^ 59
def prefixEnd_2813589 : Nat := 4983230072969 + 3 ^ 40 * 2813589 * 2
def baseEnd_2813589 : Nat := 963149014135398369198697

theorem tailTrace_2813589 : CollatzResearch.WordTrace tailWord_2813589 prefixEnd_2813589 963149014135398369198697 := by
  unfold tailWord_2813589
  simp only [CollatzResearch.WordTrace]
  refine ⟨102620021403855050589939821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68413347602570033726626547 102620021403855050589939821)
  ·
    refine ⟨38482508026445643971227433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102620021403855050589939821 38482508026445643971227433)
    ·
      refine ⟨28861881019834232978420575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38482508026445643971227433 28861881019834232978420575)
      ·
        refine ⟨43292821529751349467630863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28861881019834232978420575 43292821529751349467630863)
        ·
          refine ⟨64939232294627024201446295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43292821529751349467630863 64939232294627024201446295)
          ·
            refine ⟨97408848441940536302169443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64939232294627024201446295 97408848441940536302169443)
            ·
              refine ⟨146113272662910804453254165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97408848441940536302169443 146113272662910804453254165)
              ·
                refine ⟨6849059656073943958746289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146113272662910804453254165 6849059656073943958746289)
                ·
                  refine ⟨5136794742055457969059717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6849059656073943958746289 5136794742055457969059717)
                  ·
                    refine ⟨963149014135398369198697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136794742055457969059717 963149014135398369198697)
                    ·
                      rfl

theorem cell22_2813589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2813589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813589 prefixEnd_2813589 := by exact prefixLift 2813589
  have htrace : WordTrace (prefixWord ++ tailWord_2813589) baseStart_2813589 baseEnd_2813589 := by
    simpa [prefixWord, tailWord_2813589, baseEnd_2813589] using wordTrace_append hprefix tailTrace_2813589
  have hstable : (prefixWord ++ tailWord_2813589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813589).length < 2 ^ (prefixWord ++ tailWord_2813589).sum := by decide
  have hdescent : baseEnd_2813589 < baseStart_2813589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813591 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 4, 3]
def baseStart_2813591 : Nat := 118140960795 + 2813591 * 2 ^ 59
def prefixEnd_2813591 : Nat := 4983230072969 + 3 ^ 40 * 2813591 * 2
def baseEnd_2813591 : Nat := 963149698776271030648691

theorem tailTrace_2813591 : CollatzResearch.WordTrace tailWord_2813591 prefixEnd_2813591 963149698776271030648691 := by
  unfold tailWord_2813591
  simp only [CollatzResearch.WordTrace]
  refine ⟨102620094349847804931512627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68413396233231869954341751 102620094349847804931512627)
  ·
    refine ⟨153930141524771707397268941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102620094349847804931512627 153930141524771707397268941)
    ·
      refine ⟨57723803071789390273975853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153930141524771707397268941 57723803071789390273975853)
      ·
        refine ⟨21646426151921021352740945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57723803071789390273975853 21646426151921021352740945)
        ·
          refine ⟨16234819613940766014555709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21646426151921021352740945 16234819613940766014555709)
          ·
            refine ⟨6088057355227787255458391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16234819613940766014555709 6088057355227787255458391)
            ·
              refine ⟨9132086032841680883187587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088057355227787255458391 9132086032841680883187587)
              ·
                refine ⟨13698129049262521324781381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132086032841680883187587 13698129049262521324781381)
                ·
                  refine ⟨2568399196736722748396509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13698129049262521324781381 2568399196736722748396509)
                  ·
                    refine ⟨963149698776271030648691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568399196736722748396509 963149698776271030648691)
                    ·
                      rfl

theorem cell22_2813591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_2813591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813591 prefixEnd_2813591 := by exact prefixLift 2813591
  have htrace : WordTrace (prefixWord ++ tailWord_2813591) baseStart_2813591 baseEnd_2813591 := by
    simpa [prefixWord, tailWord_2813591, baseEnd_2813591] using wordTrace_append hprefix tailTrace_2813591
  have hstable : (prefixWord ++ tailWord_2813591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813591).length < 2 ^ (prefixWord ++ tailWord_2813591).sum := by decide
  have hdescent : baseEnd_2813591 < baseStart_2813591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813621 : List Nat := [1, 3, 3, 3, 2, 1, 1, 8]
def baseStart_2813621 : Nat := 118140960795 + 2813621 * 2 ^ 59
def prefixEnd_2813621 : Nat := 4983230072969 + 3 ^ 40 * 2813621 * 2
def baseEnd_2813621 : Nat := 107017774265484550266511

theorem tailTrace_2813621 : CollatzResearch.WordTrace tailWord_2813621 prefixEnd_2813621 107017774265484550266511 := by
  unfold tailWord_2813621
  simp only [CollatzResearch.WordTrace]
  refine ⟨102621188539739120055104717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68414125693159413370069811 102621188539739120055104717)
  ·
    refine ⟨38482945702402170020664269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102621188539739120055104717 38482945702402170020664269)
    ·
      refine ⟨14431104638400813757749101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38482945702402170020664269 14431104638400813757749101)
      ·
        refine ⟨5411664239400305159155913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14431104638400813757749101 5411664239400305159155913)
        ·
          refine ⟨4058748179550228869366935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5411664239400305159155913 4058748179550228869366935)
          ·
            refine ⟨6088122269325343304050403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058748179550228869366935 6088122269325343304050403)
            ·
              refine ⟨9132183403988014956075605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088122269325343304050403 9132183403988014956075605)
              ·
                refine ⟨107017774265484550266511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9132183403988014956075605 107017774265484550266511)
                ·
                  rfl

theorem cell22_2813621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 8].length) (baseStart_2813621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813621 prefixEnd_2813621 := by exact prefixLift 2813621
  have htrace : WordTrace (prefixWord ++ tailWord_2813621) baseStart_2813621 baseEnd_2813621 := by
    simpa [prefixWord, tailWord_2813621, baseEnd_2813621] using wordTrace_append hprefix tailTrace_2813621
  have hstable : (prefixWord ++ tailWord_2813621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813621).length < 2 ^ (prefixWord ++ tailWord_2813621).sum := by decide
  have hdescent : baseEnd_2813621 < baseStart_2813621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813638 : List Nat := [6, 1, 2, 1, 1, 1, 10]
def baseStart_2813638 : Nat := 118140960795 + 2813638 * 2 ^ 59
def prefixEnd_2813638 : Nat := 4983230072969 + 3 ^ 40 * 2813638 * 2
def baseEnd_2813638 : Nat := 35672806956917724989761

theorem tailTrace_2813638 : CollatzResearch.WordTrace tailWord_2813638 prefixEnd_2813638 35672806956917724989761 := by
  unfold tailWord_2813638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3206931518146172873702299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68414539053785021305649045 3206931518146172873702299)
  ·
    refine ⟨4810397277219259310553449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3206931518146172873702299 4810397277219259310553449)
    ·
      refine ⟨3607797957914444482915087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4810397277219259310553449 3607797957914444482915087)
      ·
        refine ⟨5411696936871666724372631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607797957914444482915087 5411696936871666724372631)
        ·
          refine ⟨8117545405307500086558947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411696936871666724372631 8117545405307500086558947)
          ·
            refine ⟨12176318107961250129838421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8117545405307500086558947 12176318107961250129838421)
            ·
              refine ⟨35672806956917724989761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12176318107961250129838421 35672806956917724989761)
              ·
                rfl

theorem cell22_2813638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 10].length) (baseStart_2813638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813638 prefixEnd_2813638 := by exact prefixLift 2813638
  have htrace : WordTrace (prefixWord ++ tailWord_2813638) baseStart_2813638 baseEnd_2813638 := by
    simpa [prefixWord, tailWord_2813638, baseEnd_2813638] using wordTrace_append hprefix tailTrace_2813638
  have hstable : (prefixWord ++ tailWord_2813638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813638).length < 2 ^ (prefixWord ++ tailWord_2813638).sum := by decide
  have hdescent : baseEnd_2813638 < baseStart_2813638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813649 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 7]
def baseStart_2813649 : Nat := 118140960795 + 2813649 * 2 ^ 59
def prefixEnd_2813649 : Nat := 4983230072969 + 3 ^ 40 * 2813649 * 2
def baseEnd_2813649 : Nat := 321056517787192737566171

theorem tailTrace_2813649 : CollatzResearch.WordTrace tailWord_2813649 prefixEnd_2813649 321056517787192737566171 := by
  unfold tailWord_2813649
  simp only [CollatzResearch.WordTrace]
  refine ⟨102622209783637680837124001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68414806522425120558082667 102622209783637680837124001)
  ·
    refine ⟨76966657337728260627843001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102622209783637680837124001 76966657337728260627843001)
    ·
      refine ⟨57724993003296195470882251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76966657337728260627843001 57724993003296195470882251)
      ·
        refine ⟨86587489504944293206323377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57724993003296195470882251 86587489504944293206323377)
        ·
          refine ⟨64940617128708219904742533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86587489504944293206323377 64940617128708219904742533)
          ·
            refine ⟨12176365711632791232139225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64940617128708219904742533 12176365711632791232139225)
            ·
              refine ⟨9132274283724593424104419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12176365711632791232139225 9132274283724593424104419)
              ·
                refine ⟨13698411425586890136156629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132274283724593424104419 13698411425586890136156629)
                ·
                  refine ⟨321056517787192737566171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13698411425586890136156629 321056517787192737566171)
                  ·
                    rfl

theorem cell22_2813649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_2813649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813649 prefixEnd_2813649 := by exact prefixLift 2813649
  have htrace : WordTrace (prefixWord ++ tailWord_2813649) baseStart_2813649 baseEnd_2813649 := by
    simpa [prefixWord, tailWord_2813649, baseEnd_2813649] using wordTrace_append hprefix tailTrace_2813649
  have hstable : (prefixWord ++ tailWord_2813649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813649).length < 2 ^ (prefixWord ++ tailWord_2813649).sum := by decide
  have hdescent : baseEnd_2813649 < baseStart_2813649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813664 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_2813664 : Nat := 118140960795 + 2813664 * 2 ^ 59
def prefixEnd_2813664 : Nat := 4983230072969 + 3 ^ 40 * 2813664 * 2
def baseEnd_2813664 : Nat := 963174688168123173573467

theorem tailTrace_2813664 : CollatzResearch.WordTrace tailWord_2813664 prefixEnd_2813664 963174688168123173573467 := by
  unfold tailWord_2813664
  simp only [CollatzResearch.WordTrace]
  refine ⟨51311378439291669199460023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68415171252388892265946697 51311378439291669199460023)
  ·
    refine ⟨76967067658937503799190035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51311378439291669199460023 76967067658937503799190035)
    ·
      refine ⟨115450601488406255698785053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76967067658937503799190035 115450601488406255698785053)
      ·
        refine ⟨43293975558152345887044395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115450601488406255698785053 43293975558152345887044395)
        ·
          refine ⟨64940963337228518830566593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43293975558152345887044395 64940963337228518830566593)
          ·
            refine ⟨48705722502921389122924945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64940963337228518830566593 48705722502921389122924945)
            ·
              refine ⟨36529291877191041842193709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48705722502921389122924945 36529291877191041842193709)
              ·
                refine ⟨13698484453946640690822641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36529291877191041842193709 13698484453946640690822641)
                ·
                  refine ⟨10273863340459980518116981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13698484453946640690822641 10273863340459980518116981)
                  ·
                    refine ⟨963174688168123173573467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10273863340459980518116981 963174688168123173573467)
                    ·
                      rfl

theorem cell22_2813664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_2813664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813664 prefixEnd_2813664 := by exact prefixLift 2813664
  have htrace : WordTrace (prefixWord ++ tailWord_2813664) baseStart_2813664 baseEnd_2813664 := by
    simpa [prefixWord, tailWord_2813664, baseEnd_2813664] using wordTrace_append hprefix tailTrace_2813664
  have hstable : (prefixWord ++ tailWord_2813664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813664).length < 2 ^ (prefixWord ++ tailWord_2813664).sum := by decide
  have hdescent : baseEnd_2813664 < baseStart_2813664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813747 : List Nat := [1, 1, 1, 2, 8, 1, 2, 1, 1, 4]
def baseStart_2813747 : Nat := 118140960795 + 2813747 * 2 ^ 59
def prefixEnd_2813747 : Nat := 4983230072969 + 3 ^ 40 * 2813747 * 2
def baseEnd_2813747 : Nat := 963203100764338623748213

theorem tailTrace_2813747 : CollatzResearch.WordTrace tailWord_2813747 prefixEnd_2813747 963203100764338623748213 := by
  unfold tailWord_2813747
  simp only [CollatzResearch.WordTrace]
  refine ⟨102625784137282643574191495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68417189424855095716127663 102625784137282643574191495)
  ·
    refine ⟨153938676205923965361287243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102625784137282643574191495 153938676205923965361287243)
    ·
      refine ⟨230908014308885948041930865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153938676205923965361287243 230908014308885948041930865)
      ·
        refine ⟨173181010731664461031448149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230908014308885948041930865 173181010731664461031448149)
        ·
          refine ⟨2029464969511692902712283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 173181010731664461031448149 2029464969511692902712283)
          ·
            refine ⟨3044197454267539354068425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029464969511692902712283 3044197454267539354068425)
            ·
              refine ⟨2283148090700654515551319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044197454267539354068425 2283148090700654515551319)
              ·
                refine ⟨3424722136050981773326979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283148090700654515551319 3424722136050981773326979)
                ·
                  refine ⟨5137083204076472659990469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424722136050981773326979 5137083204076472659990469)
                  ·
                    refine ⟨963203100764338623748213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137083204076472659990469 963203100764338623748213)
                    ·
                      rfl

theorem cell22_2813747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 1, 4].length) (baseStart_2813747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813747 prefixEnd_2813747 := by exact prefixLift 2813747
  have htrace : WordTrace (prefixWord ++ tailWord_2813747) baseStart_2813747 baseEnd_2813747 := by
    simpa [prefixWord, tailWord_2813747, baseEnd_2813747] using wordTrace_append hprefix tailTrace_2813747
  have hstable : (prefixWord ++ tailWord_2813747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813747).length < 2 ^ (prefixWord ++ tailWord_2813747).sum := by decide
  have hdescent : baseEnd_2813747 < baseStart_2813747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813822 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2813822 : Nat := 118140960795 + 2813822 * 2 ^ 59
def prefixEnd_2813822 : Nat := 4983230072969 + 3 ^ 40 * 2813822 * 2
def baseEnd_2813822 : Nat := 963228774797063428122983

theorem tailTrace_2813822 : CollatzResearch.WordTrace tailWord_2813822 prefixEnd_2813822 963228774797063428122983 := by
  unfold tailWord_2813822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828564951501366422896465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68419013074673954255447813 12828564951501366422896465)
  ·
    refine ⟨9621423713626024817172349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12828564951501366422896465 9621423713626024817172349)
    ·
      refine ⟨3608033892609759306439631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9621423713626024817172349 3608033892609759306439631)
      ·
        refine ⟨5412050838914638959659447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608033892609759306439631 5412050838914638959659447)
        ·
          refine ⟨8118076258371958439489171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412050838914638959659447 8118076258371958439489171)
          ·
            refine ⟨12177114387557937659233757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118076258371958439489171 12177114387557937659233757)
            ·
              refine ⟨4566417895334226622212659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12177114387557937659233757 4566417895334226622212659)
              ·
                refine ⟨6849626843001339933318989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566417895334226622212659 6849626843001339933318989)
                ·
                  refine ⟨2568610066125502474994621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6849626843001339933318989 2568610066125502474994621)
                  ·
                    refine ⟨963228774797063428122983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568610066125502474994621 963228774797063428122983)
                    ·
                      rfl

theorem cell22_2813822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2813822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813822 prefixEnd_2813822 := by exact prefixLift 2813822
  have htrace : WordTrace (prefixWord ++ tailWord_2813822) baseStart_2813822 baseEnd_2813822 := by
    simpa [prefixWord, tailWord_2813822, baseEnd_2813822] using wordTrace_append hprefix tailTrace_2813822
  have hstable : (prefixWord ++ tailWord_2813822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813822).length < 2 ^ (prefixWord ++ tailWord_2813822).sum := by decide
  have hdescent : baseEnd_2813822 < baseStart_2813822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2813991 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2813991 : Nat := 118140960795 + 2813991 * 2 ^ 59
def prefixEnd_2813991 : Nat := 4983230072969 + 3 ^ 40 * 2813991 * 2
def baseEnd_2813991 : Nat := 963286626950803320647465

theorem tailTrace_2813991 : CollatzResearch.WordTrace tailWord_2813991 prefixEnd_2813991 963286626950803320647465 := by
  unfold tailWord_2813991
  simp only [CollatzResearch.WordTrace]
  refine ⟨102634683548398673246073827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68423122365599115497382551 102634683548398673246073827)
  ·
    refine ⟨153952025322598009869110741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102634683548398673246073827 153952025322598009869110741)
    ·
      refine ⟨3608250593498390856307283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 153952025322598009869110741 3608250593498390856307283)
      ·
        refine ⟨5412375890247586284460925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608250593498390856307283 5412375890247586284460925)
        ·
          refine ⟨2029640958842844856672847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5412375890247586284460925 2029640958842844856672847)
          ·
            refine ⟨3044461438264267285009271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029640958842844856672847 3044461438264267285009271)
            ·
              refine ⟨4566692157396400927513907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044461438264267285009271 4566692157396400927513907)
              ·
                refine ⟨6850038236094601391270861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566692157396400927513907 6850038236094601391270861)
                ·
                  refine ⟨2568764338535475521726573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6850038236094601391270861 2568764338535475521726573)
                  ·
                    refine ⟨963286626950803320647465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568764338535475521726573 963286626950803320647465)
                    ·
                      rfl

theorem cell22_2813991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2813991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2813991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2813991 prefixEnd_2813991 := by exact prefixLift 2813991
  have htrace : WordTrace (prefixWord ++ tailWord_2813991) baseStart_2813991 baseEnd_2813991 := by
    simpa [prefixWord, tailWord_2813991, baseEnd_2813991] using wordTrace_append hprefix tailTrace_2813991
  have hstable : (prefixWord ++ tailWord_2813991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2813991).length < 2 ^ (prefixWord ++ tailWord_2813991).sum := by decide
  have hdescent : baseEnd_2813991 < baseStart_2813991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2813991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814017 : List Nat := [1, 2, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2814017 : Nat := 118140960795 + 2814017 * 2 ^ 59
def prefixEnd_2814017 : Nat := 4983230072969 + 3 ^ 40 * 2814017 * 2
def baseEnd_2814017 : Nat := 963295527282147919497385

theorem tailTrace_2814017 : CollatzResearch.WordTrace tailWord_2814017 prefixEnd_2814017 963295527282147919497385 := by
  unfold tailWord_2814017
  simp only [CollatzResearch.WordTrace]
  refine ⟨102635631846304479686520305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68423754564202986457680203 102635631846304479686520305)
  ·
    refine ⟨76976723884728359764890229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102635631846304479686520305 76976723884728359764890229)
    ·
      refine ⟨7216567864193283727958459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76976723884728359764890229 7216567864193283727958459)
      ·
        refine ⟨10824851796289925591937689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7216567864193283727958459 10824851796289925591937689)
        ·
          refine ⟨8118638847217444193953267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10824851796289925591937689 8118638847217444193953267)
          ·
            refine ⟨12177958270826166290929901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118638847217444193953267 12177958270826166290929901)
            ·
              refine ⟨4566734351559812359098713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12177958270826166290929901 4566734351559812359098713)
              ·
                refine ⟨3425050763669859269324035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4566734351559812359098713 3425050763669859269324035)
                ·
                  refine ⟨5137576145504788903986053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425050763669859269324035 5137576145504788903986053)
                  ·
                    refine ⟨963295527282147919497385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137576145504788903986053 963295527282147919497385)
                    ·
                      rfl

theorem cell22_2814017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2814017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814017 prefixEnd_2814017 := by exact prefixLift 2814017
  have htrace : WordTrace (prefixWord ++ tailWord_2814017) baseStart_2814017 baseEnd_2814017 := by
    simpa [prefixWord, tailWord_2814017, baseEnd_2814017] using wordTrace_append hprefix tailTrace_2814017
  have hstable : (prefixWord ++ tailWord_2814017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814017).length < 2 ^ (prefixWord ++ tailWord_2814017).sum := by decide
  have hdescent : baseEnd_2814017 < baseStart_2814017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814028 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_2814028 : Nat := 118140960795 + 2814028 * 2 ^ 59
def prefixEnd_2814028 : Nat := 4983230072969 + 3 ^ 40 * 2814028 * 2
def baseEnd_2814028 : Nat := 963299292806947557472351

theorem tailTrace_2814028 : CollatzResearch.WordTrace tailWord_2814028 prefixEnd_2814028 963299292806947557472351 := by
  unfold tailWord_2814028
  simp only [CollatzResearch.WordTrace]
  refine ⟨51318016524632314282585369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68424022032843085710113825 51318016524632314282585369)
  ·
    refine ⟨38488512393474235711939027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51318016524632314282585369 38488512393474235711939027)
    ·
      refine ⟨57732768590211353567908541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38488512393474235711939027 57732768590211353567908541)
      ·
        refine ⟨21649788221329257587965703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57732768590211353567908541 21649788221329257587965703)
        ·
          refine ⟨32474682331993886381948555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21649788221329257587965703 32474682331993886381948555)
          ·
            refine ⟨48712023497990829572922833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32474682331993886381948555 48712023497990829572922833)
            ·
              refine ⟨36534017623493122179692125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48712023497990829572922833 36534017623493122179692125)
              ·
                refine ⟨13700256608809920817384547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36534017623493122179692125 13700256608809920817384547)
                ·
                  refine ⟨20550384913214881226076821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13700256608809920817384547 20550384913214881226076821)
                  ·
                    refine ⟨963299292806947557472351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20550384913214881226076821 963299292806947557472351)
                    ·
                      rfl

theorem cell22_2814028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_2814028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814028 prefixEnd_2814028 := by exact prefixLift 2814028
  have htrace : WordTrace (prefixWord ++ tailWord_2814028) baseStart_2814028 baseEnd_2814028 := by
    simpa [prefixWord, tailWord_2814028, baseEnd_2814028] using wordTrace_append hprefix tailTrace_2814028
  have hstable : (prefixWord ++ tailWord_2814028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814028).length < 2 ^ (prefixWord ++ tailWord_2814028).sum := by decide
  have hdescent : baseEnd_2814028 < baseStart_2814028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814030 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_2814030 : Nat := 118140960795 + 2814030 * 2 ^ 59
def prefixEnd_2814030 : Nat := 4983230072969 + 3 ^ 40 * 2814030 * 2
def baseEnd_2814030 : Nat := 963299977447820218922345

theorem tailTrace_2814030 : CollatzResearch.WordTrace tailWord_2814030 prefixEnd_2814030 963299977447820218922345 := by
  unfold tailWord_2814030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12829513249407172863342943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68424070663504921937829029 12829513249407172863342943)
  ·
    refine ⟨19244269874110759295014415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12829513249407172863342943 19244269874110759295014415)
    ·
      refine ⟨28866404811166138942521623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19244269874110759295014415 28866404811166138942521623)
      ·
        refine ⟨43299607216749208413782435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28866404811166138942521623 43299607216749208413782435)
        ·
          refine ⟨64949410825123812620673653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43299607216749208413782435 64949410825123812620673653)
          ·
            refine ⟨6089007264855357433188155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64949410825123812620673653 6089007264855357433188155)
            ·
              refine ⟨9133510897283036149782233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089007264855357433188155 9133510897283036149782233)
              ·
                refine ⟨6850133172962277112336675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9133510897283036149782233 6850133172962277112336675)
                ·
                  refine ⟨10275199759443415668505013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850133172962277112336675 10275199759443415668505013)
                  ·
                    refine ⟨963299977447820218922345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10275199759443415668505013 963299977447820218922345)
                    ·
                      rfl

theorem cell22_2814030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_2814030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814030 prefixEnd_2814030 := by exact prefixLift 2814030
  have htrace : WordTrace (prefixWord ++ tailWord_2814030) baseStart_2814030 baseEnd_2814030 := by
    simpa [prefixWord, tailWord_2814030, baseEnd_2814030] using wordTrace_append hprefix tailTrace_2814030
  have hstable : (prefixWord ++ tailWord_2814030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814030).length < 2 ^ (prefixWord ++ tailWord_2814030).sum := by decide
  have hdescent : baseEnd_2814030 < baseStart_2814030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814034 : List Nat := [3, 2, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2814034 : Nat := 118140960795 + 2814034 * 2 ^ 59
def prefixEnd_2814034 : Nat := 4983230072969 + 3 ^ 40 * 2814034 * 2
def baseEnd_2814034 : Nat := 963301346729565541822333

theorem tailTrace_2814034 : CollatzResearch.WordTrace tailWord_2814034 prefixEnd_2814034 963301346729565541822333 := by
  unfold tailWord_2814034
  simp only [CollatzResearch.WordTrace]
  refine ⟨25659062971810722897472289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68424167924828594393259437 25659062971810722897472289)
  ·
    refine ⟨19244297228858042173104217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25659062971810722897472289 19244297228858042173104217)
    ·
      refine ⟨14433222921643531629828163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19244297228858042173104217 14433222921643531629828163)
      ·
        refine ⟨21649834382465297444742245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14433222921643531629828163 21649834382465297444742245)
        ·
          refine ⟨4059343946712243270889171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21649834382465297444742245 4059343946712243270889171)
          ·
            refine ⟨6089015920068364906333757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059343946712243270889171 6089015920068364906333757)
            ·
              refine ⟨2283380970025636839875159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6089015920068364906333757 2283380970025636839875159)
              ·
                refine ⟨3425071455038455259812739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2283380970025636839875159 3425071455038455259812739)
                ·
                  refine ⟨5137607182557682889719109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425071455038455259812739 5137607182557682889719109)
                  ·
                    refine ⟨963301346729565541822333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137607182557682889719109 963301346729565541822333)
                    ·
                      rfl

theorem cell22_2814034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2814034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814034 prefixEnd_2814034 := by exact prefixLift 2814034
  have htrace : WordTrace (prefixWord ++ tailWord_2814034) baseStart_2814034 baseEnd_2814034 := by
    simpa [prefixWord, tailWord_2814034, baseEnd_2814034] using wordTrace_append hprefix tailTrace_2814034
  have hstable : (prefixWord ++ tailWord_2814034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814034).length < 2 ^ (prefixWord ++ tailWord_2814034).sum := by decide
  have hdescent : baseEnd_2814034 < baseStart_2814034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814060 : List Nat := [2, 2, 1, 1, 3, 5, 1, 7]
def baseStart_2814060 : Nat := 118140960795 + 2814060 * 2 ^ 59
def prefixEnd_2814060 : Nat := 4983230072969 + 3 ^ 40 * 2814060 * 2
def baseEnd_2814060 : Nat := 107034471895656682296917

theorem tailTrace_2814060 : CollatzResearch.WordTrace tailWord_2814060 prefixEnd_2814060 107034471895656682296917 := by
  unfold tailWord_2814060
  simp only [CollatzResearch.WordTrace]
  refine ⟨51318600092574349015167817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68424800123432465353557089 51318600092574349015167817)
  ·
    refine ⟨38488950069430761761375863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51318600092574349015167817 38488950069430761761375863)
    ·
      refine ⟨57733425104146142642063795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38488950069430761761375863 57733425104146142642063795)
      ·
        refine ⟨86600137656219213963095693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57733425104146142642063795 86600137656219213963095693)
        ·
          refine ⟨32475051621082205236160885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86600137656219213963095693 32475051621082205236160885)
          ·
            refine ⟨3044536089476456740890083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32475051621082205236160885 3044536089476456740890083)
            ·
              refine ⟨4566804134214685111335125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044536089476456740890083 4566804134214685111335125)
              ·
                refine ⟨107034471895656682296917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4566804134214685111335125 107034471895656682296917)
                ·
                  rfl

theorem cell22_2814060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 7].length) (baseStart_2814060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814060 prefixEnd_2814060 := by exact prefixLift 2814060
  have htrace : WordTrace (prefixWord ++ tailWord_2814060) baseStart_2814060 baseEnd_2814060 := by
    simpa [prefixWord, tailWord_2814060, baseEnd_2814060] using wordTrace_append hprefix tailTrace_2814060
  have hstable : (prefixWord ++ tailWord_2814060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814060).length < 2 ^ (prefixWord ++ tailWord_2814060).sum := by decide
  have hdescent : baseEnd_2814060 < baseStart_2814060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814109 : List Nat := [1, 4, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2814109 : Nat := 118140960795 + 2814109 * 2 ^ 59
def prefixEnd_2814109 : Nat := 4983230072969 + 3 ^ 40 * 2814109 * 2
def baseEnd_2814109 : Nat := 963327020762290346197103

theorem tailTrace_2814109 : CollatzResearch.WordTrace tailWord_2814109 prefixEnd_2814109 963327020762290346197103 := by
  unfold tailWord_2814109
  simp only [CollatzResearch.WordTrace]
  refine ⟨102638987361971179398869381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68425991574647452932579587 102638987361971179398869381)
  ·
    refine ⟨19244810130369596137288009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102638987361971179398869381 19244810130369596137288009)
    ·
      refine ⟨14433607597777197102966007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19244810130369596137288009 14433607597777197102966007)
      ·
        refine ⟨21650411396665795654449011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14433607597777197102966007 21650411396665795654449011)
        ·
          refine ⟨32475617094998693481673517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21650411396665795654449011 32475617094998693481673517)
          ·
            refine ⟨12178356410624510055627569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32475617094998693481673517 12178356410624510055627569)
            ·
              refine ⟨9133767307968382541720677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12178356410624510055627569 9133767307968382541720677)
              ·
                refine ⟨1712581370244071726572627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9133767307968382541720677 1712581370244071726572627)
                ·
                  refine ⟨2568872055366107589858941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712581370244071726572627 2568872055366107589858941)
                  ·
                    refine ⟨963327020762290346197103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568872055366107589858941 963327020762290346197103)
                    ·
                      rfl

theorem cell22_2814109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2814109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814109 prefixEnd_2814109 := by exact prefixLift 2814109
  have htrace : WordTrace (prefixWord ++ tailWord_2814109) baseStart_2814109 baseEnd_2814109 := by
    simpa [prefixWord, tailWord_2814109, baseEnd_2814109] using wordTrace_append hprefix tailTrace_2814109
  have hstable : (prefixWord ++ tailWord_2814109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814109).length < 2 ^ (prefixWord ++ tailWord_2814109).sum := by decide
  have hdescent : baseEnd_2814109 < baseStart_2814109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814180 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2814180 : Nat := 118140960795 + 2814180 * 2 ^ 59
def prefixEnd_2814180 : Nat := 4983230072969 + 3 ^ 40 * 2814180 * 2
def baseEnd_2814180 : Nat := 963351325513269827671885

theorem tailTrace_2814180 : CollatzResearch.WordTrace tailWord_2814180 prefixEnd_2814180 963351325513269827671885 := by
  unfold tailWord_2814180
  simp only [CollatzResearch.WordTrace]
  refine ⟨51320788472356979262351997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68427717963142639016469329 51320788472356979262351997)
  ·
    refine ⟨19245295677133867223381999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51320788472356979262351997 19245295677133867223381999)
    ·
      refine ⟨28867943515700800835072999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19245295677133867223381999 28867943515700800835072999)
      ·
        refine ⟨43301915273551201252609499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28867943515700800835072999 43301915273551201252609499)
        ·
          refine ⟨64952872910326801878914249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43301915273551201252609499 64952872910326801878914249)
          ·
            refine ⟨48714654682745101409185687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64952872910326801878914249 48714654682745101409185687)
            ·
              refine ⟨73071982024117652113778531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48714654682745101409185687 73071982024117652113778531)
              ·
                refine ⟨109607973036176478170667797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73071982024117652113778531 109607973036176478170667797)
                ·
                  refine ⟨5137873736070772414250053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109607973036176478170667797 5137873736070772414250053)
                  ·
                    refine ⟨963351325513269827671885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137873736070772414250053 963351325513269827671885)
                    ·
                      rfl

theorem cell22_2814180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2814180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814180 prefixEnd_2814180 := by exact prefixLift 2814180
  have htrace : WordTrace (prefixWord ++ tailWord_2814180) baseStart_2814180 baseEnd_2814180 := by
    simpa [prefixWord, tailWord_2814180, baseEnd_2814180] using wordTrace_append hprefix tailTrace_2814180
  have hstable : (prefixWord ++ tailWord_2814180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814180).length < 2 ^ (prefixWord ++ tailWord_2814180).sum := by decide
  have hdescent : baseEnd_2814180 < baseStart_2814180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814212 : List Nat := [2, 3, 2, 2, 4, 9]
def baseStart_2814212 : Nat := 118140960795 + 2814212 * 2 ^ 59
def prefixEnd_2814212 : Nat := 4983230072969 + 3 ^ 40 * 2814212 * 2
def baseEnd_2814212 : Nat := 11893361478607807541627

theorem tailTrace_2814212 : CollatzResearch.WordTrace tailWord_2814212 prefixEnd_2814212 11893361478607807541627 := by
  unfold tailWord_2814212
  simp only [CollatzResearch.WordTrace]
  refine ⟨51321372040299013994934445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68428496053732018659912593 51321372040299013994934445)
  ·
    refine ⟨19245514515112130248100417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51321372040299013994934445 19245514515112130248100417)
    ·
      refine ⟨14434135886334097686075313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19245514515112130248100417 14434135886334097686075313)
      ·
        refine ⟨10825601914750573264556485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14434135886334097686075313 10825601914750573264556485)
        ·
          refine ⟨2029800359015732487104341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10825601914750573264556485 2029800359015732487104341)
          ·
            refine ⟨11893361478607807541627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2029800359015732487104341 11893361478607807541627)
            ·
              rfl

theorem cell22_2814212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 9].length) (baseStart_2814212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814212 prefixEnd_2814212 := by exact prefixLift 2814212
  have htrace : WordTrace (prefixWord ++ tailWord_2814212) baseStart_2814212 baseEnd_2814212 := by
    simpa [prefixWord, tailWord_2814212, baseEnd_2814212] using wordTrace_append hprefix tailTrace_2814212
  have hstable : (prefixWord ++ tailWord_2814212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814212).length < 2 ^ (prefixWord ++ tailWord_2814212).sum := by decide
  have hdescent : baseEnd_2814212 < baseStart_2814212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814225 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2814225 : Nat := 118140960795 + 2814225 * 2 ^ 59
def prefixEnd_2814225 : Nat := 4983230072969 + 3 ^ 40 * 2814225 * 2
def baseEnd_2814225 : Nat := 963366729932904710296747

theorem tailTrace_2814225 : CollatzResearch.WordTrace tailWord_2814225 prefixEnd_2814225 963366729932904710296747 := by
  unfold tailWord_2814225
  simp only [CollatzResearch.WordTrace]
  refine ⟨102643218229550931210092129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68428812153033954140061419 102643218229550931210092129)
  ·
    refine ⟨76982413672163198407569097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102643218229550931210092129 76982413672163198407569097)
    ·
      refine ⟨57736810254122398805676823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76982413672163198407569097 57736810254122398805676823)
      ·
        refine ⟨86605215381183598208515235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57736810254122398805676823 86605215381183598208515235)
        ·
          refine ⟨129907823071775397312772853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86605215381183598208515235 129907823071775397312772853)
          ·
            refine ⟨12178858412978943498072455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129907823071775397312772853 12178858412978943498072455)
            ·
              refine ⟨18268287619468415247108683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12178858412978943498072455 18268287619468415247108683)
              ·
                refine ⟨27402431429202622870663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18268287619468415247108683 27402431429202622870663025)
                ·
                  refine ⟨20551823571901967152997269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27402431429202622870663025 20551823571901967152997269)
                  ·
                    refine ⟨963366729932904710296747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20551823571901967152997269 963366729932904710296747)
                    ·
                      rfl

theorem cell22_2814225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2814225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814225 prefixEnd_2814225 := by exact prefixLift 2814225
  have htrace : WordTrace (prefixWord ++ tailWord_2814225) baseStart_2814225 baseEnd_2814225 := by
    simpa [prefixWord, tailWord_2814225, baseEnd_2814225] using wordTrace_append hprefix tailTrace_2814225
  have hstable : (prefixWord ++ tailWord_2814225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814225).length < 2 ^ (prefixWord ++ tailWord_2814225).sum := by decide
  have hdescent : baseEnd_2814225 < baseStart_2814225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814244 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_2814244 : Nat := 118140960795 + 2814244 * 2 ^ 59
def prefixEnd_2814244 : Nat := 4983230072969 + 3 ^ 40 * 2814244 * 2
def baseEnd_2814244 : Nat := 963373234021194994071689

theorem tailTrace_2814244 : CollatzResearch.WordTrace tailWord_2814244 prefixEnd_2814244 963373234021194994071689 := by
  unfold tailWord_2814244
  simp only [CollatzResearch.WordTrace]
  refine ⟨51321955608241048727516893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68429274144321398303355857 51321955608241048727516893)
  ·
    refine ⟨19245733353090393272818835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51321955608241048727516893 19245733353090393272818835)
    ·
      refine ⟨28868600029635589909228253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19245733353090393272818835 28868600029635589909228253)
      ·
        refine ⟨10825725011113346215960595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28868600029635589909228253 10825725011113346215960595)
        ·
          refine ⟨16238587516670019323940893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10825725011113346215960595 16238587516670019323940893)
          ·
            refine ⟨6089470318751257246477835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16238587516670019323940893 6089470318751257246477835)
            ·
              refine ⟨9134205478126885869716753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089470318751257246477835 9134205478126885869716753)
              ·
                refine ⟨6850654108595164402287565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9134205478126885869716753 6850654108595164402287565)
                ·
                  refine ⟨2568995290723186650857837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6850654108595164402287565 2568995290723186650857837)
                  ·
                    refine ⟨963373234021194994071689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2568995290723186650857837 963373234021194994071689)
                    ·
                      rfl

theorem cell22_2814244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_2814244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814244 prefixEnd_2814244 := by exact prefixLift 2814244
  have htrace : WordTrace (prefixWord ++ tailWord_2814244) baseStart_2814244 baseEnd_2814244 := by
    simpa [prefixWord, tailWord_2814244, baseEnd_2814244] using wordTrace_append hprefix tailTrace_2814244
  have hstable : (prefixWord ++ tailWord_2814244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814244).length < 2 ^ (prefixWord ++ tailWord_2814244).sum := by decide
  have hdescent : baseEnd_2814244 < baseStart_2814244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814261 : List Nat := [1, 3, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2814261 : Nat := 118140960795 + 2814261 * 2 ^ 59
def prefixEnd_2814261 : Nat := 4983230072969 + 3 ^ 40 * 2814261 * 2
def baseEnd_2814261 : Nat := 963379053468612616396637

theorem tailTrace_2814261 : CollatzResearch.WordTrace tailWord_2814261 prefixEnd_2814261 963379053468612616396637 := by
  unfold tailWord_2814261
  simp only [CollatzResearch.WordTrace]
  refine ⟨102644531257420509358402637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68429687504947006238935091 102644531257420509358402637)
  ·
    refine ⟨38491699221532691009400989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102644531257420509358402637 38491699221532691009400989)
    ·
      refine ⟨14434387208074759128525371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38491699221532691009400989 14434387208074759128525371)
      ·
        refine ⟨21651580812112138692788057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14434387208074759128525371 21651580812112138692788057)
        ·
          refine ⟨16238685609084104019591043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21651580812112138692788057 16238685609084104019591043)
          ·
            refine ⟨24358028413626156029386565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16238685609084104019591043 24358028413626156029386565)
            ·
              refine ⟨4567130327554904255509981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24358028413626156029386565 4567130327554904255509981)
              ·
                refine ⟨1712673872833089095816243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567130327554904255509981 1712673872833089095816243)
                ·
                  refine ⟨2569010809249633643724365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712673872833089095816243 2569010809249633643724365)
                  ·
                    refine ⟨963379053468612616396637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569010809249633643724365 963379053468612616396637)
                    ·
                      rfl

theorem cell22_2814261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2814261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814261 prefixEnd_2814261 := by exact prefixLift 2814261
  have htrace : WordTrace (prefixWord ++ tailWord_2814261) baseStart_2814261 baseEnd_2814261 := by
    simpa [prefixWord, tailWord_2814261, baseEnd_2814261] using wordTrace_append hprefix tailTrace_2814261
  have hstable : (prefixWord ++ tailWord_2814261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814261).length < 2 ^ (prefixWord ++ tailWord_2814261).sum := by decide
  have hdescent : baseEnd_2814261 < baseStart_2814261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814317 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2814317 : Nat := 118140960795 + 2814317 * 2 ^ 59
def prefixEnd_2814317 : Nat := 4983230072969 + 3 ^ 40 * 2814317 * 2
def baseEnd_2814317 : Nat := 963398223413047136996465

theorem tailTrace_2814317 : CollatzResearch.WordTrace tailWord_2814317 prefixEnd_2814317 963398223413047136996465 := by
  unfold tailWord_2814317
  simp only [CollatzResearch.WordTrace]
  refine ⟨102646573745217630922441205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68431049163478420614960803 102646573745217630922441205)
  ·
    refine ⟨9623116288614152898978863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102646573745217630922441205 9623116288614152898978863)
    ·
      refine ⟨14434674432921229348468295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9623116288614152898978863 14434674432921229348468295)
      ·
        refine ⟨21652011649381844022702443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14434674432921229348468295 21652011649381844022702443)
        ·
          refine ⟨32478017474072766034053665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21652011649381844022702443 32478017474072766034053665)
          ·
            refine ⟨24358513105554574525540249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32478017474072766034053665 24358513105554574525540249)
            ·
              refine ⟨18268884829165930894155187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24358513105554574525540249 18268884829165930894155187)
              ·
                refine ⟨27403327243748896341232781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18268884829165930894155187 27403327243748896341232781)
                ·
                  refine ⟨10276247716405836127962293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27403327243748896341232781 10276247716405836127962293)
                  ·
                    refine ⟨963398223413047136996465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10276247716405836127962293 963398223413047136996465)
                    ·
                      rfl

theorem cell22_2814317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2814317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814317 prefixEnd_2814317 := by exact prefixLift 2814317
  have htrace : WordTrace (prefixWord ++ tailWord_2814317) baseStart_2814317 baseEnd_2814317 := by
    simpa [prefixWord, tailWord_2814317, baseEnd_2814317] using wordTrace_append hprefix tailTrace_2814317
  have hstable : (prefixWord ++ tailWord_2814317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814317).length < 2 ^ (prefixWord ++ tailWord_2814317).sum := by decide
  have hdescent : baseEnd_2814317 < baseStart_2814317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814347 : List Nat := [1, 1, 1, 1, 4, 5, 2, 7]
def baseStart_2814347 : Nat := 118140960795 + 2814347 * 2 ^ 59
def prefixEnd_2814347 : Nat := 4983230072969 + 3 ^ 40 * 2814347 * 2
def baseEnd_2814347 : Nat := 107045388114015228749597

theorem tailTrace_2814347 : CollatzResearch.WordTrace tailWord_2814347 prefixEnd_2814347 107045388114015228749597 := by
  unfold tailWord_2814347
  simp only [CollatzResearch.WordTrace]
  refine ⟨102647667935108946046033295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68431778623405964030688863 102647667935108946046033295)
  ·
    refine ⟨153971501902663419069049943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102647667935108946046033295 153971501902663419069049943)
    ·
      refine ⟨230957252853995128603574915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153971501902663419069049943 230957252853995128603574915)
      ·
        refine ⟨346435879280992692905362373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230957252853995128603574915 346435879280992692905362373)
        ·
          refine ⟨64956727365186129919755445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346435879280992692905362373 64956727365186129919755445)
          ·
            refine ⟨6089693190486199679977073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64956727365186129919755445 6089693190486199679977073)
            ·
              refine ⟨4567269892864649759982805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6089693190486199679977073 4567269892864649759982805)
              ·
                refine ⟨107045388114015228749597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4567269892864649759982805 107045388114015228749597)
                ·
                  rfl

theorem cell22_2814347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 7].length) (baseStart_2814347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814347 prefixEnd_2814347 := by exact prefixLift 2814347
  have htrace : WordTrace (prefixWord ++ tailWord_2814347) baseStart_2814347 baseEnd_2814347 := by
    simpa [prefixWord, tailWord_2814347, baseEnd_2814347] using wordTrace_append hprefix tailTrace_2814347
  have hstable : (prefixWord ++ tailWord_2814347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814347).length < 2 ^ (prefixWord ++ tailWord_2814347).sum := by decide
  have hdescent : baseEnd_2814347 < baseStart_2814347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814366 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2814366 : Nat := 118140960795 + 2814366 * 2 ^ 59
def prefixEnd_2814366 : Nat := 4983230072969 + 3 ^ 40 * 2814366 * 2
def baseEnd_2814366 : Nat := 963414997114427342521315

theorem tailTrace_2814366 : CollatzResearch.WordTrace tailWord_2814366 prefixEnd_2814366 963414997114427342521315 := by
  unfold tailWord_2814366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12831045115255014036371869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68432240614693408193983301 12831045115255014036371869)
  ·
    refine ⟨4811641918220630263639451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12831045115255014036371869 4811641918220630263639451)
    ·
      refine ⟨7217462877330945395459177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4811641918220630263639451 7217462877330945395459177)
      ·
        refine ⟨5413097157998209046594383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7217462877330945395459177 5413097157998209046594383)
        ·
          refine ⟨8119645736997313569891575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413097157998209046594383 8119645736997313569891575)
          ·
            refine ⟨12179468605495970354837363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8119645736997313569891575 12179468605495970354837363)
            ·
              refine ⟨18269202908243955532256045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12179468605495970354837363 18269202908243955532256045)
              ·
                refine ⟨6850951090591483324596017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18269202908243955532256045 6850951090591483324596017)
                ·
                  refine ⟨5138213317943612493447013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6850951090591483324596017 5138213317943612493447013)
                  ·
                    refine ⟨963414997114427342521315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5138213317943612493447013 963414997114427342521315)
                    ·
                      rfl

theorem cell22_2814366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2814366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814366 prefixEnd_2814366 := by exact prefixLift 2814366
  have htrace : WordTrace (prefixWord ++ tailWord_2814366) baseStart_2814366 baseEnd_2814366 := by
    simpa [prefixWord, tailWord_2814366, baseEnd_2814366] using wordTrace_append hprefix tailTrace_2814366
  have hstable : (prefixWord ++ tailWord_2814366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814366).length < 2 ^ (prefixWord ++ tailWord_2814366).sum := by decide
  have hdescent : baseEnd_2814366 < baseStart_2814366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814407 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2814407 : Nat := 118140960795 + 2814407 * 2 ^ 59
def prefixEnd_2814407 : Nat := 4983230072969 + 3 ^ 40 * 2814407 * 2
def baseEnd_2814407 : Nat := 963429032252316902246189

theorem tailTrace_2814407 : CollatzResearch.WordTrace tailWord_2814407 prefixEnd_2814407 963429032252316902246189 := by
  unfold tailWord_2814407
  simp only [CollatzResearch.WordTrace]
  refine ⟨102649856314891576293217475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68433237543261050862144983 102649856314891576293217475)
  ·
    refine ⟨153974784472337364439826213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102649856314891576293217475 153974784472337364439826213)
    ·
      refine ⟨28870272088563255832467415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153974784472337364439826213 28870272088563255832467415)
      ·
        refine ⟨43305408132844883748701123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28870272088563255832467415 43305408132844883748701123)
        ·
          refine ⟨64958112199267325623051685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43305408132844883748701123 64958112199267325623051685)
          ·
            refine ⟨12179646037362623554322191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64958112199267325623051685 12179646037362623554322191)
            ·
              refine ⟨18269469056043935331483287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12179646037362623554322191 18269469056043935331483287)
              ·
                refine ⟨27404203584065902997224931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18269469056043935331483287 27404203584065902997224931)
                ·
                  refine ⟨41106305376098854495837397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27404203584065902997224931 41106305376098854495837397)
                  ·
                    refine ⟨963429032252316902246189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41106305376098854495837397 963429032252316902246189)
                    ·
                      rfl

theorem cell22_2814407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2814407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814407 prefixEnd_2814407 := by exact prefixLift 2814407
  have htrace : WordTrace (prefixWord ++ tailWord_2814407) baseStart_2814407 baseEnd_2814407 := by
    simpa [prefixWord, tailWord_2814407, baseEnd_2814407] using wordTrace_append hprefix tailTrace_2814407
  have hstable : (prefixWord ++ tailWord_2814407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814407).length < 2 ^ (prefixWord ++ tailWord_2814407).sum := by decide
  have hdescent : baseEnd_2814407 < baseStart_2814407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814467 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 3, 6]
def baseStart_2814467 : Nat := 118140960795 + 2814467 * 2 ^ 59
def prefixEnd_2814467 : Nat := 4983230072969 + 3 ^ 40 * 2814467 * 2
def baseEnd_2814467 : Nat := 963449571478496745746005

theorem tailTrace_2814467 : CollatzResearch.WordTrace tailWord_2814467 prefixEnd_2814467 963449571478496745746005 := by
  unfold tailWord_2814467
  simp only [CollatzResearch.WordTrace]
  refine ⟨102652044694674206540401655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68434696463116137693601103 102652044694674206540401655)
  ·
    refine ⟨153978067042011309810602483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102652044694674206540401655 153978067042011309810602483)
    ·
      refine ⟨230967100563016964715903725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153978067042011309810602483 230967100563016964715903725)
      ·
        refine ⟨86612662711131361768463897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230967100563016964715903725 86612662711131361768463897)
        ·
          refine ⟨64959497033348521326347923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86612662711131361768463897 64959497033348521326347923)
          ·
            refine ⟨97439245550022781989521885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64959497033348521326347923 97439245550022781989521885)
            ·
              refine ⟨36539717081258543246070707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97439245550022781989521885 36539717081258543246070707)
              ·
                refine ⟨54809575621887814869106061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36539717081258543246070707 54809575621887814869106061)
                ·
                  refine ⟨20553590858207930575914773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54809575621887814869106061 20553590858207930575914773)
                  ·
                    refine ⟨963449571478496745746005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20553590858207930575914773 963449571478496745746005)
                    ·
                      rfl

theorem cell22_2814467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_2814467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814467 prefixEnd_2814467 := by exact prefixLift 2814467
  have htrace : WordTrace (prefixWord ++ tailWord_2814467) baseStart_2814467 baseEnd_2814467 := by
    simpa [prefixWord, tailWord_2814467, baseEnd_2814467] using wordTrace_append hprefix tailTrace_2814467
  have hstable : (prefixWord ++ tailWord_2814467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814467).length < 2 ^ (prefixWord ++ tailWord_2814467).sum := by decide
  have hdescent : baseEnd_2814467 < baseStart_2814467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814469 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2814469 : Nat := 118140960795 + 2814469 * 2 ^ 59
def prefixEnd_2814469 : Nat := 4983230072969 + 3 ^ 40 * 2814469 * 2
def baseEnd_2814469 : Nat := 963450256119369407195999

theorem tailTrace_2814469 : CollatzResearch.WordTrace tailWord_2814469 prefixEnd_2814469 963450256119369407195999 := by
  unfold tailWord_2814469
  simp only [CollatzResearch.WordTrace]
  refine ⟨102652117640666960881974461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68434745093777973921316307 102652117640666960881974461)
  ·
    refine ⟨38494544115250110330740423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102652117640666960881974461 38494544115250110330740423)
    ·
      refine ⟨57741816172875165496110635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38494544115250110330740423 57741816172875165496110635)
      ·
        refine ⟨86612724259312748244165953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57741816172875165496110635 86612724259312748244165953)
        ·
          refine ⟨64959543194484561183124465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86612724259312748244165953 64959543194484561183124465)
          ·
            refine ⟨48719657395863420887343349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64959543194484561183124465 48719657395863420887343349)
            ·
              refine ⟨4567467880862195708188439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48719657395863420887343349 4567467880862195708188439)
              ·
                refine ⟨6851201821293293562282659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567467880862195708188439 6851201821293293562282659)
                ·
                  refine ⟨10276802731939940343423989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6851201821293293562282659 10276802731939940343423989)
                  ·
                    refine ⟨963450256119369407195999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10276802731939940343423989 963450256119369407195999)
                    ·
                      rfl

theorem cell22_2814469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2814469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814469 prefixEnd_2814469 := by exact prefixLift 2814469
  have htrace : WordTrace (prefixWord ++ tailWord_2814469) baseStart_2814469 baseEnd_2814469 := by
    simpa [prefixWord, tailWord_2814469, baseEnd_2814469] using wordTrace_append hprefix tailTrace_2814469
  have hstable : (prefixWord ++ tailWord_2814469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814469).length < 2 ^ (prefixWord ++ tailWord_2814469).sum := by decide
  have hdescent : baseEnd_2814469 < baseStart_2814469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814488 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 4]
def baseStart_2814488 : Nat := 118140960795 + 2814488 * 2 ^ 59
def prefixEnd_2814488 : Nat := 4983230072969 + 3 ^ 40 * 2814488 * 2
def baseEnd_2814488 : Nat := 321152253402553230323647

theorem tailTrace_2814488 : CollatzResearch.WordTrace tailWord_2814488 prefixEnd_2814488 321152253402553230323647 := by
  unfold tailWord_2814488
  simp only [CollatzResearch.WordTrace]
  refine ⟨51326405313799063563458059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68435207085065418084610745 51326405313799063563458059)
  ·
    refine ⟨76989607970698595345187089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51326405313799063563458059 76989607970698595345187089)
    ·
      refine ⟨57742205978023946508890317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76989607970698595345187089 57742205978023946508890317)
      ·
        refine ⟨21653327241758979940833869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57742205978023946508890317 21653327241758979940833869)
        ·
          refine ⟨8119997715659617477812701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21653327241758979940833869 8119997715659617477812701)
          ·
            refine ⟨3044999143372356554179763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8119997715659617477812701 3044999143372356554179763)
            ·
              refine ⟨4567498715058534831269645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3044999143372356554179763 4567498715058534831269645)
              ·
                refine ⟨1712812018146950561726117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4567498715058534831269645 1712812018146950561726117)
                ·
                  refine ⟨321152253402553230323647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1712812018146950561726117 321152253402553230323647)
                  ·
                    rfl

theorem cell22_2814488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_2814488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814488 prefixEnd_2814488 := by exact prefixLift 2814488
  have htrace : WordTrace (prefixWord ++ tailWord_2814488) baseStart_2814488 baseEnd_2814488 := by
    simpa [prefixWord, tailWord_2814488, baseEnd_2814488] using wordTrace_append hprefix tailTrace_2814488
  have hstable : (prefixWord ++ tailWord_2814488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814488).length < 2 ^ (prefixWord ++ tailWord_2814488).sum := by decide
  have hdescent : baseEnd_2814488 < baseStart_2814488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814499 : List Nat := [1, 1, 1, 4, 4, 3, 8]
def baseStart_2814499 : Nat := 118140960795 + 2814499 * 2 ^ 59
def prefixEnd_2814499 : Nat := 4983230072969 + 3 ^ 40 * 2814499 * 2
def baseEnd_2814499 : Nat := 35683723175276271442441

theorem tailTrace_2814499 : CollatzResearch.WordTrace tailWord_2814499 prefixEnd_2814499 35683723175276271442441 := by
  unfold tailWord_2814499
  simp only [CollatzResearch.WordTrace]
  refine ⟨102653211830558276005566551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68435474553705517337044367 102653211830558276005566551)
  ·
    refine ⟨153979817745837414008349827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102653211830558276005566551 153979817745837414008349827)
    ·
      refine ⟨230969726618756121012524741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153979817745837414008349827 230969726618756121012524741)
      ·
        refine ⟨43306823741016772689848389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230969726618756121012524741 43306823741016772689848389)
        ·
          refine ⟨8120029451440644879346573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43306823741016772689848389 8120029451440644879346573)
          ·
            refine ⟨3045011044290241829754965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8120029451440644879346573 3045011044290241829754965)
            ·
              refine ⟨35683723175276271442441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3045011044290241829754965 35683723175276271442441)
              ·
                rfl

theorem cell22_2814499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 8].length) (baseStart_2814499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814499 prefixEnd_2814499 := by exact prefixLift 2814499
  have htrace : WordTrace (prefixWord ++ tailWord_2814499) baseStart_2814499 baseEnd_2814499 := by
    simpa [prefixWord, tailWord_2814499, baseEnd_2814499] using wordTrace_append hprefix tailTrace_2814499
  have hstable : (prefixWord ++ tailWord_2814499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814499).length < 2 ^ (prefixWord ++ tailWord_2814499).sum := by decide
  have hdescent : baseEnd_2814499 < baseStart_2814499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814561 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 5]
def baseStart_2814561 : Nat := 118140960795 + 2814561 * 2 ^ 59
def prefixEnd_2814561 : Nat := 4983230072969 + 3 ^ 40 * 2814561 * 2
def baseEnd_2814561 : Nat := 321160583199837277965239

theorem tailTrace_2814561 : CollatzResearch.WordTrace tailWord_2814561 prefixEnd_2814561 321160583199837277965239 := by
  unfold tailWord_2814561
  simp only [CollatzResearch.WordTrace]
  refine ⟨102655473156333660594323537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68436982104222440396215691 102655473156333660594323537)
  ·
    refine ⟨76991604867250245445742653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102655473156333660594323537 76991604867250245445742653)
    ·
      refine ⟨28871851825218842042153495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76991604867250245445742653 28871851825218842042153495)
      ·
        refine ⟨43307777737828263063230243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28871851825218842042153495 43307777737828263063230243)
        ·
          refine ⟨64961666606742394594845365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43307777737828263063230243 64961666606742394594845365)
          ·
            refine ⟨6090156244382099493266753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64961666606742394594845365 6090156244382099493266753)
            ·
              refine ⟨4567617183286574619950065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6090156244382099493266753 4567617183286574619950065)
              ·
                refine ⟨3425712887464930964962549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4567617183286574619950065 3425712887464930964962549)
                ·
                  refine ⟨321160583199837277965239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3425712887464930964962549 321160583199837277965239)
                  ·
                    rfl

theorem cell22_2814561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_2814561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814561 prefixEnd_2814561 := by exact prefixLift 2814561
  have htrace : WordTrace (prefixWord ++ tailWord_2814561) baseStart_2814561 baseEnd_2814561 := by
    simpa [prefixWord, tailWord_2814561, baseEnd_2814561] using wordTrace_append hprefix tailTrace_2814561
  have hstable : (prefixWord ++ tailWord_2814561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814561).length < 2 ^ (prefixWord ++ tailWord_2814561).sum := by decide
  have hdescent : baseEnd_2814561 < baseStart_2814561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814565 : List Nat := [1, 3, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_2814565 : Nat := 118140960795 + 2814565 * 2 ^ 59
def prefixEnd_2814565 : Nat := 4983230072969 + 3 ^ 40 * 2814565 * 2
def baseEnd_2814565 : Nat := 963483118881257156795705

theorem tailTrace_2814565 : CollatzResearch.WordTrace tailWord_2814565 prefixEnd_2814565 963483118881257156795705 := by
  unfold tailWord_2814565
  simp only [CollatzResearch.WordTrace]
  refine ⟨102655619048319169277469149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68437079365546112851646099 102655619048319169277469149)
  ·
    refine ⟨38495857143119688479050931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102655619048319169277469149 38495857143119688479050931)
    ·
      refine ⟨57743785714679532718576397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38495857143119688479050931 57743785714679532718576397)
      ·
        refine ⟨21653919643004824769466149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57743785714679532718576397 21653919643004824769466149)
        ·
          refine ⟨4060109933063404644274903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21653919643004824769466149 4060109933063404644274903)
          ·
            refine ⟨6090164899595106966412355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060109933063404644274903 6090164899595106966412355)
            ·
              refine ⟨9135247349392660449618533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090164899595106966412355 9135247349392660449618533)
              ·
                refine ⟨1712858878011123834303475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9135247349392660449618533 1712858878011123834303475)
                ·
                  refine ⟨2569288317016685751455213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1712858878011123834303475 2569288317016685751455213)
                  ·
                    refine ⟨963483118881257156795705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569288317016685751455213 963483118881257156795705)
                    ·
                      rfl

theorem cell22_2814565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_2814565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814565 prefixEnd_2814565 := by exact prefixLift 2814565
  have htrace : WordTrace (prefixWord ++ tailWord_2814565) baseStart_2814565 baseEnd_2814565 := by
    simpa [prefixWord, tailWord_2814565, baseEnd_2814565] using wordTrace_append hprefix tailTrace_2814565
  have hstable : (prefixWord ++ tailWord_2814565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814565).length < 2 ^ (prefixWord ++ tailWord_2814565).sum := by decide
  have hdescent : baseEnd_2814565 < baseStart_2814565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814576 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_2814576 : Nat := 118140960795 + 2814576 * 2 ^ 59
def prefixEnd_2814576 : Nat := 4983230072969 + 3 ^ 40 * 2814576 * 2
def baseEnd_2814576 : Nat := 963486884406056794770671

theorem tailTrace_2814576 : CollatzResearch.WordTrace tailWord_2814576 prefixEnd_2814576 963486884406056794770671 := by
  unfold tailWord_2814576
  simp only [CollatzResearch.WordTrace]
  refine ⟨51328010125639659078059791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68437346834186212104079721 51328010125639659078059791)
  ·
    refine ⟨76992015188459488617089687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51328010125639659078059791 76992015188459488617089687)
    ·
      refine ⟨115488022782689232925634531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76992015188459488617089687 115488022782689232925634531)
      ·
        refine ⟨173232034174033849388451797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115488022782689232925634531 173232034174033849388451797)
        ·
          refine ⟨4060125800953918345041839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173232034174033849388451797 4060125800953918345041839)
          ·
            refine ⟨6090188701430877517562759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060125800953918345041839 6090188701430877517562759)
            ·
              refine ⟨9135283052146316276344139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090188701430877517562759 9135283052146316276344139)
              ·
                refine ⟨13702924578219474414516209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9135283052146316276344139 13702924578219474414516209)
                ·
                  refine ⟨10277193433664605810887157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13702924578219474414516209 10277193433664605810887157)
                  ·
                    refine ⟨963486884406056794770671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10277193433664605810887157 963486884406056794770671)
                    ·
                      rfl

theorem cell22_2814576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_2814576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814576 prefixEnd_2814576 := by exact prefixLift 2814576
  have htrace : WordTrace (prefixWord ++ tailWord_2814576) baseStart_2814576 baseEnd_2814576 := by
    simpa [prefixWord, tailWord_2814576, baseEnd_2814576] using wordTrace_append hprefix tailTrace_2814576
  have hstable : (prefixWord ++ tailWord_2814576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814576).length < 2 ^ (prefixWord ++ tailWord_2814576).sum := by decide
  have hdescent : baseEnd_2814576 < baseStart_2814576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814604 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_2814604 : Nat := 118140960795 + 2814604 * 2 ^ 59
def prefixEnd_2814604 : Nat := 4983230072969 + 3 ^ 40 * 2814604 * 2
def baseEnd_2814604 : Nat := 963496469378274055070585

theorem tailTrace_2814604 : CollatzResearch.WordTrace tailWord_2814604 prefixEnd_2814604 963496469378274055070585 := by
  unfold tailWord_2814604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51328520747588939469069433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68438027663451919292092577 51328520747588939469069433)
  ·
    refine ⟨38496390560691704601802075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51328520747588939469069433 38496390560691704601802075)
    ·
      refine ⟨57744585841037556902703113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38496390560691704601802075 57744585841037556902703113)
      ·
        refine ⟨43308439380778167677027335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57744585841037556902703113 43308439380778167677027335)
        ·
          refine ⟨64962659071167251515541003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43308439380778167677027335 64962659071167251515541003)
          ·
            refine ⟨97443988606750877273311505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64962659071167251515541003 97443988606750877273311505)
            ·
              refine ⟨73082991455063157954983629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97443988606750877273311505 73082991455063157954983629)
              ·
                refine ⟨27406121795648684233118861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73082991455063157954983629 27406121795648684233118861)
                ·
                  refine ⟨10277295673368256587419573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27406121795648684233118861 10277295673368256587419573)
                  ·
                    refine ⟨963496469378274055070585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10277295673368256587419573 963496469378274055070585)
                    ·
                      rfl

theorem cell22_2814604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_2814604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814604 prefixEnd_2814604 := by exact prefixLift 2814604
  have htrace : WordTrace (prefixWord ++ tailWord_2814604) baseStart_2814604 baseEnd_2814604 := by
    simpa [prefixWord, tailWord_2814604, baseEnd_2814604] using wordTrace_append hprefix tailTrace_2814604
  have hstable : (prefixWord ++ tailWord_2814604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814604).length < 2 ^ (prefixWord ++ tailWord_2814604).sum := by decide
  have hdescent : baseEnd_2814604 < baseStart_2814604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814619 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 8, 4]
def baseStart_2814619 : Nat := 118140960795 + 2814619 * 2 ^ 59
def prefixEnd_2814619 : Nat := 4983230072969 + 3 ^ 40 * 2814619 * 2
def baseEnd_2814619 : Nat := 963501604184819015945539

theorem tailTrace_2814619 : CollatzResearch.WordTrace tailWord_2814619 prefixEnd_2814619 963501604184819015945539 := by
  unfold tailWord_2814619
  simp only [CollatzResearch.WordTrace]
  refine ⟨102657588590123536499934911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68438392393415690999956607 102657588590123536499934911)
  ·
    refine ⟨153986382885185304749902367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102657588590123536499934911 153986382885185304749902367)
    ·
      refine ⟨230979574327777957124853551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153986382885185304749902367 230979574327777957124853551)
      ·
        refine ⟨346469361491666935687280327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230979574327777957124853551 346469361491666935687280327)
        ·
          refine ⟨519704042237500403530920491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346469361491666935687280327 519704042237500403530920491)
          ·
            refine ⟨779556063356250605296380737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519704042237500403530920491 779556063356250605296380737)
            ·
              refine ⟨584667047517187953972285553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779556063356250605296380737 584667047517187953972285553)
              ·
                refine ⟨438500285637890965479214165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584667047517187953972285553 438500285637890965479214165)
                ·
                  refine ⟨5138675222319034751709541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 438500285637890965479214165 5138675222319034751709541)
                  ·
                    refine ⟨963501604184819015945539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5138675222319034751709541 963501604184819015945539)
                    ·
                      rfl

theorem cell22_2814619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 4].length) (baseStart_2814619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814619 prefixEnd_2814619 := by exact prefixLift 2814619
  have htrace : WordTrace (prefixWord ++ tailWord_2814619) baseStart_2814619 baseEnd_2814619 := by
    simpa [prefixWord, tailWord_2814619, baseEnd_2814619] using wordTrace_append hprefix tailTrace_2814619
  have hstable : (prefixWord ++ tailWord_2814619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814619).length < 2 ^ (prefixWord ++ tailWord_2814619).sum := by decide
  have hdescent : baseEnd_2814619 < baseStart_2814619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814649 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_2814649 : Nat := 118140960795 + 2814649 * 2 ^ 59
def prefixEnd_2814649 : Nat := 4983230072969 + 3 ^ 40 * 2814649 * 2
def baseEnd_2814649 : Nat := 963511873797908937695447

theorem tailTrace_2814649 : CollatzResearch.WordTrace tailWord_2814649 prefixEnd_2814649 963511873797908937695447 := by
  unfold tailWord_2814649
  simp only [CollatzResearch.WordTrace]
  refine ⟨102658682780014851623527001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68439121853343234415684667 102658682780014851623527001)
  ·
    refine ⟨76994012085011138717645251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102658682780014851623527001 76994012085011138717645251)
    ·
      refine ⟨115491018127516708076467877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76994012085011138717645251 115491018127516708076467877)
      ·
        refine ⟨21654565898909382764337727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115491018127516708076467877 21654565898909382764337727)
        ·
          refine ⟨32481848848364074146506591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21654565898909382764337727 32481848848364074146506591)
          ·
            refine ⟨48722773272546111219759887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32481848848364074146506591 48722773272546111219759887)
            ·
              refine ⟨73084159908819166829639831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48722773272546111219759887 73084159908819166829639831)
              ·
                refine ⟨109626239863228750244459747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73084159908819166829639831 109626239863228750244459747)
                ·
                  refine ⟨164439359794843125366689621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109626239863228750244459747 164439359794843125366689621)
                  ·
                    refine ⟨963511873797908937695447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 164439359794843125366689621 963511873797908937695447)
                    ·
                      rfl

theorem cell22_2814649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_2814649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814649 prefixEnd_2814649 := by exact prefixLift 2814649
  have htrace : WordTrace (prefixWord ++ tailWord_2814649) baseStart_2814649 baseEnd_2814649 := by
    simpa [prefixWord, tailWord_2814649, baseEnd_2814649] using wordTrace_append hprefix tailTrace_2814649
  have hstable : (prefixWord ++ tailWord_2814649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814649).length < 2 ^ (prefixWord ++ tailWord_2814649).sum := by decide
  have hdescent : baseEnd_2814649 < baseStart_2814649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814741 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 6]
def baseStart_2814741 : Nat := 118140960795 + 2814741 * 2 ^ 59
def prefixEnd_2814741 : Nat := 4983230072969 + 3 ^ 40 * 2814741 * 2
def baseEnd_2814741 : Nat := 321181122426017121465055

theorem tailTrace_2814741 : CollatzResearch.WordTrace tailWord_2814741 prefixEnd_2814741 321181122426017121465055 := by
  unfold tailWord_2814741
  simp only [CollatzResearch.WordTrace]
  refine ⟨102662038295681551335876077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68441358863787700890584051 102662038295681551335876077)
  ·
    refine ⟨38498264360880581750953529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102662038295681551335876077 38498264360880581750953529)
    ·
      refine ⟨28873698270660436313215147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38498264360880581750953529 28873698270660436313215147)
      ·
        refine ⟨43310547405990654469822721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28873698270660436313215147 43310547405990654469822721)
        ·
          refine ⟨32482910554492990852367041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43310547405990654469822721 32482910554492990852367041)
          ·
            refine ⟨24362182915869743139275281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32482910554492990852367041 24362182915869743139275281)
            ·
              refine ⟨18271637186902307354456461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24362182915869743139275281 18271637186902307354456461)
              ·
                refine ⟨6851863945088365257921173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18271637186902307354456461 6851863945088365257921173)
                ·
                  refine ⟨321181122426017121465055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6851863945088365257921173 321181122426017121465055)
                  ·
                    rfl

theorem cell22_2814741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_2814741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814741 prefixEnd_2814741 := by exact prefixLift 2814741
  have htrace : WordTrace (prefixWord ++ tailWord_2814741) baseStart_2814741 baseEnd_2814741 := by
    simpa [prefixWord, tailWord_2814741, baseEnd_2814741] using wordTrace_append hprefix tailTrace_2814741
  have hstable : (prefixWord ++ tailWord_2814741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814741).length < 2 ^ (prefixWord ++ tailWord_2814741).sum := by decide
  have hdescent : baseEnd_2814741 < baseStart_2814741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814773 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2814773 : Nat := 118140960795 + 2814773 * 2 ^ 59
def prefixEnd_2814773 : Nat := 4983230072969 + 3 ^ 40 * 2814773 * 2
def baseEnd_2814773 : Nat := 963554321532013947595067

theorem tailTrace_2814773 : CollatzResearch.WordTrace tailWord_2814773 prefixEnd_2814773 963554321532013947595067 := by
  unfold tailWord_2814773
  simp only [CollatzResearch.WordTrace]
  refine ⟨102663205431565620801040973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68442136954377080534027315 102663205431565620801040973)
  ·
    refine ⟨38498702036837107800390365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102663205431565620801040973 38498702036837107800390365)
    ·
      refine ⟨14437013263813915425146387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38498702036837107800390365 14437013263813915425146387)
      ·
        refine ⟨21655519895720873137719581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14437013263813915425146387 21655519895720873137719581)
        ·
          refine ⟨8120819960895327426644843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21655519895720873137719581 8120819960895327426644843)
          ·
            refine ⟨12181229941342991139967265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8120819960895327426644843 12181229941342991139967265)
            ·
              refine ⟨9135922456007243354975449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12181229941342991139967265 9135922456007243354975449)
              ·
                refine ⟨6851941842005432516231587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9135922456007243354975449 6851941842005432516231587)
                ·
                  refine ⟨10277912763008148774347381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6851941842005432516231587 10277912763008148774347381)
                  ·
                    refine ⟨963554321532013947595067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10277912763008148774347381 963554321532013947595067)
                    ·
                      rfl

theorem cell22_2814773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2814773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814773 prefixEnd_2814773 := by exact prefixLift 2814773
  have htrace : WordTrace (prefixWord ++ tailWord_2814773) baseStart_2814773 baseEnd_2814773 := by
    simpa [prefixWord, tailWord_2814773, baseEnd_2814773] using wordTrace_append hprefix tailTrace_2814773
  have hstable : (prefixWord ++ tailWord_2814773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814773).length < 2 ^ (prefixWord ++ tailWord_2814773).sum := by decide
  have hdescent : baseEnd_2814773 < baseStart_2814773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814807 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 2, 3]
def baseStart_2814807 : Nat := 118140960795 + 2814807 * 2 ^ 59
def prefixEnd_2814807 : Nat := 4983230072969 + 3 ^ 40 * 2814807 * 2
def baseEnd_2814807 : Nat := 963565960426849192244963

theorem tailTrace_2814807 : CollatzResearch.WordTrace tailWord_2814807 prefixEnd_2814807 963565960426849192244963 := by
  unfold tailWord_2814807
  simp only [CollatzResearch.WordTrace]
  refine ⟨102664445513442444607778675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68442963675628296405185783 102664445513442444607778675)
  ·
    refine ⟨153996668270163666911668013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102664445513442444607778675 153996668270163666911668013)
    ·
      refine ⟨57748750601311375091875505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153996668270163666911668013 57748750601311375091875505)
      ·
        refine ⟨43311562950983531318906629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57748750601311375091875505 43311562950983531318906629)
        ·
          refine ⟨8120918053309412122294993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43311562950983531318906629 8120918053309412122294993)
          ·
            refine ⟨6090688539982059091721245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8120918053309412122294993 6090688539982059091721245)
            ·
              refine ⟨2284008202493272159395467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6090688539982059091721245 2284008202493272159395467)
              ·
                refine ⟨3426012303739908239093201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284008202493272159395467 3426012303739908239093201)
                ·
                  refine ⟨2569509227804931179319901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426012303739908239093201 2569509227804931179319901)
                  ·
                    refine ⟨963565960426849192244963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569509227804931179319901 963565960426849192244963)
                    ·
                      rfl

theorem cell22_2814807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_2814807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814807 prefixEnd_2814807 := by exact prefixLift 2814807
  have htrace : WordTrace (prefixWord ++ tailWord_2814807) baseStart_2814807 baseEnd_2814807 := by
    simpa [prefixWord, tailWord_2814807, baseEnd_2814807] using wordTrace_append hprefix tailTrace_2814807
  have hstable : (prefixWord ++ tailWord_2814807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814807).length < 2 ^ (prefixWord ++ tailWord_2814807).sum := by decide
  have hdescent : baseEnd_2814807 < baseStart_2814807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814820 : List Nat := [2, 3, 1, 1, 4, 3, 2, 6]
def baseStart_2814820 : Nat := 118140960795 + 2814820 * 2 ^ 59
def prefixEnd_2814820 : Nat := 4983230072969 + 3 ^ 40 * 2814820 * 2
def baseEnd_2814820 : Nat := 107063378954724610185547

theorem tailTrace_2814820 : CollatzResearch.WordTrace tailWord_2814820 prefixEnd_2814820 107063378954724610185547 := by
  unfold tailWord_2814820
  simp only [CollatzResearch.WordTrace]
  refine ⟨51332459831197673914000957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68443279774930231885334609 51332459831197673914000957)
  ·
    refine ⟨19249672436699127717750359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51332459831197673914000957 19249672436699127717750359)
    ·
      refine ⟨28874508655048691576625539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19249672436699127717750359 28874508655048691576625539)
      ·
        refine ⟨43311762982573037364938309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28874508655048691576625539 43311762982573037364938309)
        ·
          refine ⟨8120955559232444505925933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43311762982573037364938309 8120955559232444505925933)
          ·
            refine ⟨3045358334712166689722225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8120955559232444505925933 3045358334712166689722225)
            ·
              refine ⟨2284018751034125017291669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3045358334712166689722225 2284018751034125017291669)
              ·
                refine ⟨107063378954724610185547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2284018751034125017291669 107063378954724610185547)
                ·
                  rfl

theorem cell22_2814820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 6].length) (baseStart_2814820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814820 prefixEnd_2814820 := by exact prefixLift 2814820
  have htrace : WordTrace (prefixWord ++ tailWord_2814820) baseStart_2814820 baseEnd_2814820 := by
    simpa [prefixWord, tailWord_2814820, baseEnd_2814820] using wordTrace_append hprefix tailTrace_2814820
  have hstable : (prefixWord ++ tailWord_2814820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814820).length < 2 ^ (prefixWord ++ tailWord_2814820).sum := by decide
  have hdescent : baseEnd_2814820 < baseStart_2814820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2814946 : List Nat := [3, 3, 3, 1, 1, 3, 2, 1, 1, 4]
def baseStart_2814946 : Nat := 118140960795 + 2814946 * 2 ^ 59
def prefixEnd_2814946 : Nat := 4983230072969 + 3 ^ 40 * 2814946 * 2
def baseEnd_2814946 : Nat := 963613542967499163019537

theorem tailTrace_2814946 : CollatzResearch.WordTrace tailWord_2814946 prefixEnd_2814946 963613542967499163019537 := by
  unfold tailWord_2814946
  simp only [CollatzResearch.WordTrace]
  refine ⟨25667378814984717836772173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68446343506625914231392461 25667378814984717836772173)
  ·
    refine ⟨9625267055619269188789565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25667378814984717836772173 9625267055619269188789565)
    ·
      refine ⟨3609475145857225945796087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9625267055619269188789565 3609475145857225945796087)
      ·
        refine ⟨5414212718785838918694131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3609475145857225945796087 5414212718785838918694131)
        ·
          refine ⟨8121319078178758378041197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414212718785838918694131 8121319078178758378041197)
          ·
            refine ⟨3045494654317034391765449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8121319078178758378041197 3045494654317034391765449)
            ·
              refine ⟨2284120990737775793824087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3045494654317034391765449 2284120990737775793824087)
              ·
                refine ⟨3426181486106663690736131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284120990737775793824087 3426181486106663690736131)
                ·
                  refine ⟨5139272229159995536104197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426181486106663690736131 5139272229159995536104197)
                  ·
                    refine ⟨963613542967499163019537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139272229159995536104197 963613542967499163019537)
                    ·
                      rfl

theorem cell22_2814946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_2814946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2814946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2814946 prefixEnd_2814946 := by exact prefixLift 2814946
  have htrace : WordTrace (prefixWord ++ tailWord_2814946) baseStart_2814946 baseEnd_2814946 := by
    simpa [prefixWord, tailWord_2814946, baseEnd_2814946] using wordTrace_append hprefix tailTrace_2814946
  have hstable : (prefixWord ++ tailWord_2814946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2814946).length < 2 ^ (prefixWord ++ tailWord_2814946).sum := by decide
  have hdescent : baseEnd_2814946 < baseStart_2814946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2814946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815047 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 1, 4]
def baseStart_2815047 : Nat := 118140960795 + 2815047 * 2 ^ 59
def prefixEnd_2815047 : Nat := 4983230072969 + 3 ^ 40 * 2815047 * 2
def baseEnd_2815047 : Nat := 963648117331568566244227

theorem tailTrace_2815047 : CollatzResearch.WordTrace tailWord_2815047 prefixEnd_2815047 963648117331568566244227 := by
  unfold tailWord_2815047
  simp only [CollatzResearch.WordTrace]
  refine ⟨102673199032572965596515395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68448799355048643731010263 102673199032572965596515395)
  ·
    refine ⟨154009798548859448394773093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102673199032572965596515395 154009798548859448394773093)
    ·
      refine ⟨28876837227911146574019955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154009798548859448394773093 28876837227911146574019955)
      ·
        refine ⟨43315255841866719861029933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28876837227911146574019955 43315255841866719861029933)
        ·
          refine ⟨16243220940700019947886225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43315255841866719861029933 16243220940700019947886225)
          ·
            refine ⟨12182415705525014960914669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16243220940700019947886225 12182415705525014960914669)
            ·
              refine ⟨4568405889571880610343001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12182415705525014960914669 4568405889571880610343001)
              ·
                refine ⟨3426304417178910457757251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568405889571880610343001 3426304417178910457757251)
                ·
                  refine ⟨5139456625768365686635877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426304417178910457757251 5139456625768365686635877)
                  ·
                    refine ⟨963648117331568566244227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139456625768365686635877 963648117331568566244227)
                    ·
                      rfl

theorem cell22_2815047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_2815047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815047 prefixEnd_2815047 := by exact prefixLift 2815047
  have htrace : WordTrace (prefixWord ++ tailWord_2815047) baseStart_2815047 baseEnd_2815047 := by
    simpa [prefixWord, tailWord_2815047, baseEnd_2815047] using wordTrace_append hprefix tailTrace_2815047
  have hstable : (prefixWord ++ tailWord_2815047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815047).length < 2 ^ (prefixWord ++ tailWord_2815047).sum := by decide
  have hdescent : baseEnd_2815047 < baseStart_2815047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815060 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2815060 : Nat := 118140960795 + 2815060 * 2 ^ 59
def prefixEnd_2815060 : Nat := 4983230072969 + 3 ^ 40 * 2815060 * 2
def baseEnd_2815060 : Nat := 963652567497240865669187

theorem tailTrace_2815060 : CollatzResearch.WordTrace tailWord_2815060 prefixEnd_2815060 963652567497240865669187 := by
  unfold tailWord_2815060
  simp only [CollatzResearch.WordTrace]
  refine ⟨51336836590762934408369317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68449115454350579211159089 51336836590762934408369317)
  ·
    refine ⟨9625656860768050201569247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51336836590762934408369317 9625656860768050201569247)
    ·
      refine ⟨14438485291152075302353871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9625656860768050201569247 14438485291152075302353871)
      ·
        refine ⟨21657727936728112953530807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14438485291152075302353871 21657727936728112953530807)
        ·
          refine ⟨32486591905092169430296211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21657727936728112953530807 32486591905092169430296211)
          ·
            refine ⟨48729887857638254145444317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32486591905092169430296211 48729887857638254145444317)
            ·
              refine ⟨18273707946614345304541619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48729887857638254145444317 18273707946614345304541619)
              ·
                refine ⟨27410561919921517956812429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18273707946614345304541619 27410561919921517956812429)
                ·
                  refine ⟨10278960719970569233804661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27410561919921517956812429 10278960719970569233804661)
                  ·
                    refine ⟨963652567497240865669187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10278960719970569233804661 963652567497240865669187)
                    ·
                      rfl

theorem cell22_2815060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2815060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815060 prefixEnd_2815060 := by exact prefixLift 2815060
  have htrace : WordTrace (prefixWord ++ tailWord_2815060) baseStart_2815060 baseEnd_2815060 := by
    simpa [prefixWord, tailWord_2815060, baseEnd_2815060] using wordTrace_append hprefix tailTrace_2815060
  have hstable : (prefixWord ++ tailWord_2815060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815060).length < 2 ^ (prefixWord ++ tailWord_2815060).sum := by decide
  have hdescent : baseEnd_2815060 < baseStart_2815060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815079 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 4]
def baseStart_2815079 : Nat := 118140960795 + 2815079 * 2 ^ 59
def prefixEnd_2815079 : Nat := 4983230072969 + 3 ^ 40 * 2815079 * 2
def baseEnd_2815079 : Nat := 321219690528510383148043

theorem tailTrace_2815079 : CollatzResearch.WordTrace tailWord_2815079 prefixEnd_2815079 321219690528510383148043 := by
  unfold tailWord_2815079
  simp only [CollatzResearch.WordTrace]
  refine ⟨102674366168457035061680291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68449577445638023374453527 102674366168457035061680291)
  ·
    refine ⟨154011549252685552592520437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102674366168457035061680291 154011549252685552592520437)
    ·
      refine ⟨14438582742439270555548791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154011549252685552592520437 14438582742439270555548791)
      ·
        refine ⟨21657874113658905833323187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14438582742439270555548791 21657874113658905833323187)
        ·
          refine ⟨32486811170488358749984781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21657874113658905833323187 32486811170488358749984781)
          ·
            refine ⟨12182554188933134531244293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32486811170488358749984781 12182554188933134531244293)
            ·
              refine ⟨2284228910424962724608305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12182554188933134531244293 2284228910424962724608305)
              ·
                refine ⟨1713171682818722043456229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284228910424962724608305 1713171682818722043456229)
                ·
                  refine ⟨321219690528510383148043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713171682818722043456229 321219690528510383148043)
                  ·
                    rfl

theorem cell22_2815079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 4].length) (baseStart_2815079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815079 prefixEnd_2815079 := by exact prefixLift 2815079
  have htrace : WordTrace (prefixWord ++ tailWord_2815079) baseStart_2815079 baseEnd_2815079 := by
    simpa [prefixWord, tailWord_2815079, baseEnd_2815079] using wordTrace_append hprefix tailTrace_2815079
  have hstable : (prefixWord ++ tailWord_2815079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815079).length < 2 ^ (prefixWord ++ tailWord_2815079).sum := by decide
  have hdescent : baseEnd_2815079 < baseStart_2815079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815094 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2815094 : Nat := 118140960795 + 2815094 * 2 ^ 59
def prefixEnd_2815094 : Nat := 4983230072969 + 3 ^ 40 * 2815094 * 2
def baseEnd_2815094 : Nat := 963664206392076110319083

theorem tailTrace_2815094 : CollatzResearch.WordTrace tailWord_2815094 prefixEnd_2815094 963664206392076110319083 := by
  unfold tailWord_2815094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417182078962668288967271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68449942175601795082317557 6417182078962668288967271)
  ·
    refine ⟨9625773118444002433450907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6417182078962668288967271 9625773118444002433450907)
    ·
      refine ⟨14438659677666003650176361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9625773118444002433450907 14438659677666003650176361)
      ·
        refine ⟨10828994758249502737632271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14438659677666003650176361 10828994758249502737632271)
        ·
          refine ⟨16243492137374254106448407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10828994758249502737632271 16243492137374254106448407)
          ·
            refine ⟨24365238206061381159672611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16243492137374254106448407 24365238206061381159672611)
            ·
              refine ⟨36547857309092071739508917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24365238206061381159672611 36547857309092071739508917)
              ·
                refine ⟨3426361622727381725578961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36547857309092071739508917 3426361622727381725578961)
                ·
                  refine ⟨2569771217045536294184221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426361622727381725578961 2569771217045536294184221)
                  ·
                    refine ⟨963664206392076110319083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569771217045536294184221 963664206392076110319083)
                    ·
                      rfl

theorem cell22_2815094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2815094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815094 prefixEnd_2815094 := by exact prefixLift 2815094
  have htrace : WordTrace (prefixWord ++ tailWord_2815094) baseStart_2815094 baseEnd_2815094 := by
    simpa [prefixWord, tailWord_2815094, baseEnd_2815094] using wordTrace_append hprefix tailTrace_2815094
  have hstable : (prefixWord ++ tailWord_2815094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815094).length < 2 ^ (prefixWord ++ tailWord_2815094).sum := by decide
  have hdescent : baseEnd_2815094 < baseStart_2815094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815109 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_2815109 : Nat := 118140960795 + 2815109 * 2 ^ 59
def prefixEnd_2815109 : Nat := 4983230072969 + 3 ^ 40 * 2815109 * 2
def baseEnd_2815109 : Nat := 963669341198621071194037

theorem tailTrace_2815109 : CollatzResearch.WordTrace tailWord_2815109 prefixEnd_2815109 963669341198621071194037 := by
  unfold tailWord_2815109
  simp only [CollatzResearch.WordTrace]
  refine ⟨102675460358348350185272381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68450306905565566790181587 102675460358348350185272381)
  ·
    refine ⟨38503297634380631319477143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102675460358348350185272381 38503297634380631319477143)
    ·
      refine ⟨57754946451570946979215715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38503297634380631319477143 57754946451570946979215715)
      ·
        refine ⟨86632419677356420468823573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57754946451570946979215715 86632419677356420468823573)
        ·
          refine ⟨4060894672376082209476105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86632419677356420468823573 4060894672376082209476105)
          ·
            refine ⟨3045671004282061657107079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060894672376082209476105 3045671004282061657107079)
            ·
              refine ⟨4568506506423092485660619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045671004282061657107079 4568506506423092485660619)
              ·
                refine ⟨6852759759634638728490929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568506506423092485660619 6852759759634638728490929)
                ·
                  refine ⟨5139569819725979046368197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6852759759634638728490929 5139569819725979046368197)
                  ·
                    refine ⟨963669341198621071194037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139569819725979046368197 963669341198621071194037)
                    ·
                      rfl

theorem cell22_2815109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_2815109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815109 prefixEnd_2815109 := by exact prefixLift 2815109
  have htrace : WordTrace (prefixWord ++ tailWord_2815109) baseStart_2815109 baseEnd_2815109 := by
    simpa [prefixWord, tailWord_2815109, baseEnd_2815109] using wordTrace_append hprefix tailTrace_2815109
  have hstable : (prefixWord ++ tailWord_2815109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815109).length < 2 ^ (prefixWord ++ tailWord_2815109).sum := by decide
  have hdescent : baseEnd_2815109 < baseStart_2815109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815158 : List Nat := [5, 1, 3, 2, 1, 2, 2, 6]
def baseStart_2815158 : Nat := 118140960795 + 2815158 * 2 ^ 59
def prefixEnd_2815158 : Nat := 4983230072969 + 3 ^ 40 * 2815158 * 2
def baseEnd_2815158 : Nat := 107076234988889030746543

theorem tailTrace_2815158 : CollatzResearch.WordTrace tailWord_2815158 prefixEnd_2815158 107076234988889030746543 := by
  unfold tailWord_2815158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417327970948176972112883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68451498356780554369204085 6417327970948176972112883)
  ·
    refine ⟨9625991956422265458169325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6417327970948176972112883 9625991956422265458169325)
    ·
      refine ⟨3609746983658349546813497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9625991956422265458169325 3609746983658349546813497)
      ·
        refine ⟨2707310237743762160110123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3609746983658349546813497 2707310237743762160110123)
        ·
          refine ⟨4060965356615643240165185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707310237743762160110123 4060965356615643240165185)
          ·
            refine ⟨3045724017461732430123889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4060965356615643240165185 3045724017461732430123889)
            ·
              refine ⟨2284293013096299322592917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3045724017461732430123889 2284293013096299322592917)
              ·
                refine ⟨107076234988889030746543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2284293013096299322592917 107076234988889030746543)
                ·
                  rfl

theorem cell22_2815158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_2815158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815158 prefixEnd_2815158 := by exact prefixLift 2815158
  have htrace : WordTrace (prefixWord ++ tailWord_2815158) baseStart_2815158 baseEnd_2815158 := by
    simpa [prefixWord, tailWord_2815158, baseEnd_2815158] using wordTrace_append hprefix tailTrace_2815158
  have hstable : (prefixWord ++ tailWord_2815158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815158).length < 2 ^ (prefixWord ++ tailWord_2815158).sum := by decide
  have hdescent : baseEnd_2815158 < baseStart_2815158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815190 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2815190 : Nat := 118140960795 + 2815190 * 2 ^ 59
def prefixEnd_2815190 : Nat := 4983230072969 + 3 ^ 40 * 2815190 * 2
def baseEnd_2815190 : Nat := 963697069153963859918789

theorem tailTrace_2815190 : CollatzResearch.WordTrace tailWord_2815190 prefixEnd_2815190 963697069153963859918789 := by
  unfold tailWord_2815190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417400916940931313685689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68452276447369934012647349 6417400916940931313685689)
  ·
    refine ⟨4813050687705698485264267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6417400916940931313685689 4813050687705698485264267)
    ·
      refine ⟨7219576031558547727896401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4813050687705698485264267 7219576031558547727896401)
      ·
        refine ⟨5414682023668910795922301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7219576031558547727896401 5414682023668910795922301)
        ·
          refine ⟨2030505758875841548470863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5414682023668910795922301 2030505758875841548470863)
          ·
            refine ⟨3045758638313762322706295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030505758875841548470863 3045758638313762322706295)
            ·
              refine ⟨4568637957470643484059443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045758638313762322706295 4568637957470643484059443)
              ·
                refine ⟨6852956936205965226089165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568637957470643484059443 6852956936205965226089165)
                ·
                  refine ⟨2569858851077236959783437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6852956936205965226089165 2569858851077236959783437)
                  ·
                    refine ⟨963697069153963859918789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569858851077236959783437 963697069153963859918789)
                    ·
                      rfl

theorem cell22_2815190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2815190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815190 prefixEnd_2815190 := by exact prefixLift 2815190
  have htrace : WordTrace (prefixWord ++ tailWord_2815190) baseStart_2815190 baseEnd_2815190 := by
    simpa [prefixWord, tailWord_2815190, baseEnd_2815190] using wordTrace_append hprefix tailTrace_2815190
  have hstable : (prefixWord ++ tailWord_2815190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815190).length < 2 ^ (prefixWord ++ tailWord_2815190).sum := by decide
  have hdescent : baseEnd_2815190 < baseStart_2815190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815225 : List Nat := [1, 2, 1, 3, 1, 1, 3, 10]
def baseStart_2815225 : Nat := 118140960795 + 2815225 * 2 ^ 59
def prefixEnd_2815225 : Nat := 4983230072969 + 3 ^ 40 * 2815225 * 2
def baseEnd_2815225 : Nat := 107078783374359492810409

theorem tailTrace_2815225 : CollatzResearch.WordTrace tailWord_2815225 prefixEnd_2815225 107078783374359492810409 := by
  unfold tailWord_2815225
  simp only [CollatzResearch.WordTrace]
  refine ⟨102679691225928101996495129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68453127483952067997663419 102679691225928101996495129)
  ·
    refine ⟨77009768419446076497371347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102679691225928101996495129 77009768419446076497371347)
    ·
      refine ⟨115514652629169114746057021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77009768419446076497371347 115514652629169114746057021)
      ·
        refine ⟨43317994735938418029771383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115514652629169114746057021 43317994735938418029771383)
        ·
          refine ⟨64976992103907627044657075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43317994735938418029771383 64976992103907627044657075)
          ·
            refine ⟨97465488155861440566985613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64976992103907627044657075 97465488155861440566985613)
            ·
              refine ⟨36549558058448040212619605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97465488155861440566985613 36549558058448040212619605)
              ·
                refine ⟨107078783374359492810409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36549558058448040212619605 107078783374359492810409)
                ·
                  rfl

theorem cell22_2815225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 10].length) (baseStart_2815225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815225 prefixEnd_2815225 := by exact prefixLift 2815225
  have htrace : WordTrace (prefixWord ++ tailWord_2815225) baseStart_2815225 baseEnd_2815225 := by
    simpa [prefixWord, tailWord_2815225, baseEnd_2815225] using wordTrace_append hprefix tailTrace_2815225
  have hstable : (prefixWord ++ tailWord_2815225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815225).length < 2 ^ (prefixWord ++ tailWord_2815225).sum := by decide
  have hdescent : baseEnd_2815225 < baseStart_2815225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815246 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_2815246 : Nat := 118140960795 + 2815246 * 2 ^ 59
def prefixEnd_2815246 : Nat := 4983230072969 + 3 ^ 40 * 2815246 * 2
def baseEnd_2815246 : Nat := 963716239098398380518617

theorem tailTrace_2815246 : CollatzResearch.WordTrace tailWord_2815246 prefixEnd_2815246 963716239098398380518617 := by
  unfold tailWord_2815246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835057144856502822876199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68453638105901348388673061 12835057144856502822876199)
  ·
    refine ⟨19252585717284754234314299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12835057144856502822876199 19252585717284754234314299)
    ·
      refine ⟨28878878575927131351471449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19252585717284754234314299 28878878575927131351471449)
      ·
        refine ⟨21659158931945348513603587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28878878575927131351471449 21659158931945348513603587)
        ·
          refine ⟨32488738397918022770405381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21659158931945348513603587 32488738397918022770405381)
          ·
            refine ⟨6091638449609629269451009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32488738397918022770405381 6091638449609629269451009)
            ·
              refine ⟨4568728837207221952088257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6091638449609629269451009 4568728837207221952088257)
              ·
                refine ⟨3426546627905416464066193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4568728837207221952088257 3426546627905416464066193)
                ·
                  refine ⟨2569909970929062348049645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3426546627905416464066193 2569909970929062348049645)
                  ·
                    refine ⟨963716239098398380518617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569909970929062348049645 963716239098398380518617)
                    ·
                      rfl

theorem cell22_2815246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_2815246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815246 prefixEnd_2815246 := by exact prefixLift 2815246
  have htrace : WordTrace (prefixWord ++ tailWord_2815246) baseStart_2815246 baseEnd_2815246 := by
    simpa [prefixWord, tailWord_2815246, baseEnd_2815246] using wordTrace_append hprefix tailTrace_2815246
  have hstable : (prefixWord ++ tailWord_2815246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815246).length < 2 ^ (prefixWord ++ tailWord_2815246).sum := by decide
  have hdescent : baseEnd_2815246 < baseStart_2815246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815257 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_2815257 : Nat := 118140960795 + 2815257 * 2 ^ 59
def prefixEnd_2815257 : Nat := 4983230072969 + 3 ^ 40 * 2815257 * 2
def baseEnd_2815257 : Nat := 963720004623198018493583

theorem tailTrace_2815257 : CollatzResearch.WordTrace tailWord_2815257 prefixEnd_2815257 963720004623198018493583 := by
  unfold tailWord_2815257
  simp only [CollatzResearch.WordTrace]
  refine ⟨102680858361812171461660025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68453905574541447641106683 102680858361812171461660025)
  ·
    refine ⟨77010643771359128596245019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102680858361812171461660025 77010643771359128596245019)
    ·
      refine ⟨115515965657038692894367529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77010643771359128596245019 115515965657038692894367529)
      ·
        refine ⟨86636974242779019670775647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115515965657038692894367529 86636974242779019670775647)
        ·
          refine ⟨129955461364168529506163471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86636974242779019670775647 129955461364168529506163471)
          ·
            refine ⟨194933192046252794259245207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129955461364168529506163471 194933192046252794259245207)
            ·
              refine ⟨292399788069379191388867811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194933192046252794259245207 292399788069379191388867811)
              ·
                refine ⟨438599682104068787083301717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292399788069379191388867811 438599682104068787083301717)
                ·
                  refine ⟨2569920012328528049316221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 438599682104068787083301717 2569920012328528049316221)
                  ·
                    refine ⟨963720004623198018493583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569920012328528049316221 963720004623198018493583)
                    ·
                      rfl

theorem cell22_2815257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_2815257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815257 prefixEnd_2815257 := by exact prefixLift 2815257
  have htrace : WordTrace (prefixWord ++ tailWord_2815257) baseStart_2815257 baseEnd_2815257 := by
    simpa [prefixWord, tailWord_2815257, baseEnd_2815257] using wordTrace_append hprefix tailTrace_2815257
  have hstable : (prefixWord ++ tailWord_2815257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815257).length < 2 ^ (prefixWord ++ tailWord_2815257).sum := by decide
  have hdescent : baseEnd_2815257 < baseStart_2815257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815342 : List Nat := [4, 1, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2815342 : Nat := 118140960795 + 2815342 * 2 ^ 59
def prefixEnd_2815342 : Nat := 4983230072969 + 3 ^ 40 * 2815342 * 2
def baseEnd_2815342 : Nat := 963749101860286130118323

theorem tailTrace_2815342 : CollatzResearch.WordTrace tailWord_2815342 prefixEnd_2815342 963749101860286130118323 := by
  unfold tailWord_2815342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12835494820813028872313035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68455972377669487319002853 12835494820813028872313035)
  ·
    refine ⟨19253242231219543308469553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12835494820813028872313035 19253242231219543308469553)
    ·
      refine ⟨14439931673414657481352165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19253242231219543308469553 14439931673414657481352165)
      ·
        refine ⟨2707487188765248277753531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14439931673414657481352165 2707487188765248277753531)
        ·
          refine ⟨4061230783147872416630297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707487188765248277753531 4061230783147872416630297)
          ·
            refine ⟨3045923087360904312472723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4061230783147872416630297 3045923087360904312472723)
            ·
              refine ⟨4568884631041356468709085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3045923087360904312472723 4568884631041356468709085)
              ·
                refine ⟨1713331736640508675765907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4568884631041356468709085 1713331736640508675765907)
                ·
                  refine ⟨2569997604960763013648861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713331736640508675765907 2569997604960763013648861)
                  ·
                    refine ⟨963749101860286130118323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2569997604960763013648861 963749101860286130118323)
                    ·
                      rfl

theorem cell22_2815342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2815342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815342 prefixEnd_2815342 := by exact prefixLift 2815342
  have htrace : WordTrace (prefixWord ++ tailWord_2815342) baseStart_2815342 baseEnd_2815342 := by
    simpa [prefixWord, tailWord_2815342, baseEnd_2815342] using wordTrace_append hprefix tailTrace_2815342
  have hstable : (prefixWord ++ tailWord_2815342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815342).length < 2 ^ (prefixWord ++ tailWord_2815342).sum := by decide
  have hdescent : baseEnd_2815342 < baseStart_2815342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815394 : List Nat := [3, 3, 1, 2, 1, 2, 2, 8]
def baseStart_2815394 : Nat := 118140960795 + 2815394 * 2 ^ 59
def prefixEnd_2815394 : Nat := 4983230072969 + 3 ^ 40 * 2815394 * 2
def baseEnd_2815394 : Nat := 107085211391441703090907

theorem tailTrace_2815394 : CollatzResearch.WordTrace tailWord_2815394 prefixEnd_2815394 107085211391441703090907 := by
  unfold tailWord_2815394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25671463790578960964849309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68457236774877229239598157 25671463790578960964849309)
  ·
    refine ⟨9626798921467110361818491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25671463790578960964849309 9626798921467110361818491)
    ·
      refine ⟨14440198382200665542727737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9626798921467110361818491 14440198382200665542727737)
      ·
        refine ⟨10830148786650499157045803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14440198382200665542727737 10830148786650499157045803)
        ·
          refine ⟨16245223179975748735568705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10830148786650499157045803 16245223179975748735568705)
          ·
            refine ⟨12183917384981811551676529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16245223179975748735568705 12183917384981811551676529)
            ·
              refine ⟨9137938038736358663757397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12183917384981811551676529 9137938038736358663757397)
              ·
                refine ⟨107085211391441703090907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9137938038736358663757397 107085211391441703090907)
                ·
                  rfl

theorem cell22_2815394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_2815394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815394 prefixEnd_2815394 := by exact prefixLift 2815394
  have htrace : WordTrace (prefixWord ++ tailWord_2815394) baseStart_2815394 baseEnd_2815394 := by
    simpa [prefixWord, tailWord_2815394, baseEnd_2815394] using wordTrace_append hprefix tailTrace_2815394
  have hstable : (prefixWord ++ tailWord_2815394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815394).length < 2 ^ (prefixWord ++ tailWord_2815394).sum := by decide
  have hdescent : baseEnd_2815394 < baseStart_2815394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815407 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 4, 6]
def baseStart_2815407 : Nat := 118140960795 + 2815407 * 2 ^ 59
def prefixEnd_2815407 : Nat := 4983230072969 + 3 ^ 40 * 2815407 * 2
def baseEnd_2815407 : Nat := 963771352688647627243123

theorem tailTrace_2815407 : CollatzResearch.WordTrace tailWord_2815407 prefixEnd_2815407 963771352688647627243123 := by
  unfold tailWord_2815407
  simp only [CollatzResearch.WordTrace]
  refine ⟨102686329311268747079620475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68457552874179164719746983 102686329311268747079620475)
  ·
    refine ⟨154029493966903120619430713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102686329311268747079620475 154029493966903120619430713)
    ·
      refine ⟨115522120475177340464573035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154029493966903120619430713 115522120475177340464573035)
      ·
        refine ⟨173283180712766010696859553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115522120475177340464573035 173283180712766010696859553)
        ·
          refine ⟨129962385534574508022644665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173283180712766010696859553 129962385534574508022644665)
          ·
            refine ⟨97471789150930881016983499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129962385534574508022644665 97471789150930881016983499)
            ·
              refine ⟨146207683726396321525475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97471789150930881016983499 146207683726396321525475249)
              ·
                refine ⟨109655762794797241144106437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146207683726396321525475249 109655762794797241144106437)
                ·
                  refine ⟨20560455524024482714519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109655762794797241144106437 20560455524024482714519957)
                  ·
                    refine ⟨963771352688647627243123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20560455524024482714519957 963771352688647627243123)
                    ·
                      rfl

theorem cell22_2815407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_2815407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815407 prefixEnd_2815407 := by exact prefixLift 2815407
  have htrace : WordTrace (prefixWord ++ tailWord_2815407) baseStart_2815407 baseEnd_2815407 := by
    simpa [prefixWord, tailWord_2815407, baseEnd_2815407] using wordTrace_append hprefix tailTrace_2815407
  have hstable : (prefixWord ++ tailWord_2815407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815407).length < 2 ^ (prefixWord ++ tailWord_2815407).sum := by decide
  have hdescent : baseEnd_2815407 < baseStart_2815407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815439 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 5]
def baseStart_2815439 : Nat := 118140960795 + 2815439 * 2 ^ 59
def prefixEnd_2815439 : Nat := 4983230072969 + 3 ^ 40 * 2815439 * 2
def baseEnd_2815439 : Nat := 321260768980870070147675

theorem tailTrace_2815439 : CollatzResearch.WordTrace tailWord_2815439 prefixEnd_2815439 321260768980870070147675 := by
  unfold tailWord_2815439
  simp only [CollatzResearch.WordTrace]
  refine ⟨102687496447152816544785371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68458330964768544363190247 102687496447152816544785371)
  ·
    refine ⟨154031244670729224817178057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102687496447152816544785371 154031244670729224817178057)
    ·
      refine ⟨115523433503046918612883543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154031244670729224817178057 115523433503046918612883543)
      ·
        refine ⟨173285150254570377919325315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115523433503046918612883543 173285150254570377919325315)
        ·
          refine ⟨259927725381855566878987973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173285150254570377919325315 259927725381855566878987973)
          ·
            refine ⟨48736448509097918789810245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259927725381855566878987973 48736448509097918789810245)
            ·
              refine ⟨9138084095455859773089421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48736448509097918789810245 9138084095455859773089421)
              ·
                refine ⟨3426781535795947414908533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9138084095455859773089421 3426781535795947414908533)
                ·
                  refine ⟨321260768980870070147675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3426781535795947414908533 321260768980870070147675)
                  ·
                    rfl

theorem cell22_2815439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 5].length) (baseStart_2815439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815439 prefixEnd_2815439 := by exact prefixLift 2815439
  have htrace : WordTrace (prefixWord ++ tailWord_2815439) baseStart_2815439 baseEnd_2815439 := by
    simpa [prefixWord, tailWord_2815439, baseEnd_2815439] using wordTrace_append hprefix tailTrace_2815439
  have hstable : (prefixWord ++ tailWord_2815439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815439).length < 2 ^ (prefixWord ++ tailWord_2815439).sum := by decide
  have hdescent : baseEnd_2815439 < baseStart_2815439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815484 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 6]
def baseStart_2815484 : Nat := 118140960795 + 2815484 * 2 ^ 59
def prefixEnd_2815484 : Nat := 4983230072969 + 3 ^ 40 * 2815484 * 2
def baseEnd_2815484 : Nat := 321265903787415031022629

theorem tailTrace_2815484 : CollatzResearch.WordTrace tailWord_2815484 prefixEnd_2815484 321265903787415031022629 := by
  unfold tailWord_2815484
  simp only [CollatzResearch.WordTrace]
  refine ⟨51344568865994894615086753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68459425154659859486782337 51344568865994894615086753)
  ·
    refine ⟨38508426649496170961315065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51344568865994894615086753 38508426649496170961315065)
    ·
      refine ⟨28881319987122128220986299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38508426649496170961315065 28881319987122128220986299)
      ·
        refine ⟨43321979980683192331479449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28881319987122128220986299 43321979980683192331479449)
        ·
          refine ⟨32491484985512394248609587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43321979980683192331479449 32491484985512394248609587)
          ·
            refine ⟨48737227478268591372914381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32491484985512394248609587 48737227478268591372914381)
            ·
              refine ⟨18276460304350721764842893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48737227478268591372914381 18276460304350721764842893)
              ·
                refine ⟨6853672614131520661816085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18276460304350721764842893 6853672614131520661816085)
                ·
                  refine ⟨321265903787415031022629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6853672614131520661816085 321265903787415031022629)
                  ·
                    rfl

theorem cell22_2815484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_2815484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815484 prefixEnd_2815484 := by exact prefixLift 2815484
  have htrace : WordTrace (prefixWord ++ tailWord_2815484) baseStart_2815484 baseEnd_2815484 := by
    simpa [prefixWord, tailWord_2815484, baseEnd_2815484] using wordTrace_append hprefix tailTrace_2815484
  have hstable : (prefixWord ++ tailWord_2815484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815484).length < 2 ^ (prefixWord ++ tailWord_2815484).sum := by decide
  have hdescent : baseEnd_2815484 < baseStart_2815484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815490 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2815490 : Nat := 118140960795 + 2815490 * 2 ^ 59
def prefixEnd_2815490 : Nat := 4983230072969 + 3 ^ 40 * 2815490 * 2
def baseEnd_2815490 : Nat := 321266588428287692472623

theorem tailTrace_2815490 : CollatzResearch.WordTrace tailWord_2815490 prefixEnd_2815490 321266588428287692472623 := by
  unfold tailWord_2815490
  simp only [CollatzResearch.WordTrace]
  refine ⟨25672339142492013063722981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68459571046645368169927949 25672339142492013063722981)
  ·
    refine ⟨4813563589217252449448059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25672339142492013063722981 4813563589217252449448059)
    ·
      refine ⟨7220345383825878674172089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4813563589217252449448059 7220345383825878674172089)
      ·
        refine ⟨5415259037869409005629067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7220345383825878674172089 5415259037869409005629067)
        ·
          refine ⟨8122888556804113508443601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415259037869409005629067 8122888556804113508443601)
          ·
            refine ⟨6092166417603085131332701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8122888556804113508443601 6092166417603085131332701)
            ·
              refine ⟨2284562406601156924249763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6092166417603085131332701 2284562406601156924249763)
              ·
                refine ⟨3426843609901735386374645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2284562406601156924249763 3426843609901735386374645)
                ·
                  refine ⟨321266588428287692472623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3426843609901735386374645 321266588428287692472623)
                  ·
                    rfl

theorem cell22_2815490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2815490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815490 prefixEnd_2815490 := by exact prefixLift 2815490
  have htrace : WordTrace (prefixWord ++ tailWord_2815490) baseStart_2815490 baseEnd_2815490 := by
    simpa [prefixWord, tailWord_2815490, baseEnd_2815490] using wordTrace_append hprefix tailTrace_2815490
  have hstable : (prefixWord ++ tailWord_2815490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815490).length < 2 ^ (prefixWord ++ tailWord_2815490).sum := by decide
  have hdescent : baseEnd_2815490 < baseStart_2815490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815516 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_2815516 : Nat := 118140960795 + 2815516 * 2 ^ 59
def prefixEnd_2815516 : Nat := 4983230072969 + 3 ^ 40 * 2815516 * 2
def baseEnd_2815516 : Nat := 963808665616207676267789

theorem tailTrace_2815516 : CollatzResearch.WordTrace tailWord_2815516 prefixEnd_2815516 963808665616207676267789 := by
  unfold tailWord_2815516
  simp only [CollatzResearch.WordTrace]
  refine ⟨51345152433936929347669201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68460203245249239130225601 51345152433936929347669201)
  ·
    refine ⟨38508864325452697010751901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51345152433936929347669201 38508864325452697010751901)
    ·
      refine ⟨14440824122044761379031963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38508864325452697010751901 14440824122044761379031963)
      ·
        refine ⟨21661236183067142068547945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14440824122044761379031963 21661236183067142068547945)
        ·
          refine ⟨16245927137300356551410959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21661236183067142068547945 16245927137300356551410959)
          ·
            refine ⟨24368890705950534827116439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16245927137300356551410959 24368890705950534827116439)
            ·
              refine ⟨36553336058925802240674659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24368890705950534827116439 36553336058925802240674659)
              ·
                refine ⟨54830004088388703361011989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36553336058925802240674659 54830004088388703361011989)
                ·
                  refine ⟨2570156441643220470047437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54830004088388703361011989 2570156441643220470047437)
                  ·
                    refine ⟨963808665616207676267789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570156441643220470047437 963808665616207676267789)
                    ·
                      rfl

theorem cell22_2815516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_2815516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815516 prefixEnd_2815516 := by exact prefixLift 2815516
  have htrace : WordTrace (prefixWord ++ tailWord_2815516) baseStart_2815516 baseEnd_2815516 := by
    simpa [prefixWord, tailWord_2815516, baseEnd_2815516] using wordTrace_append hprefix tailTrace_2815516
  have hstable : (prefixWord ++ tailWord_2815516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815516).length < 2 ^ (prefixWord ++ tailWord_2815516).sum := by decide
  have hdescent : baseEnd_2815516 < baseStart_2815516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815561 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_2815561 : Nat := 118140960795 + 2815561 * 2 ^ 59
def prefixEnd_2815561 : Nat := 4983230072969 + 3 ^ 40 * 2815561 * 2
def baseEnd_2815561 : Nat := 963824070035842558892651

theorem tailTrace_2815561 : CollatzResearch.WordTrace tailWord_2815561 prefixEnd_2815561 963824070035842558892651 := by
  unfold tailWord_2815561
  simp only [CollatzResearch.WordTrace]
  refine ⟨102691946152710831380726537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68461297435140554253817691 102691946152710831380726537)
  ·
    refine ⟨77018959614533123535544903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102691946152710831380726537 77018959614533123535544903)
    ·
      refine ⟨115528439421799685303317355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77018959614533123535544903 115528439421799685303317355)
      ·
        refine ⟨173292659132699527954976033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115528439421799685303317355 173292659132699527954976033)
        ·
          refine ⟨129969494349524645966232025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173292659132699527954976033 129969494349524645966232025)
          ·
            refine ⟨97477120762143484474674019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129969494349524645966232025 97477120762143484474674019)
            ·
              refine ⟨146215681143215226712011029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97477120762143484474674019 146215681143215226712011029)
              ·
                refine ⟨6853860053588213752125517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146215681143215226712011029 6853860053588213752125517)
                ·
                  refine ⟨2570197520095580157047069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6853860053588213752125517 2570197520095580157047069)
                  ·
                    refine ⟨963824070035842558892651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570197520095580157047069 963824070035842558892651)
                    ·
                      rfl

theorem cell22_2815561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_2815561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815561 prefixEnd_2815561 := by exact prefixLift 2815561
  have htrace : WordTrace (prefixWord ++ tailWord_2815561) baseStart_2815561 baseEnd_2815561 := by
    simpa [prefixWord, tailWord_2815561, baseEnd_2815561] using wordTrace_append hprefix tailTrace_2815561
  have hstable : (prefixWord ++ tailWord_2815561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815561).length < 2 ^ (prefixWord ++ tailWord_2815561).sum := by decide
  have hdescent : baseEnd_2815561 < baseStart_2815561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815565 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2815565 : Nat := 118140960795 + 2815565 * 2 ^ 59
def prefixEnd_2815565 : Nat := 4983230072969 + 3 ^ 40 * 2815565 * 2
def baseEnd_2815565 : Nat := 963825439317587881792639

theorem tailTrace_2815565 : CollatzResearch.WordTrace tailWord_2815565 prefixEnd_2815565 963825439317587881792639 := by
  unfold tailWord_2815565
  simp only [CollatzResearch.WordTrace]
  refine ⟨102692092044696340063872149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68461394696464226709248099 102692092044696340063872149)
  ·
    refine ⟨4813691814595140940494007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102692092044696340063872149 4813691814595140940494007)
    ·
      refine ⟨7220537721892711410741011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4813691814595140940494007 7220537721892711410741011)
      ·
        refine ⟨10830806582839067116111517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7220537721892711410741011 10830806582839067116111517)
        ·
          refine ⟨4061552468564650168541819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10830806582839067116111517 4061552468564650168541819)
          ·
            refine ⟨6092328702846975252812729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061552468564650168541819 6092328702846975252812729)
            ·
              refine ⟨4569246527135231439609547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6092328702846975252812729 4569246527135231439609547)
              ·
                refine ⟨6853869790702847159414321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4569246527135231439609547 6853869790702847159414321)
                ·
                  refine ⟨5140402343027135369560741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6853869790702847159414321 5140402343027135369560741)
                  ·
                    refine ⟨963825439317587881792639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140402343027135369560741 963825439317587881792639)
                    ·
                      rfl

theorem cell22_2815565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2815565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815565 prefixEnd_2815565 := by exact prefixLift 2815565
  have htrace : WordTrace (prefixWord ++ tailWord_2815565) baseStart_2815565 baseEnd_2815565 := by
    simpa [prefixWord, tailWord_2815565, baseEnd_2815565] using wordTrace_append hprefix tailTrace_2815565
  have hstable : (prefixWord ++ tailWord_2815565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815565).length < 2 ^ (prefixWord ++ tailWord_2815565).sum := by decide
  have hdescent : baseEnd_2815565 < baseStart_2815565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815591 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 5]
def baseStart_2815591 : Nat := 118140960795 + 2815591 * 2 ^ 59
def prefixEnd_2815591 : Nat := 4983230072969 + 3 ^ 40 * 2815591 * 2
def baseEnd_2815591 : Nat := 321278113216310826880853

theorem tailTrace_2815591 : CollatzResearch.WordTrace tailWord_2815591 prefixEnd_2815591 321278113216310826880853 := by
  unfold tailWord_2815591
  simp only [CollatzResearch.WordTrace]
  refine ⟨102693040342602146504318627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68462026895068097669545751 102693040342602146504318627)
  ·
    refine ⟨154039560513903219756477941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102693040342602146504318627 154039560513903219756477941)
    ·
      refine ⟨14441208798178426852169807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154039560513903219756477941 14441208798178426852169807)
      ·
        refine ⟨21661813197267640278254711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14441208798178426852169807 21661813197267640278254711)
        ·
          refine ⟨32492719795901460417382067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21661813197267640278254711 32492719795901460417382067)
          ·
            refine ⟨48739079693852190626073101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32492719795901460417382067 48739079693852190626073101)
            ·
              refine ⟨18277154885194571484777413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48739079693852190626073101 18277154885194571484777413)
              ·
                refine ⟨3426966540973982153395765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18277154885194571484777413 3426966540973982153395765)
                ·
                  refine ⟨321278113216310826880853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3426966540973982153395765 321278113216310826880853)
                  ·
                    rfl

theorem cell22_2815591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 5].length) (baseStart_2815591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815591 prefixEnd_2815591 := by exact prefixLift 2815591
  have htrace : WordTrace (prefixWord ++ tailWord_2815591) baseStart_2815591 baseEnd_2815591 := by
    simpa [prefixWord, tailWord_2815591, baseEnd_2815591] using wordTrace_append hprefix tailTrace_2815591
  have hstable : (prefixWord ++ tailWord_2815591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815591).length < 2 ^ (prefixWord ++ tailWord_2815591).sum := by decide
  have hdescent : baseEnd_2815591 < baseStart_2815591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815621 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2815621 : Nat := 118140960795 + 2815621 * 2 ^ 59
def prefixEnd_2815621 : Nat := 4983230072969 + 3 ^ 40 * 2815621 * 2
def baseEnd_2815621 : Nat := 963844609262022402392467

theorem tailTrace_2815621 : CollatzResearch.WordTrace tailWord_2815621 prefixEnd_2815621 963844609262022402392467 := by
  unfold tailWord_2815621
  simp only [CollatzResearch.WordTrace]
  refine ⟨102694134532493461627910717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68462756354995641085273811 102694134532493461627910717)
  ·
    refine ⟨38510300449685048110466519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102694134532493461627910717 38510300449685048110466519)
    ·
      refine ⟨57765450674527572165699779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38510300449685048110466519 57765450674527572165699779)
      ·
        refine ⟨86648176011791358248549669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57765450674527572165699779 86648176011791358248549669)
        ·
          refine ⟨16246533002210879671603063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86648176011791358248549669 16246533002210879671603063)
          ·
            refine ⟨24369799503316319507404595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16246533002210879671603063 24369799503316319507404595)
            ·
              refine ⟨36554699254974479261106893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24369799503316319507404595 36554699254974479261106893)
              ·
                refine ⟨13708012220615429722915085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36554699254974479261106893 13708012220615429722915085)
                ·
                  refine ⟨5140504582730786146093157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13708012220615429722915085 5140504582730786146093157)
                  ·
                    refine ⟨963844609262022402392467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140504582730786146093157 963844609262022402392467)
                    ·
                      rfl

theorem cell22_2815621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2815621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815621 prefixEnd_2815621 := by exact prefixLift 2815621
  have htrace : WordTrace (prefixWord ++ tailWord_2815621) baseStart_2815621 baseEnd_2815621 := by
    simpa [prefixWord, tailWord_2815621, baseEnd_2815621] using wordTrace_append hprefix tailTrace_2815621
  have hstable : (prefixWord ++ tailWord_2815621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815621).length < 2 ^ (prefixWord ++ tailWord_2815621).sum := by decide
  have hdescent : baseEnd_2815621 < baseStart_2815621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815653 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 4]
def baseStart_2815653 : Nat := 118140960795 + 2815653 * 2 ^ 59
def prefixEnd_2815653 : Nat := 4983230072969 + 3 ^ 40 * 2815653 * 2
def baseEnd_2815653 : Nat := 321285187838661661864123

theorem tailTrace_2815653 : CollatzResearch.WordTrace tailWord_2815653 prefixEnd_2815653 321285187838661661864123 := by
  unfold tailWord_2815653
  simp only [CollatzResearch.WordTrace]
  refine ⟨102695301668377531093075613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68463534445585020728717075 102695301668377531093075613)
  ·
    refine ⟨38510738125641574159903355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102695301668377531093075613 38510738125641574159903355)
    ·
      refine ⟨57766107188462361239855033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38510738125641574159903355 57766107188462361239855033)
      ·
        refine ⟨43324580391346770929891275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57766107188462361239855033 43324580391346770929891275)
        ·
          refine ⟨64986870587020156394836913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43324580391346770929891275 64986870587020156394836913)
          ·
            refine ⟨48740152940265117296127685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64986870587020156394836913 48740152940265117296127685)
            ·
              refine ⟨9138778676299709493023941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48740152940265117296127685 9138778676299709493023941)
              ·
                refine ⟨1713521001806195529941989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9138778676299709493023941 1713521001806195529941989)
                ·
                  refine ⟨321285187838661661864123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713521001806195529941989 321285187838661661864123)
                  ·
                    rfl

theorem cell22_2815653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_2815653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815653 prefixEnd_2815653 := by exact prefixLift 2815653
  have htrace : WordTrace (prefixWord ++ tailWord_2815653) baseStart_2815653 baseEnd_2815653 := by
    simpa [prefixWord, tailWord_2815653, baseEnd_2815653] using wordTrace_append hprefix tailTrace_2815653
  have hstable : (prefixWord ++ tailWord_2815653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815653).length < 2 ^ (prefixWord ++ tailWord_2815653).sum := by decide
  have hdescent : baseEnd_2815653 < baseStart_2815653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815666 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2815666 : Nat := 118140960795 + 2815666 * 2 ^ 59
def prefixEnd_2815666 : Nat := 4983230072969 + 3 ^ 40 * 2815666 * 2
def baseEnd_2815666 : Nat := 963860013681657285017329

theorem tailTrace_2815666 : CollatzResearch.WordTrace tailWord_2815666 prefixEnd_2815666 963860013681657285017329 := by
  unfold tailWord_2815666
  simp only [CollatzResearch.WordTrace]
  refine ⟨25673943954332608578324713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68463850544886956208865901 25673943954332608578324713)
  ·
    refine ⟨19255457965749456433743535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25673943954332608578324713 19255457965749456433743535)
    ·
      refine ⟨28883186948624184650615303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19255457965749456433743535 28883186948624184650615303)
      ·
        refine ⟨43324780422936276975922955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28883186948624184650615303 43324780422936276975922955)
        ·
          refine ⟨64987170634404415463884433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43324780422936276975922955 64987170634404415463884433)
          ·
            refine ⟨48740377975803311597913325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64987170634404415463884433 48740377975803311597913325)
            ·
              refine ⟨18277641740926241849217497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48740377975803311597913325 18277641740926241849217497)
              ·
                refine ⟨13708231305694681386913123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18277641740926241849217497 13708231305694681386913123)
                ·
                  refine ⟨20562346958542022080369685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13708231305694681386913123 20562346958542022080369685)
                  ·
                    refine ⟨963860013681657285017329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20562346958542022080369685 963860013681657285017329)
                    ·
                      rfl

theorem cell22_2815666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2815666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815666 prefixEnd_2815666 := by exact prefixLift 2815666
  have htrace : WordTrace (prefixWord ++ tailWord_2815666) baseStart_2815666 baseEnd_2815666 := by
    simpa [prefixWord, tailWord_2815666, baseEnd_2815666] using wordTrace_append hprefix tailTrace_2815666
  have hstable : (prefixWord ++ tailWord_2815666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815666).length < 2 ^ (prefixWord ++ tailWord_2815666).sum := by decide
  have hdescent : baseEnd_2815666 < baseStart_2815666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815670 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2815670 : Nat := 118140960795 + 2815670 * 2 ^ 59
def prefixEnd_2815670 : Nat := 4983230072969 + 3 ^ 40 * 2815670 * 2
def baseEnd_2815670 : Nat := 321287127654467535972439

theorem tailTrace_2815670 : CollatzResearch.WordTrace tailWord_2815670 prefixEnd_2815670 321287127654467535972439 := by
  unfold tailWord_2815670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418495106832246437277779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68463947806210628664296309 6418495106832246437277779)
  ·
    refine ⟨9627742660248369655916669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6418495106832246437277779 9627742660248369655916669)
    ·
      refine ⟨3610403497593138620968751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9627742660248369655916669 3610403497593138620968751)
      ·
        refine ⟨5415605246389707931453127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3610403497593138620968751 5415605246389707931453127)
        ·
          refine ⟨8123407869584561897179691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415605246389707931453127 8123407869584561897179691)
          ·
            refine ⟨12185111804376842845769537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8123407869584561897179691 12185111804376842845769537)
            ·
              refine ⟨9138833853282632134327153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12185111804376842845769537 9138833853282632134327153)
              ·
                refine ⟨6854125389961974100745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9138833853282632134327153 6854125389961974100745365)
                ·
                  refine ⟨321287127654467535972439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6854125389961974100745365 321287127654467535972439)
                  ·
                    rfl

theorem cell22_2815670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2815670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815670 prefixEnd_2815670 := by exact prefixLift 2815670
  have htrace : WordTrace (prefixWord ++ tailWord_2815670) baseStart_2815670 baseEnd_2815670 := by
    simpa [prefixWord, tailWord_2815670, baseEnd_2815670] using wordTrace_append hprefix tailTrace_2815670
  have hstable : (prefixWord ++ tailWord_2815670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815670).length < 2 ^ (prefixWord ++ tailWord_2815670).sum := by decide
  have hdescent : baseEnd_2815670 < baseStart_2815670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815698 : List Nat := [3, 2, 2, 2, 2, 3, 8]
def baseStart_2815698 : Nat := 118140960795 + 2815698 * 2 ^ 59
def prefixEnd_2815698 : Nat := 4983230072969 + 3 ^ 40 * 2815698 * 2
def baseEnd_2815698 : Nat := 35698924738356291415453

theorem tailTrace_2815698 : CollatzResearch.WordTrace tailWord_2815698 prefixEnd_2815698 35698924738356291415453 := by
  unfold tailWord_2815698
  simp only [CollatzResearch.WordTrace]
  refine ⟨25674235738303625944615937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68464628635476335852309165 25674235738303625944615937)
  ·
    refine ⟨19255676803727719458461953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25674235738303625944615937 19255676803727719458461953)
    ·
      refine ⟨14441757602795789593846465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19255676803727719458461953 14441757602795789593846465)
      ·
        refine ⟨10831318202096842195384849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14441757602795789593846465 10831318202096842195384849)
        ·
          refine ⟨8123488651572631646538637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10831318202096842195384849 8123488651572631646538637)
          ·
            refine ⟨3046308244339736867451989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8123488651572631646538637 3046308244339736867451989)
            ·
              refine ⟨35698924738356291415453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3046308244339736867451989 35698924738356291415453)
              ·
                rfl

theorem cell22_2815698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 8].length) (baseStart_2815698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815698 prefixEnd_2815698 := by exact prefixLift 2815698
  have htrace : WordTrace (prefixWord ++ tailWord_2815698) baseStart_2815698 baseEnd_2815698 := by
    simpa [prefixWord, tailWord_2815698, baseEnd_2815698] using wordTrace_append hprefix tailTrace_2815698
  have hstable : (prefixWord ++ tailWord_2815698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815698).length < 2 ^ (prefixWord ++ tailWord_2815698).sum := by decide
  have hdescent : baseEnd_2815698 < baseStart_2815698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815700 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2815700 : Nat := 118140960795 + 2815700 * 2 ^ 59
def prefixEnd_2815700 : Nat := 4983230072969 + 3 ^ 40 * 2815700 * 2
def baseEnd_2815700 : Nat := 963871652576492529667225

theorem tailTrace_2815700 : CollatzResearch.WordTrace tailWord_2815700 prefixEnd_2815700 963871652576492529667225 := by
  unfold tailWord_2815700
  simp only [CollatzResearch.WordTrace]
  refine ⟨51348507949603629060018277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68464677266138172080024369 51348507949603629060018277)
  ·
    refine ⟨9627845240550680448753427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51348507949603629060018277 9627845240550680448753427)
    ·
      refine ⟨14441767860826020673130141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9627845240550680448753427 14441767860826020673130141)
      ·
        refine ⟨5415662947809757752423803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14441767860826020673130141 5415662947809757752423803)
        ·
          refine ⟨8123494421714636628635705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5415662947809757752423803 8123494421714636628635705)
          ·
            refine ⟨6092620816285977471476779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8123494421714636628635705 6092620816285977471476779)
            ·
              refine ⟨9138931224428966207215169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092620816285977471476779 9138931224428966207215169)
              ·
                refine ⟨6854198418321724655411377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9138931224428966207215169 6854198418321724655411377)
                ·
                  refine ⟨5140648813741293491558533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6854198418321724655411377 5140648813741293491558533)
                  ·
                    refine ⟨963871652576492529667225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140648813741293491558533 963871652576492529667225)
                    ·
                      rfl

theorem cell22_2815700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2815700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815700 prefixEnd_2815700 := by exact prefixLift 2815700
  have htrace : WordTrace (prefixWord ++ tailWord_2815700) baseStart_2815700 baseEnd_2815700 := by
    simpa [prefixWord, tailWord_2815700, baseEnd_2815700] using wordTrace_append hprefix tailTrace_2815700
  have hstable : (prefixWord ++ tailWord_2815700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815700).length < 2 ^ (prefixWord ++ tailWord_2815700).sum := by decide
  have hdescent : baseEnd_2815700 < baseStart_2815700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815711 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 2, 6]
def baseStart_2815711 : Nat := 118140960795 + 2815711 * 2 ^ 59
def prefixEnd_2815711 : Nat := 4983230072969 + 3 ^ 40 * 2815711 * 2
def baseEnd_2815711 : Nat := 963875418101292167642191

theorem tailTrace_2815711 : CollatzResearch.WordTrace tailWord_2815711 prefixEnd_2815711 963875418101292167642191 := by
  unfold tailWord_2815711
  simp only [CollatzResearch.WordTrace]
  refine ⟨102697417102167406998686987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68464944734778271332457991 102697417102167406998686987)
  ·
    refine ⟨154046125653251110498030481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102697417102167406998686987 154046125653251110498030481)
    ·
      refine ⟨115534594239938332873522861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154046125653251110498030481 115534594239938332873522861)
      ·
        refine ⟨43325472839976874827571073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115534594239938332873522861 43325472839976874827571073)
        ·
          refine ⟨32494104629982656120678305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43325472839976874827571073 32494104629982656120678305)
          ·
            refine ⟨24370578472486992090508729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32494104629982656120678305 24370578472486992090508729)
            ·
              refine ⟨18277933854365244067881547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24370578472486992090508729 18277933854365244067881547)
              ·
                refine ⟨27416900781547866101822321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18277933854365244067881547 27416900781547866101822321)
                ·
                  refine ⟨20562675586160899576366741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27416900781547866101822321 20562675586160899576366741)
                  ·
                    refine ⟨963875418101292167642191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20562675586160899576366741 963875418101292167642191)
                    ·
                      rfl

theorem cell22_2815711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_2815711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815711 prefixEnd_2815711 := by exact prefixLift 2815711
  have htrace : WordTrace (prefixWord ++ tailWord_2815711) baseStart_2815711 baseEnd_2815711 := by
    simpa [prefixWord, tailWord_2815711, baseEnd_2815711] using wordTrace_append hprefix tailTrace_2815711
  have hstable : (prefixWord ++ tailWord_2815711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815711).length < 2 ^ (prefixWord ++ tailWord_2815711).sum := by decide
  have hdescent : baseEnd_2815711 < baseStart_2815711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815741 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2815741 : Nat := 118140960795 + 2815741 * 2 ^ 59
def prefixEnd_2815741 : Nat := 4983230072969 + 3 ^ 40 * 2815741 * 2
def baseEnd_2815741 : Nat := 963885687714382089392099

theorem tailTrace_2815741 : CollatzResearch.WordTrace tailWord_2815741 prefixEnd_2815741 963885687714382089392099 := by
  unfold tailWord_2815741
  simp only [CollatzResearch.WordTrace]
  refine ⟨102698511292058722122279077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68465674194705814748186051 102698511292058722122279077)
  ·
    refine ⟨19255970867261010397927327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102698511292058722122279077 19255970867261010397927327)
    ·
      refine ⟨28883956300891515596890991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19255970867261010397927327 28883956300891515596890991)
      ·
        refine ⟨43325934451337273395336487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28883956300891515596890991 43325934451337273395336487)
        ·
          refine ⟨64988901677005910093004731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43325934451337273395336487 64988901677005910093004731)
          ·
            refine ⟨97483352515508865139507097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64988901677005910093004731 97483352515508865139507097)
            ·
              refine ⟨73112514386631648854630323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97483352515508865139507097 73112514386631648854630323)
              ·
                refine ⟨109668771579947473281945485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73112514386631648854630323 109668771579947473281945485)
                ·
                  refine ⟨41125789342480302480729557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109668771579947473281945485 41125789342480302480729557)
                  ·
                    refine ⟨963885687714382089392099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41125789342480302480729557 963885687714382089392099)
                    ·
                      rfl

theorem cell22_2815741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2815741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815741 prefixEnd_2815741 := by exact prefixLift 2815741
  have htrace : WordTrace (prefixWord ++ tailWord_2815741) baseStart_2815741 baseEnd_2815741 := by
    simpa [prefixWord, tailWord_2815741, baseEnd_2815741] using wordTrace_append hprefix tailTrace_2815741
  have hstable : (prefixWord ++ tailWord_2815741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815741).length < 2 ^ (prefixWord ++ tailWord_2815741).sum := by decide
  have hdescent : baseEnd_2815741 < baseStart_2815741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815788 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 6]
def baseStart_2815788 : Nat := 118140960795 + 2815788 * 2 ^ 59
def prefixEnd_2815788 : Nat := 4983230072969 + 3 ^ 40 * 2815788 * 2
def baseEnd_2815788 : Nat := 321300592258296544488985

theorem tailTrace_2815788 : CollatzResearch.WordTrace tailWord_2815788 prefixEnd_2815788 321300592258296544488985 := by
  unfold tailWord_2815788
  simp only [CollatzResearch.WordTrace]
  refine ⟨51350112761444224574620009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68466817015258966099493345 51350112761444224574620009)
  ·
    refine ⟨38512584571083168430965007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51350112761444224574620009 38512584571083168430965007)
    ·
      refine ⟨57768876856624752646447511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38512584571083168430965007 57768876856624752646447511)
      ·
        refine ⟨86653315284937128969671267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57768876856624752646447511 86653315284937128969671267)
        ·
          refine ⟨129979972927405693454506901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86653315284937128969671267 129979972927405693454506901)
          ·
            refine ⟨6092811230972141880680011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129979972927405693454506901 6092811230972141880680011)
            ·
              refine ⟨9139216846458212821020017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6092811230972141880680011 9139216846458212821020017)
              ·
                refine ⟨6854412634843659615765013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9139216846458212821020017 6854412634843659615765013)
                ·
                  refine ⟨321300592258296544488985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6854412634843659615765013 321300592258296544488985)
                  ·
                    rfl

theorem cell22_2815788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_2815788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815788 prefixEnd_2815788 := by exact prefixLift 2815788
  have htrace : WordTrace (prefixWord ++ tailWord_2815788) baseStart_2815788 baseEnd_2815788 := by
    simpa [prefixWord, tailWord_2815788, baseEnd_2815788] using wordTrace_append hprefix tailTrace_2815788
  have hstable : (prefixWord ++ tailWord_2815788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815788).length < 2 ^ (prefixWord ++ tailWord_2815788).sum := by decide
  have hdescent : baseEnd_2815788 < baseStart_2815788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815818 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_2815818 : Nat := 118140960795 + 2815818 * 2 ^ 59
def prefixEnd_2815818 : Nat := 4983230072969 + 3 ^ 40 * 2815818 * 2
def baseEnd_2815818 : Nat := 963912046387979555216863

theorem tailTrace_2815818 : CollatzResearch.WordTrace tailWord_2815818 prefixEnd_2815818 963912046387979555216863 := by
  unfold tailWord_2815818
  simp only [CollatzResearch.WordTrace]
  refine ⟨25675329928194941068208027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68467546475186509515221405 25675329928194941068208027)
  ·
    refine ⟨38512994892292411602312041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25675329928194941068208027 38512994892292411602312041)
    ·
      refine ⟨28884746169219308701734031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38512994892292411602312041 28884746169219308701734031)
      ·
        refine ⟨43327119253828963052601047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28884746169219308701734031 43327119253828963052601047)
        ·
          refine ⟨64990678880743444578901571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43327119253828963052601047 64990678880743444578901571)
          ·
            refine ⟨97486018321115166868352357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64990678880743444578901571 97486018321115166868352357)
            ·
              refine ⟨18278628435209093787816067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97486018321115166868352357 18278628435209093787816067)
              ·
                refine ⟨27417942652813640681724101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18278628435209093787816067 27417942652813640681724101)
                ·
                  refine ⟨5140864247402557627823269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27417942652813640681724101 5140864247402557627823269)
                  ·
                    refine ⟨963912046387979555216863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5140864247402557627823269 963912046387979555216863)
                    ·
                      rfl

theorem cell22_2815818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_2815818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815818 prefixEnd_2815818 := by exact prefixLift 2815818
  have htrace : WordTrace (prefixWord ++ tailWord_2815818) baseStart_2815818 baseEnd_2815818 := by
    simpa [prefixWord, tailWord_2815818, baseEnd_2815818] using wordTrace_append hprefix tailTrace_2815818
  have hstable : (prefixWord ++ tailWord_2815818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815818).length < 2 ^ (prefixWord ++ tailWord_2815818).sum := by decide
  have hdescent : baseEnd_2815818 < baseStart_2815818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815848 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2815848 : Nat := 118140960795 + 2815848 * 2 ^ 59
def prefixEnd_2815848 : Nat := 4983230072969 + 3 ^ 40 * 2815848 * 2
def baseEnd_2815848 : Nat := 963922316001069476966771

theorem tailTrace_2815848 : CollatzResearch.WordTrace tailWord_2815848 prefixEnd_2815848 963922316001069476966771 := by
  unfold tailWord_2815848
  simp only [CollatzResearch.WordTrace]
  refine ⟨51351206951335539698212099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68468275935114052930949465 51351206951335539698212099)
  ·
    refine ⟨77026810427003309547318149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51351206951335539698212099 77026810427003309547318149)
    ·
      refine ⟨14442526955063120540122153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77026810427003309547318149 14442526955063120540122153)
      ·
        refine ⟨10831895216297340405091615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14442526955063120540122153 10831895216297340405091615)
        ·
          refine ⟨16247842824446010607637423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10831895216297340405091615 16247842824446010607637423)
          ·
            refine ⟨24371764236669015911456135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16247842824446010607637423 24371764236669015911456135)
            ·
              refine ⟨36557646355003523867184203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24371764236669015911456135 36557646355003523867184203)
              ·
                refine ⟨54836469532505285800776305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36557646355003523867184203 54836469532505285800776305)
                ·
                  refine ⟨41127352149378964350582229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54836469532505285800776305 41127352149378964350582229)
                  ·
                    refine ⟨963922316001069476966771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41127352149378964350582229 963922316001069476966771)
                    ·
                      rfl

theorem cell22_2815848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2815848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815848 prefixEnd_2815848 := by exact prefixLift 2815848
  have htrace : WordTrace (prefixWord ++ tailWord_2815848) baseStart_2815848 baseEnd_2815848 := by
    simpa [prefixWord, tailWord_2815848, baseEnd_2815848] using wordTrace_append hprefix tailTrace_2815848
  have hstable : (prefixWord ++ tailWord_2815848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815848).length < 2 ^ (prefixWord ++ tailWord_2815848).sum := by decide
  have hdescent : baseEnd_2815848 < baseStart_2815848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815893 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2815893 : Nat := 118140960795 + 2815893 * 2 ^ 59
def prefixEnd_2815893 : Nat := 4983230072969 + 3 ^ 40 * 2815893 * 2
def baseEnd_2815893 : Nat := 963937720420704359591633

theorem tailTrace_2815893 : CollatzResearch.WordTrace tailWord_2815893 prefixEnd_2815893 963937720420704359591633 := by
  unfold tailWord_2815893
  simp only [CollatzResearch.WordTrace]
  refine ⟨102704055187508052081812333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68469370125005368054541555 102704055187508052081812333)
  ·
    refine ⟨38514020695315519530679625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102704055187508052081812333 38514020695315519530679625)
    ·
      refine ⟨28885515521486639648009719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38514020695315519530679625 28885515521486639648009719)
      ·
        refine ⟨43328273282229959472014579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28885515521486639648009719 43328273282229959472014579)
        ·
          refine ⟨64992409923344939208021869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43328273282229959472014579 64992409923344939208021869)
          ·
            refine ⟨24372153721254352203008201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64992409923344939208021869 24372153721254352203008201)
            ·
              refine ⟨18279115290940764152256151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24372153721254352203008201 18279115290940764152256151)
              ·
                refine ⟨27418672936411146228384227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18279115290940764152256151 27418672936411146228384227)
                ·
                  refine ⟨41128009404616719342576341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27418672936411146228384227 41128009404616719342576341)
                  ·
                    refine ⟨963937720420704359591633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41128009404616719342576341 963937720420704359591633)
                    ·
                      rfl

theorem cell22_2815893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2815893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815893 prefixEnd_2815893 := by exact prefixLift 2815893
  have htrace : WordTrace (prefixWord ++ tailWord_2815893) baseStart_2815893 baseEnd_2815893 := by
    simpa [prefixWord, tailWord_2815893, baseEnd_2815893] using wordTrace_append hprefix tailTrace_2815893
  have hstable : (prefixWord ++ tailWord_2815893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815893).length < 2 ^ (prefixWord ++ tailWord_2815893).sum := by decide
  have hdescent : baseEnd_2815893 < baseStart_2815893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815895 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 5]
def baseStart_2815895 : Nat := 118140960795 + 2815895 * 2 ^ 59
def prefixEnd_2815895 : Nat := 4983230072969 + 3 ^ 40 * 2815895 * 2
def baseEnd_2815895 : Nat := 321312801687192340347209

theorem tailTrace_2815895 : CollatzResearch.WordTrace tailWord_2815895 prefixEnd_2815895 321312801687192340347209 := by
  unfold tailWord_2815895
  simp only [CollatzResearch.WordTrace]
  refine ⟨102704128133500806423385139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68469418755667204282256759 102704128133500806423385139)
  ·
    refine ⟨154056192200251209635077709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102704128133500806423385139 154056192200251209635077709)
    ·
      refine ⟨57771072075094203613154141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154056192200251209635077709 57771072075094203613154141)
      ·
        refine ⟨21664152028160326354932803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57771072075094203613154141 21664152028160326354932803)
        ·
          refine ⟨32496228042240489532399205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21664152028160326354932803 32496228042240489532399205)
          ·
            refine ⟨6093042757920091787324851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32496228042240489532399205 6093042757920091787324851)
            ·
              refine ⟨9139564136880137680987277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6093042757920091787324851 9139564136880137680987277)
              ·
                refine ⟨3427336551330051630370229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9139564136880137680987277 3427336551330051630370229)
                ·
                  refine ⟨321312801687192340347209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3427336551330051630370229 321312801687192340347209)
                  ·
                    rfl

theorem cell22_2815895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 5].length) (baseStart_2815895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815895 prefixEnd_2815895 := by exact prefixLift 2815895
  have htrace : WordTrace (prefixWord ++ tailWord_2815895) baseStart_2815895 baseEnd_2815895 := by
    simpa [prefixWord, tailWord_2815895, baseEnd_2815895] using wordTrace_append hprefix tailTrace_2815895
  have hstable : (prefixWord ++ tailWord_2815895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815895).length < 2 ^ (prefixWord ++ tailWord_2815895).sum := by decide
  have hdescent : baseEnd_2815895 < baseStart_2815895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815968 : List Nat := [2, 1, 1, 3, 1, 1, 1, 12]
def baseStart_2815968 : Nat := 118140960795 + 2815968 * 2 ^ 59
def prefixEnd_2815968 : Nat := 4983230072969 + 3 ^ 40 * 2815968 * 2
def baseEnd_2815968 : Nat := 107107043828158795996267

theorem tailTrace_2815968 : CollatzResearch.WordTrace tailWord_2815968 prefixEnd_2815968 107107043828158795996267 := by
  unfold tailWord_2815968
  simp only [CollatzResearch.WordTrace]
  refine ⟨51353395331118169945396279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68471193774824226593861705 51353395331118169945396279)
  ·
    refine ⟨77030092996677254918094419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51353395331118169945396279 77030092996677254918094419)
    ·
      refine ⟨115545139495015882377141629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77030092996677254918094419 115545139495015882377141629)
      ·
        refine ⟨43329427310630955891428111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115545139495015882377141629 43329427310630955891428111)
        ·
          refine ⟨64994140965946433837142167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43329427310630955891428111 64994140965946433837142167)
          ·
            refine ⟨97491211448919650755713251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64994140965946433837142167 97491211448919650755713251)
            ·
              refine ⟨146236817173379476133569877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97491211448919650755713251 146236817173379476133569877)
              ·
                refine ⟨107107043828158795996267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 146236817173379476133569877 107107043828158795996267)
                ·
                  rfl

theorem cell22_2815968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 12].length) (baseStart_2815968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815968 prefixEnd_2815968 := by exact prefixLift 2815968
  have htrace : WordTrace (prefixWord ++ tailWord_2815968) baseStart_2815968 baseEnd_2815968 := by
    simpa [prefixWord, tailWord_2815968, baseEnd_2815968] using wordTrace_append hprefix tailTrace_2815968
  have hstable : (prefixWord ++ tailWord_2815968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815968).length < 2 ^ (prefixWord ++ tailWord_2815968).sum := by decide
  have hdescent : baseEnd_2815968 < baseStart_2815968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2815985 : List Nat := [1, 2, 2, 2, 5, 1, 9]
def baseStart_2815985 : Nat := 118140960795 + 2815985 * 2 ^ 59
def prefixEnd_2815985 : Nat := 4983230072969 + 3 ^ 40 * 2815985 * 2
def baseEnd_2815985 : Nat := 35702563477809140233013

theorem tailTrace_2815985 : CollatzResearch.WordTrace tailWord_2815985 prefixEnd_2815985 35702563477809140233013 := by
  unfold tailWord_2815985
  simp only [CollatzResearch.WordTrace]
  refine ⟨102707410703174751794161409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68471607135449834529440939 102707410703174751794161409)
  ·
    refine ⟨77030558027381063845621057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102707410703174751794161409 77030558027381063845621057)
    ·
      refine ⟨57772918520535797884215793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77030558027381063845621057 57772918520535797884215793)
      ·
        refine ⟨43329688890401848413161845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57772918520535797884215793 43329688890401848413161845)
        ·
          refine ⟨4062158333475173288733923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43329688890401848413161845 4062158333475173288733923)
          ·
            refine ⟨6093237500212759933100885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062158333475173288733923 6093237500212759933100885)
            ·
              refine ⟨35702563477809140233013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6093237500212759933100885 35702563477809140233013)
              ·
                rfl

theorem cell22_2815985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 9].length) (baseStart_2815985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2815985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2815985 prefixEnd_2815985 := by exact prefixLift 2815985
  have htrace : WordTrace (prefixWord ++ tailWord_2815985) baseStart_2815985 baseEnd_2815985 := by
    simpa [prefixWord, tailWord_2815985, baseEnd_2815985] using wordTrace_append hprefix tailTrace_2815985
  have hstable : (prefixWord ++ tailWord_2815985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2815985).length < 2 ^ (prefixWord ++ tailWord_2815985).sum := by decide
  have hdescent : baseEnd_2815985 < baseStart_2815985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2815985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816064 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 5]
def baseStart_2816064 : Nat := 118140960795 + 2816064 * 2 ^ 59
def prefixEnd_2816064 : Nat := 4983230072969 + 3 ^ 40 * 2816064 * 2
def baseEnd_2816064 : Nat := 321332085738438971188703

theorem tailTrace_2816064 : CollatzResearch.WordTrace tailWord_2816064 prefixEnd_2816064 321332085738438971188703 := by
  unfold tailWord_2816064
  simp only [CollatzResearch.WordTrace]
  refine ⟨51355146034944274143143623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68473528046592365524191497 51355146034944274143143623)
  ·
    refine ⟨77032719052416411214715435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51355146034944274143143623 77032719052416411214715435)
    ·
      refine ⟨115549078578624616822073153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77032719052416411214715435 115549078578624616822073153)
      ·
        refine ⟨86661808933968462616554865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115549078578624616822073153 86661808933968462616554865)
        ·
          refine ⟨64996356700476346962416149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86661808933968462616554865 64996356700476346962416149)
          ·
            refine ⟨3046704220334828763863257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64996356700476346962416149 3046704220334828763863257)
            ·
              refine ⟨2285028165251121572897443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3046704220334828763863257 2285028165251121572897443)
              ·
                refine ⟨3427542247876682359346165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285028165251121572897443 3427542247876682359346165)
                ·
                  refine ⟨321332085738438971188703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3427542247876682359346165 321332085738438971188703)
                  ·
                    rfl

theorem cell22_2816064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_2816064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816064 prefixEnd_2816064 := by exact prefixLift 2816064
  have htrace : WordTrace (prefixWord ++ tailWord_2816064) baseStart_2816064 baseEnd_2816064 := by
    simpa [prefixWord, tailWord_2816064, baseEnd_2816064] using wordTrace_append hprefix tailTrace_2816064
  have hstable : (prefixWord ++ tailWord_2816064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816064).length < 2 ^ (prefixWord ++ tailWord_2816064).sum := by decide
  have hdescent : baseEnd_2816064 < baseStart_2816064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816109 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2816109 : Nat := 118140960795 + 2816109 * 2 ^ 59
def prefixEnd_2816109 : Nat := 4983230072969 + 3 ^ 40 * 2816109 * 2
def baseEnd_2816109 : Nat := 321337220544983932063657

theorem tailTrace_2816109 : CollatzResearch.WordTrace tailWord_2816109 prefixEnd_2816109 321337220544983932063657 := by
  unfold tailWord_2816109
  simp only [CollatzResearch.WordTrace]
  refine ⟨102711933354725520971675381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68474622236483680647783587 102711933354725520971675381)
  ·
    refine ⟨9629243752005517591094567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102711933354725520971675381 9629243752005517591094567)
    ·
      refine ⟨14443865628008276386641851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9629243752005517591094567 14443865628008276386641851)
      ·
        refine ⟨21665798442012414579962777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14443865628008276386641851 21665798442012414579962777)
        ·
          refine ⟨16249348831509310934972083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21665798442012414579962777 16249348831509310934972083)
          ·
            refine ⟨24374023247263966402458125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16249348831509310934972083 24374023247263966402458125)
            ·
              refine ⟨9140258717723987400921797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24374023247263966402458125 9140258717723987400921797)
              ·
                refine ⟨1713798509573247637672837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9140258717723987400921797 1713798509573247637672837)
                ·
                  refine ⟨321337220544983932063657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1713798509573247637672837 321337220544983932063657)
                  ·
                    rfl

theorem cell22_2816109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2816109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816109 prefixEnd_2816109 := by exact prefixLift 2816109
  have htrace : WordTrace (prefixWord ++ tailWord_2816109) baseStart_2816109 baseEnd_2816109 := by
    simpa [prefixWord, tailWord_2816109, baseEnd_2816109] using wordTrace_append hprefix tailTrace_2816109
  have hstable : (prefixWord ++ tailWord_2816109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816109).length < 2 ^ (prefixWord ++ tailWord_2816109).sum := by decide
  have hdescent : baseEnd_2816109 < baseStart_2816109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816124 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_2816124 : Nat := 118140960795 + 2816124 * 2 ^ 59
def prefixEnd_2816124 : Nat := 4983230072969 + 3 ^ 40 * 2816124 * 2
def baseEnd_2816124 : Nat := 964016796441496757065925

theorem tailTrace_2816124 : CollatzResearch.WordTrace tailWord_2816124 prefixEnd_2816124 964016796441496757065925 := by
  unfold tailWord_2816124
  simp only [CollatzResearch.WordTrace]
  refine ⟨51356240224835589266735713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68474986966447452355647617 51356240224835589266735713)
  ·
    refine ⟨38517180168626691950051785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51356240224835589266735713 38517180168626691950051785)
    ·
      refine ⟨28887885126470018962538839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38517180168626691950051785 28887885126470018962538839)
      ·
        refine ⟨43331827689705028443808259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28887885126470018962538839 43331827689705028443808259)
        ·
          refine ⟨64997741534557542665712389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43331827689705028443808259 64997741534557542665712389)
          ·
            refine ⟨12187076537729539249821073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64997741534557542665712389 12187076537729539249821073)
            ·
              refine ⟨9140307403297154437365805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12187076537729539249821073 9140307403297154437365805)
              ·
                refine ⟨3427615276236432914012177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9140307403297154437365805 3427615276236432914012177)
                ·
                  refine ⟨2570711457177324685509133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3427615276236432914012177 2570711457177324685509133)
                  ·
                    refine ⟨964016796441496757065925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570711457177324685509133 964016796441496757065925)
                    ·
                      rfl

theorem cell22_2816124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_2816124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816124 prefixEnd_2816124 := by exact prefixLift 2816124
  have htrace : WordTrace (prefixWord ++ tailWord_2816124) baseStart_2816124 baseEnd_2816124 := by
    simpa [prefixWord, tailWord_2816124, baseEnd_2816124] using wordTrace_append hprefix tailTrace_2816124
  have hstable : (prefixWord ++ tailWord_2816124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816124).length < 2 ^ (prefixWord ++ tailWord_2816124).sum := by decide
  have hdescent : baseEnd_2816124 < baseStart_2816124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816137 : List Nat := [1, 2, 1, 1, 4, 2, 5, 6]
def baseStart_2816137 : Nat := 118140960795 + 2816137 * 2 ^ 59
def prefixEnd_2816137 : Nat := 4983230072969 + 3 ^ 40 * 2816137 * 2
def baseEnd_2816137 : Nat := 107113471845241006276765

theorem tailTrace_2816137 : CollatzResearch.WordTrace tailWord_2816137 prefixEnd_2816137 107113471845241006276765 := by
  unfold tailWord_2816137
  simp only [CollatzResearch.WordTrace]
  refine ⟨102712954598624081753694665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68475303065749387835796443 102712954598624081753694665)
  ·
    refine ⟨77034715948968061315270999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102712954598624081753694665 77034715948968061315270999)
    ·
      refine ⟨115552073923452091972906499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77034715948968061315270999 115552073923452091972906499)
      ·
        refine ⟨173328110885178137959359749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115552073923452091972906499 173328110885178137959359749)
        ·
          refine ⟨32499020790970900867379953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173328110885178137959359749 32499020790970900867379953)
          ·
            refine ⟨24374265593228175650534965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32499020790970900867379953 24374265593228175650534965)
            ·
              refine ⟨2285087399365141467237653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24374265593228175650534965 2285087399365141467237653)
              ·
                refine ⟨107113471845241006276765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2285087399365141467237653 107113471845241006276765)
                ·
                  rfl

theorem cell22_2816137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 6].length) (baseStart_2816137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816137 prefixEnd_2816137 := by exact prefixLift 2816137
  have htrace : WordTrace (prefixWord ++ tailWord_2816137) baseStart_2816137 baseEnd_2816137 := by
    simpa [prefixWord, tailWord_2816137, baseEnd_2816137] using wordTrace_append hprefix tailTrace_2816137
  have hstable : (prefixWord ++ tailWord_2816137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816137).length < 2 ^ (prefixWord ++ tailWord_2816137).sum := by decide
  have hdescent : baseEnd_2816137 < baseStart_2816137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816220 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2816220 : Nat := 118140960795 + 2816220 * 2 ^ 59
def prefixEnd_2816220 : Nat := 4983230072969 + 3 ^ 40 * 2816220 * 2
def baseEnd_2816220 : Nat := 964049659203384506665631

theorem tailTrace_2816220 : CollatzResearch.WordTrace tailWord_2816220 prefixEnd_2816220 964049659203384506665631 := by
  unfold tailWord_2816220
  simp only [CollatzResearch.WordTrace]
  refine ⟨51357990928661693464483057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68477321238215591285977409 51357990928661693464483057)
  ·
    refine ⟨38518493196496270098362293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51357990928661693464483057 38518493196496270098362293)
    ·
      refine ⟨3611108737171525321721465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38518493196496270098362293 3611108737171525321721465)
      ·
        refine ⟨2708331552878643991291099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3611108737171525321721465 2708331552878643991291099)
        ·
          refine ⟨4062497329317965986936649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708331552878643991291099 4062497329317965986936649)
          ·
            refine ⟨3046872996988474490202487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4062497329317965986936649 3046872996988474490202487)
            ·
              refine ⟨4570309495482711735303731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046872996988474490202487 4570309495482711735303731)
              ·
                refine ⟨6855464243224067602955597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570309495482711735303731 6855464243224067602955597)
                ·
                  refine ⟨2570799091209025351108349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6855464243224067602955597 2570799091209025351108349)
                  ·
                    refine ⟨964049659203384506665631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570799091209025351108349 964049659203384506665631)
                    ·
                      rfl

theorem cell22_2816220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2816220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816220 prefixEnd_2816220 := by exact prefixLift 2816220
  have htrace : WordTrace (prefixWord ++ tailWord_2816220) baseStart_2816220 baseEnd_2816220 := by
    simpa [prefixWord, tailWord_2816220, baseEnd_2816220] using wordTrace_append hprefix tailTrace_2816220
  have hstable : (prefixWord ++ tailWord_2816220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816220).length < 2 ^ (prefixWord ++ tailWord_2816220).sum := by decide
  have hdescent : baseEnd_2816220 < baseStart_2816220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816246 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2816246 : Nat := 118140960795 + 2816246 * 2 ^ 59
def prefixEnd_2816246 : Nat := 4983230072969 + 3 ^ 40 * 2816246 * 2
def baseEnd_2816246 : Nat := 964058559534729105515551

theorem tailTrace_2816246 : CollatzResearch.WordTrace tailWord_2816246 prefixEnd_2816246 964058559534729105515551 := by
  unfold tailWord_2816246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419808134701824585588287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68477953436819462246275061 6419808134701824585588287)
  ·
    refine ⟨9629712202052736878382431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6419808134701824585588287 9629712202052736878382431)
    ·
      refine ⟨14444568303079105317573647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9629712202052736878382431 14444568303079105317573647)
      ·
        refine ⟨21666852454618657976360471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14444568303079105317573647 21666852454618657976360471)
        ·
          refine ⟨32500278681927986964540707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21666852454618657976360471 32500278681927986964540707)
          ·
            refine ⟨48750418022891980446811061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32500278681927986964540707 48750418022891980446811061)
            ·
              refine ⟨4570351689646123166888537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48750418022891980446811061 4570351689646123166888537)
              ·
                refine ⟨3427763767234592375166403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570351689646123166888537 3427763767234592375166403)
                ·
                  refine ⟨5141645650851888562749605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427763767234592375166403 5141645650851888562749605)
                  ·
                    refine ⟨964058559534729105515551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141645650851888562749605 964058559534729105515551)
                    ·
                      rfl

theorem cell22_2816246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2816246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816246 prefixEnd_2816246 := by exact prefixLift 2816246
  have htrace : WordTrace (prefixWord ++ tailWord_2816246) baseStart_2816246 baseEnd_2816246 := by
    simpa [prefixWord, tailWord_2816246, baseEnd_2816246] using wordTrace_append hprefix tailTrace_2816246
  have hstable : (prefixWord ++ tailWord_2816246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816246).length < 2 ^ (prefixWord ++ tailWord_2816246).sum := by decide
  have hdescent : baseEnd_2816246 < baseStart_2816246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816306 : List Nat := [3, 2, 1, 1, 5, 1, 3, 6]
def baseStart_2816306 : Nat := 118140960795 + 2816306 * 2 ^ 59
def prefixEnd_2816306 : Nat := 4983230072969 + 3 ^ 40 * 2816306 * 2
def baseEnd_2816306 : Nat := 107119899862323216557263

theorem tailTrace_2816306 : CollatzResearch.WordTrace tailWord_2816306 prefixEnd_2816306 107119899862323216557263 := by
  unfold tailWord_2816306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25679779633752955904149193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68479412356674549077731181 25679779633752955904149193)
  ·
    refine ⟨19259834725314716928111895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25679779633752955904149193 19259834725314716928111895)
    ·
      refine ⟨28889752087972075392167843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19259834725314716928111895 28889752087972075392167843)
      ·
        refine ⟨43334628131958113088251765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28889752087972075392167843 43334628131958113088251765)
        ·
          refine ⟨4062621387371073102023603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43334628131958113088251765 4062621387371073102023603)
          ·
            refine ⟨6093932081056609653035405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062621387371073102023603 6093932081056609653035405)
            ·
              refine ⟨2285224530396228619888277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6093932081056609653035405 2285224530396228619888277)
              ·
                refine ⟨107119899862323216557263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2285224530396228619888277 107119899862323216557263)
                ·
                  rfl

theorem cell22_2816306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 6].length) (baseStart_2816306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816306 prefixEnd_2816306 := by exact prefixLift 2816306
  have htrace : WordTrace (prefixWord ++ tailWord_2816306) baseStart_2816306 baseEnd_2816306 := by
    simpa [prefixWord, tailWord_2816306, baseEnd_2816306] using wordTrace_append hprefix tailTrace_2816306
  have hstable : (prefixWord ++ tailWord_2816306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816306).length < 2 ^ (prefixWord ++ tailWord_2816306).sum := by decide
  have hdescent : baseEnd_2816306 < baseStart_2816306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816308 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_2816308 : Nat := 118140960795 + 2816308 * 2 ^ 59
def prefixEnd_2816308 : Nat := 4983230072969 + 3 ^ 40 * 2816308 * 2
def baseEnd_2816308 : Nat := 964079783401781610465361

theorem tailTrace_2816308 : CollatzResearch.WordTrace tailWord_2816308 prefixEnd_2816308 964079783401781610465361 := by
  unfold tailWord_2816308
  simp only [CollatzResearch.WordTrace]
  refine ⟨51359595740502288979084789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68479460987336385305446385 51359595740502288979084789)
  ·
    refine ⟨4814962100672089591789199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51359595740502288979084789 4814962100672089591789199)
    ·
      refine ⟨7222443151008134387683799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814962100672089591789199 7222443151008134387683799)
      ·
        refine ⟨10833664726512201581525699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222443151008134387683799 10833664726512201581525699)
        ·
          refine ⟨16250497089768302372288549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10833664726512201581525699 16250497089768302372288549)
          ·
            refine ⟨3046968204331556694804103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16250497089768302372288549 3046968204331556694804103)
            ·
              refine ⟨4570452306497335042206155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046968204331556694804103 4570452306497335042206155)
              ·
                refine ⟨6855678459746002563309233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570452306497335042206155 6855678459746002563309233)
                ·
                  refine ⟨5141758844809501922481925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6855678459746002563309233 5141758844809501922481925)
                  ·
                    refine ⟨964079783401781610465361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141758844809501922481925 964079783401781610465361)
                    ·
                      rfl

theorem cell22_2816308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_2816308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816308 prefixEnd_2816308 := by exact prefixLift 2816308
  have htrace : WordTrace (prefixWord ++ tailWord_2816308) baseStart_2816308 baseEnd_2816308 := by
    simpa [prefixWord, tailWord_2816308, baseEnd_2816308] using wordTrace_append hprefix tailTrace_2816308
  have hstable : (prefixWord ++ tailWord_2816308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816308).length < 2 ^ (prefixWord ++ tailWord_2816308).sum := by decide
  have hdescent : baseEnd_2816308 < baseStart_2816308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816334 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2816334 : Nat := 118140960795 + 2816334 * 2 ^ 59
def prefixEnd_2816334 : Nat := 4983230072969 + 3 ^ 40 * 2816334 * 2
def baseEnd_2816334 : Nat := 321362894577708736438427

theorem tailTrace_2816334 : CollatzResearch.WordTrace tailWord_2816334 prefixEnd_2816334 321362894577708736438427 := by
  unfold tailWord_2816334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840017472363798049827007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68480093185940256265744037 12840017472363798049827007)
  ·
    refine ⟨19260026208545697074740511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12840017472363798049827007 19260026208545697074740511)
    ·
      refine ⟨28890039312818545612110767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19260026208545697074740511 28890039312818545612110767)
      ·
        refine ⟨43335058969227818418166151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28890039312818545612110767 43335058969227818418166151)
        ·
          refine ⟨65002588453841727627249227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43335058969227818418166151 65002588453841727627249227)
          ·
            refine ⟨97503882680762591440873841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65002588453841727627249227 97503882680762591440873841)
            ·
              refine ⟨73127912010571943580655381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97503882680762591440873841 73127912010571943580655381)
              ·
                refine ⟨3427870875495559855343221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73127912010571943580655381 3427870875495559855343221)
                ·
                  refine ⟨321362894577708736438427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3427870875495559855343221 321362894577708736438427)
                  ·
                    rfl

theorem cell22_2816334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2816334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816334 prefixEnd_2816334 := by exact prefixLift 2816334
  have htrace : WordTrace (prefixWord ++ tailWord_2816334) baseStart_2816334 baseEnd_2816334 := by
    simpa [prefixWord, tailWord_2816334, baseEnd_2816334] using wordTrace_append hprefix tailTrace_2816334
  have hstable : (prefixWord ++ tailWord_2816334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816334).length < 2 ^ (prefixWord ++ tailWord_2816334).sum := by decide
  have hdescent : baseEnd_2816334 < baseStart_2816334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816338 : List Nat := [3, 2, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2816338 : Nat := 118140960795 + 2816338 * 2 ^ 59
def prefixEnd_2816338 : Nat := 4983230072969 + 3 ^ 40 * 2816338 * 2
def baseEnd_2816338 : Nat := 964090053014871532215269

theorem tailTrace_2816338 : CollatzResearch.WordTrace tailWord_2816338 prefixEnd_2816338 964090053014871532215269 := by
  unfold tailWord_2816338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25680071417723973270440417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68480190447263928721174445 25680071417723973270440417)
  ·
    refine ⟨19260053563292979952830313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25680071417723973270440417 19260053563292979952830313)
    ·
      refine ⟨14445040172469734964622735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19260053563292979952830313 14445040172469734964622735)
      ·
        refine ⟨21667560258704602446934103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14445040172469734964622735 21667560258704602446934103)
        ·
          refine ⟨32501340388056903670401155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21667560258704602446934103 32501340388056903670401155)
          ·
            refine ⟨48752010582085355505601733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32501340388056903670401155 48752010582085355505601733)
            ·
              refine ⟨9141001984141004157300325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48752010582085355505601733 9141001984141004157300325)
              ·
                refine ⟨1713937872026438279493811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9141001984141004157300325 1713937872026438279493811)
                ·
                  refine ⟨2570906808039657419240717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1713937872026438279493811 2570906808039657419240717)
                  ·
                    refine ⟨964090053014871532215269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2570906808039657419240717 964090053014871532215269)
                    ·
                      rfl

theorem cell22_2816338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2816338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816338 prefixEnd_2816338 := by exact prefixLift 2816338
  have htrace : WordTrace (prefixWord ++ tailWord_2816338) baseStart_2816338 baseEnd_2816338 := by
    simpa [prefixWord, tailWord_2816338, baseEnd_2816338] using wordTrace_append hprefix tailTrace_2816338
  have hstable : (prefixWord ++ tailWord_2816338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816338).length < 2 ^ (prefixWord ++ tailWord_2816338).sum := by decide
  have hdescent : baseEnd_2816338 < baseStart_2816338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816381 : List Nat := [1, 4, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2816381 : Nat := 118140960795 + 2816381 * 2 ^ 59
def prefixEnd_2816381 : Nat := 4983230072969 + 3 ^ 40 * 2816381 * 2
def baseEnd_2816381 : Nat := 964104772793633753390137

theorem tailTrace_2816381 : CollatzResearch.WordTrace tailWord_2816381 prefixEnd_2816381 964104772793633753390137 := by
  unfold tailWord_2816381
  simp only [CollatzResearch.WordTrace]
  refine ⟨102721854009740111425576997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68481236006493407617051331 102721854009740111425576997)
  ·
    refine ⟨19260347626826270892295687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102721854009740111425576997 19260347626826270892295687)
    ·
      refine ⟨28890521440239406338443531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19260347626826270892295687 28890521440239406338443531)
      ·
        refine ⟨43335782160359109507665297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28890521440239406338443531 43335782160359109507665297)
        ·
          refine ⟨32501836620269332130748973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43335782160359109507665297 32501836620269332130748973)
          ·
            refine ⟨12188188732600999549030865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32501836620269332130748973 12188188732600999549030865)
            ·
              refine ⟨9141141549450749661773149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12188188732600999549030865 9141141549450749661773149)
              ·
                refine ⟨3427928081044031123164931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9141141549450749661773149 3427928081044031123164931)
                ·
                  refine ⟨5141892121566046684747397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3427928081044031123164931 5141892121566046684747397)
                  ·
                    refine ⟨964104772793633753390137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141892121566046684747397 964104772793633753390137)
                    ·
                      rfl

theorem cell22_2816381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2816381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816381 prefixEnd_2816381 := by exact prefixLift 2816381
  have htrace : WordTrace (prefixWord ++ tailWord_2816381) baseStart_2816381 baseEnd_2816381 := by
    simpa [prefixWord, tailWord_2816381, baseEnd_2816381] using wordTrace_append hprefix tailTrace_2816381
  have hstable : (prefixWord ++ tailWord_2816381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816381).length < 2 ^ (prefixWord ++ tailWord_2816381).sum := by decide
  have hdescent : baseEnd_2816381 < baseStart_2816381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816396 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 6]
def baseStart_2816396 : Nat := 118140960795 + 2816396 * 2 ^ 59
def prefixEnd_2816396 : Nat := 4983230072969 + 3 ^ 40 * 2816396 * 2
def baseEnd_2816396 : Nat := 321369969200059571421697

theorem tailTrace_2816396 : CollatzResearch.WordTrace tailWord_2816396 prefixEnd_2816396 321369969200059571421697 := by
  unfold tailWord_2816396
  simp only [CollatzResearch.WordTrace]
  refine ⟨51361200552342884493686521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68481600736457179324915361 51361200552342884493686521)
  ·
    refine ⟨38520900414257163370264891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51361200552342884493686521 38520900414257163370264891)
    ·
      refine ⟨57781350621385745055397337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38520900414257163370264891 57781350621385745055397337)
      ·
        refine ⟨43336012966039308791548003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57781350621385745055397337 43336012966039308791548003)
        ·
          refine ⟨65004019449058963187322005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43336012966039308791548003 65004019449058963187322005)
          ·
            refine ⟨3047063411674638899405719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65004019449058963187322005 3047063411674638899405719)
            ·
              refine ⟨4570595117511958349108579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047063411674638899405719 4570595117511958349108579)
              ·
                refine ⟨6855892676267937523662869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4570595117511958349108579 6855892676267937523662869)
                ·
                  refine ⟨321369969200059571421697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6855892676267937523662869 321369969200059571421697)
                  ·
                    rfl

theorem cell22_2816396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_2816396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816396 prefixEnd_2816396 := by exact prefixLift 2816396
  have htrace : WordTrace (prefixWord ++ tailWord_2816396) baseStart_2816396 baseEnd_2816396 := by
    simpa [prefixWord, tailWord_2816396, baseEnd_2816396] using wordTrace_append hprefix tailTrace_2816396
  have hstable : (prefixWord ++ tailWord_2816396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816396).length < 2 ^ (prefixWord ++ tailWord_2816396).sum := by decide
  have hdescent : baseEnd_2816396 < baseStart_2816396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816409 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_2816409 : Nat := 118140960795 + 2816409 * 2 ^ 59
def prefixEnd_2816409 : Nat := 4983230072969 + 3 ^ 40 * 2816409 * 2
def baseEnd_2816409 : Nat := 964114357765851013690051

theorem tailTrace_2816409 : CollatzResearch.WordTrace tailWord_2816409 prefixEnd_2816409 964114357765851013690051 := by
  unfold tailWord_2816409
  simp only [CollatzResearch.WordTrace]
  refine ⟨102722875253638672207596281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68481916835759114805064187 102722875253638672207596281)
  ·
    refine ⟨77042156440229004155697211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102722875253638672207596281 77042156440229004155697211)
    ·
      refine ⟨115563234660343506233545817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77042156440229004155697211 115563234660343506233545817)
      ·
        refine ⟨86672425995257629675159363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115563234660343506233545817 86672425995257629675159363)
        ·
          refine ⟨130008638992886444512739045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86672425995257629675159363 130008638992886444512739045)
          ·
            refine ⟨24376619811166208346138571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130008638992886444512739045 24376619811166208346138571)
            ·
              refine ⟨36564929716749312519207857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24376619811166208346138571 36564929716749312519207857)
              ·
                refine ⟨27423697287561984389405893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36564929716749312519207857 27423697287561984389405893)
                ·
                  refine ⟨5141943241417872073013605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27423697287561984389405893 5141943241417872073013605)
                  ·
                    refine ⟨964114357765851013690051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5141943241417872073013605 964114357765851013690051)
                    ·
                      rfl

theorem cell22_2816409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_2816409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816409 prefixEnd_2816409 := by exact prefixLift 2816409
  have htrace : WordTrace (prefixWord ++ tailWord_2816409) baseStart_2816409 baseEnd_2816409 := by
    simpa [prefixWord, tailWord_2816409, baseEnd_2816409] using wordTrace_append hprefix tailTrace_2816409
  have hstable : (prefixWord ++ tailWord_2816409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816409).length < 2 ^ (prefixWord ++ tailWord_2816409).sum := by decide
  have hdescent : baseEnd_2816409 < baseStart_2816409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816490 : List Nat := [3, 1, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_2816490 : Nat := 118140960795 + 2816490 * 2 ^ 59
def prefixEnd_2816490 : Nat := 4983230072969 + 3 ^ 40 * 2816490 * 2
def baseEnd_2816490 : Nat := 964142085721193802414803

theorem tailTrace_2816490 : CollatzResearch.WordTrace tailWord_2816490 prefixEnd_2816490 964142085721193802414803 := by
  unfold tailWord_2816490
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681457391586305760323731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68483886377563482027529949 25681457391586305760323731)
  ·
    refine ⟨38522186087379458640485597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25681457391586305760323731 38522186087379458640485597)
    ·
      refine ⟨14445819782767296990182099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38522186087379458640485597 14445819782767296990182099)
      ·
        refine ⟨21668729674150945485273149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14445819782767296990182099 21668729674150945485273149)
        ·
          refine ⟨8125773627806604556977431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21668729674150945485273149 8125773627806604556977431)
          ·
            refine ⟨12188660441709906835466147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8125773627806604556977431 12188660441709906835466147)
            ·
              refine ⟨18282990662564860253199221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12188660441709906835466147 18282990662564860253199221)
              ·
                refine ⟨1714030374615455648737427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18282990662564860253199221 1714030374615455648737427)
                ·
                  refine ⟨2571045561923183473106141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714030374615455648737427 2571045561923183473106141)
                  ·
                    refine ⟨964142085721193802414803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571045561923183473106141 964142085721193802414803)
                    ·
                      rfl

theorem cell22_2816490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_2816490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816490 prefixEnd_2816490 := by exact prefixLift 2816490
  have htrace : WordTrace (prefixWord ++ tailWord_2816490) baseStart_2816490 baseEnd_2816490 := by
    simpa [prefixWord, tailWord_2816490, baseEnd_2816490] using wordTrace_append hprefix tailTrace_2816490
  have hstable : (prefixWord ++ tailWord_2816490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816490).length < 2 ^ (prefixWord ++ tailWord_2816490).sum := by decide
  have hdescent : baseEnd_2816490 < baseStart_2816490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816533 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2816533 : Nat := 118140960795 + 2816533 * 2 ^ 59
def prefixEnd_2816533 : Nat := 4983230072969 + 3 ^ 40 * 2816533 * 2
def baseEnd_2816533 : Nat := 964156805499956023589671

theorem tailTrace_2816533 : CollatzResearch.WordTrace tailWord_2816533 prefixEnd_2816533 964156805499956023589671 := by
  unfold tailWord_2816533
  simp only [CollatzResearch.WordTrace]
  refine ⟨102727397905189441385110253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68484931936792960923406835 102727397905189441385110253)
  ·
    refine ⟨38522774214446040519416345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102727397905189441385110253 38522774214446040519416345)
    ·
      refine ⟨28892080660834530389562259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38522774214446040519416345 28892080660834530389562259)
      ·
        refine ⟨43338120991251795584343389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28892080660834530389562259 43338120991251795584343389)
        ·
          refine ⟨16251795371719423344128771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43338120991251795584343389 16251795371719423344128771)
          ·
            refine ⟨24377693057579135016193157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16251795371719423344128771 24377693057579135016193157)
            ·
              refine ⟨4570817448296087815536217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24377693057579135016193157 4570817448296087815536217)
              ·
                refine ⟨3428113086222065861652163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4570817448296087815536217 3428113086222065861652163)
                ·
                  refine ⟨5142169629333098792478245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3428113086222065861652163 5142169629333098792478245)
                  ·
                    refine ⟨964156805499956023589671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5142169629333098792478245 964156805499956023589671)
                    ·
                      rfl

theorem cell22_2816533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2816533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816533 prefixEnd_2816533 := by exact prefixLift 2816533
  have htrace : WordTrace (prefixWord ++ tailWord_2816533) baseStart_2816533 baseEnd_2816533 := by
    simpa [prefixWord, tailWord_2816533, baseEnd_2816533] using wordTrace_append hprefix tailTrace_2816533
  have hstable : (prefixWord ++ tailWord_2816533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816533).length < 2 ^ (prefixWord ++ tailWord_2816533).sum := by decide
  have hdescent : baseEnd_2816533 < baseStart_2816533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816546 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2816546 : Nat := 118140960795 + 2816546 * 2 ^ 59
def prefixEnd_2816546 : Nat := 4983230072969 + 3 ^ 40 * 2816546 * 2
def baseEnd_2816546 : Nat := 964161255665628323014631

theorem tailTrace_2816546 : CollatzResearch.WordTrace tailWord_2816546 prefixEnd_2816546 964161255665628323014631 := by
  unfold tailWord_2816546
  simp only [CollatzResearch.WordTrace]
  refine ⟨25681968013535586151333373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68485248036094896403555661 25681968013535586151333373)
  ·
    refine ⟨9630738005075844806750015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25681968013535586151333373 9630738005075844806750015)
    ·
      refine ⟨14446107007613767210125023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9630738005075844806750015 14446107007613767210125023)
      ·
        refine ⟨21669160511420650815187535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14446107007613767210125023 21669160511420650815187535)
        ·
          refine ⟨32503740767130976222781303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21669160511420650815187535 32503740767130976222781303)
          ·
            refine ⟨48755611150696464334171955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32503740767130976222781303 48755611150696464334171955)
            ·
              refine ⟨73133416726044696501257933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48755611150696464334171955 73133416726044696501257933)
              ·
                refine ⟨27425031272266761187971725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73133416726044696501257933 27425031272266761187971725)
                ·
                  refine ⟨10284386727100035445489397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27425031272266761187971725 10284386727100035445489397)
                  ·
                    refine ⟨964161255665628323014631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10284386727100035445489397 964161255665628323014631)
                    ·
                      rfl

theorem cell22_2816546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2816546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816546 prefixEnd_2816546 := by exact prefixLift 2816546
  have htrace : WordTrace (prefixWord ++ tailWord_2816546) baseStart_2816546 baseEnd_2816546 := by
    simpa [prefixWord, tailWord_2816546, baseEnd_2816546] using wordTrace_append hprefix tailTrace_2816546
  have hstable : (prefixWord ++ tailWord_2816546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816546).length < 2 ^ (prefixWord ++ tailWord_2816546).sum := by decide
  have hdescent : baseEnd_2816546 < baseStart_2816546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816561 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 4, 4]
def baseStart_2816561 : Nat := 118140960795 + 2816561 * 2 ^ 59
def prefixEnd_2816561 : Nat := 4983230072969 + 3 ^ 40 * 2816561 * 2
def baseEnd_2816561 : Nat := 964166390472173283889585

theorem tailTrace_2816561 : CollatzResearch.WordTrace tailWord_2816561 prefixEnd_2816561 964166390472173283889585 := by
  unfold tailWord_2816561
  simp only [CollatzResearch.WordTrace]
  refine ⟨102728419149088002167129537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68485612766058668111419691 102728419149088002167129537)
  ·
    refine ⟨77046314361816001625347153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102728419149088002167129537 77046314361816001625347153)
    ·
      refine ⟨57784735771362001219010365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77046314361816001625347153 57784735771362001219010365)
      ·
        refine ⟨21669275914260750457128887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57784735771362001219010365 21669275914260750457128887)
        ·
          refine ⟨32503913871391125685693331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21669275914260750457128887 32503913871391125685693331)
          ·
            refine ⟨48755870807086688528539997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32503913871391125685693331 48755870807086688528539997)
            ·
              refine ⟨18283451552657508198202499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48755870807086688528539997 18283451552657508198202499)
              ·
                refine ⟨27425177328986262297303749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18283451552657508198202499 27425177328986262297303749)
                ·
                  refine ⟨5142220749184924180744453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27425177328986262297303749 5142220749184924180744453)
                  ·
                    refine ⟨964166390472173283889585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5142220749184924180744453 964166390472173283889585)
                    ·
                      rfl

theorem cell22_2816561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_2816561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816561 prefixEnd_2816561 := by exact prefixLift 2816561
  have htrace : WordTrace (prefixWord ++ tailWord_2816561) baseStart_2816561 baseEnd_2816561 := by
    simpa [prefixWord, tailWord_2816561, baseEnd_2816561] using wordTrace_append hprefix tailTrace_2816561
  have hstable : (prefixWord ++ tailWord_2816561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816561).length < 2 ^ (prefixWord ++ tailWord_2816561).sum := by decide
  have hdescent : baseEnd_2816561 < baseStart_2816561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816563 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 2, 3]
def baseStart_2816563 : Nat := 118140960795 + 2816563 * 2 ^ 59
def prefixEnd_2816563 : Nat := 4983230072969 + 3 ^ 40 * 2816563 * 2
def baseEnd_2816563 : Nat := 964167075113045945339579

theorem tailTrace_2816563 : CollatzResearch.WordTrace tailWord_2816563 prefixEnd_2816563 964167075113045945339579 := by
  unfold tailWord_2816563
  simp only [CollatzResearch.WordTrace]
  refine ⟨102728492095080756508702343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68485661396720504339134895 102728492095080756508702343)
  ·
    refine ⟨154092738142621134763053515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102728492095080756508702343 154092738142621134763053515)
    ·
      refine ⟨231139107213931702144580273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154092738142621134763053515 231139107213931702144580273)
      ·
        refine ⟨173354330410448776608435205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231139107213931702144580273 173354330410448776608435205)
        ·
          refine ⟨32503936951959145614081601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173354330410448776608435205 32503936951959145614081601)
          ·
            refine ⟨24377952713969359210561201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32503936951959145614081601 24377952713969359210561201)
            ·
              refine ⟨18283464535477019407920901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24377952713969359210561201 18283464535477019407920901)
              ·
                refine ⟨3428149600401941138985169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18283464535477019407920901 3428149600401941138985169)
                ·
                  refine ⟨2571112200301455854238877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3428149600401941138985169 2571112200301455854238877)
                  ·
                    refine ⟨964167075113045945339579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571112200301455854238877 964167075113045945339579)
                    ·
                      rfl

theorem cell22_2816563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 3].length) (baseStart_2816563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816563 prefixEnd_2816563 := by exact prefixLift 2816563
  have htrace : WordTrace (prefixWord ++ tailWord_2816563) baseStart_2816563 baseEnd_2816563 := by
    simpa [prefixWord, tailWord_2816563, baseEnd_2816563] using wordTrace_append hprefix tailTrace_2816563
  have hstable : (prefixWord ++ tailWord_2816563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816563).length < 2 ^ (prefixWord ++ tailWord_2816563).sum := by decide
  have hdescent : baseEnd_2816563 < baseStart_2816563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816565 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 4]
def baseStart_2816565 : Nat := 118140960795 + 2816565 * 2 ^ 59
def prefixEnd_2816565 : Nat := 4983230072969 + 3 ^ 40 * 2816565 * 2
def baseEnd_2816565 : Nat := 321389253251306202263191

theorem tailTrace_2816565 : CollatzResearch.WordTrace tailWord_2816565 prefixEnd_2816565 321389253251306202263191 := by
  unfold tailWord_2816565
  simp only [CollatzResearch.WordTrace]
  refine ⟨102728565041073510850275149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68485710027382340566850099 102728565041073510850275149)
  ·
    refine ⟨38523211890402566568853181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102728565041073510850275149 38523211890402566568853181)
    ·
      refine ⟨14446204458900962463319943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38523211890402566568853181 14446204458900962463319943)
      ·
        refine ⟨21669306688351443694979915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14446204458900962463319943 21669306688351443694979915)
        ·
          refine ⟨32503960032527165542469873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21669306688351443694979915 32503960032527165542469873)
          ·
            refine ⟨24377970024395374156852405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32503960032527165542469873 24377970024395374156852405)
            ·
              refine ⟨2285434689787066327204913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24377970024395374156852405 2285434689787066327204913)
              ·
                refine ⟨1714076017340299745403685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2285434689787066327204913 1714076017340299745403685)
                ·
                  refine ⟨321389253251306202263191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714076017340299745403685 321389253251306202263191)
                  ·
                    rfl

theorem cell22_2816565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_2816565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816565 prefixEnd_2816565 := by exact prefixLift 2816565
  have htrace : WordTrace (prefixWord ++ tailWord_2816565) baseStart_2816565 baseEnd_2816565 := by
    simpa [prefixWord, tailWord_2816565, baseEnd_2816565] using wordTrace_append hprefix tailTrace_2816565
  have hstable : (prefixWord ++ tailWord_2816565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816565).length < 2 ^ (prefixWord ++ tailWord_2816565).sum := by decide
  have hdescent : baseEnd_2816565 < baseStart_2816565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816610 : List Nat := [3, 3, 2, 3, 2, 9]
def baseStart_2816610 : Nat := 118140960795 + 2816610 * 2 ^ 59
def prefixEnd_2816610 : Nat := 4983230072969 + 3 ^ 40 * 2816610 * 2
def baseEnd_2816610 : Nat := 11903495853994487523635

theorem tailTrace_2816610 : CollatzResearch.WordTrace tailWord_2816610 prefixEnd_2816610 11903495853994487523635 := by
  unfold tailWord_2816610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25682551581477620883915821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68486804217273655690442189 25682551581477620883915821)
  ·
    refine ⟨9630956843054107831468433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25682551581477620883915821 9630956843054107831468433)
    ·
      refine ⟨7223217632290580873601325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9630956843054107831468433 7223217632290580873601325)
      ·
        refine ⟨2708706612108967827600497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7223217632290580873601325 2708706612108967827600497)
        ·
          refine ⟨2031529959081725870700373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708706612108967827600497 2031529959081725870700373)
          ·
            refine ⟨11903495853994487523635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2031529959081725870700373 11903495853994487523635)
            ·
              rfl

theorem cell22_2816610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 9].length) (baseStart_2816610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816610 prefixEnd_2816610 := by exact prefixLift 2816610
  have htrace : WordTrace (prefixWord ++ tailWord_2816610) baseStart_2816610 baseEnd_2816610 := by
    simpa [prefixWord, tailWord_2816610, baseEnd_2816610] using wordTrace_append hprefix tailTrace_2816610
  have hstable : (prefixWord ++ tailWord_2816610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816610).length < 2 ^ (prefixWord ++ tailWord_2816610).sum := by decide
  have hdescent : baseEnd_2816610 < baseStart_2816610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816636 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_2816636 : Nat := 118140960795 + 2816636 * 2 ^ 59
def prefixEnd_2816636 : Nat := 4983230072969 + 3 ^ 40 * 2816636 * 2
def baseEnd_2816636 : Nat := 964192064504898088264355

theorem tailTrace_2816636 : CollatzResearch.WordTrace tailWord_2816636 prefixEnd_2816636 964192064504898088264355 := by
  unfold tailWord_2816636
  simp only [CollatzResearch.WordTrace]
  refine ⟨51365577311908144988054881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68487436415877526650739841 51365577311908144988054881)
  ·
    refine ⟨38524182983931108741041161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51365577311908144988054881 38524182983931108741041161)
    ·
      refine ⟨28893137237948331555780871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38524182983931108741041161 28893137237948331555780871)
      ·
        refine ⟨43339705856922497333671307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28893137237948331555780871 43339705856922497333671307)
        ·
          refine ⟨65009558785383746000506961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43339705856922497333671307 65009558785383746000506961)
          ·
            refine ⟨48757169089037809500380221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65009558785383746000506961 48757169089037809500380221)
            ·
              refine ⟨18283938408389178562642583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48757169089037809500380221 18283938408389178562642583)
              ·
                refine ⟨27425907612583767843963875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18283938408389178562642583 27425907612583767843963875)
                ·
                  refine ⟨41138861418875651765945813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27425907612583767843963875 41138861418875651765945813)
                  ·
                    refine ⟨964192064504898088264355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41138861418875651765945813 964192064504898088264355)
                    ·
                      rfl

theorem cell22_2816636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_2816636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816636 prefixEnd_2816636 := by exact prefixLift 2816636
  have htrace : WordTrace (prefixWord ++ tailWord_2816636) baseStart_2816636 baseEnd_2816636 := by
    simpa [prefixWord, tailWord_2816636, baseEnd_2816636] using wordTrace_append hprefix tailTrace_2816636
  have hstable : (prefixWord ++ tailWord_2816636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816636).length < 2 ^ (prefixWord ++ tailWord_2816636).sum := by decide
  have hdescent : baseEnd_2816636 < baseStart_2816636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816672 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 5]
def baseStart_2816672 : Nat := 118140960795 + 2816672 * 2 ^ 59
def prefixEnd_2816672 : Nat := 4983230072969 + 3 ^ 40 * 2816672 * 2
def baseEnd_2816672 : Nat := 321401462680201998121415

theorem tailTrace_2816672 : CollatzResearch.WordTrace tailWord_2816672 prefixEnd_2816672 321401462680201998121415 := by
  unfold tailWord_2816672
  simp only [CollatzResearch.WordTrace]
  refine ⟨51366233825842934062210135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68488311767790578749613513 51366233825842934062210135)
  ·
    refine ⟨77049350738764401093315203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51366233825842934062210135 77049350738764401093315203)
    ·
      refine ⟨115574026108146601639972805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77049350738764401093315203 115574026108146601639972805)
      ·
        refine ⟨21670129895277487807494901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115574026108146601639972805 21670129895277487807494901)
        ·
          refine ⟨2031574677682264481952647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21670129895277487807494901 2031574677682264481952647)
          ·
            refine ⟨3047362016523396722928971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031574677682264481952647 3047362016523396722928971)
            ·
              refine ⟨4571043024785095084393457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047362016523396722928971 4571043024785095084393457)
              ·
                refine ⟨3428282268588821313295093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4571043024785095084393457 3428282268588821313295093)
                ·
                  refine ⟨321401462680201998121415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3428282268588821313295093 321401462680201998121415)
                  ·
                    rfl

theorem cell22_2816672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_2816672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816672 prefixEnd_2816672 := by exact prefixLift 2816672
  have htrace : WordTrace (prefixWord ++ tailWord_2816672) baseStart_2816672 baseEnd_2816672 := by
    simpa [prefixWord, tailWord_2816672, baseEnd_2816672] using wordTrace_append hprefix tailTrace_2816672
  have hstable : (prefixWord ++ tailWord_2816672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816672).length < 2 ^ (prefixWord ++ tailWord_2816672).sum := by decide
  have hdescent : baseEnd_2816672 < baseStart_2816672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816681 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_2816681 : Nat := 118140960795 + 2816681 * 2 ^ 59
def prefixEnd_2816681 : Nat := 4983230072969 + 3 ^ 40 * 2816681 * 2
def baseEnd_2816681 : Nat := 964207468924532970889217

theorem tailTrace_2816681 : CollatzResearch.WordTrace tailWord_2816681 prefixEnd_2816681 964207468924532970889217 := by
  unfold tailWord_2816681
  simp only [CollatzResearch.WordTrace]
  refine ⟨102732795908653262661497897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68488530605768841774331931 102732795908653262661497897)
  ·
    refine ⟨77049596931489946996123423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102732795908653262661497897 77049596931489946996123423)
    ·
      refine ⟨115574395397234920494185135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77049596931489946996123423 115574395397234920494185135)
      ·
        refine ⟨173361593095852380741277703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115574395397234920494185135 173361593095852380741277703)
        ·
          refine ⟨260042389643778571111916555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173361593095852380741277703 260042389643778571111916555)
          ·
            refine ⟨390063584465667856667874833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260042389643778571111916555 390063584465667856667874833)
            ·
              refine ⟨292547688349250892500906125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390063584465667856667874833 292547688349250892500906125)
              ·
                refine ⟨109705383130969084687839797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292547688349250892500906125 109705383130969084687839797)
                ·
                  refine ⟨10284879668528351689484981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109705383130969084687839797 10284879668528351689484981)
                  ·
                    refine ⟨964207468924532970889217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10284879668528351689484981 964207468924532970889217)
                    ·
                      rfl

theorem cell22_2816681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_2816681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816681 prefixEnd_2816681 := by exact prefixLift 2816681
  have htrace : WordTrace (prefixWord ++ tailWord_2816681) baseStart_2816681 baseEnd_2816681 := by
    simpa [prefixWord, tailWord_2816681, baseEnd_2816681] using wordTrace_append hprefix tailTrace_2816681
  have hstable : (prefixWord ++ tailWord_2816681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816681).length < 2 ^ (prefixWord ++ tailWord_2816681).sum := by decide
  have hdescent : baseEnd_2816681 < baseStart_2816681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816710 : List Nat := [6, 1, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2816710 : Nat := 118140960795 + 2816710 * 2 ^ 59
def prefixEnd_2816710 : Nat := 4983230072969 + 3 ^ 40 * 2816710 * 2
def baseEnd_2816710 : Nat := 964217396217186561914129

theorem tailTrace_2816710 : CollatzResearch.WordTrace tailWord_2816710 prefixEnd_2816710 964217396217186561914129 := by
  unfold tailWord_2816710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210432925798381269196987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68489235750365467076202389 3210432925798381269196987)
  ·
    refine ⟨4815649388697571903795481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3210432925798381269196987 4815649388697571903795481)
    ·
      refine ⟨3611737041523178927846611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4815649388697571903795481 3611737041523178927846611)
      ·
        refine ⟨5417605562284768391769917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611737041523178927846611 5417605562284768391769917)
        ·
          refine ⟨2031602085856788146913719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5417605562284768391769917 2031602085856788146913719)
          ·
            refine ⟨3047403128785182220370579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031602085856788146913719 3047403128785182220370579)
            ·
              refine ⟨4571104693177773330555869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047403128785182220370579 4571104693177773330555869)
              ·
                refine ⟨1714164259941664998958451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4571104693177773330555869 1714164259941664998958451)
                ·
                  refine ⟨2571246389912497498437677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714164259941664998958451 2571246389912497498437677)
                  ·
                    refine ⟨964217396217186561914129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571246389912497498437677 964217396217186561914129)
                    ·
                      rfl

theorem cell22_2816710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2816710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816710 prefixEnd_2816710 := by exact prefixLift 2816710
  have htrace : WordTrace (prefixWord ++ tailWord_2816710) baseStart_2816710 baseEnd_2816710 := by
    simpa [prefixWord, tailWord_2816710, baseEnd_2816710] using wordTrace_append hprefix tailTrace_2816710
  have hstable : (prefixWord ++ tailWord_2816710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816710).length < 2 ^ (prefixWord ++ tailWord_2816710).sum := by decide
  have hdescent : baseEnd_2816710 < baseStart_2816710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816728 : List Nat := [2, 1, 2, 2, 3, 4, 8]
def baseStart_2816728 : Nat := 118140960795 + 2816728 * 2 ^ 59
def prefixEnd_2816728 : Nat := 4983230072969 + 3 ^ 40 * 2816728 * 2
def baseEnd_2816728 : Nat := 35711983629075574628299

theorem tailTrace_2816728 : CollatzResearch.WordTrace tailWord_2816728 prefixEnd_2816728 35711983629075574628299 := by
  unfold tailWord_2816728
  simp only [CollatzResearch.WordTrace]
  refine ⟨51367255069741494844229419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68489673426321993125639225 51367255069741494844229419)
  ·
    refine ⟨77050882604612242266344129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51367255069741494844229419 77050882604612242266344129)
    ·
      refine ⟨57788161953459181699758097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77050882604612242266344129 57788161953459181699758097)
      ·
        refine ⟨43341121465094386274818573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57788161953459181699758097 43341121465094386274818573)
        ·
          refine ⟨16252920549410394853056965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43341121465094386274818573 16252920549410394853056965)
          ·
            refine ⟨3047422603014449034948181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16252920549410394853056965 3047422603014449034948181)
            ·
              refine ⟨35711983629075574628299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3047422603014449034948181 35711983629075574628299)
              ·
                rfl

theorem cell22_2816728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 8].length) (baseStart_2816728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816728 prefixEnd_2816728 := by exact prefixLift 2816728
  have htrace : WordTrace (prefixWord ++ tailWord_2816728) baseStart_2816728 baseEnd_2816728 := by
    simpa [prefixWord, tailWord_2816728, baseEnd_2816728] using wordTrace_append hprefix tailTrace_2816728
  have hstable : (prefixWord ++ tailWord_2816728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816728).length < 2 ^ (prefixWord ++ tailWord_2816728).sum := by decide
  have hdescent : baseEnd_2816728 < baseStart_2816728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816732 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2816732 : Nat := 118140960795 + 2816732 * 2 ^ 59
def prefixEnd_2816732 : Nat := 4983230072969 + 3 ^ 40 * 2816732 * 2
def baseEnd_2816732 : Nat := 964224927266785837864061

theorem tailTrace_2816732 : CollatzResearch.WordTrace tailWord_2816732 prefixEnd_2816732 964224927266785837864061 := by
  unfold tailWord_2816732
  simp only [CollatzResearch.WordTrace]
  refine ⟨51367328015734249185802225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68489770687645665581069633 51367328015734249185802225)
  ·
    refine ⟨38525496011800686889351669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51367328015734249185802225 38525496011800686889351669)
    ·
      refine ⟨3611765251106314395876719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38525496011800686889351669 3611765251106314395876719)
      ·
        refine ⟨5417647876659471593815079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611765251106314395876719 5417647876659471593815079)
        ·
          refine ⟨8126471814989207390722619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417647876659471593815079 8126471814989207390722619)
          ·
            refine ⟨12189707722483811086083929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8126471814989207390722619 12189707722483811086083929)
            ·
              refine ⟨9142280791862858314562947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12189707722483811086083929 9142280791862858314562947)
              ·
                refine ⟨13713421187794287471844421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142280791862858314562947 13713421187794287471844421)
                ·
                  refine ⟨2571266472711428900970829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13713421187794287471844421 2571266472711428900970829)
                  ·
                    refine ⟨964224927266785837864061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571266472711428900970829 964224927266785837864061)
                    ·
                      rfl

theorem cell22_2816732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2816732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816732 prefixEnd_2816732 := by exact prefixLift 2816732
  have htrace : WordTrace (prefixWord ++ tailWord_2816732) baseStart_2816732 baseEnd_2816732 := by
    simpa [prefixWord, tailWord_2816732, baseEnd_2816732] using wordTrace_append hprefix tailTrace_2816732
  have hstable : (prefixWord ++ tailWord_2816732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816732).length < 2 ^ (prefixWord ++ tailWord_2816732).sum := by decide
  have hdescent : baseEnd_2816732 < baseStart_2816732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816852 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_2816852 : Nat := 118140960795 + 2816852 * 2 ^ 59
def prefixEnd_2816852 : Nat := 4983230072969 + 3 ^ 40 * 2816852 * 2
def baseEnd_2816852 : Nat := 321422001906381841621231

theorem tailTrace_2816852 : CollatzResearch.WordTrace tailWord_2816852 prefixEnd_2816852 321422001906381841621231 := by
  unfold tailWord_2816852
  simp only [CollatzResearch.WordTrace]
  refine ⟨51369516395516879432986405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68492688527355839243981873 51369516395516879432986405)
  ·
    refine ⟨9631784324159414893684951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51369516395516879432986405 9631784324159414893684951)
    ·
      refine ⟨14447676486239122340527427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631784324159414893684951 14447676486239122340527427)
      ·
        refine ⟨21671514729358683510791141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14447676486239122340527427 21671514729358683510791141)
        ·
          refine ⟨4063409011754753158273339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21671514729358683510791141 4063409011754753158273339)
          ·
            refine ⟨6095113517632129737410009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063409011754753158273339 6095113517632129737410009)
            ·
              refine ⟨4571335138224097303057507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6095113517632129737410009 4571335138224097303057507)
              ·
                refine ⟨6857002707336145954586261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571335138224097303057507 6857002707336145954586261)
                ·
                  refine ⟨321422001906381841621231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6857002707336145954586261 321422001906381841621231)
                  ·
                    rfl

theorem cell22_2816852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_2816852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816852 prefixEnd_2816852 := by exact prefixLift 2816852
  have htrace : WordTrace (prefixWord ++ tailWord_2816852) baseStart_2816852 baseEnd_2816852 := by
    simpa [prefixWord, tailWord_2816852, baseEnd_2816852] using wordTrace_append hprefix tailTrace_2816852
  have hstable : (prefixWord ++ tailWord_2816852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816852).length < 2 ^ (prefixWord ++ tailWord_2816852).sum := by decide
  have hdescent : baseEnd_2816852 < baseStart_2816852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816863 : List Nat := [1, 1, 2, 3, 1, 3, 2, 9]
def baseStart_2816863 : Nat := 118140960795 + 2816863 * 2 ^ 59
def prefixEnd_2816863 : Nat := 4983230072969 + 3 ^ 40 * 2816863 * 2
def baseEnd_2816863 : Nat := 107141085693771684759851

theorem tailTrace_2816863 : CollatzResearch.WordTrace tailWord_2816863 prefixEnd_2816863 107141085693771684759851 := by
  unfold tailWord_2816863
  simp only [CollatzResearch.WordTrace]
  refine ⟨102739433993993907744623243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68492955995995938496415495 102739433993993907744623243)
  ·
    refine ⟨154109150990990861616934865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102739433993993907744623243 154109150990990861616934865)
    ·
      refine ⟨115581863243243146212701149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154109150990990861616934865 115581863243243146212701149)
      ·
        refine ⟨43343198716216179829762931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115581863243243146212701149 43343198716216179829762931)
        ·
          refine ⟨65014798074324269744644397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43343198716216179829762931 65014798074324269744644397)
          ·
            refine ⟨24380549277871601154241649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65014798074324269744644397 24380549277871601154241649)
            ·
              refine ⟨18285411958403700865681237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24380549277871601154241649 18285411958403700865681237)
              ·
                refine ⟨107141085693771684759851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18285411958403700865681237 107141085693771684759851)
                ·
                  rfl

theorem cell22_2816863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 9].length) (baseStart_2816863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816863 prefixEnd_2816863 := by exact prefixLift 2816863
  have htrace : WordTrace (prefixWord ++ tailWord_2816863) baseStart_2816863 baseEnd_2816863 := by
    simpa [prefixWord, tailWord_2816863, baseEnd_2816863] using wordTrace_append hprefix tailTrace_2816863
  have hstable : (prefixWord ++ tailWord_2816863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816863).length < 2 ^ (prefixWord ++ tailWord_2816863).sum := by decide
  have hdescent : baseEnd_2816863 < baseStart_2816863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816867 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 1, 5]
def baseStart_2816867 : Nat := 118140960795 + 2816867 * 2 ^ 59
def prefixEnd_2816867 : Nat := 4983230072969 + 3 ^ 40 * 2816867 * 2
def baseEnd_2816867 : Nat := 964271140525690485738647

theorem tailTrace_2816867 : CollatzResearch.WordTrace tailWord_2816867 prefixEnd_2816867 964271140525690485738647 := by
  unfold tailWord_2816867
  simp only [CollatzResearch.WordTrace]
  refine ⟨102739579885979416427768855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68493053257319610951845903 102739579885979416427768855)
  ·
    refine ⟨154109369828969124641653283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102739579885979416427768855 154109369828969124641653283)
    ·
      refine ⟨231164054743453686962479925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154109369828969124641653283 231164054743453686962479925)
      ·
        refine ⟨21671630132198783152732493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231164054743453686962479925 21671630132198783152732493)
        ·
          refine ⟨8126861299574543682274685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21671630132198783152732493 8126861299574543682274685)
          ·
            refine ⟨3047572987340453880853007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8126861299574543682274685 3047572987340453880853007)
            ·
              refine ⟨4571359481010680821279511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047572987340453880853007 4571359481010680821279511)
              ·
                refine ⟨6857039221516021231919267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571359481010680821279511 6857039221516021231919267)
                ·
                  refine ⟨10285558832274031847878901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6857039221516021231919267 10285558832274031847878901)
                  ·
                    refine ⟨964271140525690485738647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10285558832274031847878901 964271140525690485738647)
                    ·
                      rfl

theorem cell22_2816867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 5].length) (baseStart_2816867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816867 prefixEnd_2816867 := by exact prefixLift 2816867
  have htrace : WordTrace (prefixWord ++ tailWord_2816867) baseStart_2816867 baseEnd_2816867 := by
    simpa [prefixWord, tailWord_2816867, baseEnd_2816867] using wordTrace_append hprefix tailTrace_2816867
  have hstable : (prefixWord ++ tailWord_2816867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816867).length < 2 ^ (prefixWord ++ tailWord_2816867).sum := by decide
  have hdescent : baseEnd_2816867 < baseStart_2816867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816880 : List Nat := [2, 1, 1, 1, 4, 1, 6, 6]
def baseStart_2816880 : Nat := 118140960795 + 2816880 * 2 ^ 59
def prefixEnd_2816880 : Nat := 4983230072969 + 3 ^ 40 * 2816880 * 2
def baseEnd_2816880 : Nat := 107141732299040309462623

theorem tailTrace_2816880 : CollatzResearch.WordTrace tailWord_2816880 prefixEnd_2816880 107141732299040309462623 := by
  unfold tailWord_2816880
  simp only [CollatzResearch.WordTrace]
  refine ⟨51370027017466159823996047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68493369356621546431994729 51370027017466159823996047)
  ·
    refine ⟨77055040526199239735994071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51370027017466159823996047 77055040526199239735994071)
    ·
      refine ⟨115582560789298859603991107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77055040526199239735994071 115582560789298859603991107)
      ·
        refine ⟨173373841183948289405986661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115582560789298859603991107 173373841183948289405986661)
        ·
          refine ⟨32507595221990304263622499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173373841183948289405986661 32507595221990304263622499)
          ·
            refine ⟨48761392832985456395433749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32507595221990304263622499 48761392832985456395433749)
            ·
              refine ⟨2285690289046193268535957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48761392832985456395433749 2285690289046193268535957)
              ·
                refine ⟨107141732299040309462623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2285690289046193268535957 107141732299040309462623)
                ·
                  rfl

theorem cell22_2816880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 6].length) (baseStart_2816880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816880 prefixEnd_2816880 := by exact prefixLift 2816880
  have htrace : WordTrace (prefixWord ++ tailWord_2816880) baseStart_2816880 baseEnd_2816880 := by
    simpa [prefixWord, tailWord_2816880, baseEnd_2816880] using wordTrace_append hprefix tailTrace_2816880
  have hstable : (prefixWord ++ tailWord_2816880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816880).length < 2 ^ (prefixWord ++ tailWord_2816880).sum := by decide
  have hdescent : baseEnd_2816880 < baseStart_2816880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816886 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2816886 : Nat := 118140960795 + 2816886 * 2 ^ 59
def prefixEnd_2816886 : Nat := 4983230072969 + 3 ^ 40 * 2816886 * 2
def baseEnd_2816886 : Nat := 321425881537993589837863

theorem tailTrace_2816886 : CollatzResearch.WordTrace tailWord_2816886 prefixEnd_2816886 321425881537993589837863 := by
  unfold tailWord_2816886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421267054556911417044407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68493515248607055115140341 6421267054556911417044407)
  ·
    refine ⟨9631900581835367125566611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6421267054556911417044407 9631900581835367125566611)
    ·
      refine ⟨14447850872753050688349917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9631900581835367125566611 14447850872753050688349917)
      ·
        refine ⟨5417944077282394008131219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14447850872753050688349917 5417944077282394008131219)
        ·
          refine ⟨8126916115923591012196829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417944077282394008131219 8126916115923591012196829)
          ·
            refine ⟨3047593543471346629573811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8126916115923591012196829 3047593543471346629573811)
            ·
              refine ⟨4571390315207019944360717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047593543471346629573811 4571390315207019944360717)
              ·
                refine ⟨1714271368202632479135269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4571390315207019944360717 1714271368202632479135269)
                ·
                  refine ⟨321425881537993589837863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714271368202632479135269 321425881537993589837863)
                  ·
                    rfl

theorem cell22_2816886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2816886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816886 prefixEnd_2816886 := by exact prefixLift 2816886
  have htrace : WordTrace (prefixWord ++ tailWord_2816886) baseStart_2816886 baseEnd_2816886 := by
    simpa [prefixWord, tailWord_2816886, baseEnd_2816886] using wordTrace_append hprefix tailTrace_2816886
  have hstable : (prefixWord ++ tailWord_2816886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816886).length < 2 ^ (prefixWord ++ tailWord_2816886).sum := by decide
  have hdescent : baseEnd_2816886 < baseStart_2816886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816895 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 5, 3]
def baseStart_2816895 : Nat := 118140960795 + 2816895 * 2 ^ 59
def prefixEnd_2816895 : Nat := 4983230072969 + 3 ^ 40 * 2816895 * 2
def baseEnd_2816895 : Nat := 964280725497907746038561

theorem tailTrace_2816895 : CollatzResearch.WordTrace tailWord_2816895 prefixEnd_2816895 964280725497907746038561 := by
  unfold tailWord_2816895
  simp only [CollatzResearch.WordTrace]
  refine ⟨102740601129877977209788139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68493734086585318139858759 102740601129877977209788139)
  ·
    refine ⟨154110901694816965814682209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102740601129877977209788139 154110901694816965814682209)
    ·
      refine ⟨115583176271112724361011657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154110901694816965814682209 115583176271112724361011657)
      ·
        refine ⟨86687382203334543270758743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115583176271112724361011657 86687382203334543270758743)
        ·
          refine ⟨130031073305001814906138115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86687382203334543270758743 130031073305001814906138115)
          ·
            refine ⟨195046609957502722359207173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130031073305001814906138115 195046609957502722359207173)
            ·
              refine ⟨36571239367031760442351345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195046609957502722359207173 36571239367031760442351345)
              ·
                refine ⟨27428429525273820331763509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36571239367031760442351345 27428429525273820331763509)
                ·
                  refine ⟨2571415267994420656102829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27428429525273820331763509 2571415267994420656102829)
                  ·
                    refine ⟨964280725497907746038561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571415267994420656102829 964280725497907746038561)
                    ·
                      rfl

theorem cell22_2816895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_2816895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816895 prefixEnd_2816895 := by exact prefixLift 2816895
  have htrace : WordTrace (prefixWord ++ tailWord_2816895) baseStart_2816895 baseEnd_2816895 := by
    simpa [prefixWord, tailWord_2816895, baseEnd_2816895] using wordTrace_append hprefix tailTrace_2816895
  have hstable : (prefixWord ++ tailWord_2816895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816895).length < 2 ^ (prefixWord ++ tailWord_2816895).sum := by decide
  have hdescent : baseEnd_2816895 < baseStart_2816895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816918 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2816918 : Nat := 118140960795 + 2816918 * 2 ^ 59
def prefixEnd_2816918 : Nat := 4983230072969 + 3 ^ 40 * 2816918 * 2
def baseEnd_2816918 : Nat := 964288598867943352713491

theorem tailTrace_2816918 : CollatzResearch.WordTrace tailWord_2816918 prefixEnd_2816918 964288598867943352713491 := by
  unfold tailWord_2816918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421340000549665758617213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68494293339196434758583605 6421340000549665758617213)
  ·
    refine ⟨2408002500206124659481455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6421340000549665758617213 2408002500206124659481455)
    ·
      refine ⟨3612003750309186989222183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408002500206124659481455 3612003750309186989222183)
      ·
        refine ⟨5418005625463780483833275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612003750309186989222183 5418005625463780483833275)
        ·
          refine ⟨8127008438195670725749913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5418005625463780483833275 8127008438195670725749913)
          ·
            refine ⟨6095256328646753044312435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8127008438195670725749913 6095256328646753044312435)
            ·
              refine ⟨9142884492970129566468653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095256328646753044312435 9142884492970129566468653)
              ·
                refine ⟨3428581684863798587425745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9142884492970129566468653 3428581684863798587425745)
                ·
                  refine ⟨2571436263647848940569309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3428581684863798587425745 2571436263647848940569309)
                  ·
                    refine ⟨964288598867943352713491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571436263647848940569309 964288598867943352713491)
                    ·
                      rfl

theorem cell22_2816918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2816918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816918 prefixEnd_2816918 := by exact prefixLift 2816918
  have htrace : WordTrace (prefixWord ++ tailWord_2816918) baseStart_2816918 baseEnd_2816918 := by
    simpa [prefixWord, tailWord_2816918, baseEnd_2816918] using wordTrace_append hprefix tailTrace_2816918
  have hstable : (prefixWord ++ tailWord_2816918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816918).length < 2 ^ (prefixWord ++ tailWord_2816918).sum := by decide
  have hdescent : baseEnd_2816918 < baseStart_2816918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2816970 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_2816970 : Nat := 118140960795 + 2816970 * 2 ^ 59
def prefixEnd_2816970 : Nat := 4983230072969 + 3 ^ 40 * 2816970 * 2
def baseEnd_2816970 : Nat := 321435466510210850137777

theorem tailTrace_2816970 : CollatzResearch.WordTrace tailWord_2816970 prefixEnd_2816970 321435466510210850137777 := by
  unfold tailWord_2816970
  simp only [CollatzResearch.WordTrace]
  refine ⟨25685834151151566254692091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68495557736404176679178909 25685834151151566254692091)
  ·
    refine ⟨38528751226727349382038137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25685834151151566254692091 38528751226727349382038137)
    ·
      refine ⟨28896563420045512036528603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38528751226727349382038137 28896563420045512036528603)
      ·
        refine ⟨43344845130068268054792905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28896563420045512036528603 43344845130068268054792905)
        ·
          refine ⟨32508633847551201041094679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43344845130068268054792905 32508633847551201041094679)
          ·
            refine ⟨48762950771326801561642019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32508633847551201041094679 48762950771326801561642019)
            ·
              refine ⟨73144426156990202342463029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48762950771326801561642019 73144426156990202342463029)
              ·
                refine ⟨6857289952217831469605909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73144426156990202342463029 6857289952217831469605909)
                ·
                  refine ⟨321435466510210850137777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6857289952217831469605909 321435466510210850137777)
                  ·
                    rfl

theorem cell22_2816970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_2816970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2816970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2816970 prefixEnd_2816970 := by exact prefixLift 2816970
  have htrace : WordTrace (prefixWord ++ tailWord_2816970) baseStart_2816970 baseEnd_2816970 := by
    simpa [prefixWord, tailWord_2816970, baseEnd_2816970] using wordTrace_append hprefix tailTrace_2816970
  have hstable : (prefixWord ++ tailWord_2816970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2816970).length < 2 ^ (prefixWord ++ tailWord_2816970).sum := by decide
  have hdescent : baseEnd_2816970 < baseStart_2816970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2816970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817002 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_2817002 : Nat := 118140960795 + 2817002 * 2 ^ 59
def prefixEnd_2817002 : Nat := 4983230072969 + 3 ^ 40 * 2817002 * 2
def baseEnd_2817002 : Nat := 964317353784595133613233

theorem tailTrace_2817002 : CollatzResearch.WordTrace tailWord_2817002 prefixEnd_2817002 964317353784595133613233 := by
  unfold tailWord_2817002
  simp only [CollatzResearch.WordTrace]
  refine ⟨25686125935122583620983315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68496335826993556322622173 25686125935122583620983315)
  ·
    refine ⟨38529188902683875431474973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25686125935122583620983315 38529188902683875431474973)
    ·
      refine ⟨14448445838506453286803115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38529188902683875431474973 14448445838506453286803115)
      ·
        refine ⟨21672668757759679930204673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14448445838506453286803115 21672668757759679930204673)
        ·
          refine ⟨16254501568319759947653505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21672668757759679930204673 16254501568319759947653505)
          ·
            refine ⟨12190876176239819960740129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16254501568319759947653505 12190876176239819960740129)
            ·
              refine ⟨9143157132179864970555097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12190876176239819960740129 9143157132179864970555097)
              ·
                refine ⟨6857367849134898727916323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9143157132179864970555097 6857367849134898727916323)
                ·
                  refine ⟨10286051773702348091874485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6857367849134898727916323 10286051773702348091874485)
                  ·
                    refine ⟨964317353784595133613233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10286051773702348091874485 964317353784595133613233)
                    ·
                      rfl

theorem cell22_2817002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_2817002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817002 prefixEnd_2817002 := by exact prefixLift 2817002
  have htrace : WordTrace (prefixWord ++ tailWord_2817002) baseStart_2817002 baseEnd_2817002 := by
    simpa [prefixWord, tailWord_2817002, baseEnd_2817002] using wordTrace_append hprefix tailTrace_2817002
  have hstable : (prefixWord ++ tailWord_2817002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817002).length < 2 ^ (prefixWord ++ tailWord_2817002).sum := by decide
  have hdescent : baseEnd_2817002 < baseStart_2817002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817036 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_2817036 : Nat := 118140960795 + 2817036 * 2 ^ 59
def prefixEnd_2817036 : Nat := 4983230072969 + 3 ^ 40 * 2817036 * 2
def baseEnd_2817036 : Nat := 964328992679430378263129

theorem tailTrace_2817036 : CollatzResearch.WordTrace tailWord_2817036 prefixEnd_2817036 964328992679430378263129 := by
  unfold tailWord_2817036
  simp only [CollatzResearch.WordTrace]
  refine ⟨51372871911183579145335481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68497162548244772193780641 51372871911183579145335481)
  ·
    refine ⟨38529653933387684359001611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51372871911183579145335481 38529653933387684359001611)
    ·
      refine ⟨57794480900081526538502417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38529653933387684359001611 57794480900081526538502417)
      ·
        refine ⟨43345860675061144903876813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57794480900081526538502417 43345860675061144903876813)
        ·
          refine ⟨16254697753147929338953805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43345860675061144903876813 16254697753147929338953805)
          ·
            refine ⟨6095511657430473502107677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16254697753147929338953805 6095511657430473502107677)
            ·
              refine ⟨2285816871536427563290379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6095511657430473502107677 2285816871536427563290379)
              ·
                refine ⟨3428725307304641344935569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2285816871536427563290379 3428725307304641344935569)
                ·
                  refine ⟨2571543980478481008701677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3428725307304641344935569 2571543980478481008701677)
                  ·
                    refine ⟨964328992679430378263129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571543980478481008701677 964328992679430378263129)
                    ·
                      rfl

theorem cell22_2817036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_2817036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817036 prefixEnd_2817036 := by exact prefixLift 2817036
  have htrace : WordTrace (prefixWord ++ tailWord_2817036) baseStart_2817036 baseEnd_2817036 := by
    simpa [prefixWord, tailWord_2817036, baseEnd_2817036] using wordTrace_append hprefix tailTrace_2817036
  have hstable : (prefixWord ++ tailWord_2817036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817036).length < 2 ^ (prefixWord ++ tailWord_2817036).sum := by decide
  have hdescent : baseEnd_2817036 < baseStart_2817036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817077 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 5]
def baseStart_2817077 : Nat := 118140960795 + 2817077 * 2 ^ 59
def prefixEnd_2817077 : Nat := 4983230072969 + 3 ^ 40 * 2817077 * 2
def baseEnd_2817077 : Nat := 321447675939106645996001

theorem tailTrace_2817077 : CollatzResearch.WordTrace tailWord_2817077 prefixEnd_2817077 321447675939106645996001 := by
  unfold tailWord_2817077
  simp only [CollatzResearch.WordTrace]
  refine ⟨102747239215218622292913485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68498159476812414861942323 102747239215218622292913485)
  ·
    refine ⟨38530214705706983359842557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102747239215218622292913485 38530214705706983359842557)
    ·
      refine ⟨14448830514640118759940959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38530214705706983359842557 14448830514640118759940959)
      ·
        refine ⟨21673245771960178139911439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14448830514640118759940959 21673245771960178139911439)
        ·
          refine ⟨32509868657940267209867159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21673245771960178139911439 32509868657940267209867159)
          ·
            refine ⟨48764802986910400814800739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32509868657940267209867159 48764802986910400814800739)
            ·
              refine ⟨73147204480365601222201109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48764802986910400814800739 73147204480365601222201109)
              ·
                refine ⟨3428775210017137557290677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73147204480365601222201109 3428775210017137557290677)
                ·
                  refine ⟨321447675939106645996001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3428775210017137557290677 321447675939106645996001)
                  ·
                    rfl

theorem cell22_2817077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_2817077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817077 prefixEnd_2817077 := by exact prefixLift 2817077
  have htrace : WordTrace (prefixWord ++ tailWord_2817077) baseStart_2817077 baseEnd_2817077 := by
    simpa [prefixWord, tailWord_2817077, baseEnd_2817077] using wordTrace_append hprefix tailTrace_2817077
  have hstable : (prefixWord ++ tailWord_2817077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817077).length < 2 ^ (prefixWord ++ tailWord_2817077).sum := by decide
  have hdescent : baseEnd_2817077 < baseStart_2817077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817081 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_2817081 : Nat := 118140960795 + 2817081 * 2 ^ 59
def prefixEnd_2817081 : Nat := 4983230072969 + 3 ^ 40 * 2817081 * 2
def baseEnd_2817081 : Nat := 964344397099065260887991

theorem tailTrace_2817081 : CollatzResearch.WordTrace tailWord_2817081 prefixEnd_2817081 964344397099065260887991 := by
  unfold tailWord_2817081
  simp only [CollatzResearch.WordTrace]
  refine ⟨102747385107204130976059097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68498256738136087317372731 102747385107204130976059097)
  ·
    refine ⟨77060538830403098232044323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102747385107204130976059097 77060538830403098232044323)
    ·
      refine ⟨115590808245604647348066485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77060538830403098232044323 115590808245604647348066485)
      ·
        refine ⟨10836638273025435688881233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115590808245604647348066485 10836638273025435688881233)
        ·
          refine ⟨8127478704769076766660925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10836638273025435688881233 8127478704769076766660925)
          ·
            refine ⟨3047804514288403787497847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8127478704769076766660925 3047804514288403787497847)
            ·
              refine ⟨4571706771432605681246771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047804514288403787497847 4571706771432605681246771)
              ·
                refine ⟨6857560157148908521870157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4571706771432605681246771 6857560157148908521870157)
                ·
                  refine ⟨2571585058930840695701309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6857560157148908521870157 2571585058930840695701309)
                  ·
                    refine ⟨964344397099065260887991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571585058930840695701309 964344397099065260887991)
                    ·
                      rfl

theorem cell22_2817081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_2817081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817081 prefixEnd_2817081 := by exact prefixLift 2817081
  have htrace : WordTrace (prefixWord ++ tailWord_2817081) baseStart_2817081 baseEnd_2817081 := by
    simpa [prefixWord, tailWord_2817081, baseEnd_2817081] using wordTrace_append hprefix tailTrace_2817081
  have hstable : (prefixWord ++ tailWord_2817081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817081).length < 2 ^ (prefixWord ++ tailWord_2817081).sum := by decide
  have hdescent : baseEnd_2817081 < baseStart_2817081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817152 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_2817152 : Nat := 118140960795 + 2817152 * 2 ^ 59
def prefixEnd_2817152 : Nat := 4983230072969 + 3 ^ 40 * 2817152 * 2
def baseEnd_2817152 : Nat := 964368701850044742362773

theorem tailTrace_2817152 : CollatzResearch.WordTrace tailWord_2817152 prefixEnd_2817152 964368701850044742362773 := by
  unfold tailWord_2817152
  simp only [CollatzResearch.WordTrace]
  refine ⟨51374987344973455050946855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68499983126631273401262473 51374987344973455050946855)
  ·
    refine ⟨77062481017460182576420283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51374987344973455050946855 77062481017460182576420283)
    ·
      refine ⟨115593721526190273864630425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77062481017460182576420283 115593721526190273864630425)
      ·
        refine ⟨86695291144642705398472819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115593721526190273864630425 86695291144642705398472819)
        ·
          refine ⟨130042936716964058097709229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86695291144642705398472819 130042936716964058097709229)
          ·
            refine ⟨48766101268861521786640961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130042936716964058097709229 48766101268861521786640961)
            ·
              refine ⟨36574575951646141339980721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48766101268861521786640961 36574575951646141339980721)
              ·
                refine ⟨27430931963734606004985541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36574575951646141339980721 27430931963734606004985541)
                ·
                  refine ⟨5143299743200238625934789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27430931963734606004985541 5143299743200238625934789)
                  ·
                    refine ⟨964368701850044742362773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5143299743200238625934789 964368701850044742362773)
                    ·
                      rfl

theorem cell22_2817152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_2817152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817152 prefixEnd_2817152 := by exact prefixLift 2817152
  have htrace : WordTrace (prefixWord ++ tailWord_2817152) baseStart_2817152 baseEnd_2817152 := by
    simpa [prefixWord, tailWord_2817152, baseEnd_2817152] using wordTrace_append hprefix tailTrace_2817152
  have hstable : (prefixWord ++ tailWord_2817152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817152).length < 2 ^ (prefixWord ++ tailWord_2817152).sum := by decide
  have hdescent : baseEnd_2817152 < baseStart_2817152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817188 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_2817188 : Nat := 118140960795 + 2817188 * 2 ^ 59
def prefixEnd_2817188 : Nat := 4983230072969 + 3 ^ 40 * 2817188 * 2
def baseEnd_2817188 : Nat := 964381025385752648462663

theorem tailTrace_2817188 : CollatzResearch.WordTrace tailWord_2817188 prefixEnd_2817188 964381025385752648462663 := by
  unfold tailWord_2817188
  simp only [CollatzResearch.WordTrace]
  refine ⟨51375643858908244125102109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68500858478544325500136145 51375643858908244125102109)
  ·
    refine ⟨19265866447090591546913291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51375643858908244125102109 19265866447090591546913291)
    ·
      refine ⟨28898799670635887320369937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19265866447090591546913291 28898799670635887320369937)
      ·
        refine ⟨21674099752976915490277453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28898799670635887320369937 21674099752976915490277453)
        ·
          refine ⟨8127787407366343308854045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21674099752976915490277453 8127787407366343308854045)
          ·
            refine ⟨3047920277762378740820267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8127787407366343308854045 3047920277762378740820267)
            ·
              refine ⟨4571880416643568111230401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3047920277762378740820267 4571880416643568111230401)
              ·
                refine ⟨3428910312482676083422801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4571880416643568111230401 3428910312482676083422801)
                ·
                  refine ⟨2571682734362007062567101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3428910312482676083422801 2571682734362007062567101)
                  ·
                    refine ⟨964381025385752648462663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571682734362007062567101 964381025385752648462663)
                    ·
                      rfl

theorem cell22_2817188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_2817188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817188 prefixEnd_2817188 := by exact prefixLift 2817188
  have htrace : WordTrace (prefixWord ++ tailWord_2817188) baseStart_2817188 baseEnd_2817188 := by
    simpa [prefixWord, tailWord_2817188, baseEnd_2817188] using wordTrace_append hprefix tailTrace_2817188
  have hstable : (prefixWord ++ tailWord_2817188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817188).length < 2 ^ (prefixWord ++ tailWord_2817188).sum := by decide
  have hdescent : baseEnd_2817188 < baseStart_2817188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817199 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 3, 3]
def baseStart_2817199 : Nat := 118140960795 + 2817199 * 2 ^ 59
def prefixEnd_2817199 : Nat := 4983230072969 + 3 ^ 40 * 2817199 * 2
def baseEnd_2817199 : Nat := 964384790910552286437629

theorem tailTrace_2817199 : CollatzResearch.WordTrace tailWord_2817199 prefixEnd_2817199 964384790910552286437629 := by
  unfold tailWord_2817199
  simp only [CollatzResearch.WordTrace]
  refine ⟨102751688920776637128854651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68501125947184424752569767 102751688920776637128854651)
  ·
    refine ⟨154127533381164955693281977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102751688920776637128854651 154127533381164955693281977)
    ·
      refine ⟨115595650035873716769961483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154127533381164955693281977 115595650035873716769961483)
      ·
        refine ⟨173393475053810575154942225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115595650035873716769961483 173393475053810575154942225)
        ·
          refine ⟨130045106290357931366206669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173393475053810575154942225 130045106290357931366206669)
          ·
            refine ⟨48766914858884224262327501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130045106290357931366206669 48766914858884224262327501)
            ·
              refine ⟨18287593072081584098372813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48766914858884224262327501 18287593072081584098372813)
              ·
                refine ⟨6857847402030594036889805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18287593072081584098372813 6857847402030594036889805)
                ·
                  refine ⟨2571692775761472763833677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6857847402030594036889805 2571692775761472763833677)
                  ·
                    refine ⟨964384790910552286437629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571692775761472763833677 964384790910552286437629)
                    ·
                      rfl

theorem cell22_2817199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_2817199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817199 prefixEnd_2817199 := by exact prefixLift 2817199
  have htrace : WordTrace (prefixWord ++ tailWord_2817199) baseStart_2817199 baseEnd_2817199 := by
    simpa [prefixWord, tailWord_2817199, baseEnd_2817199] using wordTrace_append hprefix tailTrace_2817199
  have hstable : (prefixWord ++ tailWord_2817199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817199).length < 2 ^ (prefixWord ++ tailWord_2817199).sum := by decide
  have hdescent : baseEnd_2817199 < baseStart_2817199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817218 : List Nat := [3, 5, 1, 1, 2, 1, 1, 8]
def baseStart_2817218 : Nat := 118140960795 + 2817218 * 2 ^ 59
def prefixEnd_2817218 : Nat := 4983230072969 + 3 ^ 40 * 2817218 * 2
def baseEnd_2817218 : Nat := 107154588333204730023619

theorem tailTrace_2817218 : CollatzResearch.WordTrace tailWord_2817218 prefixEnd_2817218 107154588333204730023619 := by
  unfold tailWord_2817218
  simp only [CollatzResearch.WordTrace]
  refine ⟨25688095476926950843449077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68501587938471868915864205 25688095476926950843449077)
  ·
    refine ⟨2408258950961901641573351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25688095476926950843449077 2408258950961901641573351)
    ·
      refine ⟨3612388426442852462360027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408258950961901641573351 3612388426442852462360027)
      ·
        refine ⟨5418582639664278693540041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612388426442852462360027 5418582639664278693540041)
        ·
          refine ⟨4063936979748209020155031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5418582639664278693540041 4063936979748209020155031)
          ·
            refine ⟨6095905469622313530232547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063936979748209020155031 6095905469622313530232547)
            ·
              refine ⟨9143858204433470295348821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095905469622313530232547 9143858204433470295348821)
              ·
                refine ⟨107154588333204730023619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9143858204433470295348821 107154588333204730023619)
                ·
                  rfl

theorem cell22_2817218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_2817218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817218 prefixEnd_2817218 := by exact prefixLift 2817218
  have htrace : WordTrace (prefixWord ++ tailWord_2817218) baseStart_2817218 baseEnd_2817218 := by
    simpa [prefixWord, tailWord_2817218, baseEnd_2817218] using wordTrace_append hprefix tailTrace_2817218
  have hstable : (prefixWord ++ tailWord_2817218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817218).length < 2 ^ (prefixWord ++ tailWord_2817218).sum := by decide
  have hdescent : baseEnd_2817218 < baseStart_2817218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817227 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_2817227 : Nat := 118140960795 + 2817227 * 2 ^ 59
def prefixEnd_2817227 : Nat := 4983230072969 + 3 ^ 40 * 2817227 * 2
def baseEnd_2817227 : Nat := 964394375882769546737543

theorem tailTrace_2817227 : CollatzResearch.WordTrace tailWord_2817227 prefixEnd_2817227 964394375882769546737543 := by
  unfold tailWord_2817227
  simp only [CollatzResearch.WordTrace]
  refine ⟨102752710164675197910873935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68501806776450131940582623 102752710164675197910873935)
  ·
    refine ⟨154129065247012796866310903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102752710164675197910873935 154129065247012796866310903)
    ·
      refine ⟨231193597870519195299466355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154129065247012796866310903 231193597870519195299466355)
      ·
        refine ⟨346790396805778792949199533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231193597870519195299466355 346790396805778792949199533)
        ·
          refine ⟨130046398802167047355949825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346790396805778792949199533 130046398802167047355949825)
          ·
            refine ⟨97534799101625285516962369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130046398802167047355949825 97534799101625285516962369)
            ·
              refine ⟨73151099326218964137721777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97534799101625285516962369 73151099326218964137721777)
              ·
                refine ⟨54863324494664223103291333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73151099326218964137721777 54863324494664223103291333)
                ·
                  refine ⟨10286873342749541831867125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54863324494664223103291333 10286873342749541831867125)
                  ·
                    refine ⟨964394375882769546737543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10286873342749541831867125 964394375882769546737543)
                    ·
                      rfl

theorem cell22_2817227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_2817227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817227 prefixEnd_2817227 := by exact prefixLift 2817227
  have htrace : WordTrace (prefixWord ++ tailWord_2817227) baseStart_2817227 baseEnd_2817227 := by
    simpa [prefixWord, tailWord_2817227, baseEnd_2817227] using wordTrace_append hprefix tailTrace_2817227
  have hstable : (prefixWord ++ tailWord_2817227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817227).length < 2 ^ (prefixWord ++ tailWord_2817227).sum := by decide
  have hdescent : baseEnd_2817227 < baseStart_2817227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817263 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 5]
def baseStart_2817263 : Nat := 118140960795 + 2817263 * 2 ^ 59
def prefixEnd_2817263 : Nat := 4983230072969 + 3 ^ 40 * 2817263 * 2
def baseEnd_2817263 : Nat := 321468899806159150945811

theorem tailTrace_2817263 : CollatzResearch.WordTrace tailWord_2817263 prefixEnd_2817263 321468899806159150945811 := by
  unfold tailWord_2817263
  simp only [CollatzResearch.WordTrace]
  refine ⟨102754023192544776059184443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68502682128363184039456295 102754023192544776059184443)
  ·
    refine ⟨154131034788817164088776665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102754023192544776059184443 154131034788817164088776665)
    ·
      refine ⟨115598276091612873066582499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154131034788817164088776665 115598276091612873066582499)
      ·
        refine ⟨173397414137419309599873749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115598276091612873066582499 173397414137419309599873749)
        ·
          refine ⟨4064001893845765068747041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 173397414137419309599873749 4064001893845765068747041)
          ·
            refine ⟨3048001420384323801560281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4064001893845765068747041 3048001420384323801560281)
            ·
              refine ⟨2286001065288242851170211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048001420384323801560281 2286001065288242851170211)
              ·
                refine ⟨3429001597932364276755317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286001065288242851170211 3429001597932364276755317)
                ·
                  refine ⟨321468899806159150945811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3429001597932364276755317 321468899806159150945811)
                  ·
                    rfl

theorem cell22_2817263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 5].length) (baseStart_2817263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817263 prefixEnd_2817263 := by exact prefixLift 2817263
  have htrace : WordTrace (prefixWord ++ tailWord_2817263) baseStart_2817263 baseEnd_2817263 := by
    simpa [prefixWord, tailWord_2817263, baseEnd_2817263] using wordTrace_append hprefix tailTrace_2817263
  have hstable : (prefixWord ++ tailWord_2817263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817263).length < 2 ^ (prefixWord ++ tailWord_2817263).sum := by decide
  have hdescent : baseEnd_2817263 < baseStart_2817263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817276 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_2817276 : Nat := 118140960795 + 2817276 * 2 ^ 59
def prefixEnd_2817276 : Nat := 4983230072969 + 3 ^ 40 * 2817276 * 2
def baseEnd_2817276 : Nat := 964411149584149752262393

theorem tailTrace_2817276 : CollatzResearch.WordTrace tailWord_2817276 prefixEnd_2817276 964411149584149752262393 := by
  unfold tailWord_2817276
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377248670748839639703841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68502998227665119519605121 51377248670748839639703841)
  ·
    refine ⟨38532936503061629729777881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51377248670748839639703841 38532936503061629729777881)
    ·
      refine ⟨28899702377296222297333411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38532936503061629729777881 28899702377296222297333411)
      ·
        refine ⟨43349553565944333446000117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28899702377296222297333411 43349553565944333446000117)
        ·
          refine ⟨4064020646807281260562511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43349553565944333446000117 4064020646807281260562511)
          ·
            refine ⟨6096030970210921890843767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064020646807281260562511 6096030970210921890843767)
            ·
              refine ⟨9144046455316382836265651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6096030970210921890843767 9144046455316382836265651)
              ·
                refine ⟨13716069682974574254398477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9144046455316382836265651 13716069682974574254398477)
                ·
                  refine ⟨5143526131115465345399429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13716069682974574254398477 5143526131115465345399429)
                  ·
                    refine ⟨964411149584149752262393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5143526131115465345399429 964411149584149752262393)
                    ·
                      rfl

theorem cell22_2817276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_2817276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817276 prefixEnd_2817276 := by exact prefixLift 2817276
  have htrace : WordTrace (prefixWord ++ tailWord_2817276) baseStart_2817276 baseEnd_2817276 := by
    simpa [prefixWord, tailWord_2817276, baseEnd_2817276] using wordTrace_append hprefix tailTrace_2817276
  have hstable : (prefixWord ++ tailWord_2817276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817276).length < 2 ^ (prefixWord ++ tailWord_2817276).sum := by decide
  have hdescent : baseEnd_2817276 < baseStart_2817276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817289 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_2817289 : Nat := 118140960795 + 2817289 * 2 ^ 59
def prefixEnd_2817289 : Nat := 4983230072969 + 3 ^ 40 * 2817289 * 2
def baseEnd_2817289 : Nat := 964415599749822051687353

theorem tailTrace_2817289 : CollatzResearch.WordTrace tailWord_2817289 prefixEnd_2817289 964415599749822051687353 := by
  unfold tailWord_2817289
  simp only [CollatzResearch.WordTrace]
  refine ⟨102754971490450582499630921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68503314326967054999753947 102754971490450582499630921)
  ·
    refine ⟨77066228617837936874723191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102754971490450582499630921 77066228617837936874723191)
    ·
      refine ⟨115599342926756905312084787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77066228617837936874723191 115599342926756905312084787)
      ·
        refine ⟨173399014390135357968127181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115599342926756905312084787 173399014390135357968127181)
        ·
          refine ⟨65024630396300759238047693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173399014390135357968127181 65024630396300759238047693)
          ·
            refine ⟨24384236398612784714267885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65024630396300759238047693 24384236398612784714267885)
            ·
              refine ⟨9144088649479794267850457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24384236398612784714267885 9144088649479794267850457)
              ·
                refine ⟨6858066487109845700887843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144088649479794267850457 6858066487109845700887843)
                ·
                  refine ⟨10287099730664768551331765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6858066487109845700887843 10287099730664768551331765)
                  ·
                    refine ⟨964415599749822051687353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10287099730664768551331765 964415599749822051687353)
                    ·
                      rfl

theorem cell22_2817289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_2817289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817289 prefixEnd_2817289 := by exact prefixLift 2817289
  have htrace : WordTrace (prefixWord ++ tailWord_2817289) baseStart_2817289 baseEnd_2817289 := by
    simpa [prefixWord, tailWord_2817289, baseEnd_2817289] using wordTrace_append hprefix tailTrace_2817289
  have hstable : (prefixWord ++ tailWord_2817289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817289).length < 2 ^ (prefixWord ++ tailWord_2817289).sum := by decide
  have hdescent : baseEnd_2817289 < baseStart_2817289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817308 : List Nat := [2, 2, 3, 1, 1, 1, 6, 2, 4]
def baseStart_2817308 : Nat := 118140960795 + 2817308 * 2 ^ 59
def prefixEnd_2817308 : Nat := 4983230072969 + 3 ^ 40 * 2817308 * 2
def baseEnd_2817308 : Nat := 321474034612704111820765

theorem tailTrace_2817308 : CollatzResearch.WordTrace tailWord_2817308 prefixEnd_2817308 321474034612704111820765 := by
  unfold tailWord_2817308
  simp only [CollatzResearch.WordTrace]
  refine ⟨51377832238690874372286289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68503776318254499163048385 51377832238690874372286289)
  ·
    refine ⟨38533374179018155779214717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51377832238690874372286289 38533374179018155779214717)
    ·
      refine ⟨14450015317131808417205519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38533374179018155779214717 14450015317131808417205519)
      ·
        refine ⟨21675022975697712625808279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14450015317131808417205519 21675022975697712625808279)
        ·
          refine ⟨32512534463546568938712419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21675022975697712625808279 32512534463546568938712419)
          ·
            refine ⟨48768801695319853408068629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32512534463546568938712419 48768801695319853408068629)
            ·
              refine ⟨2286037579468118128503217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48768801695319853408068629 2286037579468118128503217)
              ·
                refine ⟨1714528184601088596377413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286037579468118128503217 1714528184601088596377413)
                ·
                  refine ⟨321474034612704111820765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714528184601088596377413 321474034612704111820765)
                  ·
                    rfl

theorem cell22_2817308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_2817308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817308 prefixEnd_2817308 := by exact prefixLift 2817308
  have htrace : WordTrace (prefixWord ++ tailWord_2817308) baseStart_2817308 baseEnd_2817308 := by
    simpa [prefixWord, tailWord_2817308, baseEnd_2817308] using wordTrace_append hprefix tailTrace_2817308
  have hstable : (prefixWord ++ tailWord_2817308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817308).length < 2 ^ (prefixWord ++ tailWord_2817308).sum := by decide
  have hdescent : baseEnd_2817308 < baseStart_2817308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817368 : List Nat := [2, 1, 2, 2, 1, 1, 3, 6, 1, 3]
def baseStart_2817368 : Nat := 118140960795 + 2817368 * 2 ^ 59
def prefixEnd_2817368 : Nat := 4983230072969 + 3 ^ 40 * 2817368 * 2
def baseEnd_2817368 : Nat := 964442643064292178962111

theorem tailTrace_2817368 : CollatzResearch.WordTrace tailWord_2817368 prefixEnd_2817368 964442643064292178962111 := by
  unfold tailWord_2817368
  simp only [CollatzResearch.WordTrace]
  refine ⟨51378926428582189495878379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68505235238109585994504505 51378926428582189495878379)
  ·
    refine ⟨77068389642873284243817569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51378926428582189495878379 77068389642873284243817569)
    ·
      refine ⟨57801292232154963182863177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77068389642873284243817569 57801292232154963182863177)
      ·
        refine ⟨43350969174116222387147383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57801292232154963182863177 43350969174116222387147383)
        ·
          refine ⟨65026453761174333580721075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43350969174116222387147383 65026453761174333580721075)
          ·
            refine ⟨97539680641761500371081613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65026453761174333580721075 97539680641761500371081613)
            ·
              refine ⟨36577380240660562639155605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97539680641761500371081613 36577380240660562639155605)
              ·
                refine ⟨1714564698780963873710419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36577380240660562639155605 1714564698780963873710419)
                ·
                  refine ⟨2571847048171445810565629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714564698780963873710419 2571847048171445810565629)
                  ·
                    refine ⟨964442643064292178962111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571847048171445810565629 964442643064292178962111)
                    ·
                      rfl

theorem cell22_2817368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_2817368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817368 prefixEnd_2817368 := by exact prefixLift 2817368
  have htrace : WordTrace (prefixWord ++ tailWord_2817368) baseStart_2817368 baseEnd_2817368 := by
    simpa [prefixWord, tailWord_2817368, baseEnd_2817368] using wordTrace_append hprefix tailTrace_2817368
  have hstable : (prefixWord ++ tailWord_2817368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817368).length < 2 ^ (prefixWord ++ tailWord_2817368).sum := by decide
  have hdescent : baseEnd_2817368 < baseStart_2817368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817432 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 5]
def baseStart_2817432 : Nat := 118140960795 + 2817432 * 2 ^ 59
def prefixEnd_2817432 : Nat := 4983230072969 + 3 ^ 40 * 2817432 * 2
def baseEnd_2817432 : Nat := 321488183857405781787305

theorem tailTrace_2817432 : CollatzResearch.WordTrace tailWord_2817432 prefixEnd_2817432 321488183857405781787305 := by
  unfold tailWord_2817432
  simp only [CollatzResearch.WordTrace]
  refine ⟨51380093564466258961043275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68506791419288345281391033 51380093564466258961043275)
  ·
    refine ⟨77070140346699388441564913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51380093564466258961043275 77070140346699388441564913)
    ·
      refine ⟨57802605260024541331173685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77070140346699388441564913 57802605260024541331173685)
      ·
        refine ⟨5418994243127300749797533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57802605260024541331173685 5418994243127300749797533)
        ·
          refine ⟨2032122841172737781174075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5418994243127300749797533 2032122841172737781174075)
          ·
            refine ⟨3048184261759106671761113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032122841172737781174075 3048184261759106671761113)
            ·
              refine ⟨2286138196319330003820835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048184261759106671761113 2286138196319330003820835)
              ·
                refine ⟨3429207294478995005731253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286138196319330003820835 3429207294478995005731253)
                ·
                  refine ⟨321488183857405781787305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3429207294478995005731253 321488183857405781787305)
                  ·
                    rfl

theorem cell22_2817432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_2817432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817432 prefixEnd_2817432 := by exact prefixLift 2817432
  have htrace : WordTrace (prefixWord ++ tailWord_2817432) baseStart_2817432 baseEnd_2817432 := by
    simpa [prefixWord, tailWord_2817432, baseEnd_2817432] using wordTrace_append hprefix tailTrace_2817432
  have hstable : (prefixWord ++ tailWord_2817432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817432).length < 2 ^ (prefixWord ++ tailWord_2817432).sum := by decide
  have hdescent : baseEnd_2817432 < baseStart_2817432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817503 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 3, 3]
def baseStart_2817503 : Nat := 118140960795 + 2817503 * 2 ^ 59
def prefixEnd_2817503 : Nat := 4983230072969 + 3 ^ 40 * 2817503 * 2
def baseEnd_2817503 : Nat := 964488856323196826836697

theorem tailTrace_2817503 : CollatzResearch.WordTrace tailWord_2817503 prefixEnd_2817503 964488856323196826836697 := by
  unfold tailWord_2817503
  simp only [CollatzResearch.WordTrace]
  refine ⟨102762776711675297047921163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68508517807783531365280775 102762776711675297047921163)
  ·
    refine ⟨154144165067512945571881745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102762776711675297047921163 154144165067512945571881745)
    ·
      refine ⟨115608123800634709178911309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154144165067512945571881745 115608123800634709178911309)
      ·
        refine ⟨43353046425238015942091741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115608123800634709178911309 43353046425238015942091741)
        ·
          refine ⟨16257392409464255978284403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43353046425238015942091741 16257392409464255978284403)
          ·
            refine ⟨24386088614196383967426605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16257392409464255978284403 24386088614196383967426605)
            ·
              refine ⟨9144783230323643987784977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24386088614196383967426605 9144783230323643987784977)
              ·
                refine ⟨6858587422742732990838733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9144783230323643987784977 6858587422742732990838733)
                ·
                  refine ⟨2571970283528524871564525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6858587422742732990838733 2571970283528524871564525)
                  ·
                    refine ⟨964488856323196826836697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571970283528524871564525 964488856323196826836697)
                    ·
                      rfl

theorem cell22_2817503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_2817503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817503 prefixEnd_2817503 := by exact prefixLift 2817503
  have htrace : WordTrace (prefixWord ++ tailWord_2817503) baseStart_2817503 baseEnd_2817503 := by
    simpa [prefixWord, tailWord_2817503, baseEnd_2817503] using wordTrace_append hprefix tailTrace_2817503
  have hstable : (prefixWord ++ tailWord_2817503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817503).length < 2 ^ (prefixWord ++ tailWord_2817503).sum := by decide
  have hdescent : baseEnd_2817503 < baseStart_2817503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817520 : List Nat := [2, 1, 1, 1, 3, 4, 1, 5, 1, 3]
def baseStart_2817520 : Nat := 118140960795 + 2817520 * 2 ^ 59
def prefixEnd_2817520 : Nat := 4983230072969 + 3 ^ 40 * 2817520 * 2
def baseEnd_2817520 : Nat := 964494675770614449161645

theorem tailTrace_2817520 : CollatzResearch.WordTrace tailWord_2817520 prefixEnd_2817520 964494675770614449161645 := by
  unfold tailWord_2817520
  simp only [CollatzResearch.WordTrace]
  refine ⟨51381698376306854475645007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68508931168409139300860009 51381698376306854475645007)
  ·
    refine ⟨77072547564460281713467511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51381698376306854475645007 77072547564460281713467511)
    ·
      refine ⟨115608821346690422570201267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77072547564460281713467511 115608821346690422570201267)
      ·
        refine ⟨173413232020035633855301901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115608821346690422570201267 173413232020035633855301901)
        ·
          refine ⟨65029962007513362695738213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173413232020035633855301901 65029962007513362695738213)
          ·
            refine ⟨12193117876408755505450915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65029962007513362695738213 12193117876408755505450915)
            ·
              refine ⟨18289676814613133258176373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12193117876408755505450915 18289676814613133258176373)
              ·
                refine ⟨1714657201369981242954035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18289676814613133258176373 1714657201369981242954035)
                ·
                  refine ⟨2571985802054971864431053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714657201369981242954035 2571985802054971864431053)
                  ·
                    refine ⟨964494675770614449161645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2571985802054971864431053 964494675770614449161645)
                    ·
                      rfl

theorem cell22_2817520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_2817520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817520 prefixEnd_2817520 := by exact prefixLift 2817520
  have htrace : WordTrace (prefixWord ++ tailWord_2817520) baseStart_2817520 baseEnd_2817520 := by
    simpa [prefixWord, tailWord_2817520, baseEnd_2817520] using wordTrace_append hprefix tailTrace_2817520
  have hstable : (prefixWord ++ tailWord_2817520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817520).length < 2 ^ (prefixWord ++ tailWord_2817520).sum := by decide
  have hdescent : baseEnd_2817520 < baseStart_2817520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817533 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 5]
def baseStart_2817533 : Nat := 118140960795 + 2817533 * 2 ^ 59
def prefixEnd_2817533 : Nat := 4983230072969 + 3 ^ 40 * 2817533 * 2
def baseEnd_2817533 : Nat := 321499708645428916195535

theorem tailTrace_2817533 : CollatzResearch.WordTrace tailWord_2817533 prefixEnd_2817533 321499708645428916195535 := by
  unfold tailWord_2817533
  simp only [CollatzResearch.WordTrace]
  refine ⟨102763870901566612171513253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68509247267711074781008835 102763870901566612171513253)
  ·
    refine ⟨19268225794043739782158735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102763870901566612171513253 19268225794043739782158735)
    ·
      refine ⟨28902338691065609673238103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19268225794043739782158735 28902338691065609673238103)
      ·
        refine ⟨43353508036598414509857155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28902338691065609673238103 43353508036598414509857155)
        ·
          refine ⟨65030262054897621764785733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43353508036598414509857155 65030262054897621764785733)
          ·
            refine ⟨12193174135293304080897325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65030262054897621764785733 12193174135293304080897325)
            ·
              refine ⟨4572440300734989030336497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12193174135293304080897325 4572440300734989030336497)
              ·
                refine ⟨3429330225551241772752373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572440300734989030336497 3429330225551241772752373)
                ·
                  refine ⟨321499708645428916195535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3429330225551241772752373 321499708645428916195535)
                  ·
                    rfl

theorem cell22_2817533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_2817533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817533 prefixEnd_2817533 := by exact prefixLift 2817533
  have htrace : WordTrace (prefixWord ++ tailWord_2817533) baseStart_2817533 baseEnd_2817533 := by
    simpa [prefixWord, tailWord_2817533, baseEnd_2817533] using wordTrace_append hprefix tailTrace_2817533
  have hstable : (prefixWord ++ tailWord_2817533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817533).length < 2 ^ (prefixWord ++ tailWord_2817533).sum := by decide
  have hdescent : baseEnd_2817533 < baseStart_2817533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817610 : List Nat := [3, 1, 2, 1, 1, 3, 3, 3, 2, 3]
def baseStart_2817610 : Nat := 118140960795 + 2817610 * 2 ^ 59
def prefixEnd_2817610 : Nat := 4983230072969 + 3 ^ 40 * 2817610 * 2
def baseEnd_2817610 : Nat := 964525484609884214411369

theorem tailTrace_2817610 : CollatzResearch.WordTrace tailWord_2817610 prefixEnd_2817610 964525484609884214411369 := by
  unfold tailWord_2817610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25691669830571913580516571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68511119548191769548044189 25691669830571913580516571)
  ·
    refine ⟨38537504745857870370774857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25691669830571913580516571 38537504745857870370774857)
    ·
      refine ⟨28903128559393402778081143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38537504745857870370774857 28903128559393402778081143)
      ·
        refine ⟨43354692839090104167121715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28903128559393402778081143 43354692839090104167121715)
        ·
          refine ⟨65032039258635156250682573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43354692839090104167121715 65032039258635156250682573)
          ·
            refine ⟨24387014721988183594005965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65032039258635156250682573 24387014721988183594005965)
            ·
              refine ⟨9145130520745568847752237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24387014721988183594005965 9145130520745568847752237)
              ·
                refine ⟨3429423945279588317907089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9145130520745568847752237 3429423945279588317907089)
                ·
                  refine ⟨2572067958959691238430317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429423945279588317907089 2572067958959691238430317)
                  ·
                    refine ⟨964525484609884214411369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572067958959691238430317 964525484609884214411369)
                    ·
                      rfl

theorem cell22_2817610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_2817610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817610 prefixEnd_2817610 := by exact prefixLift 2817610
  have htrace : WordTrace (prefixWord ++ tailWord_2817610) baseStart_2817610 baseEnd_2817610 := by
    simpa [prefixWord, tailWord_2817610, baseEnd_2817610] using wordTrace_append hprefix tailTrace_2817610
  have hstable : (prefixWord ++ tailWord_2817610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817610).length < 2 ^ (prefixWord ++ tailWord_2817610).sum := by decide
  have hdescent : baseEnd_2817610 < baseStart_2817610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817646 : List Nat := [4, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_2817646 : Nat := 118140960795 + 2817646 * 2 ^ 59
def prefixEnd_2817646 : Nat := 4983230072969 + 3 ^ 40 * 2817646 * 2
def baseEnd_2817646 : Nat := 321512602715197373503753

theorem tailTrace_2817646 : CollatzResearch.WordTrace tailWord_2817646 prefixEnd_2817646 321512602715197373503753 := by
  unfold tailWord_2817646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845999043769654058797099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68511994900104821646917861 12845999043769654058797099)
  ·
    refine ⟨19268998565654481088195649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12845999043769654058797099 19268998565654481088195649)
    ·
      refine ⟨14451748924240860816146737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19268998565654481088195649 14451748924240860816146737)
      ·
        refine ⟨10838811693180645612110053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14451748924240860816146737 10838811693180645612110053)
        ·
          refine ⟨2032277192471371052270635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10838811693180645612110053 2032277192471371052270635)
          ·
            refine ⟨3048415788707056578405953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032277192471371052270635 3048415788707056578405953)
            ·
              refine ⟨2286311841530292433804465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048415788707056578405953 2286311841530292433804465)
              ·
                refine ⟨1714733881147719325353349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2286311841530292433804465 1714733881147719325353349)
                ·
                  refine ⟨321512602715197373503753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714733881147719325353349 321512602715197373503753)
                  ·
                    rfl

theorem cell22_2817646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_2817646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817646 prefixEnd_2817646 := by exact prefixLift 2817646
  have htrace : WordTrace (prefixWord ++ tailWord_2817646) baseStart_2817646 baseEnd_2817646 := by
    simpa [prefixWord, tailWord_2817646, baseEnd_2817646] using wordTrace_append hprefix tailTrace_2817646
  have hstable : (prefixWord ++ tailWord_2817646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817646).length < 2 ^ (prefixWord ++ tailWord_2817646).sum := by decide
  have hdescent : baseEnd_2817646 < baseStart_2817646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817651 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 11]
def baseStart_2817651 : Nat := 118140960795 + 2817651 * 2 ^ 59
def prefixEnd_2817651 : Nat := 4983230072969 + 3 ^ 40 * 2817651 * 2
def baseEnd_2817651 : Nat := 321513173249257924712081

theorem tailTrace_2817651 : CollatzResearch.WordTrace tailWord_2817651 prefixEnd_2817651 321513173249257924712081 := by
  unfold tailWord_2817651
  simp only [CollatzResearch.WordTrace]
  refine ⟨102768174715139118324308807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68512116476759412216205871 102768174715139118324308807)
  ·
    refine ⟨154152262072708677486463211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102768174715139118324308807 154152262072708677486463211)
    ·
      refine ⟨231228393109063016229694817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154152262072708677486463211 231228393109063016229694817)
      ·
        refine ⟨173421294831797262172271113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231228393109063016229694817 173421294831797262172271113)
        ·
          refine ⟨130065971123847946629203335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173421294831797262172271113 130065971123847946629203335)
          ·
            refine ⟨195098956685771919943805003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130065971123847946629203335 195098956685771919943805003)
            ·
              refine ⟨292648435028657879915707505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195098956685771919943805003 292648435028657879915707505)
              ·
                refine ⟨219486326271493409936780629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292648435028657879915707505 219486326271493409936780629)
                ·
                  refine ⟨321513173249257924712081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 219486326271493409936780629 321513173249257924712081)
                  ·
                    rfl

theorem cell22_2817651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_2817651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817651 prefixEnd_2817651 := by exact prefixLift 2817651
  have htrace : WordTrace (prefixWord ++ tailWord_2817651) baseStart_2817651 baseEnd_2817651 := by
    simpa [prefixWord, tailWord_2817651, baseEnd_2817651] using wordTrace_append hprefix tailTrace_2817651
  have hstable : (prefixWord ++ tailWord_2817651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817651).length < 2 ^ (prefixWord ++ tailWord_2817651).sum := by decide
  have hdescent : baseEnd_2817651 < baseStart_2817651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817732 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2817732 : Nat := 118140960795 + 2817732 * 2 ^ 59
def prefixEnd_2817732 : Nat := 4983230072969 + 3 ^ 40 * 2817732 * 2
def baseEnd_2817732 : Nat := 964567247703116562860995

theorem tailTrace_2817732 : CollatzResearch.WordTrace tailWord_2817732 prefixEnd_2817732 964567247703116562860995 := by
  unfold tailWord_2817732
  simp only [CollatzResearch.WordTrace]
  refine ⟨51385564513922834579003725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68514086018563779438671633 51385564513922834579003725)
  ·
    refine ⟨19269586692721062967126397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51385564513922834579003725 19269586692721062967126397)
    ·
      refine ⟨7226095009770398612672399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19269586692721062967126397 7226095009770398612672399)
      ·
        refine ⟨10839142514655597919008599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7226095009770398612672399 10839142514655597919008599)
        ·
          refine ⟨16258713771983396878512899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839142514655597919008599 16258713771983396878512899)
          ·
            refine ⟨24388070657975095317769349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16258713771983396878512899 24388070657975095317769349)
            ·
              refine ⟨4572763248370330372081753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24388070657975095317769349 4572763248370330372081753)
              ·
                refine ⟨3429572436277747779061315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4572763248370330372081753 3429572436277747779061315)
                ·
                  refine ⟨5144358654416621668591973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3429572436277747779061315 5144358654416621668591973)
                  ·
                    refine ⟨964567247703116562860995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144358654416621668591973 964567247703116562860995)
                    ·
                      rfl

theorem cell22_2817732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2817732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817732 prefixEnd_2817732 := by exact prefixLift 2817732
  have htrace : WordTrace (prefixWord ++ tailWord_2817732) baseStart_2817732 baseEnd_2817732 := by
    simpa [prefixWord, tailWord_2817732, baseEnd_2817732] using wordTrace_append hprefix tailTrace_2817732
  have hstable : (prefixWord ++ tailWord_2817732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817732).length < 2 ^ (prefixWord ++ tailWord_2817732).sum := by decide
  have hdescent : baseEnd_2817732 < baseStart_2817732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817743 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 6, 4]
def baseStart_2817743 : Nat := 118140960795 + 2817743 * 2 ^ 59
def prefixEnd_2817743 : Nat := 4983230072969 + 3 ^ 40 * 2817743 * 2
def baseEnd_2817743 : Nat := 964571013227916200835961

theorem tailTrace_2817743 : CollatzResearch.WordTrace tailWord_2817743 prefixEnd_2817743 964571013227916200835961 := by
  unfold tailWord_2817743
  simp only [CollatzResearch.WordTrace]
  refine ⟨102771530230805818036657883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68514353487203878691105255 102771530230805818036657883)
  ·
    refine ⟨154157295346208727054986825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102771530230805818036657883 154157295346208727054986825)
    ·
      refine ⟨115617971509656545291240119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154157295346208727054986825 115617971509656545291240119)
      ·
        refine ⟨173426957264484817936860179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115617971509656545291240119 173426957264484817936860179)
        ·
          refine ⟨260140435896727226905290269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173426957264484817936860179 260140435896727226905290269)
          ·
            refine ⟨97552663461272710089483851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260140435896727226905290269 97552663461272710089483851)
            ·
              refine ⟨146328995191909065134225777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97552663461272710089483851 146328995191909065134225777)
              ·
                refine ⟨109746746393931798850669333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146328995191909065134225777 109746746393931798850669333)
                ·
                  refine ⟨5144378737215553071125125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109746746393931798850669333 5144378737215553071125125)
                  ·
                    refine ⟨964571013227916200835961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144378737215553071125125 964571013227916200835961)
                    ·
                      rfl

theorem cell22_2817743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_2817743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817743 prefixEnd_2817743 := by exact prefixLift 2817743
  have htrace : WordTrace (prefixWord ++ tailWord_2817743) baseStart_2817743 baseEnd_2817743 := by
    simpa [prefixWord, tailWord_2817743, baseEnd_2817743] using wordTrace_append hprefix tailTrace_2817743
  have hstable : (prefixWord ++ tailWord_2817743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817743).length < 2 ^ (prefixWord ++ tailWord_2817743).sum := by decide
  have hdescent : baseEnd_2817743 < baseStart_2817743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817745 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_2817745 : Nat := 118140960795 + 2817745 * 2 ^ 59
def prefixEnd_2817745 : Nat := 4983230072969 + 3 ^ 40 * 2817745 * 2
def baseEnd_2817745 : Nat := 964571697868788862285955

theorem tailTrace_2817745 : CollatzResearch.WordTrace tailWord_2817745 prefixEnd_2817745 964571697868788862285955 := by
  unfold tailWord_2817745
  simp only [CollatzResearch.WordTrace]
  refine ⟨102771603176798572378230689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68514402117865714918820459 102771603176798572378230689)
  ·
    refine ⟨77078702382598929283673017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102771603176798572378230689 77078702382598929283673017)
    ·
      refine ⟨57809026786949196962754763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77078702382598929283673017 57809026786949196962754763)
      ·
        refine ⟨86713540180423795444132145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57809026786949196962754763 86713540180423795444132145)
        ·
          refine ⟨65035155135317846583099109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86713540180423795444132145 65035155135317846583099109)
          ·
            refine ⟨12194091587872096234331083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65035155135317846583099109 12194091587872096234331083)
            ·
              refine ⟨18291137381808144351496625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12194091587872096234331083 18291137381808144351496625)
              ·
                refine ⟨13718353036356108263622469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18291137381808144351496625 13718353036356108263622469)
                ·
                  refine ⟨2572191194316770299429213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13718353036356108263622469 2572191194316770299429213)
                  ·
                    refine ⟨964571697868788862285955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572191194316770299429213 964571697868788862285955)
                    ·
                      rfl

theorem cell22_2817745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_2817745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817745 prefixEnd_2817745 := by exact prefixLift 2817745
  have htrace : WordTrace (prefixWord ++ tailWord_2817745) baseStart_2817745 baseEnd_2817745 := by
    simpa [prefixWord, tailWord_2817745, baseEnd_2817745] using wordTrace_append hprefix tailTrace_2817745
  have hstable : (prefixWord ++ tailWord_2817745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817745).length < 2 ^ (prefixWord ++ tailWord_2817745).sum := by decide
  have hdescent : baseEnd_2817745 < baseStart_2817745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817803 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 9]
def baseStart_2817803 : Nat := 118140960795 + 2817803 * 2 ^ 59
def prefixEnd_2817803 : Nat := 4983230072969 + 3 ^ 40 * 2817803 * 2
def baseEnd_2817803 : Nat := 321530517484698681445259

theorem tailTrace_2817803 : CollatzResearch.WordTrace tailWord_2817803 prefixEnd_2817803 321530517484698681445259 := by
  unfold tailWord_2817803
  simp only [CollatzResearch.WordTrace]
  refine ⟨102773718610588448283842063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68515812407058965522561375 102773718610588448283842063)
  ·
    refine ⟨154160577915882672425763095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102773718610588448283842063 154160577915882672425763095)
    ·
      refine ⟨231240866873824008638644643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154160577915882672425763095 231240866873824008638644643)
      ·
        refine ⟨346861300310736012957966965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231240866873824008638644643 346861300310736012957966965)
        ·
          refine ⟨32518246904131501214809403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 346861300310736012957966965 32518246904131501214809403)
          ·
            refine ⟨48777370356197251822214105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32518246904131501214809403 48777370356197251822214105)
            ·
              refine ⟨36583027767147938866660579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48777370356197251822214105 36583027767147938866660579)
              ·
                refine ⟨54874541650721908299990869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36583027767147938866660579 54874541650721908299990869)
                ·
                  refine ⟨321530517484698681445259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54874541650721908299990869 321530517484698681445259)
                  ·
                    rfl

theorem cell22_2817803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_2817803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817803 prefixEnd_2817803 := by exact prefixLift 2817803
  have htrace : WordTrace (prefixWord ++ tailWord_2817803) baseStart_2817803 baseEnd_2817803 := by
    simpa [prefixWord, tailWord_2817803, baseEnd_2817803] using wordTrace_append hprefix tailTrace_2817803
  have hstable : (prefixWord ++ tailWord_2817803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817803).length < 2 ^ (prefixWord ++ tailWord_2817803).sum := by decide
  have hdescent : baseEnd_2817803 < baseStart_2817803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817824 : List Nat := [2, 1, 1, 5, 1, 1, 3, 4, 1, 3]
def baseStart_2817824 : Nat := 118140960795 + 2817824 * 2 ^ 59
def prefixEnd_2817824 : Nat := 4983230072969 + 3 ^ 40 * 2817824 * 2
def baseEnd_2817824 : Nat := 964598741183258989560713

theorem tailTrace_2817824 : CollatzResearch.WordTrace tailWord_2817824 prefixEnd_2817824 964598741183258989560713 := by
  unfold tailWord_2817824
  simp only [CollatzResearch.WordTrace]
  refine ⟨51387242271756184435178263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68516323029008245913571017 51387242271756184435178263)
  ·
    refine ⟨77080863407634276652767395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51387242271756184435178263 77080863407634276652767395)
    ·
      refine ⟨115621295111451414979151093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77080863407634276652767395 115621295111451414979151093)
      ·
        refine ⟨10839496416698570154295415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115621295111451414979151093 10839496416698570154295415)
        ·
          refine ⟨16259244625047855231443123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10839496416698570154295415 16259244625047855231443123)
          ·
            refine ⟨24388866937571782847164685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16259244625047855231443123 24388866937571782847164685)
            ·
              refine ⟨9145825101589418567686757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24388866937571782847164685 9145825101589418567686757)
              ·
                refine ⟨1714842206548015981441267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9145825101589418567686757 1714842206548015981441267)
                ·
                  refine ⟨2572263309822023972161901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1714842206548015981441267 2572263309822023972161901)
                  ·
                    refine ⟨964598741183258989560713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572263309822023972161901 964598741183258989560713)
                    ·
                      rfl

theorem cell22_2817824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_2817824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817824 prefixEnd_2817824 := by exact prefixLift 2817824
  have htrace : WordTrace (prefixWord ++ tailWord_2817824) baseStart_2817824 baseEnd_2817824 := by
    simpa [prefixWord, tailWord_2817824, baseEnd_2817824] using wordTrace_append hprefix tailTrace_2817824
  have hstable : (prefixWord ++ tailWord_2817824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817824).length < 2 ^ (prefixWord ++ tailWord_2817824).sum := by decide
  have hdescent : baseEnd_2817824 < baseStart_2817824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817833 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_2817833 : Nat := 118140960795 + 2817833 * 2 ^ 59
def prefixEnd_2817833 : Nat := 4983230072969 + 3 ^ 40 * 2817833 * 2
def baseEnd_2817833 : Nat := 964601822067185966085685

theorem tailTrace_2817833 : CollatzResearch.WordTrace tailWord_2817833 prefixEnd_2817833 964601822067185966085685 := by
  unfold tailWord_2817833
  simp only [CollatzResearch.WordTrace]
  refine ⟨102774812800479763407434153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68516541866986508938289435 102774812800479763407434153)
  ·
    refine ⟨77081109600359822555575615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102774812800479763407434153 77081109600359822555575615)
    ·
      refine ⟨115621664400539733833363423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77081109600359822555575615 115621664400539733833363423)
      ·
        refine ⟨173432496600809600750045135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115621664400539733833363423 173432496600809600750045135)
        ·
          refine ⟨260148744901214401125067703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173432496600809600750045135 260148744901214401125067703)
          ·
            refine ⟨390223117351821601687601555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260148744901214401125067703 390223117351821601687601555)
            ·
              refine ⟨585334676027732402531402333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390223117351821601687601555 585334676027732402531402333)
              ·
                refine ⟨219500503510399650949275875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 585334676027732402531402333 219500503510399650949275875)
                ·
                  refine ⟨329250755265599476423913813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219500503510399650949275875 329250755265599476423913813)
                  ·
                    refine ⟨964601822067185966085685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 329250755265599476423913813 964601822067185966085685)
                    ·
                      rfl

theorem cell22_2817833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_2817833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817833 prefixEnd_2817833 := by exact prefixLift 2817833
  have htrace : WordTrace (prefixWord ++ tailWord_2817833) baseStart_2817833 baseEnd_2817833 := by
    simpa [prefixWord, tailWord_2817833, baseEnd_2817833] using wordTrace_append hprefix tailTrace_2817833
  have hstable : (prefixWord ++ tailWord_2817833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817833).length < 2 ^ (prefixWord ++ tailWord_2817833).sum := by decide
  have hdescent : baseEnd_2817833 < baseStart_2817833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817882 : List Nat := [3, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_2817882 : Nat := 118140960795 + 2817882 * 2 ^ 59
def prefixEnd_2817882 : Nat := 4983230072969 + 3 ^ 40 * 2817882 * 2
def baseEnd_2817882 : Nat := 321539531922855390536845

theorem tailTrace_2817882 : CollatzResearch.WordTrace tailWord_2817882 prefixEnd_2817882 321539531922855390536845 := by
  unfold tailWord_2817882
  simp only [CollatzResearch.WordTrace]
  refine ⟨25694149994325561193991975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68517733318201496517311933 25694149994325561193991975)
  ·
    refine ⟨38541224991488341790987963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25694149994325561193991975 38541224991488341790987963)
    ·
      refine ⟨57811837487232512686481945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38541224991488341790987963 57811837487232512686481945)
      ·
        refine ⟨43358878115424384514861459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57811837487232512686481945 43358878115424384514861459)
        ·
          refine ⟨65038317173136576772292189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43358878115424384514861459 65038317173136576772292189)
          ·
            refine ⟨24389368939926216289609571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65038317173136576772292189 24389368939926216289609571)
            ·
              refine ⟨36584053409889324434414357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24389368939926216289609571 36584053409889324434414357)
              ·
                refine ⟨1714877503588562082863173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36584053409889324434414357 1714877503588562082863173)
                ·
                  refine ⟨321539531922855390536845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1714877503588562082863173 321539531922855390536845)
                  ·
                    rfl

theorem cell22_2817882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_2817882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817882 prefixEnd_2817882 := by exact prefixLift 2817882
  have htrace : WordTrace (prefixWord ++ tailWord_2817882) baseStart_2817882 baseEnd_2817882 := by
    simpa [prefixWord, tailWord_2817882, baseEnd_2817882] using wordTrace_append hprefix tailTrace_2817882
  have hstable : (prefixWord ++ tailWord_2817882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817882).length < 2 ^ (prefixWord ++ tailWord_2817882).sum := by decide
  have hdescent : baseEnd_2817882 < baseStart_2817882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817895 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2817895 : Nat := 118140960795 + 2817895 * 2 ^ 59
def prefixEnd_2817895 : Nat := 4983230072969 + 3 ^ 40 * 2817895 * 2
def baseEnd_2817895 : Nat := 964623045934238471035495

theorem tailTrace_2817895 : CollatzResearch.WordTrace tailWord_2817895 prefixEnd_2817895 964623045934238471035495 := by
  unfold tailWord_2817895
  simp only [CollatzResearch.WordTrace]
  refine ⟨102777074126255147996191139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68518049417503431997460759 102777074126255147996191139)
  ·
    refine ⟨154165611189382721994286709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102777074126255147996191139 154165611189382721994286709)
    ·
      refine ⟨14453026049004630186964379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154165611189382721994286709 14453026049004630186964379)
      ·
        refine ⟨21679539073506945280446569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14453026049004630186964379 21679539073506945280446569)
        ·
          refine ⟨16259654305130208960334927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21679539073506945280446569 16259654305130208960334927)
          ·
            refine ⟨24389481457695313440502391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16259654305130208960334927 24389481457695313440502391)
            ·
              refine ⟨36584222186542970160753587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24389481457695313440502391 36584222186542970160753587)
              ·
                refine ⟨54876333279814455241130381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36584222186542970160753587 54876333279814455241130381)
                ·
                  refine ⟨20578624979930420715423893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54876333279814455241130381 20578624979930420715423893)
                  ·
                    refine ⟨964623045934238471035495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20578624979930420715423893 964623045934238471035495)
                    ·
                      rfl

theorem cell22_2817895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2817895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817895 prefixEnd_2817895 := by exact prefixLift 2817895
  have htrace : WordTrace (prefixWord ++ tailWord_2817895) baseStart_2817895 baseEnd_2817895 := by
    simpa [prefixWord, tailWord_2817895, baseEnd_2817895] using wordTrace_append hprefix tailTrace_2817895
  have hstable : (prefixWord ++ tailWord_2817895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817895).length < 2 ^ (prefixWord ++ tailWord_2817895).sum := by decide
  have hdescent : baseEnd_2817895 < baseStart_2817895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817897 : List Nat := [1, 2, 1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_2817897 : Nat := 118140960795 + 2817897 * 2 ^ 59
def prefixEnd_2817897 : Nat := 4983230072969 + 3 ^ 40 * 2817897 * 2
def baseEnd_2817897 : Nat := 964623730575111132485489

theorem tailTrace_2817897 : CollatzResearch.WordTrace tailWord_2817897 prefixEnd_2817897 964623730575111132485489 := by
  unfold tailWord_2817897
  simp only [CollatzResearch.WordTrace]
  refine ⟨102777147072247902337763945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68518098048165268225175963 102777147072247902337763945)
  ·
    refine ⟨77082860304185926753322959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102777147072247902337763945 77082860304185926753322959)
    ·
      refine ⟨115624290456278890129984439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77082860304185926753322959 115624290456278890129984439)
      ·
        refine ⟨173436435684418335194976659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115624290456278890129984439 173436435684418335194976659)
        ·
          refine ⟨260154653526627502792464989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173436435684418335194976659 260154653526627502792464989)
          ·
            refine ⟨97557995072485313547174371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260154653526627502792464989 97557995072485313547174371)
            ·
              refine ⟨146336992608727970320761557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97557995072485313547174371 146336992608727970320761557)
              ·
                refine ⟨3429773264267061804392849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146336992608727970320761557 3429773264267061804392849)
                ·
                  refine ⟨2572329948200296353294637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429773264267061804392849 2572329948200296353294637)
                  ·
                    refine ⟨964623730575111132485489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572329948200296353294637 964623730575111132485489)
                    ·
                      rfl

theorem cell22_2817897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_2817897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817897 prefixEnd_2817897 := by exact prefixLift 2817897
  have htrace : WordTrace (prefixWord ++ tailWord_2817897) baseStart_2817897 baseEnd_2817897 := by
    simpa [prefixWord, tailWord_2817897, baseEnd_2817897] using wordTrace_append hprefix tailTrace_2817897
  have hstable : (prefixWord ++ tailWord_2817897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817897).length < 2 ^ (prefixWord ++ tailWord_2817897).sum := by decide
  have hdescent : baseEnd_2817897 < baseStart_2817897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817927 : List Nat := [1, 1, 4, 2, 4, 2, 8]
def baseStart_2817927 : Nat := 118140960795 + 2817927 * 2 ^ 59
def prefixEnd_2817927 : Nat := 4983230072969 + 3 ^ 40 * 2817927 * 2
def baseEnd_2817927 : Nat := 35727185192155594601311

theorem tailTrace_2817927 : CollatzResearch.WordTrace tailWord_2817927 prefixEnd_2817927 35727185192155594601311 := by
  unfold tailWord_2817927
  simp only [CollatzResearch.WordTrace]
  refine ⟨102778241262139217461356035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68518827508092811640904023 102778241262139217461356035)
  ·
    refine ⟨154167361893208826192034053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102778241262139217461356035 154167361893208826192034053)
    ·
      refine ⟨28906380354976654911006385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154167361893208826192034053 28906380354976654911006385)
      ·
        refine ⟨21679785266232491183254789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28906380354976654911006385 21679785266232491183254789)
        ·
          refine ⟨4064959737418592096860273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21679785266232491183254789 4064959737418592096860273)
          ·
            refine ⟨3048719803063944072645205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4064959737418592096860273 3048719803063944072645205)
            ·
              refine ⟨35727185192155594601311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3048719803063944072645205 35727185192155594601311)
              ·
                rfl

theorem cell22_2817927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 8].length) (baseStart_2817927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817927 prefixEnd_2817927 := by exact prefixLift 2817927
  have htrace : WordTrace (prefixWord ++ tailWord_2817927) baseStart_2817927 baseEnd_2817927 := by
    simpa [prefixWord, tailWord_2817927, baseEnd_2817927] using wordTrace_append hprefix tailTrace_2817927
  have hstable : (prefixWord ++ tailWord_2817927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817927).length < 2 ^ (prefixWord ++ tailWord_2817927).sum := by decide
  have hdescent : baseEnd_2817927 < baseStart_2817927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817944 : List Nat := [2, 1, 2, 6, 1, 1, 2, 7]
def baseStart_2817944 : Nat := 118140960795 + 2817944 * 2 ^ 59
def prefixEnd_2817944 : Nat := 4983230072969 + 3 ^ 40 * 2817944 * 2
def baseEnd_2817944 : Nat := 107182202181735408506705

theorem tailTrace_2817944 : CollatzResearch.WordTrace tailWord_2817944 prefixEnd_2817944 107182202181735408506705 := by
  unfold tailWord_2817944
  simp only [CollatzResearch.WordTrace]
  refine ⟨51389430651538814682362443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68519240868718419576483257 51389430651538814682362443)
  ·
    refine ⟨77084145977308222023543665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51389430651538814682362443 77084145977308222023543665)
    ·
      refine ⟨57813109482981166517657749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77084145977308222023543665 57813109482981166517657749)
      ·
        refine ⟨2709989507014742180515207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57813109482981166517657749 2709989507014742180515207)
        ·
          refine ⟨4064984260522113270772811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709989507014742180515207 4064984260522113270772811)
          ·
            refine ⟨6097476390783169906159217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064984260522113270772811 6097476390783169906159217)
            ·
              refine ⟨4573107293087377429619413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6097476390783169906159217 4573107293087377429619413)
              ·
                refine ⟨107182202181735408506705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4573107293087377429619413 107182202181735408506705)
                ·
                  rfl

theorem cell22_2817944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_2817944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817944 prefixEnd_2817944 := by exact prefixLift 2817944
  have htrace : WordTrace (prefixWord ++ tailWord_2817944) baseStart_2817944 baseEnd_2817944 := by
    simpa [prefixWord, tailWord_2817944, baseEnd_2817944] using wordTrace_append hprefix tailTrace_2817944
  have hstable : (prefixWord ++ tailWord_2817944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817944).length < 2 ^ (prefixWord ++ tailWord_2817944).sum := by decide
  have hdescent : baseEnd_2817944 < baseStart_2817944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2817948 : List Nat := [2, 2, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2817948 : Nat := 118140960795 + 2817948 * 2 ^ 59
def prefixEnd_2817948 : Nat := 4983230072969 + 3 ^ 40 * 2817948 * 2
def baseEnd_2817948 : Nat := 964641188917363999460333

theorem tailTrace_2817948 : CollatzResearch.WordTrace tailWord_2817948 prefixEnd_2817948 964641188917363999460333 := by
  unfold tailWord_2817948
  simp only [CollatzResearch.WordTrace]
  refine ⟨51389503597531569023935249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68519338130042092031913665 51389503597531569023935249)
  ·
    refine ⟨38542127698148676767951437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51389503597531569023935249 38542127698148676767951437)
    ·
      refine ⟨14453297886805753787981789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38542127698148676767951437 14453297886805753787981789)
      ·
        refine ⟨5419986707552157670493171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14453297886805753787981789 5419986707552157670493171)
        ·
          refine ⟨8129980061328236505739757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5419986707552157670493171 8129980061328236505739757)
          ·
            refine ⟨3048742522998088689652409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8129980061328236505739757 3048742522998088689652409)
            ·
              refine ⟨2286556892248566517239307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048742522998088689652409 2286556892248566517239307)
              ·
                refine ⟨3429835338372849775858961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286556892248566517239307 3429835338372849775858961)
                ·
                  refine ⟨2572376503779637331894221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429835338372849775858961 2572376503779637331894221)
                  ·
                    refine ⟨964641188917363999460333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572376503779637331894221 964641188917363999460333)
                    ·
                      rfl

theorem cell22_2817948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2817948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2817948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2817948 prefixEnd_2817948 := by exact prefixLift 2817948
  have htrace : WordTrace (prefixWord ++ tailWord_2817948) baseStart_2817948 baseEnd_2817948 := by
    simpa [prefixWord, tailWord_2817948, baseEnd_2817948] using wordTrace_append hprefix tailTrace_2817948
  have hstable : (prefixWord ++ tailWord_2817948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2817948).length < 2 ^ (prefixWord ++ tailWord_2817948).sum := by decide
  have hdescent : baseEnd_2817948 < baseStart_2817948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2817948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818032 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_2818032 : Nat := 118140960795 + 2818032 * 2 ^ 59
def prefixEnd_2818032 : Nat := 4983230072969 + 3 ^ 40 * 2818032 * 2
def baseEnd_2818032 : Nat := 964669943834015780360075

theorem tailTrace_2818032 : CollatzResearch.WordTrace tailWord_2818032 prefixEnd_2818032 964669943834015780360075 := by
  unfold tailWord_2818032
  simp only [CollatzResearch.WordTrace]
  refine ⟨51391035463379410196964175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68521380617839213595952233 51391035463379410196964175)
  ·
    refine ⟨77086553195069115295446263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51391035463379410196964175 77086553195069115295446263)
    ·
      refine ⟨115629829792603672943169395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77086553195069115295446263 115629829792603672943169395)
      ·
        refine ⟨173444744688905509414754093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115629829792603672943169395 173444744688905509414754093)
        ·
          refine ⟨65041779258339566030532785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173444744688905509414754093 65041779258339566030532785)
          ·
            refine ⟨48781334443754674522899589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65041779258339566030532785 48781334443754674522899589)
            ·
              refine ⟨9146500208204001473043673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48781334443754674522899589 9146500208204001473043673)
              ·
                refine ⟨6859875156153001104782755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9146500208204001473043673 6859875156153001104782755)
                ·
                  refine ⟨10289812734229501657174133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6859875156153001104782755 10289812734229501657174133)
                  ·
                    refine ⟨964669943834015780360075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10289812734229501657174133 964669943834015780360075)
                    ·
                      rfl

theorem cell22_2818032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_2818032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818032 prefixEnd_2818032 := by exact prefixLift 2818032
  have htrace : WordTrace (prefixWord ++ tailWord_2818032) baseStart_2818032 baseEnd_2818032 := by
    simpa [prefixWord, tailWord_2818032, baseEnd_2818032] using wordTrace_append hprefix tailTrace_2818032
  have hstable : (prefixWord ++ tailWord_2818032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818032).length < 2 ^ (prefixWord ++ tailWord_2818032).sum := by decide
  have hdescent : baseEnd_2818032 < baseStart_2818032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818047 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 2, 4]
def baseStart_2818047 : Nat := 118140960795 + 2818047 * 2 ^ 59
def prefixEnd_2818047 : Nat := 4983230072969 + 3 ^ 40 * 2818047 * 2
def baseEnd_2818047 : Nat := 964675078640560741235029

theorem tailTrace_2818047 : CollatzResearch.WordTrace tailWord_2818047 prefixEnd_2818047 964675078640560741235029 := by
  unfold tailWord_2818047
  simp only [CollatzResearch.WordTrace]
  refine ⟨102782618021704477955724395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68521745347802985303816263 102782618021704477955724395)
  ·
    refine ⟨154173927032556716933586593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102782618021704477955724395 154173927032556716933586593)
    ·
      refine ⟨115630445274417537700189945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154173927032556716933586593 115630445274417537700189945)
      ·
        refine ⟨86722833955813153275142459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115630445274417537700189945 86722833955813153275142459)
        ·
          refine ⟨130084250933719729912713689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86722833955813153275142459 130084250933719729912713689)
          ·
            refine ⟨97563188200289797434535267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130084250933719729912713689 97563188200289797434535267)
            ·
              refine ⟨146344782300434696151802901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97563188200289797434535267 146344782300434696151802901)
              ·
                refine ⟨6859911670332876382115761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146344782300434696151802901 6859911670332876382115761)
                ·
                  refine ⟨5144933752749657286586821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6859911670332876382115761 5144933752749657286586821)
                  ·
                    refine ⟨964675078640560741235029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5144933752749657286586821 964675078640560741235029)
                    ·
                      rfl

theorem cell22_2818047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_2818047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818047 prefixEnd_2818047 := by exact prefixLift 2818047
  have htrace : WordTrace (prefixWord ++ tailWord_2818047) baseStart_2818047 baseEnd_2818047 := by
    simpa [prefixWord, tailWord_2818047, baseEnd_2818047] using wordTrace_append hprefix tailTrace_2818047
  have hstable : (prefixWord ++ tailWord_2818047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818047).length < 2 ^ (prefixWord ++ tailWord_2818047).sum := by decide
  have hdescent : baseEnd_2818047 < baseStart_2818047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818049 : List Nat := [1, 2, 4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_2818049 : Nat := 118140960795 + 2818049 * 2 ^ 59
def prefixEnd_2818049 : Nat := 4983230072969 + 3 ^ 40 * 2818049 * 2
def baseEnd_2818049 : Nat := 964675763281433402685023

theorem tailTrace_2818049 : CollatzResearch.WordTrace tailWord_2818049 prefixEnd_2818049 964675763281433402685023 := by
  unfold tailWord_2818049
  simp only [CollatzResearch.WordTrace]
  refine ⟨102782690967697232297297201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68521793978464821531531467 102782690967697232297297201)
  ·
    refine ⟨77087018225772924222972901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102782690967697232297297201 77087018225772924222972901)
    ·
      refine ⟨14453815917332423291807419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77087018225772924222972901 14453815917332423291807419)
      ·
        refine ⟨21680723875998634937711129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14453815917332423291807419 21680723875998634937711129)
        ·
          refine ⟨16260542906998976203283347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21680723875998634937711129 16260542906998976203283347)
          ·
            refine ⟨24390814360498464304925021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16260542906998976203283347 24390814360498464304925021)
            ·
              refine ⟨9146555385186924114346883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24390814360498464304925021 9146555385186924114346883)
              ·
                refine ⟨13719833077780386171520325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9146555385186924114346883 13719833077780386171520325)
                ·
                  refine ⟨2572468702083822407160061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13719833077780386171520325 2572468702083822407160061)
                  ·
                    refine ⟨964675763281433402685023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572468702083822407160061 964675763281433402685023)
                    ·
                      rfl

theorem cell22_2818049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_2818049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818049 prefixEnd_2818049 := by exact prefixLift 2818049
  have htrace : WordTrace (prefixWord ++ tailWord_2818049) baseStart_2818049 baseEnd_2818049 := by
    simpa [prefixWord, tailWord_2818049, baseEnd_2818049] using wordTrace_append hprefix tailTrace_2818049
  have hstable : (prefixWord ++ tailWord_2818049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818049).length < 2 ^ (prefixWord ++ tailWord_2818049).sum := by decide
  have hdescent : baseEnd_2818049 < baseStart_2818049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818062 : List Nat := [4, 1, 1, 2, 2, 1, 2, 9]
def baseStart_2818062 : Nat := 118140960795 + 2818062 * 2 ^ 59
def prefixEnd_2818062 : Nat := 4983230072969 + 3 ^ 40 * 2818062 * 2
def baseEnd_2818062 : Nat := 107186690383011744678887

theorem tailTrace_2818062 : CollatzResearch.WordTrace tailWord_2818062 prefixEnd_2818062 107186690383011744678887 := by
  unfold tailWord_2818062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12847895639581266939690055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68522110077766757011680293 12847895639581266939690055)
  ·
    refine ⟨19271843459371900409535083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12847895639581266939690055 19271843459371900409535083)
    ·
      refine ⟨28907765189057850614302625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19271843459371900409535083 28907765189057850614302625)
      ·
        refine ⟨21680823891793387960726969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28907765189057850614302625 21680823891793387960726969)
        ·
          refine ⟨16260617918845040970545227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21680823891793387960726969 16260617918845040970545227)
          ·
            refine ⟨24390926878267561455817841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16260617918845040970545227 24390926878267561455817841)
            ·
              refine ⟨18293195158700671091863381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24390926878267561455817841 18293195158700671091863381)
              ·
                refine ⟨107186690383011744678887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18293195158700671091863381 107186690383011744678887)
                ·
                  rfl

theorem cell22_2818062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_2818062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818062 prefixEnd_2818062 := by exact prefixLift 2818062
  have htrace : WordTrace (prefixWord ++ tailWord_2818062) baseStart_2818062 baseEnd_2818062 := by
    simpa [prefixWord, tailWord_2818062, baseEnd_2818062] using wordTrace_append hprefix tailTrace_2818062
  have hstable : (prefixWord ++ tailWord_2818062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818062).length < 2 ^ (prefixWord ++ tailWord_2818062).sum := by decide
  have hdescent : baseEnd_2818062 < baseStart_2818062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818111 : List Nat := [1, 1, 2, 2, 3, 1, 2, 6, 1, 3]
def baseStart_2818111 : Nat := 118140960795 + 2818111 * 2 ^ 59
def prefixEnd_2818111 : Nat := 4983230072969 + 3 ^ 40 * 2818111 * 2
def baseEnd_2818111 : Nat := 964696987148485907634833

theorem tailTrace_2818111 : CollatzResearch.WordTrace tailWord_2818111 prefixEnd_2818111 964696987148485907634833 := by
  unfold tailWord_2818111
  simp only [CollatzResearch.WordTrace]
  refine ⟨102784952293472616886054187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68523301528981744590702791 102784952293472616886054187)
  ·
    refine ⟨154177428440208925329081281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102784952293472616886054187 154177428440208925329081281)
    ·
      refine ⟨115633071330156693996810961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154177428440208925329081281 115633071330156693996810961)
      ·
        refine ⟨86724803497617520497608221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115633071330156693996810961 86724803497617520497608221)
        ·
          refine ⟨32521801311606570186603083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86724803497617520497608221 32521801311606570186603083)
          ·
            refine ⟨48782701967409855279904625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32521801311606570186603083 48782701967409855279904625)
            ·
              refine ⟨36587026475557391459928469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48782701967409855279904625 36587026475557391459928469)
              ·
                refine ⟨1715016866041752724684147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36587026475557391459928469 1715016866041752724684147)
                ·
                  refine ⟨2572525299062629087026221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1715016866041752724684147 2572525299062629087026221)
                  ·
                    refine ⟨964696987148485907634833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572525299062629087026221 964696987148485907634833)
                    ·
                      rfl

theorem cell22_2818111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_2818111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818111 prefixEnd_2818111 := by exact prefixLift 2818111
  have htrace : WordTrace (prefixWord ++ tailWord_2818111) baseStart_2818111 baseEnd_2818111 := by
    simpa [prefixWord, tailWord_2818111, baseEnd_2818111] using wordTrace_append hprefix tailTrace_2818111
  have hstable : (prefixWord ++ tailWord_2818111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818111).length < 2 ^ (prefixWord ++ tailWord_2818111).sum := by decide
  have hdescent : baseEnd_2818111 < baseStart_2818111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818122 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_2818122 : Nat := 118140960795 + 2818122 * 2 ^ 59
def prefixEnd_2818122 : Nat := 4983230072969 + 3 ^ 40 * 2818122 * 2
def baseEnd_2818122 : Nat := 964700752673285545609799

theorem tailTrace_2818122 : CollatzResearch.WordTrace tailWord_2818122 prefixEnd_2818122 964700752673285545609799 := by
  unfold tailWord_2818122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25696338374108191441176155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68523568997621843843136413 25696338374108191441176155)
  ·
    refine ⟨38544507561162287161764233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25696338374108191441176155 38544507561162287161764233)
    ·
      refine ⟨28908380670871715371323175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38544507561162287161764233 28908380670871715371323175)
      ·
        refine ⟨43362571006307573056984763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28908380670871715371323175 43362571006307573056984763)
        ·
          refine ⟨65043856509461359585477145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43362571006307573056984763 65043856509461359585477145)
          ·
            refine ⟨48782892382096019689107859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65043856509461359585477145 48782892382096019689107859)
            ·
              refine ⟨73174338573144029533661789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48782892382096019689107859 73174338573144029533661789)
              ·
                refine ⟨27440376964929011075123171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73174338573144029533661789 27440376964929011075123171)
                ·
                  refine ⟨41160565447393516612684757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27440376964929011075123171 41160565447393516612684757)
                  ·
                    refine ⟨964700752673285545609799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41160565447393516612684757 964700752673285545609799)
                    ·
                      rfl

theorem cell22_2818122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_2818122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818122 prefixEnd_2818122 := by exact prefixLift 2818122
  have htrace : WordTrace (prefixWord ++ tailWord_2818122) baseStart_2818122 baseEnd_2818122 := by
    simpa [prefixWord, tailWord_2818122, baseEnd_2818122] using wordTrace_append hprefix tailTrace_2818122
  have hstable : (prefixWord ++ tailWord_2818122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818122).length < 2 ^ (prefixWord ++ tailWord_2818122).sum := by decide
  have hdescent : baseEnd_2818122 < baseStart_2818122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818304 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_2818304 : Nat := 118140960795 + 2818304 * 2 ^ 59
def prefixEnd_2818304 : Nat := 4983230072969 + 3 ^ 40 * 2818304 * 2
def baseEnd_2818304 : Nat := 321587684997565912519747

theorem tailTrace_2818304 : CollatzResearch.WordTrace tailWord_2818304 prefixEnd_2818304 321587684997565912519747 := by
  unfold tailWord_2818304
  simp only [CollatzResearch.WordTrace]
  refine ⟨51395995790886705423914983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68527994387848940565219977 51395995790886705423914983)
  ·
    refine ⟨77093993686330058135872475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51395995790886705423914983 77093993686330058135872475)
    ·
      refine ⟨115640990529495087203808713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77093993686330058135872475 115640990529495087203808713)
      ·
        refine ⟨86730742897121315402856535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115640990529495087203808713 86730742897121315402856535)
        ·
          refine ⟨130096114345681973104284803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86730742897121315402856535 130096114345681973104284803)
          ·
            refine ⟨195144171518522959656427205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130096114345681973104284803 195144171518522959656427205)
            ·
              refine ⟨36589532159723054935580101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195144171518522959656427205 36589532159723054935580101)
              ·
                refine ⟨6860537279948072800421269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36589532159723054935580101 6860537279948072800421269)
                ·
                  refine ⟨321587684997565912519747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6860537279948072800421269 321587684997565912519747)
                  ·
                    rfl

theorem cell22_2818304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_2818304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818304 prefixEnd_2818304 := by exact prefixLift 2818304
  have htrace : WordTrace (prefixWord ++ tailWord_2818304) baseStart_2818304 baseEnd_2818304 := by
    simpa [prefixWord, tailWord_2818304, baseEnd_2818304] using wordTrace_append hprefix tailTrace_2818304
  have hstable : (prefixWord ++ tailWord_2818304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818304).length < 2 ^ (prefixWord ++ tailWord_2818304).sum := by decide
  have hdescent : baseEnd_2818304 < baseStart_2818304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818353 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2818353 : Nat := 118140960795 + 2818353 * 2 ^ 59
def prefixEnd_2818353 : Nat := 4983230072969 + 3 ^ 40 * 2818353 * 2
def baseEnd_2818353 : Nat := 964779828694077943084091

theorem tailTrace_2818353 : CollatzResearch.WordTrace tailWord_2818353 prefixEnd_2818353 964779828694077943084091 := by
  unfold tailWord_2818353
  simp only [CollatzResearch.WordTrace]
  refine ⟨102793778758595892216363713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68529185839063928144242475 102793778758595892216363713)
  ·
    refine ⟨77095334068946919162272785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102793778758595892216363713 77095334068946919162272785)
    ·
      refine ⟨57821500551710189371704589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77095334068946919162272785 57821500551710189371704589)
      ·
        refine ⟨21683062706891321014389221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57821500551710189371704589 21683062706891321014389221)
        ·
          refine ⟨4065574257542122690197979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21683062706891321014389221 4065574257542122690197979)
          ·
            refine ⟨6098361386313184035296969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065574257542122690197979 6098361386313184035296969)
            ·
              refine ⟨4573771039734888026472727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6098361386313184035296969 4573771039734888026472727)
              ·
                refine ⟨6860656559602332039709091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573771039734888026472727 6860656559602332039709091)
                ·
                  refine ⟨10290984839403498059563637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6860656559602332039709091 10290984839403498059563637)
                  ·
                    refine ⟨964779828694077943084091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10290984839403498059563637 964779828694077943084091)
                    ·
                      rfl

theorem cell22_2818353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2818353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818353 prefixEnd_2818353 := by exact prefixLift 2818353
  have htrace : WordTrace (prefixWord ++ tailWord_2818353) baseStart_2818353 baseEnd_2818353 := by
    simpa [prefixWord, tailWord_2818353, baseEnd_2818353] using wordTrace_append hprefix tailTrace_2818353
  have hstable : (prefixWord ++ tailWord_2818353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818353).length < 2 ^ (prefixWord ++ tailWord_2818353).sum := by decide
  have hdescent : baseEnd_2818353 < baseStart_2818353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818372 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 4]
def baseStart_2818372 : Nat := 118140960795 + 2818372 * 2 ^ 59
def prefixEnd_2818372 : Nat := 4983230072969 + 3 ^ 40 * 2818372 * 2
def baseEnd_2818372 : Nat := 321595444260789408953011

theorem tailTrace_2818372 : CollatzResearch.WordTrace tailWord_2818372 prefixEnd_2818372 321595444260789408953011 := by
  unfold tailWord_2818372
  simp only [CollatzResearch.WordTrace]
  refine ⟨51397235872763529230652685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68529647830351372307536913 51397235872763529230652685)
  ·
    refine ⟨19273963452286323461494757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51397235872763529230652685 19273963452286323461494757)
    ·
      refine ⟨3613868147303685649030267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19273963452286323461494757 3613868147303685649030267)
      ·
        refine ⟨5420802220955528473545401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613868147303685649030267 5420802220955528473545401)
        ·
          refine ⟨4065601665716646355159051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5420802220955528473545401 4065601665716646355159051)
          ·
            refine ⟨6098402498574969532738577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065601665716646355159051 6098402498574969532738577)
            ·
              refine ⟨4573801873931227149553933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6098402498574969532738577 4573801873931227149553933)
              ·
                refine ⟨1715175702724210181082725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4573801873931227149553933 1715175702724210181082725)
                ·
                  refine ⟨321595444260789408953011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1715175702724210181082725 321595444260789408953011)
                  ·
                    rfl

theorem cell22_2818372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_2818372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818372 prefixEnd_2818372 := by exact prefixLift 2818372
  have htrace : WordTrace (prefixWord ++ tailWord_2818372) baseStart_2818372 baseEnd_2818372 := by
    simpa [prefixWord, tailWord_2818372, baseEnd_2818372] using wordTrace_append hprefix tailTrace_2818372
  have hstable : (prefixWord ++ tailWord_2818372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818372).length < 2 ^ (prefixWord ++ tailWord_2818372).sum := by decide
  have hdescent : baseEnd_2818372 < baseStart_2818372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818379 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_2818379 : Nat := 118140960795 + 2818379 * 2 ^ 59
def prefixEnd_2818379 : Nat := 4983230072969 + 3 ^ 40 * 2818379 * 2
def baseEnd_2818379 : Nat := 964788729025422541934011

theorem tailTrace_2818379 : CollatzResearch.WordTrace tailWord_2818379 prefixEnd_2818379 964788729025422541934011 := by
  unfold tailWord_2818379
  simp only [CollatzResearch.WordTrace]
  refine ⟨102794727056501698656810191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68529818037667799104540127 102794727056501698656810191)
  ·
    refine ⟨154192090584752547985215287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102794727056501698656810191 154192090584752547985215287)
    ·
      refine ⟨231288135877128821977822931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154192090584752547985215287 231288135877128821977822931)
      ·
        refine ⟨346932203815693232966734397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231288135877128821977822931 346932203815693232966734397)
        ·
          refine ⟨130099576430884962362525399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346932203815693232966734397 130099576430884962362525399)
          ·
            refine ⟨195149364646327443543788099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130099576430884962362525399 195149364646327443543788099)
            ·
              refine ⟨292724046969491165315682149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195149364646327443543788099 292724046969491165315682149)
              ·
                refine ⟨54885758806779593496690403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292724046969491165315682149 54885758806779593496690403)
                ·
                  refine ⟨82328638210169390245035605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54885758806779593496690403 82328638210169390245035605)
                  ·
                    refine ⟨964788729025422541934011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82328638210169390245035605 964788729025422541934011)
                    ·
                      rfl

theorem cell22_2818379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_2818379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818379 prefixEnd_2818379 := by exact prefixLift 2818379
  have htrace : WordTrace (prefixWord ++ tailWord_2818379) baseStart_2818379 baseEnd_2818379 := by
    simpa [prefixWord, tailWord_2818379, baseEnd_2818379] using wordTrace_append hprefix tailTrace_2818379
  have hstable : (prefixWord ++ tailWord_2818379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818379).length < 2 ^ (prefixWord ++ tailWord_2818379).sum := by decide
  have hdescent : baseEnd_2818379 < baseStart_2818379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818462 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2818462 : Nat := 118140960795 + 2818462 * 2 ^ 59
def prefixEnd_2818462 : Nat := 4983230072969 + 3 ^ 40 * 2818462 * 2
def baseEnd_2818462 : Nat := 321605713873879330702919

theorem tailTrace_2818462 : CollatzResearch.WordTrace tailWord_2818462 prefixEnd_2818462 321605713873879330702919 := by
  unfold tailWord_2818462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12849719289400125479010205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68531836210134002554721093 12849719289400125479010205)
  ·
    refine ⟨4818644733525047054628827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12849719289400125479010205 4818644733525047054628827)
    ·
      refine ⟨7227967100287570581943241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818644733525047054628827 7227967100287570581943241)
      ·
        refine ⟨5420975325215677936457431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7227967100287570581943241 5420975325215677936457431)
        ·
          refine ⟨8131462987823516904686147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420975325215677936457431 8131462987823516904686147)
          ·
            refine ⟨12197194481735275357029221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8131462987823516904686147 12197194481735275357029221)
            ·
              refine ⟨2286973965325364129442979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12197194481735275357029221 2286973965325364129442979)
              ·
                refine ⟨3430460947988046194164469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286973965325364129442979 3430460947988046194164469)
                ·
                  refine ⟨321605713873879330702919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3430460947988046194164469 321605713873879330702919)
                  ·
                    rfl

theorem cell22_2818462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2818462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818462 prefixEnd_2818462 := by exact prefixLift 2818462
  have htrace : WordTrace (prefixWord ++ tailWord_2818462) baseStart_2818462 baseEnd_2818462 := by
    simpa [prefixWord, tailWord_2818462, baseEnd_2818462] using wordTrace_append hprefix tailTrace_2818462
  have hstable : (prefixWord ++ tailWord_2818462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818462).length < 2 ^ (prefixWord ++ tailWord_2818462).sum := by decide
  have hdescent : baseEnd_2818462 < baseStart_2818462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818492 : List Nat := [2, 2, 2, 4, 1, 2, 3, 1, 1, 4]
def baseStart_2818492 : Nat := 118140960795 + 2818492 * 2 ^ 59
def prefixEnd_2818492 : Nat := 4983230072969 + 3 ^ 40 * 2818492 * 2
def baseEnd_2818492 : Nat := 964827411234727913858665

theorem tailTrace_2818492 : CollatzResearch.WordTrace tailWord_2818492 prefixEnd_2818492 964827411234727913858665 := by
  unfold tailWord_2818492
  simp only [CollatzResearch.WordTrace]
  refine ⟨51399424252546159477836865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68532565670061545970449153 51399424252546159477836865)
  ·
    refine ⟨38549568189409619608377649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51399424252546159477836865 38549568189409619608377649)
    ·
      refine ⟨28912176142057214706283237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38549568189409619608377649 28912176142057214706283237)
      ·
        refine ⟨5421033026635727757428107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28912176142057214706283237 5421033026635727757428107)
        ·
          refine ⟨8131549539953591636142161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5421033026635727757428107 8131549539953591636142161)
          ·
            refine ⟨6098662154965193727106621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8131549539953591636142161 6098662154965193727106621)
            ·
              refine ⟨2286998308111947647664983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6098662154965193727106621 2286998308111947647664983)
              ·
                refine ⟨3430497462167921471497475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286998308111947647664983 3430497462167921471497475)
                ·
                  refine ⟨5145746193251882207246213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430497462167921471497475 5145746193251882207246213)
                  ·
                    refine ⟨964827411234727913858665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145746193251882207246213 964827411234727913858665)
                    ·
                      rfl

theorem cell22_2818492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_2818492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818492 prefixEnd_2818492 := by exact prefixLift 2818492
  have htrace : WordTrace (prefixWord ++ tailWord_2818492) baseStart_2818492 baseEnd_2818492 := by
    simpa [prefixWord, tailWord_2818492, baseEnd_2818492] using wordTrace_append hprefix tailTrace_2818492
  have hstable : (prefixWord ++ tailWord_2818492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818492).length < 2 ^ (prefixWord ++ tailWord_2818492).sum := by decide
  have hdescent : baseEnd_2818492 < baseStart_2818492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818503 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2818503 : Nat := 118140960795 + 2818503 * 2 ^ 59
def prefixEnd_2818503 : Nat := 4983230072969 + 3 ^ 40 * 2818503 * 2
def baseEnd_2818503 : Nat := 964831176759527551833631

theorem tailTrace_2818503 : CollatzResearch.WordTrace tailWord_2818503 prefixEnd_2818503 964831176759527551833631 := by
  unfold tailWord_2818503
  simp only [CollatzResearch.WordTrace]
  refine ⟨102799249708052467834324163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68532833138701645222882775 102799249708052467834324163)
  ·
    refine ⟨154198874562078701751486245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102799249708052467834324163 154198874562078701751486245)
    ·
      refine ⟨28912288980389756578403671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154198874562078701751486245 28912288980389756578403671)
      ·
        refine ⟨43368433470584634867605507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28912288980389756578403671 43368433470584634867605507)
        ·
          refine ⟨65052650205876952301408261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43368433470584634867605507 65052650205876952301408261)
          ·
            refine ⟨12197371913601928556514049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65052650205876952301408261 12197371913601928556514049)
            ·
              refine ⟨9148028935201446417385537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12197371913601928556514049 9148028935201446417385537)
              ·
                refine ⟨6861021701401084813039153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148028935201446417385537 6861021701401084813039153)
                ·
                  refine ⟨5145766276050813609779365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6861021701401084813039153 5145766276050813609779365)
                  ·
                    refine ⟨964831176759527551833631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145766276050813609779365 964831176759527551833631)
                    ·
                      rfl

theorem cell22_2818503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2818503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818503 prefixEnd_2818503 := by exact prefixLift 2818503
  have htrace : WordTrace (prefixWord ++ tailWord_2818503) baseStart_2818503 baseEnd_2818503 := by
    simpa [prefixWord, tailWord_2818503, baseEnd_2818503] using wordTrace_append hprefix tailTrace_2818503
  have hstable : (prefixWord ++ tailWord_2818503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818503).length < 2 ^ (prefixWord ++ tailWord_2818503).sum := by decide
  have hdescent : baseEnd_2818503 < baseStart_2818503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818550 : List Nat := [5, 1, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_2818550 : Nat := 118140960795 + 2818550 * 2 ^ 59
def prefixEnd_2818550 : Nat := 4983230072969 + 3 ^ 40 * 2818550 * 2
def baseEnd_2818550 : Nat := 964847265820035095908487

theorem tailTrace_2818550 : CollatzResearch.WordTrace tailWord_2818550 prefixEnd_2818550 964847265820035095908487 := by
  unfold tailWord_2818550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6425060246180137178830319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68533975959254796574190069 6425060246180137178830319)
  ·
    refine ⟨9637590369270205768245479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6425060246180137178830319 9637590369270205768245479)
    ·
      refine ⟨14456385553905308652368219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9637590369270205768245479 14456385553905308652368219)
      ·
        refine ⟨21684578330857962978552329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14456385553905308652368219 21684578330857962978552329)
        ·
          refine ⟨16263433748143472233914247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21684578330857962978552329 16263433748143472233914247)
          ·
            refine ⟨24395150622215208350871371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16263433748143472233914247 24395150622215208350871371)
            ·
              refine ⟨36592725933322812526307057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24395150622215208350871371 36592725933322812526307057)
              ·
                refine ⟨27444544449992109394730293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36592725933322812526307057 27444544449992109394730293)
                ·
                  refine ⟨2572926042186760255755965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27444544449992109394730293 2572926042186760255755965)
                  ·
                    refine ⟨964847265820035095908487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572926042186760255755965 964847265820035095908487)
                    ·
                      rfl

theorem cell22_2818550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_2818550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818550 prefixEnd_2818550 := by exact prefixLift 2818550
  have htrace : WordTrace (prefixWord ++ tailWord_2818550) baseStart_2818550 baseEnd_2818550 := by
    simpa [prefixWord, tailWord_2818550, baseEnd_2818550] using wordTrace_append hprefix tailTrace_2818550
  have hstable : (prefixWord ++ tailWord_2818550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818550).length < 2 ^ (prefixWord ++ tailWord_2818550).sum := by decide
  have hdescent : baseEnd_2818550 < baseStart_2818550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818567 : List Nat := [1, 1, 4, 3, 3, 1, 2, 1, 3, 3]
def baseStart_2818567 : Nat := 118140960795 + 2818567 * 2 ^ 59
def prefixEnd_2818567 : Nat := 4983230072969 + 3 ^ 40 * 2818567 * 2
def baseEnd_2818567 : Nat := 964853085267452718233435

theorem tailTrace_2818567 : CollatzResearch.WordTrace tailWord_2818567 prefixEnd_2818567 964853085267452718233435 := by
  unfold tailWord_2818567
  simp only [CollatzResearch.WordTrace]
  refine ⟨102801583979820606764653955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68534389319880404509769303 102801583979820606764653955)
  ·
    refine ⟨154202375969730910146980933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102801583979820606764653955 154202375969730910146980933)
    ·
      refine ⟨28912945494324545652558925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154202375969730910146980933 28912945494324545652558925)
      ·
        refine ⟨10842354560371704619709597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28912945494324545652558925 10842354560371704619709597)
        ·
          refine ⟨4065882960139389232391099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10842354560371704619709597 4065882960139389232391099)
          ·
            refine ⟨6098824440209083848586649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4065882960139389232391099 6098824440209083848586649)
            ·
              refine ⟨4574118330156812886439987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6098824440209083848586649 4574118330156812886439987)
              ·
                refine ⟨6861177495235219329659981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574118330156812886439987 6861177495235219329659981)
                ·
                  refine ⟨2572941560713207248622493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6861177495235219329659981 2572941560713207248622493)
                  ·
                    refine ⟨964853085267452718233435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2572941560713207248622493 964853085267452718233435)
                    ·
                      rfl

theorem cell22_2818567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_2818567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818567 prefixEnd_2818567 := by exact prefixLift 2818567
  have htrace : WordTrace (prefixWord ++ tailWord_2818567) baseStart_2818567 baseEnd_2818567 := by
    simpa [prefixWord, tailWord_2818567, baseEnd_2818567] using wordTrace_append hprefix tailTrace_2818567
  have hstable : (prefixWord ++ tailWord_2818567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818567).length < 2 ^ (prefixWord ++ tailWord_2818567).sum := by decide
  have hdescent : baseEnd_2818567 < baseStart_2818567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818610 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_2818610 : Nat := 118140960795 + 2818610 * 2 ^ 59
def prefixEnd_2818610 : Nat := 4983230072969 + 3 ^ 40 * 2818610 * 2
def baseEnd_2818610 : Nat := 964867805046214939408303

theorem tailTrace_2818610 : CollatzResearch.WordTrace tailWord_2818610 prefixEnd_2818610 964867805046214939408303 := by
  unfold tailWord_2818610
  simp only [CollatzResearch.WordTrace]
  refine ⟨25700788079666206277117321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68535434879109883405646189 25700788079666206277117321)
  ·
    refine ⟨19275591059749654707837991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25700788079666206277117321 19275591059749654707837991)
    ·
      refine ⟨28913386589624482061756987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19275591059749654707837991 28913386589624482061756987)
      ·
        refine ⟨43370079884436723092635481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28913386589624482061756987 43370079884436723092635481)
        ·
          refine ⟨32527559913327542319476611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43370079884436723092635481 32527559913327542319476611)
          ·
            refine ⟨48791339869991313479214917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32527559913327542319476611 48791339869991313479214917)
            ·
              refine ⟨9148376225623371277352797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48791339869991313479214917 9148376225623371277352797)
              ·
                refine ⟨3430641084608764229007299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9148376225623371277352797 3430641084608764229007299)
                ·
                  refine ⟨5145961626913146343510949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430641084608764229007299 5145961626913146343510949)
                  ·
                    refine ⟨964867805046214939408303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5145961626913146343510949 964867805046214939408303)
                    ·
                      rfl

theorem cell22_2818610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_2818610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818610 prefixEnd_2818610 := by exact prefixLift 2818610
  have htrace : WordTrace (prefixWord ++ tailWord_2818610) baseStart_2818610 baseEnd_2818610 := by
    simpa [prefixWord, tailWord_2818610, baseEnd_2818610] using wordTrace_append hprefix tailTrace_2818610
  have hstable : (prefixWord ++ tailWord_2818610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818610).length < 2 ^ (prefixWord ++ tailWord_2818610).sum := by decide
  have hdescent : baseEnd_2818610 < baseStart_2818610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818625 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 6]
def baseStart_2818625 : Nat := 118140960795 + 2818625 * 2 ^ 59
def prefixEnd_2818625 : Nat := 4983230072969 + 3 ^ 40 * 2818625 * 2
def baseEnd_2818625 : Nat := 321624313284253300094419

theorem tailTrace_2818625 : CollatzResearch.WordTrace tailWord_2818625 prefixEnd_2818625 321624313284253300094419 := by
  unfold tailWord_2818625
  simp only [CollatzResearch.WordTrace]
  refine ⟨102803699413610482670265329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68535799609073655113510219 102803699413610482670265329)
  ·
    refine ⟨77102774560207862002698997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102803699413610482670265329 77102774560207862002698997)
    ·
      refine ⟨7228385115019487062753031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77102774560207862002698997 7228385115019487062753031)
      ·
        refine ⟨10842577672529230594129547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7228385115019487062753031 10842577672529230594129547)
        ·
          refine ⟨16263866508793845891194321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10842577672529230594129547 16263866508793845891194321)
          ·
            refine ⟨12197899881595384418395741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16263866508793845891194321 12197899881595384418395741)
            ·
              refine ⟨4574212455598269156898403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12197899881595384418395741 4574212455598269156898403)
              ·
                refine ⟨6861318683397403735347605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574212455598269156898403 6861318683397403735347605)
                ·
                  refine ⟨321624313284253300094419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6861318683397403735347605 321624313284253300094419)
                  ·
                    rfl

theorem cell22_2818625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_2818625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818625 prefixEnd_2818625 := by exact prefixLift 2818625
  have htrace : WordTrace (prefixWord ++ tailWord_2818625) baseStart_2818625 baseEnd_2818625 := by
    simpa [prefixWord, tailWord_2818625, baseEnd_2818625] using wordTrace_append hprefix tailTrace_2818625
  have hstable : (prefixWord ++ tailWord_2818625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818625).length < 2 ^ (prefixWord ++ tailWord_2818625).sum := by decide
  have hdescent : baseEnd_2818625 < baseStart_2818625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818638 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_2818638 : Nat := 118140960795 + 2818638 * 2 ^ 59
def prefixEnd_2818638 : Nat := 4983230072969 + 3 ^ 40 * 2818638 * 2
def baseEnd_2818638 : Nat := 964877390018432199708217

theorem tailTrace_2818638 : CollatzResearch.WordTrace tailWord_2818638 prefixEnd_2818638 964877390018432199708217 := by
  unfold tailWord_2818638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12850521695320423236311071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68536115708375590593659045 12850521695320423236311071)
  ·
    refine ⟨19275782542980634854466607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12850521695320423236311071 19275782542980634854466607)
    ·
      refine ⟨28913673814470952281699911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19275782542980634854466607 28913673814470952281699911)
      ·
        refine ⟨43370510721706428422549867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28913673814470952281699911 43370510721706428422549867)
        ·
          refine ⟨65055766082559642633824801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43370510721706428422549867 65055766082559642633824801)
          ·
            refine ⟨48791824561919731975368601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65055766082559642633824801 48791824561919731975368601)
            ·
              refine ⟨36593868421439798981526451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48791824561919731975368601 36593868421439798981526451)
              ·
                refine ⟨54890802632159698472289677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36593868421439798981526451 54890802632159698472289677)
                ·
                  refine ⟨20584050987059886927108629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54890802632159698472289677 20584050987059886927108629)
                  ·
                    refine ⟨964877390018432199708217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20584050987059886927108629 964877390018432199708217)
                    ·
                      rfl

theorem cell22_2818638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_2818638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818638 prefixEnd_2818638 := by exact prefixLift 2818638
  have htrace : WordTrace (prefixWord ++ tailWord_2818638) baseStart_2818638 baseEnd_2818638 := by
    simpa [prefixWord, tailWord_2818638, baseEnd_2818638] using wordTrace_append hprefix tailTrace_2818638
  have hstable : (prefixWord ++ tailWord_2818638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818638).length < 2 ^ (prefixWord ++ tailWord_2818638).sum := by decide
  have hdescent : baseEnd_2818638 < baseStart_2818638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818674 : List Nat := [3, 2, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2818674 : Nat := 118140960795 + 2818674 * 2 ^ 59
def prefixEnd_2818674 : Nat := 4983230072969 + 3 ^ 40 * 2818674 * 2
def baseEnd_2818674 : Nat := 964889713554140105808107

theorem tailTrace_2818674 : CollatzResearch.WordTrace tailWord_2818674 prefixEnd_2818674 964889713554140105808107 := by
  unfold tailWord_2818674
  simp only [CollatzResearch.WordTrace]
  refine ⟨25701371647608241009699769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68536991060288642692532717 25701371647608241009699769)
  ·
    refine ⟨19276028735706180757274827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25701371647608241009699769 19276028735706180757274827)
    ·
      refine ⟨28914043103559271135912241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19276028735706180757274827 28914043103559271135912241)
      ·
        refine ⟨21685532327669453351934181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28914043103559271135912241 21685532327669453351934181)
        ·
          refine ⟨4066037311438022503487659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21685532327669453351934181 4066037311438022503487659)
          ·
            refine ⟨6099055967157033755231489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4066037311438022503487659 6099055967157033755231489)
            ·
              refine ⟨4574291975367775316423617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6099055967157033755231489 4574291975367775316423617)
              ·
                refine ⟨3430718981525831487317713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4574291975367775316423617 3430718981525831487317713)
                ·
                  refine ⟨2573039236144373615488285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3430718981525831487317713 2573039236144373615488285)
                  ·
                    refine ⟨964889713554140105808107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573039236144373615488285 964889713554140105808107)
                    ·
                      rfl

theorem cell22_2818674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2818674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818674 prefixEnd_2818674 := by exact prefixLift 2818674
  have htrace : WordTrace (prefixWord ++ tailWord_2818674) baseStart_2818674 baseEnd_2818674 := by
    simpa [prefixWord, tailWord_2818674, baseEnd_2818674] using wordTrace_append hprefix tailTrace_2818674
  have hstable : (prefixWord ++ tailWord_2818674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818674).length < 2 ^ (prefixWord ++ tailWord_2818674).sum := by decide
  have hdescent : baseEnd_2818674 < baseStart_2818674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818702 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_2818702 : Nat := 118140960795 + 2818702 * 2 ^ 59
def prefixEnd_2818702 : Nat := 4983230072969 + 3 ^ 40 * 2818702 * 2
def baseEnd_2818702 : Nat := 964899298526357366108021

theorem tailTrace_2818702 : CollatzResearch.WordTrace tailWord_2818702 prefixEnd_2818702 964899298526357366108021 := by
  unfold tailWord_2818702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12850813479291440602602295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68537671889554349880545573 12850813479291440602602295)
  ·
    refine ⟨19276220218937160903903443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12850813479291440602602295 19276220218937160903903443)
    ·
      refine ⟨28914330328405741355855165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19276220218937160903903443 28914330328405741355855165)
      ·
        refine ⟨10842873873152153008445687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28914330328405741355855165 10842873873152153008445687)
        ·
          refine ⟨16264310809728229512668531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10842873873152153008445687 16264310809728229512668531)
          ·
            refine ⟨24396466214592344269002797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16264310809728229512668531 24396466214592344269002797)
            ·
              refine ⟨9148674830472129100876049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24396466214592344269002797 9148674830472129100876049)
              ·
                refine ⟨6861506122854096825657037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148674830472129100876049 6861506122854096825657037)
                ·
                  refine ⟨2573064796070286309621389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6861506122854096825657037 2573064796070286309621389)
                  ·
                    refine ⟨964899298526357366108021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573064796070286309621389 964899298526357366108021)
                    ·
                      rfl

theorem cell22_2818702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_2818702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818702 prefixEnd_2818702 := by exact prefixLift 2818702
  have htrace : WordTrace (prefixWord ++ tailWord_2818702) baseStart_2818702 baseEnd_2818702 := by
    simpa [prefixWord, tailWord_2818702, baseEnd_2818702] using wordTrace_append hprefix tailTrace_2818702
  have hstable : (prefixWord ++ tailWord_2818702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818702).length < 2 ^ (prefixWord ++ tailWord_2818702).sum := by decide
  have hdescent : baseEnd_2818702 < baseStart_2818702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818713 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_2818713 : Nat := 118140960795 + 2818713 * 2 ^ 59
def prefixEnd_2818713 : Nat := 4983230072969 + 3 ^ 40 * 2818713 * 2
def baseEnd_2818713 : Nat := 964903064051157004082987

theorem tailTrace_2818713 : CollatzResearch.WordTrace tailWord_2818713 prefixEnd_2818713 964903064051157004082987 := by
  unfold tailWord_2818713
  simp only [CollatzResearch.WordTrace]
  refine ⟨102806909037291673699468793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68537939358194449132979195 102806909037291673699468793)
  ·
    refine ⟨77105181777968755274601595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102806909037291673699468793 77105181777968755274601595)
    ·
      refine ⟨115657772666953132911902393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77105181777968755274601595 115657772666953132911902393)
      ·
        refine ⟨86743329500214849683926795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115657772666953132911902393 86743329500214849683926795)
        ·
          refine ⟨130114994250322274525890193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86743329500214849683926795 130114994250322274525890193)
          ·
            refine ⟨97586245687741705894417645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130114994250322274525890193 97586245687741705894417645)
            ·
              refine ⟨36594842132903139710406617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97586245687741705894417645 36594842132903139710406617)
              ·
                refine ⟨27446131599677354782804963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36594842132903139710406617 27446131599677354782804963)
                ·
                  refine ⟨41169197399516032174207445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27446131599677354782804963 41169197399516032174207445)
                  ·
                    refine ⟨964903064051157004082987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41169197399516032174207445 964903064051157004082987)
                    ·
                      rfl

theorem cell22_2818713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_2818713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818713 prefixEnd_2818713 := by exact prefixLift 2818713
  have htrace : WordTrace (prefixWord ++ tailWord_2818713) baseStart_2818713 baseEnd_2818713 := by
    simpa [prefixWord, tailWord_2818713, baseEnd_2818713] using wordTrace_append hprefix tailTrace_2818713
  have hstable : (prefixWord ++ tailWord_2818713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818713).length < 2 ^ (prefixWord ++ tailWord_2818713).sum := by decide
  have hdescent : baseEnd_2818713 < baseStart_2818713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818760 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_2818760 : Nat := 118140960795 + 2818760 * 2 ^ 59
def prefixEnd_2818760 : Nat := 4983230072969 + 3 ^ 40 * 2818760 * 2
def baseEnd_2818760 : Nat := 321639717703888182719281

theorem tailTrace_2818760 : CollatzResearch.WordTrace tailWord_2818760 prefixEnd_2818760 321639717703888182719281 := by
  unfold tailWord_2818760
  simp only [CollatzResearch.WordTrace]
  refine ⟨51404311634060700363214867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68539082178747600484286489 51404311634060700363214867)
  ·
    refine ⟨77106467451091050544822301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51404311634060700363214867 77106467451091050544822301)
    ·
      refine ⟨28914925294159143954308363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77106467451091050544822301 28914925294159143954308363)
      ·
        refine ⟨43372387941238715931462545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28914925294159143954308363 43372387941238715931462545)
        ·
          refine ⟨32529290955929036948596909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43372387941238715931462545 32529290955929036948596909)
          ·
            refine ⟨12198484108473388855723841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32529290955929036948596909 12198484108473388855723841)
            ·
              refine ⟨9148863081355041641792881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12198484108473388855723841 9148863081355041641792881)
              ·
                refine ⟨6861647311016281231344661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9148863081355041641792881 6861647311016281231344661)
                ·
                  refine ⟨321639717703888182719281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6861647311016281231344661 321639717703888182719281)
                  ·
                    rfl

theorem cell22_2818760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_2818760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818760 prefixEnd_2818760 := by exact prefixLift 2818760
  have htrace : WordTrace (prefixWord ++ tailWord_2818760) baseStart_2818760 baseEnd_2818760 := by
    simpa [prefixWord, tailWord_2818760, baseEnd_2818760] using wordTrace_append hprefix tailTrace_2818760
  have hstable : (prefixWord ++ tailWord_2818760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818760).length < 2 ^ (prefixWord ++ tailWord_2818760).sum := by decide
  have hdescent : baseEnd_2818760 < baseStart_2818760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818762 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_2818762 : Nat := 118140960795 + 2818762 * 2 ^ 59
def prefixEnd_2818762 : Nat := 4983230072969 + 3 ^ 40 * 2818762 * 2
def baseEnd_2818762 : Nat := 964919837752537209607837

theorem tailTrace_2818762 : CollatzResearch.WordTrace tailWord_2818762 prefixEnd_2818762 964919837752537209607837 := by
  unfold tailWord_2818762
  simp only [CollatzResearch.WordTrace]
  refine ⟨25702174053528538767000635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68539130809409436712001693 25702174053528538767000635)
  ·
    refine ⟨38553261080292808150500953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25702174053528538767000635 38553261080292808150500953)
    ·
      refine ⟨28914945810219606112875715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38553261080292808150500953 28914945810219606112875715)
      ·
        refine ⟨43372418715329409169313573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28914945810219606112875715 43372418715329409169313573)
        ·
          refine ⟨8132328509124264219246295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43372418715329409169313573 8132328509124264219246295)
          ·
            refine ⟨12198492763686396328869443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8132328509124264219246295 12198492763686396328869443)
            ·
              refine ⟨18297739145529594493304165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12198492763686396328869443 18297739145529594493304165)
              ·
                refine ⟨3430826089786798967494531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18297739145529594493304165 3430826089786798967494531)
                ·
                  refine ⟨5146239134680198451241797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3430826089786798967494531 5146239134680198451241797)
                  ·
                    refine ⟨964919837752537209607837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5146239134680198451241797 964919837752537209607837)
                    ·
                      rfl

theorem cell22_2818762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_2818762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818762 prefixEnd_2818762 := by exact prefixLift 2818762
  have htrace : WordTrace (prefixWord ++ tailWord_2818762) baseStart_2818762 baseEnd_2818762 := by
    simpa [prefixWord, tailWord_2818762, baseEnd_2818762] using wordTrace_append hprefix tailTrace_2818762
  have hstable : (prefixWord ++ tailWord_2818762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818762).length < 2 ^ (prefixWord ++ tailWord_2818762).sum := by decide
  have hdescent : baseEnd_2818762 < baseStart_2818762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818845 : List Nat := [1, 4, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2818845 : Nat := 118140960795 + 2818845 * 2 ^ 59
def prefixEnd_2818845 : Nat := 4983230072969 + 3 ^ 40 * 2818845 * 2
def baseEnd_2818845 : Nat := 321649416782917553260861

theorem tailTrace_2818845 : CollatzResearch.WordTrace tailWord_2818845 prefixEnd_2818845 321649416782917553260861 := by
  unfold tailWord_2818845
  simp only [CollatzResearch.WordTrace]
  refine ⟨102811723472813460243273989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68541148981875640162182659 102811723472813460243273989)
  ·
    refine ⟨19277198151152523795613873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102811723472813460243273989 19277198151152523795613873)
    ·
      refine ⟨14457898613364392846710405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19277198151152523795613873 14457898613364392846710405)
      ·
        refine ⟨2710855990005823658758201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14457898613364392846710405 2710855990005823658758201)
        ·
          refine ⟨2033141992504367744068651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710855990005823658758201 2033141992504367744068651)
          ·
            refine ⟨3049712988756551616102977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033141992504367744068651 3049712988756551616102977)
            ·
              refine ⟨2287284741567413712077233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3049712988756551616102977 2287284741567413712077233)
              ·
                refine ⟨1715463556175560284057925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2287284741567413712077233 1715463556175560284057925)
                ·
                  refine ⟨321649416782917553260861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1715463556175560284057925 321649416782917553260861)
                  ·
                    rfl

theorem cell22_2818845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2818845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818845 prefixEnd_2818845 := by exact prefixLift 2818845
  have htrace : WordTrace (prefixWord ++ tailWord_2818845) baseStart_2818845 baseEnd_2818845 := by
    simpa [prefixWord, tailWord_2818845, baseEnd_2818845] using wordTrace_append hprefix tailTrace_2818845
  have hstable : (prefixWord ++ tailWord_2818845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818845).length < 2 ^ (prefixWord ++ tailWord_2818845).sum := by decide
  have hdescent : baseEnd_2818845 < baseStart_2818845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818867 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 5]
def baseStart_2818867 : Nat := 118140960795 + 2818867 * 2 ^ 59
def prefixEnd_2818867 : Nat := 4983230072969 + 3 ^ 40 * 2818867 * 2
def baseEnd_2818867 : Nat := 321651927132783978577505

theorem tailTrace_2818867 : CollatzResearch.WordTrace tailWord_2818867 prefixEnd_2818867 321651927132783978577505 := by
  unfold tailWord_2818867
  simp only [CollatzResearch.WordTrace]
  refine ⟨102812525878733758000574855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68541683919155838667049903 102812525878733758000574855)
  ·
    refine ⟨154218788818100637000862283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102812525878733758000574855 154218788818100637000862283)
    ·
      refine ⟨231328183227150955501293425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154218788818100637000862283 231328183227150955501293425)
      ·
        refine ⟨173496137420363216625970069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231328183227150955501293425 173496137420363216625970069)
        ·
          refine ⟨8132631441579525779342347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173496137420363216625970069 8132631441579525779342347)
          ·
            refine ⟨12198947162369288669013521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8132631441579525779342347 12198947162369288669013521)
            ·
              refine ⟨9149210371776966501760141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12198947162369288669013521 9149210371776966501760141)
              ·
                refine ⟨3430953889416362438160053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9149210371776966501760141 3430953889416362438160053)
                ·
                  refine ⟨321651927132783978577505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3430953889416362438160053 321651927132783978577505)
                  ·
                    rfl

theorem cell22_2818867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 5].length) (baseStart_2818867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818867 prefixEnd_2818867 := by exact prefixLift 2818867
  have htrace : WordTrace (prefixWord ++ tailWord_2818867) baseStart_2818867 baseEnd_2818867 := by
    simpa [prefixWord, tailWord_2818867, baseEnd_2818867] using wordTrace_append hprefix tailTrace_2818867
  have hstable : (prefixWord ++ tailWord_2818867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818867).length < 2 ^ (prefixWord ++ tailWord_2818867).sum := by decide
  have hdescent : baseEnd_2818867 < baseStart_2818867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818912 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 6]
def baseStart_2818912 : Nat := 118140960795 + 2818912 * 2 ^ 59
def prefixEnd_2818912 : Nat := 4983230072969 + 3 ^ 40 * 2818912 * 2
def baseEnd_2818912 : Nat := 321657061939328939452459

theorem tailTrace_2818912 : CollatzResearch.WordTrace tailWord_2818912 prefixEnd_2818912 321657061939328939452459 := by
  unfold tailWord_2818912
  simp only [CollatzResearch.WordTrace]
  refine ⟨51407083581785365342981495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68542778109047153790641993 51407083581785365342981495)
  ·
    refine ⟨77110625372678048014472243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51407083581785365342981495 77110625372678048014472243)
    ·
      refine ⟨115665938059017072021708365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77110625372678048014472243 115665938059017072021708365)
      ·
        refine ⟨43374726772131402008140637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115665938059017072021708365 43374726772131402008140637)
        ·
          refine ⟨16265522539549275753052739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43374726772131402008140637 16265522539549275753052739)
          ·
            refine ⟨24398283809323913629579109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16265522539549275753052739 24398283809323913629579109)
            ·
              refine ⟨4574678214248233805546083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24398283809323913629579109 4574678214248233805546083)
              ·
                refine ⟨6862017321372350708319125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4574678214248233805546083 6862017321372350708319125)
                ·
                  refine ⟨321657061939328939452459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6862017321372350708319125 321657061939328939452459)
                  ·
                    rfl

theorem cell22_2818912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_2818912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818912 prefixEnd_2818912 := by exact prefixLift 2818912
  have htrace : WordTrace (prefixWord ++ tailWord_2818912) baseStart_2818912 baseEnd_2818912 := by
    simpa [prefixWord, tailWord_2818912, baseEnd_2818912] using wordTrace_append hprefix tailTrace_2818912
  have hstable : (prefixWord ++ tailWord_2818912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818912).length < 2 ^ (prefixWord ++ tailWord_2818912).sum := by decide
  have hdescent : baseEnd_2818912 < baseStart_2818912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2818978 : List Nat := [3, 3, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_2818978 : Nat := 118140960795 + 2818978 * 2 ^ 59
def prefixEnd_2818978 : Nat := 4983230072969 + 3 ^ 40 * 2818978 * 2
def baseEnd_2818978 : Nat := 964993778966784646207175

theorem tailTrace_2818978 : CollatzResearch.WordTrace tailWord_2818978 prefixEnd_2818978 964993778966784646207175 := by
  unfold tailWord_2818978
  simp only [CollatzResearch.WordTrace]
  refine ⟨25704143595332905989466397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68544382920887749305243725 25704143595332905989466397)
  ·
    refine ⟨9639053848249839746049899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25704143595332905989466397 9639053848249839746049899)
    ·
      refine ⟨14458580772374759619074849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9639053848249839746049899 14458580772374759619074849)
      ·
        refine ⟨10843935579281069714306137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14458580772374759619074849 10843935579281069714306137)
        ·
          refine ⟨8132951684460802285729603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10843935579281069714306137 8132951684460802285729603)
          ·
            refine ⟨12199427526691203428594405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8132951684460802285729603 12199427526691203428594405)
            ·
              refine ⟨2287392661254600642861451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12199427526691203428594405 2287392661254600642861451)
              ·
                refine ⟨3431088991881900964292177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2287392661254600642861451 3431088991881900964292177)
                ·
                  refine ⟨2573316743911425723219133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3431088991881900964292177 2573316743911425723219133)
                  ·
                    refine ⟨964993778966784646207175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2573316743911425723219133 964993778966784646207175)
                    ·
                      rfl

theorem cell22_2818978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_2818978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2818978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2818978 prefixEnd_2818978 := by exact prefixLift 2818978
  have htrace : WordTrace (prefixWord ++ tailWord_2818978) baseStart_2818978 baseEnd_2818978 := by
    simpa [prefixWord, tailWord_2818978, baseEnd_2818978] using wordTrace_append hprefix tailTrace_2818978
  have hstable : (prefixWord ++ tailWord_2818978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2818978).length < 2 ^ (prefixWord ++ tailWord_2818978).sum := by decide
  have hdescent : baseEnd_2818978 < baseStart_2818978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2818978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2819019 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 5]
def baseStart_2819019 : Nat := 118140960795 + 2819019 * 2 ^ 59
def prefixEnd_2819019 : Nat := 4983230072969 + 3 ^ 40 * 2819019 * 2
def baseEnd_2819019 : Nat := 321669271368224735310683

theorem tailTrace_2819019 : CollatzResearch.WordTrace tailWord_2819019 prefixEnd_2819019 321669271368224735310683 := by
  unfold tailWord_2819019
  simp only [CollatzResearch.WordTrace]
  refine ⟨102818069774183087960108111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68545379849455391973405407 102818069774183087960108111)
  ·
    refine ⟨154227104661274631940162167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102818069774183087960108111 154227104661274631940162167)
    ·
      refine ⟨231340656991911947910243251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154227104661274631940162167 231340656991911947910243251)
      ·
        refine ⟨347010985487867921865364877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231340656991911947910243251 347010985487867921865364877)
        ·
          refine ⟨130129119557950470699511829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347010985487867921865364877 130129119557950470699511829)
          ·
            refine ⟨6099802479278928314039617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130129119557950470699511829 6099802479278928314039617)
            ·
              refine ⟨4574851859459196235529713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6099802479278928314039617 4574851859459196235529713)
              ·
                refine ⟨3431138894594397176647285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4574851859459196235529713 3431138894594397176647285)
                ·
                  refine ⟨321669271368224735310683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3431138894594397176647285 321669271368224735310683)
                  ·
                    rfl

theorem cell22_2819019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 5].length) (baseStart_2819019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2819019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2819019 prefixEnd_2819019 := by exact prefixLift 2819019
  have htrace : WordTrace (prefixWord ++ tailWord_2819019) baseStart_2819019 baseEnd_2819019 := by
    simpa [prefixWord, tailWord_2819019, baseEnd_2819019] using wordTrace_append hprefix tailTrace_2819019
  have hstable : (prefixWord ++ tailWord_2819019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2819019).length < 2 ^ (prefixWord ++ tailWord_2819019).sum := by decide
  have hdescent : baseEnd_2819019 < baseStart_2819019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2819019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
