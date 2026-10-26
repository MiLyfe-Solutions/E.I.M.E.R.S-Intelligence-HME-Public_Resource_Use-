import V185TrunkScan22Chunk384

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3432500 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3432500 : Nat := 118140960795 + 3432500 * 2 ^ 59
def prefixEnd_3432500 : Nat := 4983230072969 + 3 ^ 40 * 3432500 * 2
def baseEnd_3432500 : Nat := 1175014897705283707776151

theorem tailTrace_3432500 : CollatzResearch.WordTrace tailWord_3432500 prefixEnd_3432500 1175014897705283707776151 := by
  unfold tailWord_3432500
  simp only [CollatzResearch.WordTrace]
  refine ⟨62596780032323099586703477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83462373376430799448937969 62596780032323099586703477)
  ·
    refine ⟨5868448128030290586253451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62596780032323099586703477 5868448128030290586253451)
    ·
      refine ⟨8802672192045435879380177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5868448128030290586253451 8802672192045435879380177)
      ·
        refine ⟨6602004144034076909535133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8802672192045435879380177 6602004144034076909535133)
        ·
          refine ⟨2475751554012778841075675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6602004144034076909535133 2475751554012778841075675)
          ·
            refine ⟨3713627331019168261613513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475751554012778841075675 3713627331019168261613513)
            ·
              refine ⟨2785220498264376196210135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713627331019168261613513 2785220498264376196210135)
              ·
                refine ⟨4177830747396564294315203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2785220498264376196210135 4177830747396564294315203)
                ·
                  refine ⟨6266746121094846441472805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177830747396564294315203 6266746121094846441472805)
                  ·
                    refine ⟨1175014897705283707776151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6266746121094846441472805 1175014897705283707776151)
                    ·
                      rfl

theorem cell22_3432500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3432500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432500 prefixEnd_3432500 := by exact prefixLift 3432500
  have htrace : WordTrace (prefixWord ++ tailWord_3432500) baseStart_3432500 baseEnd_3432500 := by
    simpa [prefixWord, tailWord_3432500, baseEnd_3432500] using wordTrace_append hprefix tailTrace_3432500
  have hstable : (prefixWord ++ tailWord_3432500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432500).length < 2 ^ (prefixWord ++ tailWord_3432500).sum := by decide
  have hdescent : baseEnd_3432500 < baseStart_3432500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432541 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3432541 : Nat := 118140960795 + 3432541 * 2 ^ 59
def prefixEnd_3432541 : Nat := 4983230072969 + 3 ^ 40 * 3432541 * 2
def baseEnd_3432541 : Nat := 1175028932843173267501025

theorem tailTrace_3432541 : CollatzResearch.WordTrace tailWord_3432541 prefixEnd_3432541 1175028932843173267501025 := by
  unfold tailWord_3432541
  simp only [CollatzResearch.WordTrace]
  refine ⟨125195055457497663175649477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83463370304998442117099651 125195055457497663175649477)
  ·
    refine ⟨23474072898280811845434277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125195055457497663175649477 23474072898280811845434277)
    ·
      refine ⟨4401388668427652221018927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23474072898280811845434277 4401388668427652221018927)
      ·
        refine ⟨6602083002641478331528391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401388668427652221018927 6602083002641478331528391)
        ·
          refine ⟨9903124503962217497292587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602083002641478331528391 9903124503962217497292587)
          ·
            refine ⟨14854686755943326245938881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9903124503962217497292587 14854686755943326245938881)
            ·
              refine ⟨11141015066957494684454161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14854686755943326245938881 11141015066957494684454161)
              ·
                refine ⟨8355761300218121013340621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11141015066957494684454161 8355761300218121013340621)
                ·
                  refine ⟨3133410487581795380002733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8355761300218121013340621 3133410487581795380002733)
                  ·
                    refine ⟨1175028932843173267501025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133410487581795380002733 1175028932843173267501025)
                    ·
                      rfl

theorem cell22_3432541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3432541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432541 prefixEnd_3432541 := by exact prefixLift 3432541
  have htrace : WordTrace (prefixWord ++ tailWord_3432541) baseStart_3432541 baseEnd_3432541 := by
    simpa [prefixWord, tailWord_3432541, baseEnd_3432541] using wordTrace_append hprefix tailTrace_3432541
  have hstable : (prefixWord ++ tailWord_3432541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432541).length < 2 ^ (prefixWord ++ tailWord_3432541).sum := by decide
  have hdescent : baseEnd_3432541 < baseStart_3432541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432597 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_3432597 : Nat := 118140960795 + 3432597 * 2 ^ 59
def prefixEnd_3432597 : Nat := 4983230072969 + 3 ^ 40 * 3432597 * 2
def baseEnd_3432597 : Nat := 1175048102787607788100853

theorem tailTrace_3432597 : CollatzResearch.WordTrace tailWord_3432597 prefixEnd_3432597 1175048102787607788100853 := by
  unfold tailWord_3432597
  simp only [CollatzResearch.WordTrace]
  refine ⟨125197097945294784739688045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83464731963529856493125363 125197097945294784739688045)
  ·
    refine ⟨46948911729485544277383017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125197097945294784739688045 46948911729485544277383017)
    ·
      refine ⟨35211683797114158208037263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46948911729485544277383017 35211683797114158208037263)
      ·
        refine ⟨52817525695671237312055895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35211683797114158208037263 52817525695671237312055895)
        ·
          refine ⟨79226288543506855968083843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52817525695671237312055895 79226288543506855968083843)
          ·
            refine ⟨118839432815260283952125765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79226288543506855968083843 118839432815260283952125765)
            ·
              refine ⟨22282393652861303241023581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118839432815260283952125765 22282393652861303241023581)
              ·
                refine ⟨8355897619822988715383843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22282393652861303241023581 8355897619822988715383843)
                ·
                  refine ⟨12533846429734483073075765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8355897619822988715383843 12533846429734483073075765)
                  ·
                    refine ⟨1175048102787607788100853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12533846429734483073075765 1175048102787607788100853)
                    ·
                      rfl

theorem cell22_3432597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_3432597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432597 prefixEnd_3432597 := by exact prefixLift 3432597
  have htrace : WordTrace (prefixWord ++ tailWord_3432597) baseStart_3432597 baseEnd_3432597 := by
    simpa [prefixWord, tailWord_3432597, baseEnd_3432597] using wordTrace_append hprefix tailTrace_3432597
  have hstable : (prefixWord ++ tailWord_3432597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432597).length < 2 ^ (prefixWord ++ tailWord_3432597).sum := by decide
  have hdescent : baseEnd_3432597 < baseStart_3432597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432631 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 2, 3]
def baseStart_3432631 : Nat := 118140960795 + 3432631 * 2 ^ 59
def prefixEnd_3432631 : Nat := 4983230072969 + 3 ^ 40 * 3432631 * 2
def baseEnd_3432631 : Nat := 1175059741682443032750749

theorem tailTrace_3432631 : CollatzResearch.WordTrace tailWord_3432631 prefixEnd_3432631 1175059741682443032750749 := by
  unfold tailWord_3432631
  simp only [CollatzResearch.WordTrace]
  refine ⟨125198338027171608546425747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83465558684781072364283831 125198338027171608546425747)
  ·
    refine ⟨187797507040757412819638621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125198338027171608546425747 187797507040757412819638621)
    ·
      refine ⟨70424065140284029807364483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187797507040757412819638621 70424065140284029807364483)
      ·
        refine ⟨105636097710426044711046725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70424065140284029807364483 105636097710426044711046725)
        ·
          refine ⟨19806768320704883383321261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105636097710426044711046725 19806768320704883383321261)
          ·
            refine ⟨7427538120264331268745473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19806768320704883383321261 7427538120264331268745473)
            ·
              refine ⟨5570653590198248451559105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7427538120264331268745473 5570653590198248451559105)
              ·
                refine ⟨4177990192648686338669329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570653590198248451559105 4177990192648686338669329)
                ·
                  refine ⟨3133492644486514754001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177990192648686338669329 3133492644486514754001997)
                  ·
                    refine ⟨1175059741682443032750749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133492644486514754001997 1175059741682443032750749)
                    ·
                      rfl

theorem cell22_3432631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_3432631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432631 prefixEnd_3432631 := by exact prefixLift 3432631
  have htrace : WordTrace (prefixWord ++ tailWord_3432631) baseStart_3432631 baseEnd_3432631 := by
    simpa [prefixWord, tailWord_3432631, baseEnd_3432631] using wordTrace_append hprefix tailTrace_3432631
  have hstable : (prefixWord ++ tailWord_3432631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432631).length < 2 ^ (prefixWord ++ tailWord_3432631).sum := by decide
  have hdescent : baseEnd_3432631 < baseStart_3432631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432644 : List Nat := [2, 3, 3, 1, 2, 1, 3, 7]
def baseStart_3432644 : Nat := 118140960795 + 3432644 * 2 ^ 59
def prefixEnd_3432644 : Nat := 4983230072969 + 3 ^ 40 * 3432644 * 2
def baseEnd_3432644 : Nat := 130562687983123925797301

theorem tailTrace_3432644 : CollatzResearch.WordTrace tailWord_3432644 prefixEnd_3432644 130562687983123925797301 := by
  unfold tailWord_3432644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62599406088062255883324493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83465874784083007844432657 62599406088062255883324493)
  ·
    refine ⟨23474777283023345956246685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62599406088062255883324493 23474777283023345956246685)
    ·
      refine ⟨8803041481133754733592507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23474777283023345956246685 8803041481133754733592507)
      ·
        refine ⟨13204562221700632100388761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803041481133754733592507 13204562221700632100388761)
        ·
          refine ⟨9903421666275474075291571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13204562221700632100388761 9903421666275474075291571)
          ·
            refine ⟨14855132499413211112937357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9903421666275474075291571 14855132499413211112937357)
            ·
              refine ⟨5570674687279954167351509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14855132499413211112937357 5570674687279954167351509)
              ·
                refine ⟨130562687983123925797301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5570674687279954167351509 130562687983123925797301)
                ·
                  rfl

theorem cell22_3432644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_3432644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432644 prefixEnd_3432644 := by exact prefixLift 3432644
  have htrace : WordTrace (prefixWord ++ tailWord_3432644) baseStart_3432644 baseEnd_3432644 := by
    simpa [prefixWord, tailWord_3432644, baseEnd_3432644] using wordTrace_append hprefix tailTrace_3432644
  have hstable : (prefixWord ++ tailWord_3432644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432644).length < 2 ^ (prefixWord ++ tailWord_3432644).sum := by decide
  have hdescent : baseEnd_3432644 < baseStart_3432644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432661 : List Nat := [1, 3, 2, 4, 2, 1, 3, 6]
def baseStart_3432661 : Nat := 118140960795 + 3432661 * 2 ^ 59
def prefixEnd_3432661 : Nat := 4983230072969 + 3 ^ 40 * 3432661 * 2
def baseEnd_3432661 : Nat := 130563334588392550500073

theorem tailTrace_3432661 : CollatzResearch.WordTrace tailWord_3432661 prefixEnd_3432661 130563334588392550500073 := by
  unfold tailWord_3432661
  simp only [CollatzResearch.WordTrace]
  refine ⟨125199432217062923670017837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83466288144708615780011891 125199432217062923670017837)
  ·
    refine ⟨46949787081398596376256689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125199432217062923670017837 46949787081398596376256689)
    ·
      refine ⟨35212340311048947282192517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46949787081398596376256689 35212340311048947282192517)
      ·
        refine ⟨6602313808321677615411097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35212340311048947282192517 6602313808321677615411097)
        ·
          refine ⟨4951735356241258211558323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6602313808321677615411097 4951735356241258211558323)
          ·
            refine ⟨7427603034361887317337485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4951735356241258211558323 7427603034361887317337485)
            ·
              refine ⟨2785351137885707744001557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7427603034361887317337485 2785351137885707744001557)
              ·
                refine ⟨130563334588392550500073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2785351137885707744001557 130563334588392550500073)
                ·
                  rfl

theorem cell22_3432661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 6].length) (baseStart_3432661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432661 prefixEnd_3432661 := by exact prefixLift 3432661
  have htrace : WordTrace (prefixWord ++ tailWord_3432661) baseStart_3432661 baseEnd_3432661 := by
    simpa [prefixWord, tailWord_3432661, baseEnd_3432661] using wordTrace_append hprefix tailTrace_3432661
  have hstable : (prefixWord ++ tailWord_3432661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432661).length < 2 ^ (prefixWord ++ tailWord_3432661).sum := by decide
  have hdescent : baseEnd_3432661 < baseStart_3432661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432672 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_3432672 : Nat := 118140960795 + 3432672 * 2 ^ 59
def prefixEnd_3432672 : Nat := 4983230072969 + 3 ^ 40 * 3432672 * 2
def baseEnd_3432672 : Nat := 391691258940110864158541

theorem tailTrace_3432672 : CollatzResearch.WordTrace tailWord_3432672 prefixEnd_3432672 391691258940110864158541 := by
  unfold tailWord_3432672
  simp only [CollatzResearch.WordTrace]
  refine ⟨62599916710011536274334135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83466555613348715032445513 62599916710011536274334135)
  ·
    refine ⟨93899875065017304411501203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62599916710011536274334135 93899875065017304411501203)
    ·
      refine ⟨140849812597525956617251805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93899875065017304411501203 140849812597525956617251805)
      ·
        refine ⟨52818679724072233731469427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140849812597525956617251805 52818679724072233731469427)
        ·
          refine ⟨79228019586108350597204141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52818679724072233731469427 79228019586108350597204141)
          ·
            refine ⟨29710507344790631473951553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79228019586108350597204141 29710507344790631473951553)
            ·
              refine ⟨22282880508592973605463665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29710507344790631473951553 22282880508592973605463665)
              ·
                refine ⟨16712160381444730204097749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22282880508592973605463665 16712160381444730204097749)
                ·
                  refine ⟨391691258940110864158541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16712160381444730204097749 391691258940110864158541)
                  ·
                    rfl

theorem cell22_3432672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_3432672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432672 prefixEnd_3432672 := by exact prefixLift 3432672
  have htrace : WordTrace (prefixWord ++ tailWord_3432672) baseStart_3432672 baseEnd_3432672 := by
    simpa [prefixWord, tailWord_3432672, baseEnd_3432672] using wordTrace_append hprefix tailTrace_3432672
  have hstable : (prefixWord ++ tailWord_3432672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432672).length < 2 ^ (prefixWord ++ tailWord_3432672).sum := by decide
  have hdescent : baseEnd_3432672 < baseStart_3432672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432689 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 5]
def baseStart_3432689 : Nat := 118140960795 + 3432689 * 2 ^ 59
def prefixEnd_3432689 : Nat := 4983230072969 + 3 ^ 40 * 3432689 * 2
def baseEnd_3432689 : Nat := 391693198755916738266857

theorem tailTrace_3432689 : CollatzResearch.WordTrace tailWord_3432689 prefixEnd_3432689 391693198755916738266857 := by
  unfold tailWord_3432689
  simp only [CollatzResearch.WordTrace]
  refine ⟨125200453460961484452037121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83466968973974322968024747 125200453460961484452037121)
  ·
    refine ⟨93900340095721113339027841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125200453460961484452037121 93900340095721113339027841)
    ·
      refine ⟨70425255071790835004270881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93900340095721113339027841 70425255071790835004270881)
      ·
        refine ⟨52818941303843126253203161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70425255071790835004270881 52818941303843126253203161)
        ·
          refine ⟨39614205977882344689902371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52818941303843126253203161 39614205977882344689902371)
          ·
            refine ⟨59421308966823517034853557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39614205977882344689902371 59421308966823517034853557)
            ·
              refine ⟨5570747715639704722017521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59421308966823517034853557 5570747715639704722017521)
              ·
                refine ⟨4178060786729778541513141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570747715639704722017521 4178060786729778541513141)
                ·
                  refine ⟨391693198755916738266857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4178060786729778541513141 391693198755916738266857)
                  ·
                    rfl

theorem cell22_3432689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_3432689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432689 prefixEnd_3432689 := by exact prefixLift 3432689
  have htrace : WordTrace (prefixWord ++ tailWord_3432689) baseStart_3432689 baseEnd_3432689 := by
    simpa [prefixWord, tailWord_3432689, baseEnd_3432689] using wordTrace_append hprefix tailTrace_3432689
  have hstable : (prefixWord ++ tailWord_3432689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432689).length < 2 ^ (prefixWord ++ tailWord_3432689).sum := by decide
  have hdescent : baseEnd_3432689 < baseStart_3432689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432736 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_3432736 : Nat := 118140960795 + 3432736 * 2 ^ 59
def prefixEnd_3432736 : Nat := 4983230072969 + 3 ^ 40 * 3432736 * 2
def baseEnd_3432736 : Nat := 1175095685328257758875427

theorem tailTrace_3432736 : CollatzResearch.WordTrace tailWord_3432736 prefixEnd_3432736 1175095685328257758875427 := by
  unfold tailWord_3432736
  simp only [CollatzResearch.WordTrace]
  refine ⟨62601083845895605739499031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83468111794527474319332041 62601083845895605739499031)
  ·
    refine ⟨93901625768843408609248547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62601083845895605739499031 93901625768843408609248547)
    ·
      refine ⟨140852438653265112913872821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93901625768843408609248547 140852438653265112913872821)
      ·
        refine ⟨13204916123743604335675577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140852438653265112913872821 13204916123743604335675577)
        ·
          refine ⟨9903687092807703251756683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13204916123743604335675577 9903687092807703251756683)
          ·
            refine ⟨14855530639211554877635025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9903687092807703251756683 14855530639211554877635025)
            ·
              refine ⟨11141647979408666158226269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14855530639211554877635025 11141647979408666158226269)
              ·
                refine ⟨4178117992278249809334851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11141647979408666158226269 4178117992278249809334851)
                ·
                  refine ⟨6267176988417374714002277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178117992278249809334851 6267176988417374714002277)
                  ·
                    refine ⟨1175095685328257758875427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267176988417374714002277 1175095685328257758875427)
                    ·
                      rfl

theorem cell22_3432736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_3432736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432736 prefixEnd_3432736 := by exact prefixLift 3432736
  have htrace : WordTrace (prefixWord ++ tailWord_3432736) baseStart_3432736 baseEnd_3432736 := by
    simpa [prefixWord, tailWord_3432736, baseEnd_3432736] using wordTrace_append hprefix tailTrace_3432736
  have hstable : (prefixWord ++ tailWord_3432736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432736).length < 2 ^ (prefixWord ++ tailWord_3432736).sum := by decide
  have hdescent : baseEnd_3432736 < baseStart_3432736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432764 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3432764 : Nat := 118140960795 + 3432764 * 2 ^ 59
def prefixEnd_3432764 : Nat := 4983230072969 + 3 ^ 40 * 3432764 * 2
def baseEnd_3432764 : Nat := 1175105270300475019175341

theorem tailTrace_3432764 : CollatzResearch.WordTrace tailWord_3432764 prefixEnd_3432764 1175105270300475019175341 := by
  unfold tailWord_3432764
  simp only [CollatzResearch.WordTrace]
  refine ⟨62601594467844886130508673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83468792623793181507344897 62601594467844886130508673)
  ·
    refine ⟨46951195850883664597881505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62601594467844886130508673 46951195850883664597881505)
    ·
      refine ⟨35213396888162748448411129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46951195850883664597881505 35213396888162748448411129)
      ·
        refine ⟨26410047666122061336308347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35213396888162748448411129 26410047666122061336308347)
        ·
          refine ⟨39615071499183092004462521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26410047666122061336308347 39615071499183092004462521)
          ·
            refine ⟨29711303624387319003346891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39615071499183092004462521 29711303624387319003346891)
            ·
              refine ⟨44566955436580978505020337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29711303624387319003346891 44566955436580978505020337)
              ·
                refine ⟨33425216577435733878765253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44566955436580978505020337 33425216577435733878765253)
                ·
                  refine ⟨6267228108269200102268485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33425216577435733878765253 6267228108269200102268485)
                  ·
                    refine ⟨1175105270300475019175341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267228108269200102268485 1175105270300475019175341)
                    ·
                      rfl

theorem cell22_3432764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3432764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432764 prefixEnd_3432764 := by exact prefixLift 3432764
  have htrace : WordTrace (prefixWord ++ tailWord_3432764) baseStart_3432764 baseEnd_3432764 := by
    simpa [prefixWord, tailWord_3432764, baseEnd_3432764] using wordTrace_append hprefix tailTrace_3432764
  have hstable : (prefixWord ++ tailWord_3432764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432764).length < 2 ^ (prefixWord ++ tailWord_3432764).sum := by decide
  have hdescent : baseEnd_3432764 < baseStart_3432764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432796 : List Nat := [2, 2, 4, 3, 1, 10]
def baseStart_3432796 : Nat := 118140960795 + 3432796 * 2 ^ 59
def prefixEnd_3432796 : Nat := 4983230072969 + 3 ^ 40 * 3432796 * 2
def baseEnd_3432796 : Nat := 14507607710548612375003

theorem tailTrace_3432796 : CollatzResearch.WordTrace tailWord_3432796 prefixEnd_3432796 14507607710548612375003 := by
  unfold tailWord_3432796
  simp only [CollatzResearch.WordTrace]
  refine ⟨62602178035786920863091121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83469570714382561150788161 62602178035786920863091121)
  ·
    refine ⟨46951633526840190647318341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62602178035786920863091121 46951633526840190647318341)
    ·
      refine ⟨8803431286282535746372189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46951633526840190647318341 8803431286282535746372189)
      ·
        refine ⟨3301286732355950904889571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8803431286282535746372189 3301286732355950904889571)
        ·
          refine ⟨4951930098533926357334357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301286732355950904889571 4951930098533926357334357)
          ·
            refine ⟨14507607710548612375003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4951930098533926357334357 14507607710548612375003)
            ·
              rfl

theorem cell22_3432796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 10].length) (baseStart_3432796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432796 prefixEnd_3432796 := by exact prefixLift 3432796
  have htrace : WordTrace (prefixWord ++ tailWord_3432796) baseStart_3432796 baseEnd_3432796 := by
    simpa [prefixWord, tailWord_3432796, baseEnd_3432796] using wordTrace_append hprefix tailTrace_3432796
  have hstable : (prefixWord ++ tailWord_3432796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432796).length < 2 ^ (prefixWord ++ tailWord_3432796).sum := by decide
  have hdescent : baseEnd_3432796 < baseStart_3432796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432839 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3432839 : Nat := 118140960795 + 3432839 * 2 ^ 59
def prefixEnd_3432839 : Nat := 4983230072969 + 3 ^ 40 * 3432839 * 2
def baseEnd_3432839 : Nat := 1175130944333199823550111

theorem tailTrace_3432839 : CollatzResearch.WordTrace tailWord_3432839 prefixEnd_3432839 1175130944333199823550111 := by
  unfold tailWord_3432839
  simp only [CollatzResearch.WordTrace]
  refine ⟨125205924410418060069997571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83470616273612040046665047 125205924410418060069997571)
  ·
    refine ⟨187808886615627090104996357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125205924410418060069997571 187808886615627090104996357)
    ·
      refine ⟨35214166240430079394686817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187808886615627090104996357 35214166240430079394686817)
      ·
        refine ⟨26410624680322559546015113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35214166240430079394686817 26410624680322559546015113)
        ·
          refine ⟨19807968510241919659511335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26410624680322559546015113 19807968510241919659511335)
          ·
            refine ⟨29711952765362879489267003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19807968510241919659511335 29711952765362879489267003)
            ·
              refine ⟨44567929148044319233900505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29711952765362879489267003 44567929148044319233900505)
              ·
                refine ⟨33425946861033239425425379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44567929148044319233900505 33425946861033239425425379)
                ·
                  refine ⟨50138920291549859138138069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33425946861033239425425379 50138920291549859138138069)
                  ·
                    refine ⟨1175130944333199823550111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50138920291549859138138069 1175130944333199823550111)
                    ·
                      rfl

theorem cell22_3432839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3432839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432839 prefixEnd_3432839 := by exact prefixLift 3432839
  have htrace : WordTrace (prefixWord ++ tailWord_3432839) baseStart_3432839 baseEnd_3432839 := by
    simpa [prefixWord, tailWord_3432839, baseEnd_3432839] using wordTrace_append hprefix tailTrace_3432839
  have hstable : (prefixWord ++ tailWord_3432839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432839).length < 2 ^ (prefixWord ++ tailWord_3432839).sum := by decide
  have hdescent : baseEnd_3432839 < baseStart_3432839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432856 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_3432856 : Nat := 118140960795 + 3432856 * 2 ^ 59
def prefixEnd_3432856 : Nat := 4983230072969 + 3 ^ 40 * 3432856 * 2
def baseEnd_3432856 : Nat := 1175136763780617445875059

theorem tailTrace_3432856 : CollatzResearch.WordTrace tailWord_3432856 prefixEnd_3432856 1175136763780617445875059 := by
  unfold tailWord_3432856
  simp only [CollatzResearch.WordTrace]
  refine ⟨62603272225678235986683211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83471029634237647982244281 62603272225678235986683211)
  ·
    refine ⟨93904908338517353980024817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62603272225678235986683211 93904908338517353980024817)
    ·
      refine ⟨70428681253888015485018613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93904908338517353980024817 70428681253888015485018613)
      ·
        refine ⟨6602688867552001451720495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70428681253888015485018613 6602688867552001451720495)
        ·
          refine ⟨9904033301328002177580743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602688867552001451720495 9904033301328002177580743)
          ·
            refine ⟨14856049951992003266371115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904033301328002177580743 14856049951992003266371115)
            ·
              refine ⟨22284074927988004899556673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14856049951992003266371115 22284074927988004899556673)
              ·
                refine ⟨16713056195991003674667505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22284074927988004899556673 16713056195991003674667505)
                ·
                  refine ⟨12534792146993252756000629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16713056195991003674667505 12534792146993252756000629)
                  ·
                    refine ⟨1175136763780617445875059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12534792146993252756000629 1175136763780617445875059)
                    ·
                      rfl

theorem cell22_3432856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_3432856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432856 prefixEnd_3432856 := by exact prefixLift 3432856
  have htrace : WordTrace (prefixWord ++ tailWord_3432856) baseStart_3432856 baseEnd_3432856 := by
    simpa [prefixWord, tailWord_3432856, baseEnd_3432856] using wordTrace_append hprefix tailTrace_3432856
  have hstable : (prefixWord ++ tailWord_3432856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432856).length < 2 ^ (prefixWord ++ tailWord_3432856).sum := by decide
  have hdescent : baseEnd_3432856 < baseStart_3432856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432858 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_3432858 : Nat := 118140960795 + 3432858 * 2 ^ 59
def prefixEnd_3432858 : Nat := 4983230072969 + 3 ^ 40 * 3432858 * 2
def baseEnd_3432858 : Nat := 391712482807163369108351

theorem tailTrace_3432858 : CollatzResearch.WordTrace tailWord_3432858 prefixEnd_3432858 391712482807163369108351 := by
  unfold tailWord_3432858
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301654349337306578734807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83471078264899484209959485 31301654349337306578734807)
  ·
    refine ⟨46952481524005959868102211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31301654349337306578734807 46952481524005959868102211)
    ·
      refine ⟨70428722286008939802153317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46952481524005959868102211 70428722286008939802153317)
      ·
        refine ⟨13205385428626676212903747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70428722286008939802153317 13205385428626676212903747)
        ·
          refine ⟨19808078142940014319355621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13205385428626676212903747 19808078142940014319355621)
          ·
            refine ⟨3714014651801252684879179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19808078142940014319355621 3714014651801252684879179)
            ·
              refine ⟨5571021977701879027318769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714014651801252684879179 5571021977701879027318769)
              ·
                refine ⟨4178266483276409270489077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571021977701879027318769 4178266483276409270489077)
                ·
                  refine ⟨391712482807163369108351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4178266483276409270489077 391712482807163369108351)
                  ·
                    rfl

theorem cell22_3432858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_3432858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432858 prefixEnd_3432858 := by exact prefixLift 3432858
  have htrace : WordTrace (prefixWord ++ tailWord_3432858) baseStart_3432858 baseEnd_3432858 := by
    simpa [prefixWord, tailWord_3432858, baseEnd_3432858] using wordTrace_append hprefix tailTrace_3432858
  have hstable : (prefixWord ++ tailWord_3432858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432858).length < 2 ^ (prefixWord ++ tailWord_3432858).sum := by decide
  have hdescent : baseEnd_3432858 < baseStart_3432858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432862 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3432862 : Nat := 118140960795 + 3432862 * 2 ^ 59
def prefixEnd_3432862 : Nat := 4983230072969 + 3 ^ 40 * 3432862 * 2
def baseEnd_3432862 : Nat := 1175138817703235430225041

theorem tailTrace_3432862 : CollatzResearch.WordTrace tailWord_3432862 prefixEnd_3432862 1175138817703235430225041 := by
  unfold tailWord_3432862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15650845411166841874760605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83471175526223156665389893 15650845411166841874760605)
  ·
    refine ⟨5869067029187565703035227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15650845411166841874760605 5869067029187565703035227)
    ·
      refine ⟨8803600543781348554552841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5869067029187565703035227 8803600543781348554552841)
      ·
        refine ⟨6602700407836011415914631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8803600543781348554552841 6602700407836011415914631)
        ·
          refine ⟨9904050611754017123871947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6602700407836011415914631 9904050611754017123871947)
          ·
            refine ⟨14856075917631025685807921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904050611754017123871947 14856075917631025685807921)
            ·
              refine ⟨11142056938223269264355941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14856075917631025685807921 11142056938223269264355941)
              ·
                refine ⟨2089135675916862987066739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11142056938223269264355941 2089135675916862987066739)
                ·
                  refine ⟨3133703513875294480600109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089135675916862987066739 3133703513875294480600109)
                  ·
                    refine ⟨1175138817703235430225041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133703513875294480600109 1175138817703235430225041)
                    ·
                      rfl

theorem cell22_3432862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3432862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432862 prefixEnd_3432862 := by exact prefixLift 3432862
  have htrace : WordTrace (prefixWord ++ tailWord_3432862) baseStart_3432862 baseEnd_3432862 := by
    simpa [prefixWord, tailWord_3432862, baseEnd_3432862] using wordTrace_append hprefix tailTrace_3432862
  have hstable : (prefixWord ++ tailWord_3432862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432862).length < 2 ^ (prefixWord ++ tailWord_3432862).sum := by decide
  have hdescent : baseEnd_3432862 < baseStart_3432862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3432903 : List Nat := [1, 1, 4, 1, 1, 4, 3, 3, 4]
def baseStart_3432903 : Nat := 118140960795 + 3432903 * 2 ^ 59
def prefixEnd_3432903 : Nat := 4983230072969 + 3 ^ 40 * 3432903 * 2
def baseEnd_3432903 : Nat := 391717617613708329983305

theorem tailTrace_3432903 : CollatzResearch.WordTrace tailWord_3432903 prefixEnd_3432903 391717617613708329983305 := by
  unfold tailWord_3432903
  simp only [CollatzResearch.WordTrace]
  refine ⟨125208258682186199000327363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83472172454790799333551575 125208258682186199000327363)
  ·
    refine ⟨187812388023279298500491045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125208258682186199000327363 187812388023279298500491045)
    ·
      refine ⟨35214822754364868468842071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187812388023279298500491045 35214822754364868468842071)
      ·
        refine ⟨52822234131547302703263107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35214822754364868468842071 52822234131547302703263107)
        ·
          refine ⟨79233351197320954054894661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52822234131547302703263107 79233351197320954054894661)
          ·
            refine ⟨14856253349497678885292749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79233351197320954054894661 14856253349497678885292749)
            ·
              refine ⟨5571095006061629581984781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14856253349497678885292749 5571095006061629581984781)
              ·
                refine ⟨2089160627273111093244293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5571095006061629581984781 2089160627273111093244293)
                ·
                  refine ⟨391717617613708329983305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089160627273111093244293 391717617613708329983305)
                  ·
                    rfl

theorem cell22_3432903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 3, 4].length) (baseStart_3432903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3432903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3432903 prefixEnd_3432903 := by exact prefixLift 3432903
  have htrace : WordTrace (prefixWord ++ tailWord_3432903) baseStart_3432903 baseEnd_3432903 := by
    simpa [prefixWord, tailWord_3432903, baseEnd_3432903] using wordTrace_append hprefix tailTrace_3432903
  have hstable : (prefixWord ++ tailWord_3432903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3432903).length < 2 ^ (prefixWord ++ tailWord_3432903).sum := by decide
  have hdescent : baseEnd_3432903 < baseStart_3432903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3432903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433014 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3433014 : Nat := 118140960795 + 3433014 * 2 ^ 59
def prefixEnd_3433014 : Nat := 4983230072969 + 3 ^ 40 * 3433014 * 2
def baseEnd_3433014 : Nat := 1175190850409557700424575

theorem tailTrace_3433014 : CollatzResearch.WordTrace tailWord_3433014 prefixEnd_3433014 1175190850409557700424575 := by
  unfold tailWord_3433014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825769199049004059851131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83474871456522709971745397 7825769199049004059851131)
  ·
    refine ⟨11738653798573506089776697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7825769199049004059851131 11738653798573506089776697)
    ·
      refine ⟨8803990348930129567332523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11738653798573506089776697 8803990348930129567332523)
      ·
        refine ⟨13205985523395194350998785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8803990348930129567332523 13205985523395194350998785)
        ·
          refine ⟨9904489142546395763249089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13205985523395194350998785 9904489142546395763249089)
          ·
            refine ⟨7428366856909796822436817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9904489142546395763249089 7428366856909796822436817)
            ·
              refine ⟨5571275142682347616827613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7428366856909796822436817 5571275142682347616827613)
              ·
                refine ⟨2089228178505880356310355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5571275142682347616827613 2089228178505880356310355)
                ·
                  refine ⟨3133842267758820534465533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089228178505880356310355 3133842267758820534465533)
                  ·
                    refine ⟨1175190850409557700424575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133842267758820534465533 1175190850409557700424575)
                    ·
                      rfl

theorem cell22_3433014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3433014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433014 prefixEnd_3433014 := by exact prefixLift 3433014
  have htrace : WordTrace (prefixWord ++ tailWord_3433014) baseStart_3433014 baseEnd_3433014 := by
    simpa [prefixWord, tailWord_3433014, baseEnd_3433014] using wordTrace_append hprefix tailTrace_3433014
  have hstable : (prefixWord ++ tailWord_3433014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433014).length < 2 ^ (prefixWord ++ tailWord_3433014).sum := by decide
  have hdescent : baseEnd_3433014 < baseStart_3433014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433023 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 1, 4]
def baseStart_3433023 : Nat := 118140960795 + 3433023 * 2 ^ 59
def prefixEnd_3433023 : Nat := 4983230072969 + 3 ^ 40 * 3433023 * 2
def baseEnd_3433023 : Nat := 1175193931293484676949547

theorem tailTrace_3433023 : CollatzResearch.WordTrace tailWord_3433023 prefixEnd_3433023 1175193931293484676949547 := by
  unfold tailWord_3433023
  simp only [CollatzResearch.WordTrace]
  refine ⟨125212635441751459494695723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83475090294500972996463815 125212635441751459494695723)
  ·
    refine ⟨187818953162627189242043585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125212635441751459494695723 187818953162627189242043585)
    ·
      refine ⟨140864214871970391931532689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187818953162627189242043585 140864214871970391931532689)
      ·
        refine ⟨105648161153977793948649517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140864214871970391931532689 105648161153977793948649517)
        ·
          refine ⟨39618060432741672730743569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105648161153977793948649517 39618060432741672730743569)
          ·
            refine ⟨29713545324556254548057677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39618060432741672730743569 29713545324556254548057677)
            ·
              refine ⟨11142579496708595455521629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29713545324556254548057677 11142579496708595455521629)
              ·
                refine ⟨4178467311265723295820611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11142579496708595455521629 4178467311265723295820611)
                ·
                  refine ⟨6267700966898584943730917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178467311265723295820611 6267700966898584943730917)
                  ·
                    refine ⟨1175193931293484676949547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267700966898584943730917 1175193931293484676949547)
                    ·
                      rfl

theorem cell22_3433023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_3433023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433023 prefixEnd_3433023 := by exact prefixLift 3433023
  have htrace : WordTrace (prefixWord ++ tailWord_3433023) baseStart_3433023 baseEnd_3433023 := by
    simpa [prefixWord, tailWord_3433023, baseEnd_3433023] using wordTrace_append hprefix tailTrace_3433023
  have hstable : (prefixWord ++ tailWord_3433023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433023).length < 2 ^ (prefixWord ++ tailWord_3433023).sum := by decide
  have hdescent : baseEnd_3433023 < baseStart_3433023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433070 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3433070 : Nat := 118140960795 + 3433070 * 2 ^ 59
def prefixEnd_3433070 : Nat := 4983230072969 + 3 ^ 40 * 3433070 * 2
def baseEnd_3433070 : Nat := 1175210020353992221024403

theorem tailTrace_3433070 : CollatzResearch.WordTrace tailWord_3433070 prefixEnd_3433070 1175210020353992221024403 := by
  unfold tailWord_3433070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651793709072648315207083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83476233115054124347771109 15651793709072648315207083)
  ·
    refine ⟨23477690563608972472810625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15651793709072648315207083 23477690563608972472810625)
    ·
      refine ⟨17608267922706729354607969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23477690563608972472810625 17608267922706729354607969)
      ·
        refine ⟨13206200942030047015955977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17608267922706729354607969 13206200942030047015955977)
        ·
          refine ⟨9904650706522535261966983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13206200942030047015955977 9904650706522535261966983)
          ·
            refine ⟨14856976059783802892950475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904650706522535261966983 14856976059783802892950475)
            ·
              refine ⟨22285464089675704339425713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14856976059783802892950475 22285464089675704339425713)
              ·
                refine ⟨16714098067256778254569285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22285464089675704339425713 16714098067256778254569285)
                ·
                  refine ⟨3133893387610645922731741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16714098067256778254569285 3133893387610645922731741)
                  ·
                    refine ⟨1175210020353992221024403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133893387610645922731741 1175210020353992221024403)
                    ·
                      rfl

theorem cell22_3433070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3433070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433070 prefixEnd_3433070 := by exact prefixLift 3433070
  have htrace : WordTrace (prefixWord ++ tailWord_3433070) baseStart_3433070 baseEnd_3433070 := by
    simpa [prefixWord, tailWord_3433070, baseEnd_3433070] using wordTrace_append hprefix tailTrace_3433070
  have hstable : (prefixWord ++ tailWord_3433070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433070).length < 2 ^ (prefixWord ++ tailWord_3433070).sum := by decide
  have hdescent : baseEnd_3433070 < baseStart_3433070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433072 : List Nat := [2, 1, 1, 1, 7, 2, 1, 3, 4]
def baseStart_3433072 : Nat := 118140960795 + 3433072 * 2 ^ 59
def prefixEnd_3433072 : Nat := 4983230072969 + 3 ^ 40 * 3433072 * 2
def baseEnd_3433072 : Nat := 391736901664954960824799

theorem tailTrace_3433072 : CollatzResearch.WordTrace tailWord_3433072 prefixEnd_3433072 391736901664954960824799 := by
  unfold tailWord_3433072
  simp only [CollatzResearch.WordTrace]
  refine ⟨62607211309286970431614735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83476281745715960575486313 62607211309286970431614735)
  ·
    refine ⟨93910816963930455647422103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62607211309286970431614735 93910816963930455647422103)
    ·
      refine ⟨140866225445895683471133155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93910816963930455647422103 140866225445895683471133155)
      ·
        refine ⟨211299338168843525206699733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140866225445895683471133155 211299338168843525206699733)
        ·
          refine ⟨4952328238332270122032025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 211299338168843525206699733 4952328238332270122032025)
          ·
            refine ⟨3714246178749202591524019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4952328238332270122032025 3714246178749202591524019)
            ·
              refine ⟨5571369268123803887286029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714246178749202591524019 5571369268123803887286029)
              ·
                refine ⟨2089263475546426457732261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5571369268123803887286029 2089263475546426457732261)
                ·
                  refine ⟨391736901664954960824799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089263475546426457732261 391736901664954960824799)
                  ·
                    rfl

theorem cell22_3433072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_3433072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433072 prefixEnd_3433072 := by exact prefixLift 3433072
  have htrace : WordTrace (prefixWord ++ tailWord_3433072) baseStart_3433072 baseEnd_3433072 := by
    simpa [prefixWord, tailWord_3433072, baseEnd_3433072] using wordTrace_append hprefix tailTrace_3433072
  have hstable : (prefixWord ++ tailWord_3433072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433072).length < 2 ^ (prefixWord ++ tailWord_3433072).sum := by decide
  have hdescent : baseEnd_3433072 < baseStart_3433072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433085 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_3433085 : Nat := 118140960795 + 3433085 * 2 ^ 59
def prefixEnd_3433085 : Nat := 4983230072969 + 3 ^ 40 * 3433085 * 2
def baseEnd_3433085 : Nat := 1175215155160537181899357

theorem tailTrace_3433085 : CollatzResearch.WordTrace tailWord_3433085 prefixEnd_3433085 1175215155160537181899357 := by
  unfold tailWord_3433085
  simp only [CollatzResearch.WordTrace]
  refine ⟨125214896767526844083452709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83476597845017896055635139 125214896767526844083452709)
  ·
    refine ⟨23477793143911283265647383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125214896767526844083452709 23477793143911283265647383)
    ·
      refine ⟨35216689715866924898471075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23477793143911283265647383 35216689715866924898471075)
      ·
        refine ⟨52825034573800387347706613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35216689715866924898471075 52825034573800387347706613)
        ·
          refine ⟨4952346991293786313847495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52825034573800387347706613 4952346991293786313847495)
          ·
            refine ⟨7428520486940679470771243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952346991293786313847495 7428520486940679470771243)
            ·
              refine ⟨11142780730411019206156865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428520486940679470771243 11142780730411019206156865)
              ·
                refine ⟨8357085547808264404617649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11142780730411019206156865 8357085547808264404617649)
                ·
                  refine ⟨6267814160856198303463237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8357085547808264404617649 6267814160856198303463237)
                  ·
                    refine ⟨1175215155160537181899357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6267814160856198303463237 1175215155160537181899357)
                    ·
                      rfl

theorem cell22_3433085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_3433085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433085 prefixEnd_3433085 := by exact prefixLift 3433085
  have htrace : WordTrace (prefixWord ++ tailWord_3433085) baseStart_3433085 baseEnd_3433085 := by
    simpa [prefixWord, tailWord_3433085, baseEnd_3433085] using wordTrace_append hprefix tailTrace_3433085
  have hstable : (prefixWord ++ tailWord_3433085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433085).length < 2 ^ (prefixWord ++ tailWord_3433085).sum := by decide
  have hdescent : baseEnd_3433085 < baseStart_3433085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433149 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_3433149 : Nat := 118140960795 + 3433149 * 2 ^ 59
def prefixEnd_3433149 : Nat := 4983230072969 + 3 ^ 40 * 3433149 * 2
def baseEnd_3433149 : Nat := 1175237063668462348299161

theorem tailTrace_3433149 : CollatzResearch.WordTrace tailWord_3433149 prefixEnd_3433149 1175237063668462348299161 := by
  unfold tailWord_3433149
  simp only [CollatzResearch.WordTrace]
  refine ⟨125217231039294983013782501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83478154026196655342521667 125217231039294983013782501)
  ·
    refine ⟨23478230819867809315084219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125217231039294983013782501 23478230819867809315084219)
    ·
      refine ⟨35217346229801713972626329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23478230819867809315084219 35217346229801713972626329)
      ·
        refine ⟨26413009672351285479469747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35217346229801713972626329 26413009672351285479469747)
        ·
          refine ⟨39619514508526928219204621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26413009672351285479469747 39619514508526928219204621)
          ·
            refine ⟨14857317940697598082201733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39619514508526928219204621 14857317940697598082201733)
            ·
              refine ⟨2785747113880799640412825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14857317940697598082201733 2785747113880799640412825)
              ·
                refine ⟨2089310335410599730309619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785747113880799640412825 2089310335410599730309619)
                ·
                  refine ⟨3133965503115899595464429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089310335410599730309619 3133965503115899595464429)
                  ·
                    refine ⟨1175237063668462348299161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3133965503115899595464429 1175237063668462348299161)
                    ·
                      rfl

theorem cell22_3433149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_3433149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433149 prefixEnd_3433149 := by exact prefixLift 3433149
  have htrace : WordTrace (prefixWord ++ tailWord_3433149) baseStart_3433149 baseEnd_3433149 := by
    simpa [prefixWord, tailWord_3433149, baseEnd_3433149] using wordTrace_append hprefix tailTrace_3433149
  have hstable : (prefixWord ++ tailWord_3433149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433149).length < 2 ^ (prefixWord ++ tailWord_3433149).sum := by decide
  have hdescent : baseEnd_3433149 < baseStart_3433149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433192 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_3433192 : Nat := 118140960795 + 3433192 * 2 ^ 59
def prefixEnd_3433192 : Nat := 4983230072969 + 3 ^ 40 * 3433192 * 2
def baseEnd_3433192 : Nat := 1175251783447224569474029

theorem tailTrace_3433192 : CollatzResearch.WordTrace tailWord_3433192 prefixEnd_3433192 1175251783447224569474029 := by
  unfold tailWord_3433192
  simp only [CollatzResearch.WordTrace]
  refine ⟨62609399689069600678798915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83479199585426134238398553 62609399689069600678798915)
  ·
    refine ⟨93914099533604401018198373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62609399689069600678798915 93914099533604401018198373)
    ·
      refine ⟨17608893662550825190912195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93914099533604401018198373 17608893662550825190912195)
      ·
        refine ⟨26413340493826237786368293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17608893662550825190912195 26413340493826237786368293)
        ·
          refine ⟨4952501342592419584944055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26413340493826237786368293 4952501342592419584944055)
          ·
            refine ⟨7428752013888629377416083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952501342592419584944055 7428752013888629377416083)
            ·
              refine ⟨11143128020832944066124125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7428752013888629377416083 11143128020832944066124125)
              ·
                refine ⟨4178673007812354024796547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143128020832944066124125 4178673007812354024796547)
                ·
                  refine ⟨6268009511718531037194821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178673007812354024796547 6268009511718531037194821)
                  ·
                    refine ⟨1175251783447224569474029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6268009511718531037194821 1175251783447224569474029)
                    ·
                      rfl

theorem cell22_3433192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_3433192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433192 prefixEnd_3433192 := by exact prefixLift 3433192
  have htrace : WordTrace (prefixWord ++ tailWord_3433192) baseStart_3433192 baseEnd_3433192 := by
    simpa [prefixWord, tailWord_3433192, baseEnd_3433192] using wordTrace_append hprefix tailTrace_3433192
  have hstable : (prefixWord ++ tailWord_3433192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433192).length < 2 ^ (prefixWord ++ tailWord_3433192).sum := by decide
  have hdescent : baseEnd_3433192 < baseStart_3433192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433203 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 4, 4]
def baseStart_3433203 : Nat := 118140960795 + 3433203 * 2 ^ 59
def prefixEnd_3433203 : Nat := 4983230072969 + 3 ^ 40 * 3433203 * 2
def baseEnd_3433203 : Nat := 1175255548972024207448995

theorem tailTrace_3433203 : CollatzResearch.WordTrace tailWord_3433203 prefixEnd_3433203 1175255548972024207448995 := by
  unfold tailWord_3433203
  simp only [CollatzResearch.WordTrace]
  refine ⟨125219200581099350236248263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83479467054066233490832175 125219200581099350236248263)
  ·
    refine ⟨187828800871649025354372395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125219200581099350236248263 187828800871649025354372395)
    ·
      refine ⟨281743201307473538031558593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187828800871649025354372395 281743201307473538031558593)
      ·
        refine ⟨211307400980605153523668945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281743201307473538031558593 211307400980605153523668945)
        ·
          refine ⟨158480550735453865142751709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211307400980605153523668945 158480550735453865142751709)
          ·
            refine ⟨59430206525795199428531891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158480550735453865142751709 59430206525795199428531891)
            ·
              refine ⟨89145309788692799142797837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59430206525795199428531891 89145309788692799142797837)
              ·
                refine ⟨33429491170759799678549189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89145309788692799142797837 33429491170759799678549189)
                ·
                  refine ⟨6268029594517462439727973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33429491170759799678549189 6268029594517462439727973)
                  ·
                    refine ⟨1175255548972024207448995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6268029594517462439727973 1175255548972024207448995)
                    ·
                      rfl

theorem cell22_3433203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_3433203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433203 prefixEnd_3433203 := by exact prefixLift 3433203
  have htrace : WordTrace (prefixWord ++ tailWord_3433203) baseStart_3433203 baseEnd_3433203 := by
    simpa [prefixWord, tailWord_3433203, baseEnd_3433203] using wordTrace_append hprefix tailTrace_3433203
  have hstable : (prefixWord ++ tailWord_3433203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433203).length < 2 ^ (prefixWord ++ tailWord_3433203).sum := by decide
  have hdescent : baseEnd_3433203 < baseStart_3433203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433252 : List Nat := [2, 3, 1, 3, 4, 1, 8]
def baseStart_3433252 : Nat := 118140960795 + 3433252 * 2 ^ 59
def prefixEnd_3433252 : Nat := 4983230072969 + 3 ^ 40 * 3433252 * 2
def baseEnd_3433252 : Nat := 43528604543459422702735

theorem tailTrace_3433252 : CollatzResearch.WordTrace tailWord_3433252 prefixEnd_3433252 43528604543459422702735 := by
  unfold tailWord_3433252
  simp only [CollatzResearch.WordTrace]
  refine ⟨62610493878960915802391005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83480658505281221069854673 62610493878960915802391005)
  ·
    refine ⟨23478935204610343425896627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62610493878960915802391005 23478935204610343425896627)
    ·
      refine ⟨35218402806915515138844941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23478935204610343425896627 35218402806915515138844941)
      ·
        refine ⟨13206901052593318177066853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35218402806915515138844941 13206901052593318177066853)
        ·
          refine ⟨2476293947361247158200035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13206901052593318177066853 2476293947361247158200035)
          ·
            refine ⟨3714440921041870737300053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476293947361247158200035 3714440921041870737300053)
            ·
              refine ⟨43528604543459422702735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3714440921041870737300053 43528604543459422702735)
              ·
                rfl

theorem cell22_3433252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 8].length) (baseStart_3433252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433252 prefixEnd_3433252 := by exact prefixLift 3433252
  have htrace : WordTrace (prefixWord ++ tailWord_3433252) baseStart_3433252 baseEnd_3433252 := by
    simpa [prefixWord, tailWord_3433252, baseEnd_3433252] using wordTrace_append hprefix tailTrace_3433252
  have hstable : (prefixWord ++ tailWord_3433252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433252).length < 2 ^ (prefixWord ++ tailWord_3433252).sum := by decide
  have hdescent : baseEnd_3433252 < baseStart_3433252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433267 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 3, 3]
def baseStart_3433267 : Nat := 118140960795 + 3433267 * 2 ^ 59
def prefixEnd_3433267 : Nat := 4983230072969 + 3 ^ 40 * 3433267 * 2
def baseEnd_3433267 : Nat := 1175277457479949373848799

theorem tailTrace_3433267 : CollatzResearch.WordTrace tailWord_3433267 prefixEnd_3433267 1175277457479949373848799 := by
  unfold tailWord_3433267
  simp only [CollatzResearch.WordTrace]
  refine ⟨125221534852867489166578055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83481023235244992777718703 125221534852867489166578055)
  ·
    refine ⟨187832302279301233749867083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125221534852867489166578055 187832302279301233749867083)
    ·
      refine ⟨281748453418951850624800625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187832302279301233749867083 281748453418951850624800625)
      ·
        refine ⟨211311340064213887968600469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281748453418951850624800625 211311340064213887968600469)
        ·
          refine ⟨9905219065510025998528147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211311340064213887968600469 9905219065510025998528147)
          ·
            refine ⟨14857828598265038997792221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905219065510025998528147 14857828598265038997792221)
            ·
              refine ⟨5571685724349389624172083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14857828598265038997792221 5571685724349389624172083)
              ·
                refine ⟨8357528586524084436258125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571685724349389624172083 8357528586524084436258125)
                ·
                  refine ⟨3134073219946531663596797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8357528586524084436258125 3134073219946531663596797)
                  ·
                    refine ⟨1175277457479949373848799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134073219946531663596797 1175277457479949373848799)
                    ·
                      rfl

theorem cell22_3433267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 3, 3].length) (baseStart_3433267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433267 prefixEnd_3433267 := by exact prefixLift 3433267
  have htrace : WordTrace (prefixWord ++ tailWord_3433267) baseStart_3433267 baseEnd_3433267 := by
    simpa [prefixWord, tailWord_3433267, baseEnd_3433267] using wordTrace_append hprefix tailTrace_3433267
  have hstable : (prefixWord ++ tailWord_3433267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433267).length < 2 ^ (prefixWord ++ tailWord_3433267).sum := by decide
  have hdescent : baseEnd_3433267 < baseStart_3433267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433314 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3433314 : Nat := 118140960795 + 3433314 * 2 ^ 59
def prefixEnd_3433314 : Nat := 4983230072969 + 3 ^ 40 * 3433314 * 2
def baseEnd_3433314 : Nat := 391764515513485639307885

theorem tailTrace_3433314 : CollatzResearch.WordTrace tailWord_3433314 prefixEnd_3433314 391764515513485639307885 := by
  unfold tailWord_3433314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31305812270924304048384749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83482166055798144129025997 31305812270924304048384749)
  ·
    refine ⟨11739679601596614018144281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31305812270924304048384749 11739679601596614018144281)
    ·
      refine ⟨8804759701197460513608211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11739679601596614018144281 8804759701197460513608211)
      ·
        refine ⟨13207139551796190770412317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8804759701197460513608211 13207139551796190770412317)
        ·
          refine ⟨4952677331923571538904619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13207139551796190770412317 4952677331923571538904619)
          ·
            refine ⟨7429015997885357308356929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952677331923571538904619 7429015997885357308356929)
            ·
              refine ⟨5571761998414017981267697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7429015997885357308356929 5571761998414017981267697)
              ·
                refine ⟨4178821498810513485950773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5571761998414017981267697 4178821498810513485950773)
                ·
                  refine ⟨391764515513485639307885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4178821498810513485950773 391764515513485639307885)
                  ·
                    rfl

theorem cell22_3433314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3433314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433314 prefixEnd_3433314 := by exact prefixLift 3433314
  have htrace : WordTrace (prefixWord ++ tailWord_3433314) baseStart_3433314 baseEnd_3433314 := by
    simpa [prefixWord, tailWord_3433314, baseEnd_3433314] using wordTrace_append hprefix tailTrace_3433314
  have hstable : (prefixWord ++ tailWord_3433314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433314).length < 2 ^ (prefixWord ++ tailWord_3433314).sum := by decide
  have hdescent : baseEnd_3433314 < baseStart_3433314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433325 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 6]
def baseStart_3433325 : Nat := 118140960795 + 3433325 * 2 ^ 59
def prefixEnd_3433325 : Nat := 4983230072969 + 3 ^ 40 * 3433325 * 2
def baseEnd_3433325 : Nat := 391765770688418851966207

theorem tailTrace_3433325 : CollatzResearch.WordTrace tailWord_3433325 prefixEnd_3433325 391765770688418851966207 := by
  unfold tailWord_3433325
  simp only [CollatzResearch.WordTrace]
  refine ⟨125223650286657365072189429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83482433524438243381459619 125223650286657365072189429)
  ·
    refine ⟨11739717214374127975517759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125223650286657365072189429 11739717214374127975517759)
    ·
      refine ⟨17609575821561191963276639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11739717214374127975517759 17609575821561191963276639)
      ·
        refine ⟨26414363732341787944914959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17609575821561191963276639 26414363732341787944914959)
        ·
          refine ⟨39621545598512681917372439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26414363732341787944914959 39621545598512681917372439)
          ·
            refine ⟨59432318397769022876058659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39621545598512681917372439 59432318397769022876058659)
            ·
              refine ⟨89148477596653534314087989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59432318397769022876058659 89148477596653534314087989)
              ·
                refine ⟨8357669774686268841945749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89148477596653534314087989 8357669774686268841945749)
                ·
                  refine ⟨391765770688418851966207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8357669774686268841945749 391765770688418851966207)
                  ·
                    rfl

theorem cell22_3433325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_3433325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433325 prefixEnd_3433325 := by exact prefixLift 3433325
  have htrace : WordTrace (prefixWord ++ tailWord_3433325) baseStart_3433325 baseEnd_3433325 := by
    simpa [prefixWord, tailWord_3433325, baseEnd_3433325] using wordTrace_append hprefix tailTrace_3433325
  have hstable : (prefixWord ++ tailWord_3433325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433325).length < 2 ^ (prefixWord ++ tailWord_3433325).sum := by decide
  have hdescent : baseEnd_3433325 < baseStart_3433325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433402 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_3433402 : Nat := 118140960795 + 3433402 * 2 ^ 59
def prefixEnd_3433402 : Nat := 4983230072969 + 3 ^ 40 * 3433402 * 2
def baseEnd_3433402 : Nat := 1175323670738854021723385

theorem tailTrace_3433402 : CollatzResearch.WordTrace tailWord_3433402 prefixEnd_3433402 1175323670738854021723385 := by
  unfold tailWord_3433402
  simp only [CollatzResearch.WordTrace]
  refine ⟨31306614676844601805685615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83484305804918938148494973 31306614676844601805685615)
  ·
    refine ⟨46959922015266902708528423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31306614676844601805685615 46959922015266902708528423)
    ·
      refine ⟨70439883022900354062792635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46959922015266902708528423 70439883022900354062792635)
      ·
        refine ⟨105659824534350531094188953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70439883022900354062792635 105659824534350531094188953)
        ·
          refine ⟨79244868400762898320641715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105659824534350531094188953 79244868400762898320641715)
          ·
            refine ⟨118867302601144347480962573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79244868400762898320641715 118867302601144347480962573)
            ·
              refine ⟨44575238475429130305360965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118867302601144347480962573 44575238475429130305360965)
              ·
                refine ⟨8357857214142961932255181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44575238475429130305360965 8357857214142961932255181)
                ·
                  refine ⟨3134196455303610724595693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8357857214142961932255181 3134196455303610724595693)
                  ·
                    refine ⟨1175323670738854021723385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134196455303610724595693 1175323670738854021723385)
                    ·
                      rfl

theorem cell22_3433402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_3433402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433402 prefixEnd_3433402 := by exact prefixLift 3433402
  have htrace : WordTrace (prefixWord ++ tailWord_3433402) baseStart_3433402 baseEnd_3433402 := by
    simpa [prefixWord, tailWord_3433402, baseEnd_3433402] using wordTrace_append hprefix tailTrace_3433402
  have hstable : (prefixWord ++ tailWord_3433402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433402).length < 2 ^ (prefixWord ++ tailWord_3433402).sum := by decide
  have hdescent : baseEnd_3433402 < baseStart_3433402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433415 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 7]
def baseStart_3433415 : Nat := 118140960795 + 3433415 * 2 ^ 59
def prefixEnd_3433415 : Nat := 4983230072969 + 3 ^ 40 * 3433415 * 2
def baseEnd_3433415 : Nat := 391776040301508773716115

theorem tailTrace_3433415 : CollatzResearch.WordTrace tailWord_3433415 prefixEnd_3433415 391776040301508773716115 := by
  unfold tailWord_3433415
  simp only [CollatzResearch.WordTrace]
  refine ⟨125226932856331310442965699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83484621904220873628643799 125226932856331310442965699)
  ·
    refine ⟨187840399284496965664448549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125226932856331310442965699 187840399284496965664448549)
    ·
      refine ⟨35220074865843181062084103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187840399284496965664448549 35220074865843181062084103)
      ·
        refine ⟨52830112298764771593126155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35220074865843181062084103 52830112298764771593126155)
        ·
          refine ⟨79245168448147157389689233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52830112298764771593126155 79245168448147157389689233)
          ·
            refine ⟨59433876336110368042266925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79245168448147157389689233 59433876336110368042266925)
            ·
              refine ⟨22287703626041388015850097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59433876336110368042266925 22287703626041388015850097)
              ·
                refine ⟨16715777719531041011887573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22287703626041388015850097 16715777719531041011887573)
                ·
                  refine ⟨391776040301508773716115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16715777719531041011887573 391776040301508773716115)
                  ·
                    rfl

theorem cell22_3433415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_3433415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433415 prefixEnd_3433415 := by exact prefixLift 3433415
  have htrace : WordTrace (prefixWord ++ tailWord_3433415) baseStart_3433415 baseEnd_3433415 := by
    simpa [prefixWord, tailWord_3433415, baseEnd_3433415] using wordTrace_append hprefix tailTrace_3433415
  have hstable : (prefixWord ++ tailWord_3433415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433415).length < 2 ^ (prefixWord ++ tailWord_3433415).sum := by decide
  have hdescent : baseEnd_3433415 < baseStart_3433415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433509 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_3433509 : Nat := 118140960795 + 3433509 * 2 ^ 59
def prefixEnd_3433509 : Nat := 4983230072969 + 3 ^ 40 * 3433509 * 2
def baseEnd_3433509 : Nat := 1175360299025541409298057

theorem tailTrace_3433509 : CollatzResearch.WordTrace tailWord_3433509 prefixEnd_3433509 1175360299025541409298057 := by
  unfold tailWord_3433509
  simp only [CollatzResearch.WordTrace]
  refine ⟨125230361317990764496887581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83486907545327176331258387 125230361317990764496887581)
  ·
    refine ⟨46961385494246536686332843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125230361317990764496887581 46961385494246536686332843)
    ·
      refine ⟨70442078241369805029499265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46961385494246536686332843 70442078241369805029499265)
      ·
        refine ⟨52831558681027353772124449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70442078241369805029499265 52831558681027353772124449)
        ·
          refine ⟨39623669010770515329093337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52831558681027353772124449 39623669010770515329093337)
          ·
            refine ⟨29717751758077886496820003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39623669010770515329093337 29717751758077886496820003)
            ·
              refine ⟨44576627637116829745230005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29717751758077886496820003 44576627637116829745230005)
              ·
                refine ⟨4179058840979702788615313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44576627637116829745230005 4179058840979702788615313)
                ·
                  refine ⟨3134294130734777091461485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179058840979702788615313 3134294130734777091461485)
                  ·
                    refine ⟨1175360299025541409298057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134294130734777091461485 1175360299025541409298057)
                    ·
                      rfl

theorem cell22_3433509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_3433509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433509 prefixEnd_3433509 := by exact prefixLift 3433509
  have htrace : WordTrace (prefixWord ++ tailWord_3433509) baseStart_3433509 baseEnd_3433509 := by
    simpa [prefixWord, tailWord_3433509, baseEnd_3433509] using wordTrace_append hprefix tailTrace_3433509
  have hstable : (prefixWord ++ tailWord_3433509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433509).length < 2 ^ (prefixWord ++ tailWord_3433509).sum := by decide
  have hdescent : baseEnd_3433509 < baseStart_3433509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433605 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_3433605 : Nat := 118140960795 + 3433605 * 2 ^ 59
def prefixEnd_3433605 : Nat := 4983230072969 + 3 ^ 40 * 3433605 * 2
def baseEnd_3433605 : Nat := 1175393161787429158897763

theorem tailTrace_3433605 : CollatzResearch.WordTrace tailWord_3433605 prefixEnd_3433605 1175393161787429158897763 := by
  unfold tailWord_3433605
  simp only [CollatzResearch.WordTrace]
  refine ⟨125233862725642972892382269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83489241817095315261588179 125233862725642972892382269)
  ·
    refine ⟨46962698522116114834643351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125233862725642972892382269 46962698522116114834643351)
    ·
      refine ⟨70444047783174172251965027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46962698522116114834643351 70444047783174172251965027)
      ·
        refine ⟨105666071674761258377947541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70444047783174172251965027 105666071674761258377947541)
        ·
          refine ⟨4953097109754433986466291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105666071674761258377947541 4953097109754433986466291)
          ·
            refine ⟨7429645664631650979699437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953097109754433986466291 7429645664631650979699437)
            ·
              refine ⟨2786117124236869117387289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7429645664631650979699437 2786117124236869117387289)
              ·
                refine ⟨2089587843177651838040467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786117124236869117387289 2089587843177651838040467)
                ·
                  refine ⟨3134381764766477757060701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089587843177651838040467 3134381764766477757060701)
                  ·
                    refine ⟨1175393161787429158897763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134381764766477757060701 1175393161787429158897763)
                    ·
                      rfl

theorem cell22_3433605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_3433605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433605 prefixEnd_3433605 := by exact prefixLift 3433605
  have htrace : WordTrace (prefixWord ++ tailWord_3433605) baseStart_3433605 baseEnd_3433605 := by
    simpa [prefixWord, tailWord_3433605, baseEnd_3433605] using wordTrace_append hprefix tailTrace_3433605
  have hstable : (prefixWord ++ tailWord_3433605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433605).length < 2 ^ (prefixWord ++ tailWord_3433605).sum := by decide
  have hdescent : baseEnd_3433605 < baseStart_3433605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433618 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3433618 : Nat := 118140960795 + 3433618 * 2 ^ 59
def prefixEnd_3433618 : Nat := 4983230072969 + 3 ^ 40 * 3433618 * 2
def baseEnd_3433618 : Nat := 391799203984367152774241

theorem tailTrace_3433618 : CollatzResearch.WordTrace tailWord_3433618 prefixEnd_3433618 391799203984367152774241 := by
  unfold tailWord_3433618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31308584218648969028151377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83489557916397250741737005 31308584218648969028151377)
  ·
    refine ⟨23481438163986726771113533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31308584218648969028151377 23481438163986726771113533)
    ·
      refine ⟨8805539311495022539167575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23481438163986726771113533 8805539311495022539167575)
      ·
        refine ⟨13208308967242533808751363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8805539311495022539167575 13208308967242533808751363)
        ·
          refine ⟨19812463450863800713127045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13208308967242533808751363 19812463450863800713127045)
          ·
            refine ⟨3714836897036962633711321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19812463450863800713127045 3714836897036962633711321)
            ·
              refine ⟨2786127672777721975283491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3714836897036962633711321 2786127672777721975283491)
              ·
                refine ⟨4179191509166582962925237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786127672777721975283491 4179191509166582962925237)
                ·
                  refine ⟨391799203984367152774241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4179191509166582962925237 391799203984367152774241)
                  ·
                    rfl

theorem cell22_3433618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3433618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433618 prefixEnd_3433618 := by exact prefixLift 3433618
  have htrace : WordTrace (prefixWord ++ tailWord_3433618) baseStart_3433618 baseEnd_3433618 := by
    simpa [prefixWord, tailWord_3433618, baseEnd_3433618] using wordTrace_append hprefix tailTrace_3433618
  have hstable : (prefixWord ++ tailWord_3433618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433618).length < 2 ^ (prefixWord ++ tailWord_3433618).sum := by decide
  have hdescent : baseEnd_3433618 < baseStart_3433618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433631 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 3, 4]
def baseStart_3433631 : Nat := 118140960795 + 3433631 * 2 ^ 59
def prefixEnd_3433631 : Nat := 4983230072969 + 3 ^ 40 * 3433631 * 2
def baseEnd_3433631 : Nat := 1175402062118773757747683

theorem tailTrace_3433631 : CollatzResearch.WordTrace tailWord_3433631 prefixEnd_3433631 1175402062118773757747683 := by
  unfold tailWord_3433631
  simp only [CollatzResearch.WordTrace]
  refine ⟨125234811023548779332828747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83489874015699186221885831 125234811023548779332828747)
  ·
    refine ⟨187852216535323168999243121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125234811023548779332828747 187852216535323168999243121)
    ·
      refine ⟨140889162401492376749432341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187852216535323168999243121 140889162401492376749432341)
      ·
        refine ⟨6604179487569955160129641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140889162401492376749432341 6604179487569955160129641)
        ·
          refine ⟨4953134615677466370097231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6604179487569955160129641 4953134615677466370097231)
          ·
            refine ⟨7429701923516199555145847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953134615677466370097231 7429701923516199555145847)
            ·
              refine ⟨11144552885274299332718771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7429701923516199555145847 11144552885274299332718771)
              ·
                refine ⟨16716829327911448999078157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11144552885274299332718771 16716829327911448999078157)
                ·
                  refine ⟨6268810997966793374654309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16716829327911448999078157 6268810997966793374654309)
                  ·
                    refine ⟨1175402062118773757747683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6268810997966793374654309 1175402062118773757747683)
                    ·
                      rfl

theorem cell22_3433631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_3433631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433631 prefixEnd_3433631 := by exact prefixLift 3433631
  have htrace : WordTrace (prefixWord ++ tailWord_3433631) baseStart_3433631 baseEnd_3433631 := by
    simpa [prefixWord, tailWord_3433631, baseEnd_3433631] using wordTrace_append hprefix tailTrace_3433631
  have hstable : (prefixWord ++ tailWord_3433631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433631).length < 2 ^ (prefixWord ++ tailWord_3433631).sum := by decide
  have hdescent : baseEnd_3433631 < baseStart_3433631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433644 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_3433644 : Nat := 118140960795 + 3433644 * 2 ^ 59
def prefixEnd_3433644 : Nat := 4983230072969 + 3 ^ 40 * 3433644 * 2
def baseEnd_3433644 : Nat := 1175406512284446057172643

theorem tailTrace_3433644 : CollatzResearch.WordTrace tailWord_3433644 prefixEnd_3433644 1175406512284446057172643 := by
  unfold tailWord_3433644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62617642586250841276525993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83490190115001121702034657 62617642586250841276525993)
  ·
    refine ⟨46963231939688130957394495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62617642586250841276525993 46963231939688130957394495)
    ·
      refine ⟨70444847909532196436091743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46963231939688130957394495 70444847909532196436091743)
      ·
        refine ⟨105667271864298294654137615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70444847909532196436091743 105667271864298294654137615)
        ·
          refine ⟨158500907796447441981206423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105667271864298294654137615 158500907796447441981206423)
          ·
            refine ⟨237751361694671162971809635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158500907796447441981206423 237751361694671162971809635)
            ·
              refine ⟨356627042542006744457714453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237751361694671162971809635 356627042542006744457714453)
              ·
                refine ⟨16716892619156566146455365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 356627042542006744457714453 16716892619156566146455365)
                ·
                  refine ⟨3134417366091856152460381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16716892619156566146455365 3134417366091856152460381)
                  ·
                    refine ⟨1175406512284446057172643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134417366091856152460381 1175406512284446057172643)
                    ·
                      rfl

theorem cell22_3433644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_3433644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433644 prefixEnd_3433644 := by exact prefixLift 3433644
  have htrace : WordTrace (prefixWord ++ tailWord_3433644) baseStart_3433644 baseEnd_3433644 := by
    simpa [prefixWord, tailWord_3433644, baseEnd_3433644] using wordTrace_append hprefix tailTrace_3433644
  have hstable : (prefixWord ++ tailWord_3433644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433644).length < 2 ^ (prefixWord ++ tailWord_3433644).sum := by decide
  have hdescent : baseEnd_3433644 < baseStart_3433644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433657 : List Nat := [1, 2, 1, 4, 1, 13]
def baseStart_3433657 : Nat := 118140960795 + 3433657 * 2 ^ 59
def prefixEnd_3433657 : Nat := 4983230072969 + 3 ^ 40 * 3433657 * 2
def baseEnd_3433657 : Nat := 14511246450001461192563

theorem tailTrace_3433657 : CollatzResearch.WordTrace tailWord_3433657 prefixEnd_3433657 14511246450001461192563 := by
  unfold tailWord_3433657
  simp only [CollatzResearch.WordTrace]
  refine ⟨125235759321454585773275225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83490506214303057182183483 125235759321454585773275225)
  ·
    refine ⟨93926819491090939329956419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125235759321454585773275225 93926819491090939329956419)
    ·
      refine ⟨140890229236636408994934629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93926819491090939329956419 140890229236636408994934629)
      ·
        refine ⟨26416917981869326686550243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140890229236636408994934629 26416917981869326686550243)
        ·
          refine ⟨39625376972803990029825365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26416917981869326686550243 39625376972803990029825365)
          ·
            refine ⟨14511246450001461192563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 39625376972803990029825365 14511246450001461192563)
            ·
              rfl

theorem cell22_3433657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 13].length) (baseStart_3433657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433657 prefixEnd_3433657 := by exact prefixLift 3433657
  have htrace : WordTrace (prefixWord ++ tailWord_3433657) baseStart_3433657 baseEnd_3433657 := by
    simpa [prefixWord, tailWord_3433657, baseEnd_3433657] using wordTrace_append hprefix tailTrace_3433657
  have hstable : (prefixWord ++ tailWord_3433657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433657).length < 2 ^ (prefixWord ++ tailWord_3433657).sum := by decide
  have hdescent : baseEnd_3433657 < baseStart_3433657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433661 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_3433661 : Nat := 118140960795 + 3433661 * 2 ^ 59
def prefixEnd_3433661 : Nat := 4983230072969 + 3 ^ 40 * 3433661 * 2
def baseEnd_3433661 : Nat := 1175412331731863679497591

theorem tailTrace_3433661 : CollatzResearch.WordTrace tailWord_3433661 prefixEnd_3433661 1175412331731863679497591 := by
  unfold tailWord_3433661
  simp only [CollatzResearch.WordTrace]
  refine ⟨125235905213440094456420837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83490603475626729637613891 125235905213440094456420837)
  ·
    refine ⟨23481732227520017710578907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125235905213440094456420837 23481732227520017710578907)
    ·
      refine ⟨35222598341280026565868361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23481732227520017710578907 35222598341280026565868361)
      ·
        refine ⟨26416948755960019924401271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35222598341280026565868361 26416948755960019924401271)
        ·
          refine ⟨39625423133940029886601907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26416948755960019924401271 39625423133940029886601907)
          ·
            refine ⟨59438134700910044829902861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39625423133940029886601907 59438134700910044829902861)
            ·
              refine ⟨22289300512841266811213573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59438134700910044829902861 22289300512841266811213573)
              ·
                refine ⟨4179243846157737527102545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22289300512841266811213573 4179243846157737527102545)
                ·
                  refine ⟨3134432884618303145326909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179243846157737527102545 3134432884618303145326909)
                  ·
                    refine ⟨1175412331731863679497591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134432884618303145326909 1175412331731863679497591)
                    ·
                      rfl

theorem cell22_3433661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_3433661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433661 prefixEnd_3433661 := by exact prefixLift 3433661
  have htrace : WordTrace (prefixWord ++ tailWord_3433661) baseStart_3433661 baseEnd_3433661 := by
    simpa [prefixWord, tailWord_3433661, baseEnd_3433661] using wordTrace_append hprefix tailTrace_3433661
  have hstable : (prefixWord ++ tailWord_3433661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433661).length < 2 ^ (prefixWord ++ tailWord_3433661).sum := by decide
  have hdescent : baseEnd_3433661 < baseStart_3433661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433674 : List Nat := [3, 1, 2, 1, 3, 2, 3, 7]
def baseStart_3433674 : Nat := 118140960795 + 3433674 * 2 ^ 59
def prefixEnd_3433674 : Nat := 4983230072969 + 3 ^ 40 * 3433674 * 2
def baseEnd_3433674 : Nat := 130601864655281775435839

theorem tailTrace_3433674 : CollatzResearch.WordTrace tailWord_3433674 prefixEnd_3433674 130601864655281775435839 := by
  unfold tailWord_3433674
  simp only [CollatzResearch.WordTrace]
  refine ⟨31309094840598249419161019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83490919574928665117762717 31309094840598249419161019)
  ·
    refine ⟨46963642260897374128741529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31309094840598249419161019 46963642260897374128741529)
    ·
      refine ⟨35222731695673030596556147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46963642260897374128741529 35222731695673030596556147)
      ·
        refine ⟨52834097543509545894834221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35222731695673030596556147 52834097543509545894834221)
        ·
          refine ⟨19812786578816079710562833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52834097543509545894834221 19812786578816079710562833)
          ·
            refine ⟨14859589934112059782922125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19812786578816079710562833 14859589934112059782922125)
            ·
              refine ⟨5572346225292022418595797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14859589934112059782922125 5572346225292022418595797)
              ·
                refine ⟨130601864655281775435839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5572346225292022418595797 130601864655281775435839)
                ·
                  rfl

theorem cell22_3433674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_3433674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433674 prefixEnd_3433674 := by exact prefixLift 3433674
  have htrace : WordTrace (prefixWord ++ tailWord_3433674) baseStart_3433674 baseEnd_3433674 := by
    simpa [prefixWord, tailWord_3433674, baseEnd_3433674] using wordTrace_append hprefix tailTrace_3433674
  have hstable : (prefixWord ++ tailWord_3433674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433674).length < 2 ^ (prefixWord ++ tailWord_3433674).sum := by decide
  have hdescent : baseEnd_3433674 < baseStart_3433674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433757 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_3433757 : Nat := 118140960795 + 3433757 * 2 ^ 59
def prefixEnd_3433757 : Nat := 4983230072969 + 3 ^ 40 * 3433757 * 2
def baseEnd_3433757 : Nat := 1175445194493751429097297

theorem tailTrace_3433757 : CollatzResearch.WordTrace tailWord_3433757 prefixEnd_3433757 1175445194493751429097297 := by
  unfold tailWord_3433757
  simp only [CollatzResearch.WordTrace]
  refine ⟨125239406621092302851915525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83492937747394868567943683 125239406621092302851915525)
  ·
    refine ⟨23482388741454806784734161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125239406621092302851915525 23482388741454806784734161)
    ·
      refine ⟨17611791556091105088550621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23482388741454806784734161 17611791556091105088550621)
      ·
        refine ⟨6604421833534164408206483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17611791556091105088550621 6604421833534164408206483)
        ·
          refine ⟨9906632750301246612309725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604421833534164408206483 9906632750301246612309725)
          ·
            refine ⟨3714987281362967479616147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9906632750301246612309725 3714987281362967479616147)
            ·
              refine ⟨5572480922044451219424221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714987281362967479616147 5572480922044451219424221)
              ·
                refine ⟨2089680345766669207284083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5572480922044451219424221 2089680345766669207284083)
                ·
                  refine ⟨3134520518650003810926125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089680345766669207284083 3134520518650003810926125)
                  ·
                    refine ⟨1175445194493751429097297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134520518650003810926125 1175445194493751429097297)
                    ·
                      rfl

theorem cell22_3433757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_3433757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433757 prefixEnd_3433757 := by exact prefixLift 3433757
  have htrace : WordTrace (prefixWord ++ tailWord_3433757) baseStart_3433757 baseEnd_3433757 := by
    simpa [prefixWord, tailWord_3433757, baseEnd_3433757] using wordTrace_append hprefix tailTrace_3433757
  have hstable : (prefixWord ++ tailWord_3433757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433757).length < 2 ^ (prefixWord ++ tailWord_3433757).sum := by decide
  have hdescent : baseEnd_3433757 < baseStart_3433757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433781 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 6]
def baseStart_3433781 : Nat := 118140960795 + 3433781 * 2 ^ 59
def prefixEnd_3433781 : Nat := 4983230072969 + 3 ^ 40 * 3433781 * 2
def baseEnd_3433781 : Nat := 391817803394741122165741

theorem tailTrace_3433781 : CollatzResearch.WordTrace tailWord_3433781 prefixEnd_3433781 391817803394741122165741 := by
  unfold tailWord_3433781
  simp only [CollatzResearch.WordTrace]
  refine ⟨125240281973005354950789197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83493521315336903300526131 125240281973005354950789197)
  ·
    refine ⟨46965105739877008106545949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125240281973005354950789197 46965105739877008106545949)
    ·
      refine ⟨17611914652453878039954731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46965105739877008106545949 17611914652453878039954731)
      ·
        refine ⟨26417871978680817059932097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17611914652453878039954731 26417871978680817059932097)
        ·
          refine ⟨19813403984010612794949073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26417871978680817059932097 19813403984010612794949073)
          ·
            refine ⟨14860052988007959596211805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19813403984010612794949073 14860052988007959596211805)
            ·
              refine ⟨5572519870502984848579427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14860052988007959596211805 5572519870502984848579427)
              ·
                refine ⟨8358779805754477272869141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572519870502984848579427 8358779805754477272869141)
                ·
                  refine ⟨391817803394741122165741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8358779805754477272869141 391817803394741122165741)
                  ·
                    rfl

theorem cell22_3433781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_3433781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433781 prefixEnd_3433781 := by exact prefixLift 3433781
  have htrace : WordTrace (prefixWord ++ tailWord_3433781) baseStart_3433781 baseEnd_3433781 := by
    simpa [prefixWord, tailWord_3433781, baseEnd_3433781] using wordTrace_append hprefix tailTrace_3433781
  have hstable : (prefixWord ++ tailWord_3433781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433781).length < 2 ^ (prefixWord ++ tailWord_3433781).sum := by decide
  have hdescent : baseEnd_3433781 < baseStart_3433781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433809 : List Nat := [1, 2, 2, 1, 4, 1, 1, 10]
def baseStart_3433809 : Nat := 118140960795 + 3433809 * 2 ^ 59
def prefixEnd_3433809 : Nat := 4983230072969 + 3 ^ 40 * 3433809 * 2
def baseEnd_3433809 : Nat := 130606999461826736310793

theorem tailTrace_3433809 : CollatzResearch.WordTrace tailWord_3433809 prefixEnd_3433809 130606999461826736310793 := by
  unfold tailWord_3433809
  simp only [CollatzResearch.WordTrace]
  refine ⟨125241303216903915732808481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83494202144602610488538987 125241303216903915732808481)
  ·
    refine ⟨93930977412677936799606361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125241303216903915732808481 93930977412677936799606361)
    ·
      refine ⟨70448233059508452599704771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93930977412677936799606361 70448233059508452599704771)
      ·
        refine ⟨105672349589262678899557157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70448233059508452599704771 105672349589262678899557157)
        ·
          refine ⟨19813565547986752293666967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105672349589262678899557157 19813565547986752293666967)
          ·
            refine ⟨29720348321980128440500451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19813565547986752293666967 29720348321980128440500451)
            ·
              refine ⟨44580522482970192660750677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29720348321980128440500451 44580522482970192660750677)
              ·
                refine ⟨130606999461826736310793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44580522482970192660750677 130606999461826736310793)
                ·
                  rfl

theorem cell22_3433809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 10].length) (baseStart_3433809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433809 prefixEnd_3433809 := by exact prefixLift 3433809
  have htrace : WordTrace (prefixWord ++ tailWord_3433809) baseStart_3433809 baseEnd_3433809 := by
    simpa [prefixWord, tailWord_3433809, baseEnd_3433809] using wordTrace_append hprefix tailTrace_3433809
  have hstable : (prefixWord ++ tailWord_3433809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433809).length < 2 ^ (prefixWord ++ tailWord_3433809).sum := by decide
  have hdescent : baseEnd_3433809 < baseStart_3433809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433811 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 2, 4]
def baseStart_3433811 : Nat := 118140960795 + 3433811 * 2 ^ 59
def prefixEnd_3433811 : Nat := 4983230072969 + 3 ^ 40 * 3433811 * 2
def baseEnd_3433811 : Nat := 1175463679797313288247131

theorem tailTrace_3433811 : CollatzResearch.WordTrace tailWord_3433811 prefixEnd_3433811 1175463679797313288247131 := by
  unfold tailWord_3433811
  simp only [CollatzResearch.WordTrace]
  refine ⟨125241376162896670074381287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83494250775264446716254191 125241376162896670074381287)
  ·
    refine ⟨187862064244345005111571931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125241376162896670074381287 187862064244345005111571931)
    ·
      refine ⟨281793096366517507667357897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187862064244345005111571931 281793096366517507667357897)
      ·
        refine ⟨211344822274888130750518423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281793096366517507667357897 211344822274888130750518423)
        ·
          refine ⟨317017233412332196125777635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211344822274888130750518423 317017233412332196125777635)
          ·
            refine ⟨475525850118498294188666453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317017233412332196125777635 475525850118498294188666453)
            ·
              refine ⟨5572568556076151885023435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 475525850118498294188666453 5572568556076151885023435)
              ·
                refine ⟨8358852834114227827535153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572568556076151885023435 8358852834114227827535153)
                ·
                  refine ⟨6269139625585670870651365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8358852834114227827535153 6269139625585670870651365)
                  ·
                    refine ⟨1175463679797313288247131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269139625585670870651365 1175463679797313288247131)
                    ·
                      rfl

theorem cell22_3433811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].length) (baseStart_3433811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433811 prefixEnd_3433811 := by exact prefixLift 3433811
  have htrace : WordTrace (prefixWord ++ tailWord_3433811) baseStart_3433811 baseEnd_3433811 := by
    simpa [prefixWord, tailWord_3433811, baseEnd_3433811] using wordTrace_append hprefix tailTrace_3433811
  have hstable : (prefixWord ++ tailWord_3433811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433811).length < 2 ^ (prefixWord ++ tailWord_3433811).sum := by decide
  have hdescent : baseEnd_3433811 < baseStart_3433811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433832 : List Nat := [2, 1, 4, 2, 3, 2, 2, 2, 4]
def baseStart_3433832 : Nat := 118140960795 + 3433832 * 2 ^ 59
def prefixEnd_3433832 : Nat := 4983230072969 + 3 ^ 40 * 3433832 * 2
def baseEnd_3433832 : Nat := 391823622842158744490689

theorem tailTrace_3433832 : CollatzResearch.WordTrace tailWord_3433832 prefixEnd_3433832 391823622842158744490689 := by
  unfold tailWord_3433832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62621071047910295330447875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83494761397213727107263833 62621071047910295330447875)
  ·
    refine ⟨93931606571865442995671813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62621071047910295330447875 93931606571865442995671813)
    ·
      refine ⟨17612176232224770561688465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93931606571865442995671813 17612176232224770561688465)
      ·
        refine ⟨13209132174168577921266349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17612176232224770561688465 13209132174168577921266349)
        ·
          refine ⟨4953424565313216720474881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13209132174168577921266349 4953424565313216720474881)
          ·
            refine ⟨3715068423984912540356161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4953424565313216720474881 3715068423984912540356161)
            ·
              refine ⟨2786301317988684405267121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715068423984912540356161 2786301317988684405267121)
              ·
                refine ⟨2089725988491513303950341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786301317988684405267121 2089725988491513303950341)
                ·
                  refine ⟨391823622842158744490689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2089725988491513303950341 391823622842158744490689)
                  ·
                    rfl

theorem cell22_3433832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_3433832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433832 prefixEnd_3433832 := by exact prefixLift 3433832
  have htrace : WordTrace (prefixWord ++ tailWord_3433832) baseStart_3433832 baseEnd_3433832 := by
    simpa [prefixWord, tailWord_3433832, baseEnd_3433832] using wordTrace_append hprefix tailTrace_3433832
  have hstable : (prefixWord ++ tailWord_3433832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433832).length < 2 ^ (prefixWord ++ tailWord_3433832).sum := by decide
  have hdescent : baseEnd_3433832 < baseStart_3433832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433839 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_3433839 : Nat := 118140960795 + 3433839 * 2 ^ 59
def prefixEnd_3433839 : Nat := 4983230072969 + 3 ^ 40 * 3433839 * 2
def baseEnd_3433839 : Nat := 1175473264769530548547045

theorem tailTrace_3433839 : CollatzResearch.WordTrace tailWord_3433839 prefixEnd_3433839 1175473264769530548547045 := by
  unfold tailWord_3433839
  simp only [CollatzResearch.WordTrace]
  refine ⟨125242397406795230856400571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83494931604530153904267047 125242397406795230856400571)
  ·
    refine ⟨187863596110192846284600857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125242397406795230856400571 187863596110192846284600857)
    ·
      refine ⟨140897697082644634713450643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187863596110192846284600857 140897697082644634713450643)
      ·
        refine ⟨211346545623966952070175965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140897697082644634713450643 211346545623966952070175965)
        ·
          refine ⟨79254954608987607026315987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211346545623966952070175965 79254954608987607026315987)
          ·
            refine ⟨118882431913481410539473981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79254954608987607026315987 118882431913481410539473981)
            ·
              refine ⟨44580911967555528952302743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118882431913481410539473981 44580911967555528952302743)
              ·
                refine ⟨66871367951333293428454115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44580911967555528952302743 66871367951333293428454115)
                ·
                  refine ⟨100307051926999940142681173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66871367951333293428454115 100307051926999940142681173)
                  ·
                    refine ⟨1175473264769530548547045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100307051926999940142681173 1175473264769530548547045)
                    ·
                      rfl

theorem cell22_3433839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_3433839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433839 prefixEnd_3433839 := by exact prefixLift 3433839
  have htrace : WordTrace (prefixWord ++ tailWord_3433839) baseStart_3433839 baseEnd_3433839 := by
    simpa [prefixWord, tailWord_3433839, baseEnd_3433839] using wordTrace_append hprefix tailTrace_3433839
  have hstable : (prefixWord ++ tailWord_3433839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433839).length < 2 ^ (prefixWord ++ tailWord_3433839).sum := by decide
  have hdescent : baseEnd_3433839 < baseStart_3433839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433931 : List Nat := [1, 1, 1, 1, 3, 3, 2, 4, 1, 5]
def baseStart_3433931 : Nat := 118140960795 + 3433931 * 2 ^ 59
def prefixEnd_3433931 : Nat := 4983230072969 + 3 ^ 40 * 3433931 * 2
def baseEnd_3433931 : Nat := 1175504758249672975246763

theorem tailTrace_3433931 : CollatzResearch.WordTrace tailWord_3433931 prefixEnd_3433931 1175504758249672975246763 := by
  unfold tailWord_3433931
  simp only [CollatzResearch.WordTrace]
  refine ⟨125245752922461930568749647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83497168614974620379166431 125245752922461930568749647)
  ·
    refine ⟨187868629383692895853124471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125245752922461930568749647 187868629383692895853124471)
    ·
      refine ⟨281802944075539343779686707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187868629383692895853124471 281802944075539343779686707)
      ·
        refine ⟨422704416113309015669530061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281802944075539343779686707 422704416113309015669530061)
        ·
          refine ⟨158514156042490880876073773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422704416113309015669530061 158514156042490880876073773)
          ·
            refine ⟨59442808515934080328527665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158514156042490880876073773 59442808515934080328527665)
            ·
              refine ⟨44582106386950560246395749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59442808515934080328527665 44582106386950560246395749)
              ·
                refine ⟨8359144947553230046199203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44582106386950560246395749 8359144947553230046199203)
                ·
                  refine ⟨12538717421329845069298805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8359144947553230046199203 12538717421329845069298805)
                  ·
                    refine ⟨1175504758249672975246763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12538717421329845069298805 1175504758249672975246763)
                    ·
                      rfl

theorem cell22_3433931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_3433931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433931 prefixEnd_3433931 := by exact prefixLift 3433931
  have htrace : WordTrace (prefixWord ++ tailWord_3433931) baseStart_3433931 baseEnd_3433931 := by
    simpa [prefixWord, tailWord_3433931, baseEnd_3433931] using wordTrace_append hprefix tailTrace_3433931
  have hstable : (prefixWord ++ tailWord_3433931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433931).length < 2 ^ (prefixWord ++ tailWord_3433931).sum := by decide
  have hdescent : baseEnd_3433931 < baseStart_3433931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3433982 : List Nat := [4, 2, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3433982 : Nat := 118140960795 + 3433982 * 2 ^ 59
def prefixEnd_3433982 : Nat := 4983230072969 + 3 ^ 40 * 3433982 * 2
def baseEnd_3433982 : Nat := 1175522216591925842221607

theorem tailTrace_3433982 : CollatzResearch.WordTrace tailWord_3433982 prefixEnd_3433982 1175522216591925842221607 := by
  unfold tailWord_3433982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15655951630659645784857025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83498408696851444185904133 15655951630659645784857025)
  ·
    refine ⟨11741963722994734338642769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15655951630659645784857025 11741963722994734338642769)
    ·
      refine ⟨8806472792246050753982077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11741963722994734338642769 8806472792246050753982077)
      ·
        refine ⟨3302427297092269032743279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8806472792246050753982077 3302427297092269032743279)
        ·
          refine ⟨4953640945638403549114919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302427297092269032743279 4953640945638403549114919)
          ·
            refine ⟨7430461418457605323672379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953640945638403549114919 7430461418457605323672379)
            ·
              refine ⟨11145692127686407985508569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430461418457605323672379 11145692127686407985508569)
              ·
                refine ⟨8359269095764805989131427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11145692127686407985508569 8359269095764805989131427)
                ·
                  refine ⟨12538903643647208983697141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8359269095764805989131427 12538903643647208983697141)
                  ·
                    refine ⟨1175522216591925842221607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12538903643647208983697141 1175522216591925842221607)
                    ·
                      rfl

theorem cell22_3433982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3433982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3433982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3433982 prefixEnd_3433982 := by exact prefixLift 3433982
  have htrace : WordTrace (prefixWord ++ tailWord_3433982) baseStart_3433982 baseEnd_3433982 := by
    simpa [prefixWord, tailWord_3433982, baseEnd_3433982] using wordTrace_append hprefix tailTrace_3433982
  have hstable : (prefixWord ++ tailWord_3433982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3433982).length < 2 ^ (prefixWord ++ tailWord_3433982).sum := by decide
  have hdescent : baseEnd_3433982 < baseStart_3433982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3433982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434044 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_3434044 : Nat := 118140960795 + 3434044 * 2 ^ 59
def prefixEnd_3434044 : Nat := 4983230072969 + 3 ^ 40 * 3434044 * 2
def baseEnd_3434044 : Nat := 1175543440458978347171417

theorem tailTrace_3434044 : CollatzResearch.WordTrace tailWord_3434044 prefixEnd_3434044 1175543440458978347171417 := by
  unfold tailWord_3434044
  simp only [CollatzResearch.WordTrace]
  refine ⟨62624937185526275433806593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83499916247368367245075457 62624937185526275433806593)
  ·
    refine ⟨46968702889144706575354945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62624937185526275433806593 46968702889144706575354945)
    ·
      refine ⟨35226527166858529931516209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46968702889144706575354945 35226527166858529931516209)
      ·
        refine ⟨26419895375143897448637157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35226527166858529931516209 26419895375143897448637157)
        ·
          refine ⟨4953730382839480771619467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26419895375143897448637157 4953730382839480771619467)
          ·
            refine ⟨7430595574259221157429201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4953730382839480771619467 7430595574259221157429201)
            ·
              refine ⟨5572946680694415868071901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7430595574259221157429201 5572946680694415868071901)
              ·
                refine ⟨2089855005260405950526963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5572946680694415868071901 2089855005260405950526963)
                ·
                  refine ⟨3134782507890608925790445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089855005260405950526963 3134782507890608925790445)
                  ·
                    refine ⟨1175543440458978347171417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134782507890608925790445 1175543440458978347171417)
                    ·
                      rfl

theorem cell22_3434044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_3434044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434044 prefixEnd_3434044 := by exact prefixLift 3434044
  have htrace : WordTrace (prefixWord ++ tailWord_3434044) baseStart_3434044 baseEnd_3434044 := by
    simpa [prefixWord, tailWord_3434044, baseEnd_3434044] using wordTrace_append hprefix tailTrace_3434044
  have hstable : (prefixWord ++ tailWord_3434044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434044).length < 2 ^ (prefixWord ++ tailWord_3434044).sum := by decide
  have hdescent : baseEnd_3434044 < baseStart_3434044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434113 : List Nat := [1, 2, 4, 2, 1, 2, 10]
def baseStart_3434113 : Nat := 118140960795 + 3434113 * 2 ^ 59
def prefixEnd_3434113 : Nat := 4983230072969 + 3 ^ 40 * 3434113 * 2
def baseEnd_3434113 : Nat := 43539520761817969155415

theorem tailTrace_3434113 : CollatzResearch.WordTrace tailWord_3434113 prefixEnd_3434113 43539520761817969155415 := by
  unfold tailWord_3434113
  simp only [CollatzResearch.WordTrace]
  refine ⟨125252391007802575651874993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83501594005201717101249995 125252391007802575651874993)
  ·
    refine ⟨93939293255851931738906245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125252391007802575651874993 93939293255851931738906245)
    ·
      refine ⟨17613617485472237201044921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93939293255851931738906245 17613617485472237201044921)
      ·
        refine ⟨13210213114104177900783691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17613617485472237201044921 13210213114104177900783691)
        ·
          refine ⟨19815319671156266851175537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13210213114104177900783691 19815319671156266851175537)
          ·
            refine ⟨14861489753367200138381653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19815319671156266851175537 14861489753367200138381653)
            ·
              refine ⟨43539520761817969155415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14861489753367200138381653 43539520761817969155415)
              ·
                rfl

theorem cell22_3434113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 10].length) (baseStart_3434113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434113 prefixEnd_3434113 := by exact prefixLift 3434113
  have htrace : WordTrace (prefixWord ++ tailWord_3434113) baseStart_3434113 baseEnd_3434113 := by
    simpa [prefixWord, tailWord_3434113, baseEnd_3434113] using wordTrace_append hprefix tailTrace_3434113
  have hstable : (prefixWord ++ tailWord_3434113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434113).length < 2 ^ (prefixWord ++ tailWord_3434113).sum := by decide
  have hdescent : baseEnd_3434113 < baseStart_3434113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434175 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 5]
def baseStart_3434175 : Nat := 118140960795 + 3434175 * 2 ^ 59
def prefixEnd_3434175 : Nat := 4983230072969 + 3 ^ 40 * 3434175 * 2
def baseEnd_3434175 : Nat := 391862761478712557382005

theorem tailTrace_3434175 : CollatzResearch.WordTrace tailWord_3434175 prefixEnd_3434175 391862761478712557382005 := by
  unfold tailWord_3434175
  simp only [CollatzResearch.WordTrace]
  refine ⟨125254652333577960240631979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83503101555718640160421319 125254652333577960240631979)
  ·
    refine ⟨187881978500366940360947969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125254652333577960240631979 187881978500366940360947969)
    ·
      refine ⟨140911483875275205270710977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187881978500366940360947969 140911483875275205270710977)
      ·
        refine ⟨105683612906456403953033233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140911483875275205270710977 105683612906456403953033233)
        ·
          refine ⟨79262709679842302964774925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105683612906456403953033233 79262709679842302964774925)
          ·
            refine ⟨29723516129940863611790597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79262709679842302964774925 29723516129940863611790597)
            ·
              refine ⟨5573159274363911927210737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29723516129940863611790597 5573159274363911927210737)
              ·
                refine ⟨4179869455772933945408053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5573159274363911927210737 4179869455772933945408053)
                ·
                  refine ⟨391862761478712557382005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4179869455772933945408053 391862761478712557382005)
                  ·
                    rfl

theorem cell22_3434175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 5].length) (baseStart_3434175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434175 prefixEnd_3434175 := by exact prefixLift 3434175
  have htrace : WordTrace (prefixWord ++ tailWord_3434175) baseStart_3434175 baseEnd_3434175 := by
    simpa [prefixWord, tailWord_3434175, baseEnd_3434175] using wordTrace_append hprefix tailTrace_3434175
  have hstable : (prefixWord ++ tailWord_3434175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434175).length < 2 ^ (prefixWord ++ tailWord_3434175).sum := by decide
  have hdescent : baseEnd_3434175 < baseStart_3434175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434190 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3434190 : Nat := 118140960795 + 3434190 * 2 ^ 59
def prefixEnd_3434190 : Nat := 4983230072969 + 3 ^ 40 * 3434190 * 2
def baseEnd_3434190 : Nat := 1175593419242682633020969

theorem tailTrace_3434190 : CollatzResearch.WordTrace tailWord_3434190 prefixEnd_3434190 1175593419242682633020969 := by
  unfold tailWord_3434190
  simp only [CollatzResearch.WordTrace]
  refine ⟨15656899928565452225303503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83503466285682411868285349 15656899928565452225303503)
  ·
    refine ⟨23485349892848178337955255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15656899928565452225303503 23485349892848178337955255)
    ·
      refine ⟨35228024839272267506932883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23485349892848178337955255 35228024839272267506932883)
      ·
        refine ⟨52842037258908401260399325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35228024839272267506932883 52842037258908401260399325)
        ·
          refine ⟨19815763972090650472649747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52842037258908401260399325 19815763972090650472649747)
          ·
            refine ⟨29723645958135975708974621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19815763972090650472649747 29723645958135975708974621)
            ·
              refine ⟨11146367234300990890865483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29723645958135975708974621 11146367234300990890865483)
              ·
                refine ⟨16719550851451486336298225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11146367234300990890865483 16719550851451486336298225)
                ·
                  refine ⟨12539663138588614752223669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16719550851451486336298225 12539663138588614752223669)
                  ·
                    refine ⟨1175593419242682633020969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12539663138588614752223669 1175593419242682633020969)
                    ·
                      rfl

theorem cell22_3434190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3434190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434190 prefixEnd_3434190 := by exact prefixLift 3434190
  have htrace : WordTrace (prefixWord ++ tailWord_3434190) baseStart_3434190 baseEnd_3434190 := by
    simpa [prefixWord, tailWord_3434190, baseEnd_3434190] using wordTrace_append hprefix tailTrace_3434190
  have hstable : (prefixWord ++ tailWord_3434190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434190).length < 2 ^ (prefixWord ++ tailWord_3434190).sum := by decide
  have hdescent : baseEnd_3434190 < baseStart_3434190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434222 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3434222 : Nat := 118140960795 + 3434222 * 2 ^ 59
def prefixEnd_3434222 : Nat := 4983230072969 + 3 ^ 40 * 3434222 * 2
def baseEnd_3434222 : Nat := 1175604373496645216220871

theorem tailTrace_3434222 : CollatzResearch.WordTrace tailWord_3434222 prefixEnd_3434222 1175604373496645216220871 := by
  unfold tailWord_3434222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15657045820550960908449115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83504244376271791511728613 15657045820550960908449115)
  ·
    refine ⟨23485568730826441362673673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15657045820550960908449115 23485568730826441362673673)
    ·
      refine ⟨17614176548119831022005255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23485568730826441362673673 17614176548119831022005255)
      ·
        refine ⟨26421264822179746533007883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17614176548119831022005255 26421264822179746533007883)
        ·
          refine ⟨39631897233269619799511825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26421264822179746533007883 39631897233269619799511825)
          ·
            refine ⟨29723922924952214849633869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39631897233269619799511825 29723922924952214849633869)
            ·
              refine ⟨11146471096857080568612701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29723922924952214849633869 11146471096857080568612701)
              ·
                refine ⟨4179926661321405213229763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11146471096857080568612701 4179926661321405213229763)
                ·
                  refine ⟨6269889991982107819844645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4179926661321405213229763 6269889991982107819844645)
                  ·
                    refine ⟨1175604373496645216220871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6269889991982107819844645 1175604373496645216220871)
                    ·
                      rfl

theorem cell22_3434222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3434222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434222 prefixEnd_3434222 := by exact prefixLift 3434222
  have htrace : WordTrace (prefixWord ++ tailWord_3434222) baseStart_3434222 baseEnd_3434222 := by
    simpa [prefixWord, tailWord_3434222, baseEnd_3434222] using wordTrace_append hprefix tailTrace_3434222
  have hstable : (prefixWord ++ tailWord_3434222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434222).length < 2 ^ (prefixWord ++ tailWord_3434222).sum := by decide
  have hdescent : baseEnd_3434222 < baseStart_3434222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434250 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_3434250 : Nat := 118140960795 + 3434250 * 2 ^ 59
def prefixEnd_3434250 : Nat := 4983230072969 + 3 ^ 40 * 3434250 * 2
def baseEnd_3434250 : Nat := 1175613958468862476520785

theorem tailTrace_3434250 : CollatzResearch.WordTrace tailWord_3434250 prefixEnd_3434250 1175613958468862476520785 := by
  unfold tailWord_3434250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31314346952076562012403051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83504925205537498699741469 31314346952076562012403051)
  ·
    refine ⟨46971520428114843018604577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31314346952076562012403051 46971520428114843018604577)
    ·
      refine ⟨35228640321086132263953433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46971520428114843018604577 35228640321086132263953433)
      ·
        refine ⟨26421480240814599197965075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35228640321086132263953433 26421480240814599197965075)
        ·
          refine ⟨39632220361221898796947613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26421480240814599197965075 39632220361221898796947613)
          ·
            refine ⟨14862082635458212048855355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39632220361221898796947613 14862082635458212048855355)
            ·
              refine ⟨22293123953187318073283033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14862082635458212048855355 22293123953187318073283033)
              ·
                refine ⟨16719842964890488554962275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22293123953187318073283033 16719842964890488554962275)
                ·
                  refine ⟨25079764447335732832443413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16719842964890488554962275 25079764447335732832443413)
                  ·
                    refine ⟨1175613958468862476520785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25079764447335732832443413 1175613958468862476520785)
                    ·
                      rfl

theorem cell22_3434250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_3434250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434250 prefixEnd_3434250 := by exact prefixLift 3434250
  have htrace : WordTrace (prefixWord ++ tailWord_3434250) baseStart_3434250 baseEnd_3434250 := by
    simpa [prefixWord, tailWord_3434250, baseEnd_3434250] using wordTrace_append hprefix tailTrace_3434250
  have hstable : (prefixWord ++ tailWord_3434250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434250).length < 2 ^ (prefixWord ++ tailWord_3434250).sum := by decide
  have hdescent : baseEnd_3434250 < baseStart_3434250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434252 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_3434252 : Nat := 118140960795 + 3434252 * 2 ^ 59
def prefixEnd_3434252 : Nat := 4983230072969 + 3 ^ 40 * 3434252 * 2
def baseEnd_3434252 : Nat := 1175614643109735137970779

theorem tailTrace_3434252 : CollatzResearch.WordTrace tailWord_3434252 prefixEnd_3434252 1175614643109735137970779 := by
  unfold tailWord_3434252
  simp only [CollatzResearch.WordTrace]
  refine ⟨62628730377149501195592505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83504973836199334927456673 62628730377149501195592505)
  ·
    refine ⟨46971547782862125896694379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62628730377149501195592505 46971547782862125896694379)
    ·
      refine ⟨70457321674293188845041569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46971547782862125896694379 70457321674293188845041569)
      ·
        refine ⟨52842991255719891633781177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70457321674293188845041569 52842991255719891633781177)
        ·
          refine ⟨39632243441789918725335883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52842991255719891633781177 39632243441789918725335883)
          ·
            refine ⟨59448365162684878088003825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39632243441789918725335883 59448365162684878088003825)
            ·
              refine ⟨44586273872013658566002869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59448365162684878088003825 44586273872013658566002869)
              ·
                refine ⟨4179963175501280490562769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44586273872013658566002869 4179963175501280490562769)
                ·
                  refine ⟨3134972381625960367922077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4179963175501280490562769 3134972381625960367922077)
                  ·
                    refine ⟨1175614643109735137970779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3134972381625960367922077 1175614643109735137970779)
                    ·
                      rfl

theorem cell22_3434252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_3434252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434252 prefixEnd_3434252 := by exact prefixLift 3434252
  have htrace : WordTrace (prefixWord ++ tailWord_3434252) baseStart_3434252 baseEnd_3434252 := by
    simpa [prefixWord, tailWord_3434252, baseEnd_3434252] using wordTrace_append hprefix tailTrace_3434252
  have hstable : (prefixWord ++ tailWord_3434252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434252).length < 2 ^ (prefixWord ++ tailWord_3434252).sum := by decide
  have hdescent : baseEnd_3434252 < baseStart_3434252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434303 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 2, 3]
def baseStart_3434303 : Nat := 118140960795 + 3434303 * 2 ^ 59
def prefixEnd_3434303 : Nat := 4983230072969 + 3 ^ 40 * 3434303 * 2
def baseEnd_3434303 : Nat := 1175632101451988004945623

theorem tailTrace_3434303 : CollatzResearch.WordTrace tailWord_3434303 prefixEnd_3434303 1175632101451988004945623 := by
  unfold tailWord_3434303
  simp only [CollatzResearch.WordTrace]
  refine ⟨125259320877114238101291563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83506213918076158734194375 125259320877114238101291563)
  ·
    refine ⟨187888981315671357151937345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125259320877114238101291563 187888981315671357151937345)
    ·
      refine ⟨140916735986753517863953009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187888981315671357151937345 140916735986753517863953009)
      ·
        refine ⟨105687551990065138397964757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140916735986753517863953009 105687551990065138397964757)
        ·
          refine ⟨2477051999767151681202299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 105687551990065138397964757 2477051999767151681202299)
          ·
            refine ⟨3715577999650727521803449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477051999767151681202299 3715577999650727521803449)
            ·
              refine ⟨2786683499738045641352587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715577999650727521803449 2786683499738045641352587)
              ·
                refine ⟨4180025249607068462028881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786683499738045641352587 4180025249607068462028881)
                ·
                  refine ⟨3135018937205301346521661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4180025249607068462028881 3135018937205301346521661)
                  ·
                    refine ⟨1175632101451988004945623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135018937205301346521661 1175632101451988004945623)
                    ·
                      rfl

theorem cell22_3434303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_3434303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434303 prefixEnd_3434303 := by exact prefixLift 3434303
  have htrace : WordTrace (prefixWord ++ tailWord_3434303) baseStart_3434303 baseEnd_3434303 := by
    simpa [prefixWord, tailWord_3434303, baseEnd_3434303] using wordTrace_append hprefix tailTrace_3434303
  have hstable : (prefixWord ++ tailWord_3434303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434303).length < 2 ^ (prefixWord ++ tailWord_3434303).sum := by decide
  have hdescent : baseEnd_3434303 < baseStart_3434303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434348 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_3434348 : Nat := 118140960795 + 3434348 * 2 ^ 59
def prefixEnd_3434348 : Nat := 4983230072969 + 3 ^ 40 * 3434348 * 2
def baseEnd_3434348 : Nat := 1175647505871622887570485

theorem tailTrace_3434348 : CollatzResearch.WordTrace tailWord_3434348 prefixEnd_3434348 1175647505871622887570485 := by
  unfold tailWord_3434348
  simp only [CollatzResearch.WordTrace]
  refine ⟨62630481080975605393339849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83507308107967473857786465 62630481080975605393339849)
  ·
    refine ⟨46972860810731704045004887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62630481080975605393339849 46972860810731704045004887)
    ·
      refine ⟨70459291216097556067507331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46972860810731704045004887 70459291216097556067507331)
      ·
        refine ⟨105688936824146334101260997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70459291216097556067507331 105688936824146334101260997)
        ·
          refine ⟨19816675654527437643986437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105688936824146334101260997 19816675654527437643986437)
          ·
            refine ⟨3715626685223894558247457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19816675654527437643986437 3715626685223894558247457)
            ·
              refine ⟨2786720013917920918685593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715626685223894558247457 2786720013917920918685593)
              ·
                refine ⟨2090040010438440689014195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786720013917920918685593 2090040010438440689014195)
                ·
                  refine ⟨3135060015657661033521293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090040010438440689014195 3135060015657661033521293)
                  ·
                    refine ⟨1175647505871622887570485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135060015657661033521293 1175647505871622887570485)
                    ·
                      rfl

theorem cell22_3434348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_3434348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434348 prefixEnd_3434348 := by exact prefixLift 3434348
  have htrace : WordTrace (prefixWord ++ tailWord_3434348) baseStart_3434348 baseEnd_3434348 := by
    simpa [prefixWord, tailWord_3434348, baseEnd_3434348] using wordTrace_append hprefix tailTrace_3434348
  have hstable : (prefixWord ++ tailWord_3434348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434348).length < 2 ^ (prefixWord ++ tailWord_3434348).sum := by decide
  have hdescent : baseEnd_3434348 < baseStart_3434348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434355 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 6]
def baseStart_3434355 : Nat := 118140960795 + 3434355 * 2 ^ 59
def prefixEnd_3434355 : Nat := 4983230072969 + 3 ^ 40 * 3434355 * 2
def baseEnd_3434355 : Nat := 391883300704892400881821

theorem tailTrace_3434355 : CollatzResearch.WordTrace tailWord_3434355 prefixEnd_3434355 391883300704892400881821 := by
  unfold tailWord_3434355
  simp only [CollatzResearch.WordTrace]
  refine ⟨125261217472925850982184519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83507478315283900654789679 125261217472925850982184519)
  ·
    refine ⟨187891826209388776473276779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125261217472925850982184519 187891826209388776473276779)
    ·
      refine ⟨281837739314083164709915169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187891826209388776473276779 281837739314083164709915169)
      ·
        refine ⟨211378304485562373532436377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281837739314083164709915169 211378304485562373532436377)
        ·
          refine ⟨158533728364171780149327283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211378304485562373532436377 158533728364171780149327283)
          ·
            refine ⟨237800592546257670223990925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158533728364171780149327283 237800592546257670223990925)
            ·
              refine ⟨89175222204846626333996597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237800592546257670223990925 89175222204846626333996597)
              ·
                refine ⟨8360177081704371218812181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89175222204846626333996597 8360177081704371218812181)
                ·
                  refine ⟨391883300704892400881821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8360177081704371218812181 391883300704892400881821)
                  ·
                    rfl

theorem cell22_3434355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_3434355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434355 prefixEnd_3434355 := by exact prefixLift 3434355
  have htrace : WordTrace (prefixWord ++ tailWord_3434355) baseStart_3434355 baseEnd_3434355 := by
    simpa [prefixWord, tailWord_3434355, baseEnd_3434355] using wordTrace_append hprefix tailTrace_3434355
  have hstable : (prefixWord ++ tailWord_3434355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434355).length < 2 ^ (prefixWord ++ tailWord_3434355).sum := by decide
  have hdescent : baseEnd_3434355 < baseStart_3434355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434357 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3434357 : Nat := 118140960795 + 3434357 * 2 ^ 59
def prefixEnd_3434357 : Nat := 4983230072969 + 3 ^ 40 * 3434357 * 2
def baseEnd_3434357 : Nat := 1175650586755549864095457

theorem tailTrace_3434357 : CollatzResearch.WordTrace tailWord_3434357 prefixEnd_3434357 1175650586755549864095457 := by
  unfold tailWord_3434357
  simp only [CollatzResearch.WordTrace]
  refine ⟨125261290418918605323757325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83507526945945736882504883 125261290418918605323757325)
  ·
    refine ⟨46972983907094476996408997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125261290418918605323757325 46972983907094476996408997)
    ·
      refine ⟨8807434482580214436826687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46972983907094476996408997 8807434482580214436826687)
      ·
        refine ⟨13211151723870321655240031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807434482580214436826687 13211151723870321655240031)
        ·
          refine ⟨19816727585805482482860047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13211151723870321655240031 19816727585805482482860047)
          ·
            refine ⟨29725091378708223724290071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19816727585805482482860047 29725091378708223724290071)
            ·
              refine ⟨44587637068062335586435107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29725091378708223724290071 44587637068062335586435107)
              ·
                refine ⟨66881455602093503379652661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44587637068062335586435107 66881455602093503379652661)
                ·
                  refine ⟨6270136462696265941842437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66881455602093503379652661 6270136462696265941842437)
                  ·
                    refine ⟨1175650586755549864095457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6270136462696265941842437 1175650586755549864095457)
                    ·
                      rfl

theorem cell22_3434357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3434357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434357 prefixEnd_3434357 := by exact prefixLift 3434357
  have htrace : WordTrace (prefixWord ++ tailWord_3434357) baseStart_3434357 baseEnd_3434357 := by
    simpa [prefixWord, tailWord_3434357, baseEnd_3434357] using wordTrace_append hprefix tailTrace_3434357
  have hstable : (prefixWord ++ tailWord_3434357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434357).length < 2 ^ (prefixWord ++ tailWord_3434357).sum := by decide
  have hdescent : baseEnd_3434357 < baseStart_3434357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434389 : List Nat := [1, 3, 2, 1, 1, 3, 4, 3, 4]
def baseStart_3434389 : Nat := 118140960795 + 3434389 * 2 ^ 59
def prefixEnd_3434389 : Nat := 4983230072969 + 3 ^ 40 * 3434389 * 2
def baseEnd_3434389 : Nat := 391887180336504149098453

theorem tailTrace_3434389 : CollatzResearch.WordTrace tailWord_3434389 prefixEnd_3434389 391887180336504149098453 := by
  unfold tailWord_3434389
  simp only [CollatzResearch.WordTrace]
  refine ⟨125262457554802674788922221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83508305036535116525948147 125262457554802674788922221)
  ·
    refine ⟨46973421583051003045845833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125262457554802674788922221 46973421583051003045845833)
    ·
      refine ⟨35230066187288252284384375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46973421583051003045845833 35230066187288252284384375)
      ·
        refine ⟨52845099280932378426576563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35230066187288252284384375 52845099280932378426576563)
        ·
          refine ⟨79267648921398567639864845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52845099280932378426576563 79267648921398567639864845)
          ·
            refine ⟨29725368345524462864949317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79267648921398567639864845 29725368345524462864949317)
            ·
              refine ⟨5573506564785836787177997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29725368345524462864949317 5573506564785836787177997)
              ·
                refine ⟨2090064961794688795191749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5573506564785836787177997 2090064961794688795191749)
                ·
                  refine ⟨391887180336504149098453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2090064961794688795191749 391887180336504149098453)
                  ·
                    rfl

theorem cell22_3434389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_3434389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434389 prefixEnd_3434389 := by exact prefixLift 3434389
  have htrace : WordTrace (prefixWord ++ tailWord_3434389) baseStart_3434389 baseEnd_3434389 := by
    simpa [prefixWord, tailWord_3434389, baseEnd_3434389] using wordTrace_append hprefix tailTrace_3434389
  have hstable : (prefixWord ++ tailWord_3434389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434389).length < 2 ^ (prefixWord ++ tailWord_3434389).sum := by decide
  have hdescent : baseEnd_3434389 < baseStart_3434389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434391 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 1, 4]
def baseStart_3434391 : Nat := 118140960795 + 3434391 * 2 ^ 59
def prefixEnd_3434391 : Nat := 4983230072969 + 3 ^ 40 * 3434391 * 2
def baseEnd_3434391 : Nat := 1175662225650385108745353

theorem tailTrace_3434391 : CollatzResearch.WordTrace tailWord_3434391 prefixEnd_3434391 1175662225650385108745353 := by
  unfold tailWord_3434391
  simp only [CollatzResearch.WordTrace]
  refine ⟨125262530500795429130495027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83508353667196952753663351 125262530500795429130495027)
  ·
    refine ⟨187893795751193143695742541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125262530500795429130495027 187893795751193143695742541)
    ·
      refine ⟨70460173406697428885903453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187893795751193143695742541 70460173406697428885903453)
      ·
        refine ⟨26422565027511535832213795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70460173406697428885903453 26422565027511535832213795)
        ·
          refine ⟨39633847541267303748320693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26422565027511535832213795 39633847541267303748320693)
          ·
            refine ⟨3715673206993809726405065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39633847541267303748320693 3715673206993809726405065)
            ·
              refine ⟨2786754905245357294803799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715673206993809726405065 2786754905245357294803799)
              ·
                refine ⟨4180132357868035942205699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786754905245357294803799 4180132357868035942205699)
                ·
                  refine ⟨6270198536802053913308549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180132357868035942205699 6270198536802053913308549)
                  ·
                    refine ⟨1175662225650385108745353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6270198536802053913308549 1175662225650385108745353)
                    ·
                      rfl

theorem cell22_3434391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_3434391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434391 prefixEnd_3434391 := by exact prefixLift 3434391
  have htrace : WordTrace (prefixWord ++ tailWord_3434391) baseStart_3434391 baseEnd_3434391 := by
    simpa [prefixWord, tailWord_3434391, baseEnd_3434391] using wordTrace_append hprefix tailTrace_3434391
  have hstable : (prefixWord ++ tailWord_3434391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434391).length < 2 ^ (prefixWord ++ tailWord_3434391).sum := by decide
  have hdescent : baseEnd_3434391 < baseStart_3434391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434404 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_3434404 : Nat := 118140960795 + 3434404 * 2 ^ 59
def prefixEnd_3434404 : Nat := 4983230072969 + 3 ^ 40 * 3434404 * 2
def baseEnd_3434404 : Nat := 1175666675816057408170313

theorem tailTrace_3434404 : CollatzResearch.WordTrace tailWord_3434404 prefixEnd_3434404 1175666675816057408170313 := by
  unfold tailWord_3434404
  simp only [CollatzResearch.WordTrace]
  refine ⟨62631502324874166175359133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83508669766498888233812177 62631502324874166175359133)
  ·
    refine ⟨23486813371827812315759675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62631502324874166175359133 23486813371827812315759675)
    ·
      refine ⟨35230220057741718473639513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23486813371827812315759675 35230220057741718473639513)
      ·
        refine ⟨26422665043306288855229635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35230220057741718473639513 26422665043306288855229635)
        ·
          refine ⟨39633997564959433282844453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26422665043306288855229635 39633997564959433282844453)
          ·
            refine ⟨7431374543429893740533335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39633997564959433282844453 7431374543429893740533335)
            ·
              refine ⟨11147061815144840610800003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431374543429893740533335 11147061815144840610800003)
              ·
                refine ⟨16720592722717260916200005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147061815144840610800003 16720592722717260916200005)
                ·
                  refine ⟨3135111135509486421787501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16720592722717260916200005 3135111135509486421787501)
                  ·
                    refine ⟨1175666675816057408170313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135111135509486421787501 1175666675816057408170313)
                    ·
                      rfl

theorem cell22_3434404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_3434404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434404 prefixEnd_3434404 := by exact prefixLift 3434404
  have htrace : WordTrace (prefixWord ++ tailWord_3434404) baseStart_3434404 baseEnd_3434404 := by
    simpa [prefixWord, tailWord_3434404, baseEnd_3434404] using wordTrace_append hprefix tailTrace_3434404
  have hstable : (prefixWord ++ tailWord_3434404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434404).length < 2 ^ (prefixWord ++ tailWord_3434404).sum := by decide
  have hdescent : baseEnd_3434404 < baseStart_3434404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434517 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_3434517 : Nat := 118140960795 + 3434517 * 2 ^ 59
def prefixEnd_3434517 : Nat := 4983230072969 + 3 ^ 40 * 3434517 * 2
def baseEnd_3434517 : Nat := 1175705358025362780094967

theorem tailTrace_3434517 : CollatzResearch.WordTrace tailWord_3434517 prefixEnd_3434517 1175705358025362780094967 := by
  unfold tailWord_3434517
  simp only [CollatzResearch.WordTrace]
  refine ⟨125267126098338952649581805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83511417398892635099721203 125267126098338952649581805)
  ·
    refine ⟨46975172286877107243593177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125267126098338952649581805 46975172286877107243593177)
    ·
      refine ⟨35231379215157830432694883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46975172286877107243593177 35231379215157830432694883)
      ·
        refine ⟨52847068822736745649042325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35231379215157830432694883 52847068822736745649042325)
        ·
          refine ⟨2477206351065784952298859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52847068822736745649042325 2477206351065784952298859)
          ·
            refine ⟨3715809526598677428448289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477206351065784952298859 3715809526598677428448289)
            ·
              refine ⟨2786857144949008071336217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715809526598677428448289 2786857144949008071336217)
              ·
                refine ⟨2090142858711756053502163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786857144949008071336217 2090142858711756053502163)
                ·
                  refine ⟨3135214288067634080253245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090142858711756053502163 3135214288067634080253245)
                  ·
                    refine ⟨1175705358025362780094967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135214288067634080253245 1175705358025362780094967)
                    ·
                      rfl

theorem cell22_3434517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_3434517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434517 prefixEnd_3434517 := by exact prefixLift 3434517
  have htrace : WordTrace (prefixWord ++ tailWord_3434517) baseStart_3434517 baseEnd_3434517 := by
    simpa [prefixWord, tailWord_3434517, baseEnd_3434517] using wordTrace_append hprefix tailTrace_3434517
  have hstable : (prefixWord ++ tailWord_3434517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434517).length < 2 ^ (prefixWord ++ tailWord_3434517).sum := by decide
  have hdescent : baseEnd_3434517 < baseStart_3434517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434693 : List Nat := [1, 3, 1, 1, 1, 1, 8, 2, 4]
def baseStart_3434693 : Nat := 118140960795 + 3434693 * 2 ^ 59
def prefixEnd_3434693 : Nat := 4983230072969 + 3 ^ 40 * 3434693 * 2
def baseEnd_3434693 : Nat := 391921868807385662564809

theorem tailTrace_3434693 : CollatzResearch.WordTrace tailWord_3434693 prefixEnd_3434693 391921868807385662564809 := by
  unfold tailWord_3434693
  simp only [CollatzResearch.WordTrace]
  refine ⟨125273545345701334707988733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83515696897134223138659155 125273545345701334707988733)
  ·
    refine ⟨46977579504638000515495775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125273545345701334707988733 46977579504638000515495775)
    ·
      refine ⟨70466369256957000773243663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46977579504638000515495775 70466369256957000773243663)
      ·
        refine ⟨105699553885435501159865495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70466369256957000773243663 105699553885435501159865495)
        ·
          refine ⟨158549330828153251739798243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105699553885435501159865495 158549330828153251739798243)
          ·
            refine ⟨237823996242229877609697365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158549330828153251739798243 237823996242229877609697365)
            ·
              refine ⟨2786999955963631378238641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 237823996242229877609697365 2786999955963631378238641)
              ·
                refine ⟨2090249966972723533678981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2786999955963631378238641 2090249966972723533678981)
                ·
                  refine ⟨391921868807385662564809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2090249966972723533678981 391921868807385662564809)
                  ·
                    rfl

theorem cell22_3434693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_3434693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434693 prefixEnd_3434693 := by exact prefixLift 3434693
  have htrace : WordTrace (prefixWord ++ tailWord_3434693) baseStart_3434693 baseEnd_3434693 := by
    simpa [prefixWord, tailWord_3434693, baseEnd_3434693] using wordTrace_append hprefix tailTrace_3434693
  have hstable : (prefixWord ++ tailWord_3434693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434693).length < 2 ^ (prefixWord ++ tailWord_3434693).sum := by decide
  have hdescent : baseEnd_3434693 < baseStart_3434693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434721 : List Nat := [1, 2, 3, 1, 3, 1, 5, 6]
def baseStart_3434721 : Nat := 118140960795 + 3434721 * 2 ^ 59
def prefixEnd_3434721 : Nat := 4983230072969 + 3 ^ 40 * 3434721 * 2
def baseEnd_3434721 : Nat := 130641687932708249777149

theorem tailTrace_3434721 : CollatzResearch.WordTrace tailWord_3434721 prefixEnd_3434721 130641687932708249777149 := by
  unfold tailWord_3434721
  simp only [CollatzResearch.WordTrace]
  refine ⟨125274566589599895490008017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83516377726399930326672011 125274566589599895490008017)
  ·
    refine ⟨93955924942199921617506013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125274566589599895490008017 93955924942199921617506013)
    ·
      refine ⟨35233471853324970606564755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93955924942199921617506013 35233471853324970606564755)
      ·
        refine ⟨52850207779987455909847133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35233471853324970606564755 52850207779987455909847133)
        ·
          refine ⟨19818827917495295966192675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52850207779987455909847133 19818827917495295966192675)
          ·
            refine ⟨29728241876242943949289013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19818827917495295966192675 29728241876242943949289013)
            ·
              refine ⟨2787022675897775995245845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29728241876242943949289013 2787022675897775995245845)
              ·
                refine ⟨130641687932708249777149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2787022675897775995245845 130641687932708249777149)
                ·
                  rfl

theorem cell22_3434721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 6].length) (baseStart_3434721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434721 prefixEnd_3434721 := by exact prefixLift 3434721
  have htrace : WordTrace (prefixWord ++ tailWord_3434721) baseStart_3434721 baseEnd_3434721 := by
    simpa [prefixWord, tailWord_3434721, baseEnd_3434721] using wordTrace_append hprefix tailTrace_3434721
  have hstable : (prefixWord ++ tailWord_3434721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434721).length < 2 ^ (prefixWord ++ tailWord_3434721).sum := by decide
  have hdescent : baseEnd_3434721 < baseStart_3434721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434723 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 1, 6]
def baseStart_3434723 : Nat := 118140960795 + 3434723 * 2 ^ 59
def prefixEnd_3434723 : Nat := 4983230072969 + 3 ^ 40 * 3434723 * 2
def baseEnd_3434723 : Nat := 1175775876035246909444335

theorem tailTrace_3434723 : CollatzResearch.WordTrace tailWord_3434723 prefixEnd_3434723 1175775876035246909444335 := by
  unfold tailWord_3434723
  simp only [CollatzResearch.WordTrace]
  refine ⟨125274639535592649831580823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83516426357061766554387215 125274639535592649831580823)
  ·
    refine ⟨187911959303388974747371235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125274639535592649831580823 187911959303388974747371235)
    ·
      refine ⟨281867938955083462121056853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187911959303388974747371235 281867938955083462121056853)
      ·
        refine ⟨3303139909629884321731135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 281867938955083462121056853 3303139909629884321731135)
        ·
          refine ⟨4954709864444826482596703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303139909629884321731135 4954709864444826482596703)
          ·
            refine ⟨7432064796667239723895055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954709864444826482596703 7432064796667239723895055)
            ·
              refine ⟨11148097195000859585842583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432064796667239723895055 11148097195000859585842583)
              ·
                refine ⟨16722145792501289378763875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11148097195000859585842583 16722145792501289378763875)
                ·
                  refine ⟨25083218688751934068145813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16722145792501289378763875 25083218688751934068145813)
                  ·
                    refine ⟨1175775876035246909444335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25083218688751934068145813 1175775876035246909444335)
                    ·
                      rfl

theorem cell22_3434723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 6].length) (baseStart_3434723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434723 prefixEnd_3434723 := by exact prefixLift 3434723
  have htrace : WordTrace (prefixWord ++ tailWord_3434723) baseStart_3434723 baseEnd_3434723 := by
    simpa [prefixWord, tailWord_3434723, baseEnd_3434723] using wordTrace_append hprefix tailTrace_3434723
  have hstable : (prefixWord ++ tailWord_3434723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434723).length < 2 ^ (prefixWord ++ tailWord_3434723).sum := by decide
  have hdescent : baseEnd_3434723 < baseStart_3434723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434753 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3434753 : Nat := 118140960795 + 3434753 * 2 ^ 59
def prefixEnd_3434753 : Nat := 4983230072969 + 3 ^ 40 * 3434753 * 2
def baseEnd_3434753 : Nat := 1175786145648336831194243

theorem tailTrace_3434753 : CollatzResearch.WordTrace tailWord_3434753 prefixEnd_3434753 1175786145648336831194243 := by
  unfold tailWord_3434753
  simp only [CollatzResearch.WordTrace]
  refine ⟨125275733725483964955172913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83517155816989309970115275 125275733725483964955172913)
  ·
    refine ⟨93956800294112973716379685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125275733725483964955172913 93956800294112973716379685)
    ·
      refine ⟨17616900055146182571821191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93956800294112973716379685 17616900055146182571821191)
      ·
        refine ⟨26425350082719273857731787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17616900055146182571821191 26425350082719273857731787)
        ·
          refine ⟨39638025124078910786597681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26425350082719273857731787 39638025124078910786597681)
          ·
            refine ⟨29728518843059183089948261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39638025124078910786597681 29728518843059183089948261)
            ·
              refine ⟨5574097283073596829365299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29728518843059183089948261 5574097283073596829365299)
              ·
                refine ⟨8361145924610395244047949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5574097283073596829365299 8361145924610395244047949)
                ·
                  refine ⟨3135429721728898216517981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8361145924610395244047949 3135429721728898216517981)
                  ·
                    refine ⟨1175786145648336831194243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135429721728898216517981 1175786145648336831194243)
                    ·
                      rfl

theorem cell22_3434753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3434753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434753 prefixEnd_3434753 := by exact prefixLift 3434753
  have htrace : WordTrace (prefixWord ++ tailWord_3434753) baseStart_3434753 baseEnd_3434753 := by
    simpa [prefixWord, tailWord_3434753, baseEnd_3434753] using wordTrace_append hprefix tailTrace_3434753
  have hstable : (prefixWord ++ tailWord_3434753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434753).length < 2 ^ (prefixWord ++ tailWord_3434753).sum := by decide
  have hdescent : baseEnd_3434753 < baseStart_3434753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434804 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3434804 : Nat := 118140960795 + 3434804 * 2 ^ 59
def prefixEnd_3434804 : Nat := 4983230072969 + 3 ^ 40 * 3434804 * 2
def baseEnd_3434804 : Nat := 1175803603990589698169087

theorem tailTrace_3434804 : CollatzResearch.WordTrace tailWord_3434804 prefixEnd_3434804 1175803603990589698169087 := by
  unfold tailWord_3434804
  simp only [CollatzResearch.WordTrace]
  refine ⟨62638796924149600332639733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83518395898866133776852977 62638796924149600332639733)
  ·
    refine ⟨5872387211639025031184975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62638796924149600332639733 5872387211639025031184975)
    ·
      refine ⟨8808580817458537546777463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5872387211639025031184975 8808580817458537546777463)
      ·
        refine ⟨13212871226187806320166195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8808580817458537546777463 13212871226187806320166195)
        ·
          refine ⟨19819306839281709480249293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13212871226187806320166195 19819306839281709480249293)
          ·
            refine ⟨7432240064730641055093485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19819306839281709480249293 7432240064730641055093485)
            ·
              refine ⟨2787090024273990395660057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7432240064730641055093485 2787090024273990395660057)
              ·
                refine ⟨2090317518205492796745043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787090024273990395660057 2090317518205492796745043)
                ·
                  refine ⟨3135476277308239195117565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090317518205492796745043 3135476277308239195117565)
                  ·
                    refine ⟨1175803603990589698169087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135476277308239195117565 1175803603990589698169087)
                    ·
                      rfl

theorem cell22_3434804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3434804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434804 prefixEnd_3434804 := by exact prefixLift 3434804
  have htrace : WordTrace (prefixWord ++ tailWord_3434804) baseStart_3434804 baseEnd_3434804 := by
    simpa [prefixWord, tailWord_3434804, baseEnd_3434804] using wordTrace_append hprefix tailTrace_3434804
  have hstable : (prefixWord ++ tailWord_3434804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434804).length < 2 ^ (prefixWord ++ tailWord_3434804).sum := by decide
  have hdescent : baseEnd_3434804 < baseStart_3434804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434817 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 5]
def baseStart_3434817 : Nat := 118140960795 + 3434817 * 2 ^ 59
def prefixEnd_3434817 : Nat := 4983230072969 + 3 ^ 40 * 3434817 * 2
def baseEnd_3434817 : Nat := 391936018052087332531349

theorem tailTrace_3434817 : CollatzResearch.WordTrace tailWord_3434817 prefixEnd_3434817 391936018052087332531349 := by
  unfold tailWord_3434817
  simp only [CollatzResearch.WordTrace]
  refine ⟨125278067997252103885502705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83518711998168069257001803 125278067997252103885502705)
  ·
    refine ⟨93958550997939077914127029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125278067997252103885502705 93958550997939077914127029)
    ·
      refine ⟨8808614156056788554449409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93958550997939077914127029 8808614156056788554449409)
      ·
        refine ⟨6606460617042591415837057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8808614156056788554449409 6606460617042591415837057)
        ·
          refine ⟨4954845462781943561877793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6606460617042591415837057 4954845462781943561877793)
          ·
            refine ⟨3716134097086457671408345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4954845462781943561877793 3716134097086457671408345)
            ·
              refine ⟨2787100572814843253556259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716134097086457671408345 2787100572814843253556259)
              ·
                refine ⟨4180650859222264880334389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787100572814843253556259 4180650859222264880334389)
                ·
                  refine ⟨391936018052087332531349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4180650859222264880334389 391936018052087332531349)
                  ·
                    rfl

theorem cell22_3434817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 5].length) (baseStart_3434817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434817 prefixEnd_3434817 := by exact prefixLift 3434817
  have htrace : WordTrace (prefixWord ++ tailWord_3434817) baseStart_3434817 baseEnd_3434817 := by
    simpa [prefixWord, tailWord_3434817, baseEnd_3434817] using wordTrace_append hprefix tailTrace_3434817
  have hstable : (prefixWord ++ tailWord_3434817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434817).length < 2 ^ (prefixWord ++ tailWord_3434817).sum := by decide
  have hdescent : baseEnd_3434817 < baseStart_3434817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434856 : List Nat := [2, 1, 4, 2, 2, 11]
def baseStart_3434856 : Nat := 118140960795 + 3434856 * 2 ^ 59
def prefixEnd_3434856 : Nat := 4983230072969 + 3 ^ 40 * 3434856 * 2
def baseEnd_3434856 : Nat := 14516313637694801183567

theorem tailTrace_3434856 : CollatzResearch.WordTrace tailWord_3434856 prefixEnd_3434856 14516313637694801183567 := by
  unfold tailWord_3434856
  simp only [CollatzResearch.WordTrace]
  refine ⟨62639745222055406773086211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83519660296073875697448281 62639745222055406773086211)
  ·
    refine ⟨93959617833083110159629317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62639745222055406773086211 93959617833083110159629317)
    ·
      refine ⟨17617428343703083154930497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93959617833083110159629317 17617428343703083154930497)
      ·
        refine ⟨13213071257777312366197873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17617428343703083154930497 13213071257777312366197873)
        ·
          refine ⟨9909803443332984274648405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13213071257777312366197873 9909803443332984274648405)
          ·
            refine ⟨14516313637694801183567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9909803443332984274648405 14516313637694801183567)
            ·
              rfl

theorem cell22_3434856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 11].length) (baseStart_3434856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434856 prefixEnd_3434856 := by exact prefixLift 3434856
  have htrace : WordTrace (prefixWord ++ tailWord_3434856) baseStart_3434856 baseEnd_3434856 := by
    simpa [prefixWord, tailWord_3434856, baseEnd_3434856] using wordTrace_append hprefix tailTrace_3434856
  have hstable : (prefixWord ++ tailWord_3434856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434856).length < 2 ^ (prefixWord ++ tailWord_3434856).sum := by decide
  have hdescent : baseEnd_3434856 < baseStart_3434856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434901 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 7]
def baseStart_3434901 : Nat := 118140960795 + 3434901 * 2 ^ 59
def prefixEnd_3434901 : Nat := 4983230072969 + 3 ^ 40 * 3434901 * 2
def baseEnd_3434901 : Nat := 391945603024304592831263

theorem tailTrace_3434901 : CollatzResearch.WordTrace tailWord_3434901 prefixEnd_3434901 391945603024304592831263 := by
  unfold tailWord_3434901
  simp only [CollatzResearch.WordTrace]
  refine ⟨125281131728947786231560557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83520754485965190821040371 125281131728947786231560557)
  ·
    refine ⟨46980424398355419836835209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125281131728947786231560557 46980424398355419836835209)
    ·
      refine ⟨35235318298766564877626407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46980424398355419836835209 35235318298766564877626407)
      ·
        refine ⟨52852977448149847316439611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35235318298766564877626407 52852977448149847316439611)
        ·
          refine ⟨79279466172224770974659417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52852977448149847316439611 79279466172224770974659417)
          ·
            refine ⟨59459599629168578230994563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79279466172224770974659417 59459599629168578230994563)
            ·
              refine ⟨89189399443752867346491845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59459599629168578230994563 89189399443752867346491845)
              ·
                refine ⟨16723012395703662627467221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89189399443752867346491845 16723012395703662627467221)
                ·
                  refine ⟨391945603024304592831263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16723012395703662627467221 391945603024304592831263)
                  ·
                    rfl

theorem cell22_3434901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_3434901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434901 prefixEnd_3434901 := by exact prefixLift 3434901
  have htrace : WordTrace (prefixWord ++ tailWord_3434901) baseStart_3434901 baseEnd_3434901 := by
    simpa [prefixWord, tailWord_3434901, baseEnd_3434901] using wordTrace_append hprefix tailTrace_3434901
  have hstable : (prefixWord ++ tailWord_3434901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434901).length < 2 ^ (prefixWord ++ tailWord_3434901).sum := by decide
  have hdescent : baseEnd_3434901 < baseStart_3434901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434935 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 5]
def baseStart_3434935 : Nat := 118140960795 + 3434935 * 2 ^ 59
def prefixEnd_3434935 : Nat := 4983230072969 + 3 ^ 40 * 3434935 * 2
def baseEnd_3434935 : Nat := 391949482655916341047895

theorem tailTrace_3434935 : CollatzResearch.WordTrace tailWord_3434935 prefixEnd_3434935 391949482655916341047895 := by
  unfold tailWord_3434935
  simp only [CollatzResearch.WordTrace]
  refine ⟨125282371810824610038298259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83521581207216406692198839 125282371810824610038298259)
  ·
    refine ⟨187923557716236915057447389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125282371810824610038298259 187923557716236915057447389)
    ·
      refine ⟨70471334143588843146542771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187923557716236915057447389 70471334143588843146542771)
      ·
        refine ⟨105707001215383264719814157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70471334143588843146542771 105707001215383264719814157)
        ·
          refine ⟨39640125455768724269930309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105707001215383264719814157 39640125455768724269930309)
          ·
            refine ⟨7432523522956635800611933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39640125455768724269930309 7432523522956635800611933)
            ·
              refine ⟨2787196321108738425229475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7432523522956635800611933 2787196321108738425229475)
              ·
                refine ⟨4180794481663107637844213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787196321108738425229475 4180794481663107637844213)
                ·
                  refine ⟨391949482655916341047895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4180794481663107637844213 391949482655916341047895)
                  ·
                    rfl

theorem cell22_3434935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 5].length) (baseStart_3434935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434935 prefixEnd_3434935 := by exact prefixLift 3434935
  have htrace : WordTrace (prefixWord ++ tailWord_3434935) baseStart_3434935 baseEnd_3434935 := by
    simpa [prefixWord, tailWord_3434935, baseEnd_3434935] using wordTrace_append hprefix tailTrace_3434935
  have hstable : (prefixWord ++ tailWord_3434935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434935).length < 2 ^ (prefixWord ++ tailWord_3434935).sum := by decide
  have hdescent : baseEnd_3434935 < baseStart_3434935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434956 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_3434956 : Nat := 118140960795 + 3434956 * 2 ^ 59
def prefixEnd_3434956 : Nat := 4983230072969 + 3 ^ 40 * 3434956 * 2
def baseEnd_3434956 : Nat := 1175855636696911968368621

theorem tailTrace_3434956 : CollatzResearch.WordTrace tailWord_3434956 prefixEnd_3434956 1175855636696911968368621 := by
  unfold tailWord_3434956
  simp only [CollatzResearch.WordTrace]
  refine ⟨62641568871874265312406361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83522091829165687083208481 62641568871874265312406361)
  ·
    refine ⟨46981176653905698984304771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62641568871874265312406361 46981176653905698984304771)
    ·
      refine ⟨70471764980858548476457157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46981176653905698984304771 70471764980858548476457157)
      ·
        refine ⟨13213455933910977839335717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70471764980858548476457157 13213455933910977839335717)
        ·
          refine ⟨2477522987608308344875447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13213455933910977839335717 2477522987608308344875447)
          ·
            refine ⟨3716284481412462517313171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477522987608308344875447 3716284481412462517313171)
            ·
              refine ⟨5574426722118693775969757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716284481412462517313171 5574426722118693775969757)
              ·
                refine ⟨2090410020794510165988659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5574426722118693775969757 2090410020794510165988659)
                ·
                  refine ⟨3135615031191765248982989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090410020794510165988659 3135615031191765248982989)
                  ·
                    refine ⟨1175855636696911968368621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135615031191765248982989 1175855636696911968368621)
                    ·
                      rfl

theorem cell22_3434956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_3434956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434956 prefixEnd_3434956 := by exact prefixLift 3434956
  have htrace : WordTrace (prefixWord ++ tailWord_3434956) baseStart_3434956 baseEnd_3434956 := by
    simpa [prefixWord, tailWord_3434956, baseEnd_3434956] using wordTrace_append hprefix tailTrace_3434956
  have hstable : (prefixWord ++ tailWord_3434956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434956).length < 2 ^ (prefixWord ++ tailWord_3434956).sum := by decide
  have hdescent : baseEnd_3434956 < baseStart_3434956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434965 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3434965 : Nat := 118140960795 + 3434965 * 2 ^ 59
def prefixEnd_3434965 : Nat := 4983230072969 + 3 ^ 40 * 3434965 * 2
def baseEnd_3434965 : Nat := 1175858717580838944893593

theorem tailTrace_3434965 : CollatzResearch.WordTrace tailWord_3434965 prefixEnd_3434965 1175858717580838944893593 := by
  unfold tailWord_3434965
  simp only [CollatzResearch.WordTrace]
  refine ⟨125283466000715925161890349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83522310667143950107926899 125283466000715925161890349)
  ·
    refine ⟨46981299750268471935708881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125283466000715925161890349 46981299750268471935708881)
    ·
      refine ⟨35235974812701353951781661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46981299750268471935708881 35235974812701353951781661)
      ·
        refine ⟨13213490554763007731918123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35235974812701353951781661 13213490554763007731918123)
        ·
          refine ⟨19820235832144511597877185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213490554763007731918123 19820235832144511597877185)
          ·
            refine ⟨14865176874108383698407889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19820235832144511597877185 14865176874108383698407889)
            ·
              refine ⟨11148882655581287773805917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14865176874108383698407889 11148882655581287773805917)
              ·
                refine ⟨4180830995842982915177219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11148882655581287773805917 4180830995842982915177219)
                ·
                  refine ⟨6271246493764474372765829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4180830995842982915177219 6271246493764474372765829)
                  ·
                    refine ⟨1175858717580838944893593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271246493764474372765829 1175858717580838944893593)
                    ·
                      rfl

theorem cell22_3434965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3434965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434965 prefixEnd_3434965 := by exact prefixLift 3434965
  have htrace : WordTrace (prefixWord ++ tailWord_3434965) baseStart_3434965 baseEnd_3434965 := by
    simpa [prefixWord, tailWord_3434965, baseEnd_3434965] using wordTrace_append hprefix tailTrace_3434965
  have hstable : (prefixWord ++ tailWord_3434965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434965).length < 2 ^ (prefixWord ++ tailWord_3434965).sum := by decide
  have hdescent : baseEnd_3434965 < baseStart_3434965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434993 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3434993 : Nat := 118140960795 + 3434993 * 2 ^ 59
def prefixEnd_3434993 : Nat := 4983230072969 + 3 ^ 40 * 3434993 * 2
def baseEnd_3434993 : Nat := 1175868302553056205193507

theorem tailTrace_3434993 : CollatzResearch.WordTrace tailWord_3434993 prefixEnd_3434993 1175868302553056205193507 := by
  unfold tailWord_3434993
  simp only [CollatzResearch.WordTrace]
  refine ⟨125284487244614485943909633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83522991496409657295939755 125284487244614485943909633)
  ·
    refine ⟨93963365433460864457932225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125284487244614485943909633 93963365433460864457932225)
    ·
      refine ⟨70472524075095648343449169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93963365433460864457932225 70472524075095648343449169)
      ·
        refine ⟨52854393056321736257586877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70472524075095648343449169 52854393056321736257586877)
        ·
          refine ⟨19820397396120651096595079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52854393056321736257586877 19820397396120651096595079)
          ·
            refine ⟨29730596094180976644892619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19820397396120651096595079 29730596094180976644892619)
            ·
              refine ⟨44595894141271464967338929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29730596094180976644892619 44595894141271464967338929)
              ·
                refine ⟨33446920605953598725504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44595894141271464967338929 33446920605953598725504197)
                ·
                  refine ⟨6271297613616299761032037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33446920605953598725504197 6271297613616299761032037)
                  ·
                    refine ⟨1175868302553056205193507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271297613616299761032037 1175868302553056205193507)
                    ·
                      rfl

theorem cell22_3434993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3434993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434993 prefixEnd_3434993 := by exact prefixLift 3434993
  have htrace : WordTrace (prefixWord ++ tailWord_3434993) baseStart_3434993 baseEnd_3434993 := by
    simpa [prefixWord, tailWord_3434993, baseEnd_3434993] using wordTrace_append hprefix tailTrace_3434993
  have hstable : (prefixWord ++ tailWord_3434993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434993).length < 2 ^ (prefixWord ++ tailWord_3434993).sum := by decide
  have hdescent : baseEnd_3434993 < baseStart_3434993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3434995 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 2, 3]
def baseStart_3434995 : Nat := 118140960795 + 3434995 * 2 ^ 59
def prefixEnd_3434995 : Nat := 4983230072969 + 3 ^ 40 * 3434995 * 2
def baseEnd_3434995 : Nat := 1175868987193928866643501

theorem tailTrace_3434995 : CollatzResearch.WordTrace tailWord_3434995 prefixEnd_3434995 1175868987193928866643501 := by
  unfold tailWord_3434995
  simp only [CollatzResearch.WordTrace]
  refine ⟨125284560190607240285482439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83523040127071493523654959 125284560190607240285482439)
  ·
    refine ⟨187926840285910860428223659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125284560190607240285482439 187926840285910860428223659)
    ·
      refine ⟨281890260428866290642335489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187926840285910860428223659 281890260428866290642335489)
      ·
        refine ⟨211417695321649717981751617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281890260428866290642335489 211417695321649717981751617)
        ·
          refine ⟨158563271491237288486313713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211417695321649717981751617 158563271491237288486313713)
          ·
            refine ⟨118922453618427966364735285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158563271491237288486313713 118922453618427966364735285)
            ·
              refine ⟨11148980026727621846693933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118922453618427966364735285 11148980026727621846693933)
              ·
                refine ⟨4180867510022858192510225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11148980026727621846693933 4180867510022858192510225)
                ·
                  refine ⟨3135650632517143644382669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4180867510022858192510225 3135650632517143644382669)
                  ·
                    refine ⟨1175868987193928866643501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135650632517143644382669 1175868987193928866643501)
                    ·
                      rfl

theorem cell22_3434995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 3].length) (baseStart_3434995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3434995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3434995 prefixEnd_3434995 := by exact prefixLift 3434995
  have htrace : WordTrace (prefixWord ++ tailWord_3434995) baseStart_3434995 baseEnd_3434995 := by
    simpa [prefixWord, tailWord_3434995, baseEnd_3434995] using wordTrace_append hprefix tailTrace_3434995
  have hstable : (prefixWord ++ tailWord_3434995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3434995).length < 2 ^ (prefixWord ++ tailWord_3434995).sum := by decide
  have hdescent : baseEnd_3434995 < baseStart_3434995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3434995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435031 : List Nat := [1, 1, 3, 6, 1, 2, 2, 2, 4]
def baseStart_3435031 : Nat := 118140960795 + 3435031 * 2 ^ 59
def prefixEnd_3435031 : Nat := 4983230072969 + 3 ^ 40 * 3435031 * 2
def baseEnd_3435031 : Nat := 391960436909878924247797

theorem tailTrace_3435031 : CollatzResearch.WordTrace tailWord_3435031 prefixEnd_3435031 391960436909878924247797 := by
  unfold tailWord_3435031
  simp only [CollatzResearch.WordTrace]
  refine ⟨125285873218476818433792947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83523915478984545622528631 125285873218476818433792947)
  ·
    refine ⟨187928809827715227650689421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125285873218476818433792947 187928809827715227650689421)
    ·
      refine ⟨70473303685393210369008533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187928809827715227650689421 70473303685393210369008533)
      ·
        refine ⟨3303436110252806736047275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70473303685393210369008533 3303436110252806736047275)
        ·
          refine ⟨4955154165379210104070913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303436110252806736047275 4955154165379210104070913)
          ·
            refine ⟨3716365624034407578053185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4955154165379210104070913 3716365624034407578053185)
            ·
              refine ⟨2787274218025805683539889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716365624034407578053185 2787274218025805683539889)
              ·
                refine ⟨2090455663519354262654917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787274218025805683539889 2090455663519354262654917)
                ·
                  refine ⟨391960436909878924247797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2090455663519354262654917 391960436909878924247797)
                  ·
                    rfl

theorem cell22_3435031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 2, 4].length) (baseStart_3435031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435031 prefixEnd_3435031 := by exact prefixLift 3435031
  have htrace : WordTrace (prefixWord ++ tailWord_3435031) baseStart_3435031 baseEnd_3435031 := by
    simpa [prefixWord, tailWord_3435031, baseEnd_3435031] using wordTrace_append hprefix tailTrace_3435031
  have hstable : (prefixWord ++ tailWord_3435031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435031).length < 2 ^ (prefixWord ++ tailWord_3435031).sum := by decide
  have hdescent : baseEnd_3435031 < baseStart_3435031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435117 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_3435117 : Nat := 118140960795 + 3435117 * 2 ^ 59
def prefixEnd_3435117 : Nat := 4983230072969 + 3 ^ 40 * 3435117 * 2
def baseEnd_3435117 : Nat := 1175910750287161215093127

theorem tailTrace_3435117 : CollatzResearch.WordTrace tailWord_3435117 prefixEnd_3435117 1175910750287161215093127 := by
  unfold tailWord_3435117
  simp only [CollatzResearch.WordTrace]
  refine ⟨125289009896165255121423605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83526006597443503414282403 125289009896165255121423605)
  ·
    refine ⟨11745844677765492667633463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125289009896165255121423605 11745844677765492667633463)
    ·
      refine ⟨17618767016648239001450195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11745844677765492667633463 17618767016648239001450195)
      ·
        refine ⟨26428150524972358502175293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17618767016648239001450195 26428150524972358502175293)
        ·
          refine ⟨9910556446864634438315735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26428150524972358502175293 9910556446864634438315735)
          ·
            refine ⟨14865834670296951657473603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9910556446864634438315735 14865834670296951657473603)
            ·
              refine ⟨22298752005445427486210405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14865834670296951657473603 22298752005445427486210405)
              ·
                refine ⟨4181016001021017653664451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22298752005445427486210405 4181016001021017653664451)
                ·
                  refine ⟨6271524001531526480496677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181016001021017653664451 6271524001531526480496677)
                  ·
                    refine ⟨1175910750287161215093127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271524001531526480496677 1175910750287161215093127)
                    ·
                      rfl

theorem cell22_3435117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_3435117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435117 prefixEnd_3435117 := by exact prefixLift 3435117
  have htrace : WordTrace (prefixWord ++ tailWord_3435117) baseStart_3435117 baseEnd_3435117 := by
    simpa [prefixWord, tailWord_3435117, baseEnd_3435117] using wordTrace_append hprefix tailTrace_3435117
  have hstable : (prefixWord ++ tailWord_3435117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435117).length < 2 ^ (prefixWord ++ tailWord_3435117).sum := by decide
  have hdescent : baseEnd_3435117 < baseStart_3435117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435132 : List Nat := [2, 2, 2, 1, 1, 2, 5, 3, 4]
def baseStart_3435132 : Nat := 118140960795 + 3435132 * 2 ^ 59
def prefixEnd_3435132 : Nat := 4983230072969 + 3 ^ 40 * 3435132 * 2
def baseEnd_3435132 : Nat := 391971961697902058656027

theorem tailTrace_3435132 : CollatzResearch.WordTrace tailWord_3435132 prefixEnd_3435132 391971961697902058656027 := by
  unfold tailWord_3435132
  simp only [CollatzResearch.WordTrace]
  refine ⟨62644778495555456341609825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83526371327407275122146433 62644778495555456341609825)
  ·
    refine ⟨46983583871666592256207369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62644778495555456341609825 46983583871666592256207369)
    ·
      refine ⟨35237687903749944192155527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46983583871666592256207369 35237687903749944192155527)
      ·
        refine ⟨52856531855624916288233291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35237687903749944192155527 52856531855624916288233291)
        ·
          refine ⟨79284797783437374432349937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52856531855624916288233291 79284797783437374432349937)
          ·
            refine ⟨59463598337578030824262453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79284797783437374432349937 59463598337578030824262453)
            ·
              refine ⟨5574712344147940389774605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59463598337578030824262453 5574712344147940389774605)
              ·
                refine ⟨2090517129055477646165477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5574712344147940389774605 2090517129055477646165477)
                ·
                  refine ⟨391971961697902058656027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2090517129055477646165477 391971961697902058656027)
                  ·
                    rfl

theorem cell22_3435132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_3435132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435132 prefixEnd_3435132 := by exact prefixLift 3435132
  have htrace : WordTrace (prefixWord ++ tailWord_3435132) baseStart_3435132 baseEnd_3435132 := by
    simpa [prefixWord, tailWord_3435132, baseEnd_3435132] using wordTrace_append hprefix tailTrace_3435132
  have hstable : (prefixWord ++ tailWord_3435132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435132).length < 2 ^ (prefixWord ++ tailWord_3435132).sum := by decide
  have hdescent : baseEnd_3435132 < baseStart_3435132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435160 : List Nat := [2, 1, 2, 4, 1, 1, 4, 7]
def baseStart_3435160 : Nat := 118140960795 + 3435160 * 2 ^ 59
def prefixEnd_3435160 : Nat := 4983230072969 + 3 ^ 40 * 3435160 * 2
def baseEnd_3435160 : Nat := 130658385562880381807555

theorem tailTrace_3435160 : CollatzResearch.WordTrace tailWord_3435160 prefixEnd_3435160 130658385562880381807555 := by
  unfold tailWord_3435160
  simp only [CollatzResearch.WordTrace]
  refine ⟨62645289117504736732619467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83527052156672982310159289 62645289117504736732619467)
  ·
    refine ⟨93967933676257105098929201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62645289117504736732619467 93967933676257105098929201)
    ·
      refine ⟨70475950257192828824196901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93967933676257105098929201 70475950257192828824196901)
      ·
        refine ⟨13214240673223655404536919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70475950257192828824196901 13214240673223655404536919)
        ·
          refine ⟨19821361009835483106805379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13214240673223655404536919 19821361009835483106805379)
          ·
            refine ⟨29732041514753224660208069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19821361009835483106805379 29732041514753224660208069)
            ·
              refine ⟨5574757784016229623789013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29732041514753224660208069 5574757784016229623789013)
              ·
                refine ⟨130658385562880381807555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5574757784016229623789013 130658385562880381807555)
                ·
                  rfl

theorem cell22_3435160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_3435160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435160 prefixEnd_3435160 := by exact prefixLift 3435160
  have htrace : WordTrace (prefixWord ++ tailWord_3435160) baseStart_3435160 baseEnd_3435160 := by
    simpa [prefixWord, tailWord_3435160, baseEnd_3435160] using wordTrace_append hprefix tailTrace_3435160
  have hstable : (prefixWord ++ tailWord_3435160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435160).length < 2 ^ (prefixWord ++ tailWord_3435160).sum := by decide
  have hdescent : baseEnd_3435160 < baseStart_3435160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435164 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_3435164 : Nat := 118140960795 + 3435164 * 2 ^ 59
def prefixEnd_3435164 : Nat := 4983230072969 + 3 ^ 40 * 3435164 * 2
def baseEnd_3435164 : Nat := 1175926839347668759167983

theorem tailTrace_3435164 : CollatzResearch.WordTrace tailWord_3435164 prefixEnd_3435164 1175926839347668759167983 := by
  unfold tailWord_3435164
  simp only [CollatzResearch.WordTrace]
  refine ⟨62645362063497491074192273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83527149417996654765589697 62645362063497491074192273)
  ·
    refine ⟨46984021547623118305644205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62645362063497491074192273 46984021547623118305644205)
    ·
      refine ⟨17619008080358669364616577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46984021547623118305644205 17619008080358669364616577)
      ·
        refine ⟨13214256060269002023462433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17619008080358669364616577 13214256060269002023462433)
        ·
          refine ⟨9910692045201751517596825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13214256060269002023462433 9910692045201751517596825)
          ·
            refine ⟨7433019033901313638197619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9910692045201751517596825 7433019033901313638197619)
            ·
              refine ⟨11149528550851970457296429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433019033901313638197619 11149528550851970457296429)
              ·
                refine ⟨4181073206569488921486161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11149528550851970457296429 4181073206569488921486161)
                ·
                  refine ⟨3135804904927116691114621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4181073206569488921486161 3135804904927116691114621)
                  ·
                    refine ⟨1175926839347668759167983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3135804904927116691114621 1175926839347668759167983)
                    ·
                      rfl

theorem cell22_3435164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_3435164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435164 prefixEnd_3435164 := by exact prefixLift 3435164
  have htrace : WordTrace (prefixWord ++ tailWord_3435164) baseStart_3435164 baseEnd_3435164 := by
    simpa [prefixWord, tailWord_3435164, baseEnd_3435164] using wordTrace_append hprefix tailTrace_3435164
  have hstable : (prefixWord ++ tailWord_3435164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435164).length < 2 ^ (prefixWord ++ tailWord_3435164).sum := by decide
  have hdescent : baseEnd_3435164 < baseStart_3435164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435297 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_3435297 : Nat := 118140960795 + 3435297 * 2 ^ 59
def prefixEnd_3435297 : Nat := 4983230072969 + 3 ^ 40 * 3435297 * 2
def baseEnd_3435297 : Nat := 1175972367965700745592575

theorem tailTrace_3435297 : CollatzResearch.WordTrace tailWord_3435297 prefixEnd_3435297 1175972367965700745592575 := by
  unfold tailWord_3435297
  simp only [CollatzResearch.WordTrace]
  refine ⟨125295575035513145862976145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83530383357008763908650763 125295575035513145862976145)
  ·
    refine ⟨93971681276634859397232109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125295575035513145862976145 93971681276634859397232109)
    ·
      refine ⟨35239380478738072273962041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93971681276634859397232109 35239380478738072273962041)
      ·
        refine ⟨26429535359053554205471531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35239380478738072273962041 26429535359053554205471531)
        ·
          refine ⟨39644303038580331308207297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26429535359053554205471531 39644303038580331308207297)
          ·
            refine ⟨29733227278935248481155473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39644303038580331308207297 29733227278935248481155473)
            ·
              refine ⟨22299920459201436360866605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29733227278935248481155473 22299920459201436360866605)
              ·
                refine ⟨8362470172200538635324977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22299920459201436360866605 8362470172200538635324977)
                ·
                  refine ⟨6271852629150403976493733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8362470172200538635324977 6271852629150403976493733)
                  ·
                    refine ⟨1175972367965700745592575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6271852629150403976493733 1175972367965700745592575)
                    ·
                      rfl

theorem cell22_3435297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_3435297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435297 prefixEnd_3435297 := by exact prefixLift 3435297
  have htrace : WordTrace (prefixWord ++ tailWord_3435297) baseStart_3435297 baseEnd_3435297 := by
    simpa [prefixWord, tailWord_3435297, baseEnd_3435297] using wordTrace_append hprefix tailTrace_3435297
  have hstable : (prefixWord ++ tailWord_3435297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435297).length < 2 ^ (prefixWord ++ tailWord_3435297).sum := by decide
  have hdescent : baseEnd_3435297 < baseStart_3435297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435318 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_3435318 : Nat := 118140960795 + 3435318 * 2 ^ 59
def prefixEnd_3435318 : Nat := 4983230072969 + 3 ^ 40 * 3435318 * 2
def baseEnd_3435318 : Nat := 391993185564954563605837

theorem tailTrace_3435318 : CollatzResearch.WordTrace tailWord_3435318 prefixEnd_3435318 391993185564954563605837 := by
  unfold tailWord_3435318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7831021310527316653093163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83530893978958044299660405 7831021310527316653093163)
  ·
    refine ⟨11746531965790974979639745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7831021310527316653093163 11746531965790974979639745)
    ·
      refine ⟨8809898974343231234729809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11746531965790974979639745 8809898974343231234729809)
      ·
        refine ⟨6607424230757423426047357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8809898974343231234729809 6607424230757423426047357)
        ·
          refine ⟨2477784086534033784767759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6607424230757423426047357 2477784086534033784767759)
          ·
            refine ⟨3716676129801050677151639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477784086534033784767759 3716676129801050677151639)
            ·
              refine ⟨5575014194701576015727459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716676129801050677151639 5575014194701576015727459)
              ·
                refine ⟨8362521292052364023591189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575014194701576015727459 8362521292052364023591189)
                ·
                  refine ⟨391993185564954563605837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8362521292052364023591189 391993185564954563605837)
                  ·
                    rfl

theorem cell22_3435318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_3435318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435318 prefixEnd_3435318 := by exact prefixLift 3435318
  have htrace : WordTrace (prefixWord ++ tailWord_3435318) baseStart_3435318 baseEnd_3435318 := by
    simpa [prefixWord, tailWord_3435318, baseEnd_3435318] using wordTrace_append hprefix tailTrace_3435318
  have hstable : (prefixWord ++ tailWord_3435318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435318).length < 2 ^ (prefixWord ++ tailWord_3435318).sum := by decide
  have hdescent : baseEnd_3435318 < baseStart_3435318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435372 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3435372 : Nat := 118140960795 + 3435372 * 2 ^ 59
def prefixEnd_3435372 : Nat := 4983230072969 + 3 ^ 40 * 3435372 * 2
def baseEnd_3435372 : Nat := 1175998041998425549967345

theorem tailTrace_3435372 : CollatzResearch.WordTrace tailWord_3435372 prefixEnd_3435372 1175998041998425549967345 := by
  unfold tailWord_3435372
  simp only [CollatzResearch.WordTrace]
  refine ⟨62649155255120716835978185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83532207006827622447970913 62649155255120716835978185)
  ·
    refine ⟨46986866441340537626983639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62649155255120716835978185 46986866441340537626983639)
    ·
      refine ⟨70480299662010806440475459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46986866441340537626983639 70480299662010806440475459)
      ·
        refine ⟨105720449493016209660713189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70480299662010806440475459 105720449493016209660713189)
        ·
          refine ⟨19822584279940539311383723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105720449493016209660713189 19822584279940539311383723)
          ·
            refine ⟨29733876419910808967075585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19822584279940539311383723 29733876419910808967075585)
            ·
              refine ⟨22300407314933106725306689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29733876419910808967075585 22300407314933106725306689)
              ·
                refine ⟨16725305486199830043980017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22300407314933106725306689 16725305486199830043980017)
                ·
                  refine ⟨12543979114649872532985013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16725305486199830043980017 12543979114649872532985013)
                  ·
                    refine ⟨1175998041998425549967345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12543979114649872532985013 1175998041998425549967345)
                    ·
                      rfl

theorem cell22_3435372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3435372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435372 prefixEnd_3435372 := by exact prefixLift 3435372
  have htrace : WordTrace (prefixWord ++ tailWord_3435372) baseStart_3435372 baseEnd_3435372 := by
    simpa [prefixWord, tailWord_3435372, baseEnd_3435372] using wordTrace_append hprefix tailTrace_3435372
  have hstable : (prefixWord ++ tailWord_3435372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435372).length < 2 ^ (prefixWord ++ tailWord_3435372).sum := by decide
  have hdescent : baseEnd_3435372 < baseStart_3435372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435378 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_3435378 : Nat := 118140960795 + 3435378 * 2 ^ 59
def prefixEnd_3435378 : Nat := 4983230072969 + 3 ^ 40 * 3435378 * 2
def baseEnd_3435378 : Nat := 1176000095921043534317327

theorem tailTrace_3435378 : CollatzResearch.WordTrace tailWord_3435378 prefixEnd_3435378 1176000095921043534317327 := by
  unfold tailWord_3435378
  simp only [CollatzResearch.WordTrace]
  refine ⟨31324632337054924174168697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83532352898813131131116525 31324632337054924174168697)
  ·
    refine ⟨23493474252791193130626523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31324632337054924174168697 23493474252791193130626523)
    ·
      refine ⟨35240211379186789695939785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23493474252791193130626523 35240211379186789695939785)
      ·
        refine ⟨26430158534390092271954839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35240211379186789695939785 26430158534390092271954839)
        ·
          refine ⟨39645237801585138407932259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26430158534390092271954839 39645237801585138407932259)
          ·
            refine ⟨59467856702377707611898389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39645237801585138407932259 59467856702377707611898389)
            ·
              refine ⟨2787555782923955044307737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59467856702377707611898389 2787555782923955044307737)
              ·
                refine ⟨2090666837192966283230803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787555782923955044307737 2090666837192966283230803)
                ·
                  refine ⟨3136000255789449424846205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090666837192966283230803 3136000255789449424846205)
                  ·
                    refine ⟨1176000095921043534317327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136000255789449424846205 1176000095921043534317327)
                    ·
                      rfl

theorem cell22_3435378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_3435378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435378 prefixEnd_3435378 := by exact prefixLift 3435378
  have htrace : WordTrace (prefixWord ++ tailWord_3435378) baseStart_3435378 baseEnd_3435378 := by
    simpa [prefixWord, tailWord_3435378, baseEnd_3435378] using wordTrace_append hprefix tailTrace_3435378
  have hstable : (prefixWord ++ tailWord_3435378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435378).length < 2 ^ (prefixWord ++ tailWord_3435378).sum := by decide
  have hdescent : baseEnd_3435378 < baseStart_3435378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435387 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 3, 4]
def baseStart_3435387 : Nat := 118140960795 + 3435387 * 2 ^ 59
def prefixEnd_3435387 : Nat := 4983230072969 + 3 ^ 40 * 3435387 * 2
def baseEnd_3435387 : Nat := 1176003176804970510842299

theorem tailTrace_3435387 : CollatzResearch.WordTrace tailWord_3435387 prefixEnd_3435387 1176003176804970510842299 := by
  unfold tailWord_3435387
  simp only [CollatzResearch.WordTrace]
  refine ⟨125298857605187091233752415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83532571736791394155834943 125298857605187091233752415)
  ·
    refine ⟨187948286407780636850628623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125298857605187091233752415 187948286407780636850628623)
    ·
      refine ⟨281922429611670955275942935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187948286407780636850628623 281922429611670955275942935)
      ·
        refine ⟨422883644417506432913914403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281922429611670955275942935 422883644417506432913914403)
        ·
          refine ⟨634325466626259649370871605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422883644417506432913914403 634325466626259649370871605)
          ·
            refine ⟨59468012496211842128519213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 634325466626259649370871605 59468012496211842128519213)
            ·
              refine ⟨22300504686079440798194705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59468012496211842128519213 22300504686079440798194705)
              ·
                refine ⟨16725378514559580598646029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22300504686079440798194705 16725378514559580598646029)
                ·
                  refine ⟨6272016942959842724492261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16725378514559580598646029 6272016942959842724492261)
                  ·
                    refine ⟨1176003176804970510842299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272016942959842724492261 1176003176804970510842299)
                    ·
                      rfl

theorem cell22_3435387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_3435387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435387 prefixEnd_3435387 := by exact prefixLift 3435387
  have htrace : WordTrace (prefixWord ++ tailWord_3435387) baseStart_3435387 baseEnd_3435387 := by
    simpa [prefixWord, tailWord_3435387, baseEnd_3435387] using wordTrace_append hprefix tailTrace_3435387
  have hstable : (prefixWord ++ tailWord_3435387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435387).length < 2 ^ (prefixWord ++ tailWord_3435387).sum := by decide
  have hdescent : baseEnd_3435387 < baseStart_3435387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435464 : List Nat := [2, 1, 3, 1, 5, 1, 1, 8]
def baseStart_3435464 : Nat := 118140960795 + 3435464 * 2 ^ 59
def prefixEnd_3435464 : Nat := 4983230072969 + 3 ^ 40 * 3435464 * 2
def baseEnd_3435464 : Nat := 130669948386507552963007

theorem tailTrace_3435464 : CollatzResearch.WordTrace tailWord_3435464 prefixEnd_3435464 130669948386507552963007 := by
  unfold tailWord_3435464
  simp only [CollatzResearch.WordTrace]
  refine ⟨62650833012954066692152723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83534444017272088922870297 62650833012954066692152723)
  ·
    refine ⟨93976249519431100038229085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62650833012954066692152723 93976249519431100038229085)
    ·
      refine ⟨35241093569786662514335907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93976249519431100038229085 35241093569786662514335907)
      ·
        refine ⟨52861640354679993771503861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35241093569786662514335907 52861640354679993771503861)
        ·
          refine ⟨4955778783251249416078487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52861640354679993771503861 4955778783251249416078487)
          ·
            refine ⟨7433668174876874124117731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955778783251249416078487 7433668174876874124117731)
            ·
              refine ⟨11150502262315311186176597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433668174876874124117731 11150502262315311186176597)
              ·
                refine ⟨130669948386507552963007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11150502262315311186176597 130669948386507552963007)
                ·
                  rfl

theorem cell22_3435464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_3435464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435464 prefixEnd_3435464 := by exact prefixLift 3435464
  have htrace : WordTrace (prefixWord ++ tailWord_3435464) baseStart_3435464 baseEnd_3435464 := by
    simpa [prefixWord, tailWord_3435464, baseEnd_3435464] using wordTrace_append hprefix tailTrace_3435464
  have hstable : (prefixWord ++ tailWord_3435464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435464).length < 2 ^ (prefixWord ++ tailWord_3435464).sum := by decide
  have hdescent : baseEnd_3435464 < baseStart_3435464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435496 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_3435496 : Nat := 118140960795 + 3435496 * 2 ^ 59
def prefixEnd_3435496 : Nat := 4983230072969 + 3 ^ 40 * 3435496 * 2
def baseEnd_3435496 : Nat := 1176040489732530559866965

theorem tailTrace_3435496 : CollatzResearch.WordTrace tailWord_3435496 prefixEnd_3435496 1176040489732530559866965 := by
  unfold tailWord_3435496
  simp only [CollatzResearch.WordTrace]
  refine ⟨62651416580896101424735171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83535222107861468566313561 62651416580896101424735171)
  ·
    refine ⟨93977124871344152137102757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62651416580896101424735171 93977124871344152137102757)
    ·
      refine ⟨17620710913377028525706767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93977124871344152137102757 17620710913377028525706767)
      ·
        refine ⟨26431066370065542788560151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17620710913377028525706767 26431066370065542788560151)
        ·
          refine ⟨39646599555098314182840227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26431066370065542788560151 39646599555098314182840227)
          ·
            refine ⟨59469899332647471274260341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39646599555098314182840227 59469899332647471274260341)
            ·
              refine ⟨5575303062435700431961907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59469899332647471274260341 5575303062435700431961907)
              ·
                refine ⟨8362954593653550647942861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5575303062435700431961907 8362954593653550647942861)
                ·
                  refine ⟨3136107972620081492978573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8362954593653550647942861 3136107972620081492978573)
                  ·
                    refine ⟨1176040489732530559866965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136107972620081492978573 1176040489732530559866965)
                    ·
                      rfl

theorem cell22_3435496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_3435496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435496 prefixEnd_3435496 := by exact prefixLift 3435496
  have htrace : WordTrace (prefixWord ++ tailWord_3435496) baseStart_3435496 baseEnd_3435496 := by
    simpa [prefixWord, tailWord_3435496, baseEnd_3435496] using wordTrace_append hprefix tailTrace_3435496
  have hstable : (prefixWord ++ tailWord_3435496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435496).length < 2 ^ (prefixWord ++ tailWord_3435496).sum := by decide
  have hdescent : baseEnd_3435496 < baseStart_3435496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435502 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3435502 : Nat := 118140960795 + 3435502 * 2 ^ 59
def prefixEnd_3435502 : Nat := 4983230072969 + 3 ^ 40 * 3435502 * 2
def baseEnd_3435502 : Nat := 1176042543655148544216947

theorem tailTrace_3435502 : CollatzResearch.WordTrace tailWord_3435502 prefixEnd_3435502 1176042543655148544216947 := by
  unfold tailWord_3435502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15662881499971308234273595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83535367999846977249459173 15662881499971308234273595)
  ·
    refine ⟨23494322249956962351410393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15662881499971308234273595 23494322249956962351410393)
    ·
      refine ⟨17620741687467721763557795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23494322249956962351410393 17620741687467721763557795)
      ·
        refine ⟨26431112531201582645336693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17620741687467721763557795 26431112531201582645336693)
        ·
          refine ⟨2477916799800148373000315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26431112531201582645336693 2477916799800148373000315)
          ·
            refine ⟨3716875199700222559500473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477916799800148373000315 3716875199700222559500473)
            ·
              refine ⟨2787656399775166919625355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3716875199700222559500473 2787656399775166919625355)
              ·
                refine ⟨4181484599662750379438033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787656399775166919625355 4181484599662750379438033)
                ·
                  refine ⟨3136113449747062784578525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4181484599662750379438033 3136113449747062784578525)
                  ·
                    refine ⟨1176042543655148544216947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136113449747062784578525 1176042543655148544216947)
                    ·
                      rfl

theorem cell22_3435502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3435502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435502 prefixEnd_3435502 := by exact prefixLift 3435502
  have htrace : WordTrace (prefixWord ++ tailWord_3435502) baseStart_3435502 baseEnd_3435502 := by
    simpa [prefixWord, tailWord_3435502, baseEnd_3435502] using wordTrace_append hprefix tailTrace_3435502
  have hstable : (prefixWord ++ tailWord_3435502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435502).length < 2 ^ (prefixWord ++ tailWord_3435502).sum := by decide
  have hdescent : baseEnd_3435502 < baseStart_3435502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435556 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3435556 : Nat := 118140960795 + 3435556 * 2 ^ 59
def prefixEnd_3435556 : Nat := 4983230072969 + 3 ^ 40 * 3435556 * 2
def baseEnd_3435556 : Nat := 1176061028958710403366781

theorem tailTrace_3435556 : CollatzResearch.WordTrace tailWord_3435556 prefixEnd_3435556 1176061028958710403366781 := by
  unfold tailWord_3435556
  simp only [CollatzResearch.WordTrace]
  refine ⟨62652510770787416548327261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83536681027716555397769681 62652510770787416548327261)
  ·
    refine ⟨23494691539045281205622723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62652510770787416548327261 23494691539045281205622723)
    ·
      refine ⟨35242037308567921808434085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23494691539045281205622723 35242037308567921808434085)
      ·
        refine ⟨6607881995356485339081391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35242037308567921808434085 6607881995356485339081391)
        ·
          refine ⟨9911822993034728008622087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607881995356485339081391 9911822993034728008622087)
          ·
            refine ⟨14867734489552092012933131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911822993034728008622087 14867734489552092012933131)
            ·
              refine ⟨22301601734328138019399697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14867734489552092012933131 22301601734328138019399697)
              ·
                refine ⟨16726201300746103514549773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22301601734328138019399697 16726201300746103514549773)
                ·
                  refine ⟨6272325487779788817956165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16726201300746103514549773 6272325487779788817956165)
                  ·
                    refine ⟨1176061028958710403366781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272325487779788817956165 1176061028958710403366781)
                    ·
                      rfl

theorem cell22_3435556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3435556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435556 prefixEnd_3435556 := by exact prefixLift 3435556
  have htrace : WordTrace (prefixWord ++ tailWord_3435556) baseStart_3435556 baseEnd_3435556 := by
    simpa [prefixWord, tailWord_3435556, baseEnd_3435556] using wordTrace_append hprefix tailTrace_3435556
  have hstable : (prefixWord ++ tailWord_3435556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435556).length < 2 ^ (prefixWord ++ tailWord_3435556).sum := by decide
  have hdescent : baseEnd_3435556 < baseStart_3435556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435584 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_3435584 : Nat := 118140960795 + 3435584 * 2 ^ 59
def prefixEnd_3435584 : Nat := 4983230072969 + 3 ^ 40 * 3435584 * 2
def baseEnd_3435584 : Nat := 1176070613930927663666695

theorem tailTrace_3435584 : CollatzResearch.WordTrace tailWord_3435584 prefixEnd_3435584 1176070613930927663666695 := by
  unfold tailWord_3435584
  simp only [CollatzResearch.WordTrace]
  refine ⟨62653021392736696939336903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83537361856982262585782537 62653021392736696939336903)
  ·
    refine ⟨93979532089105045409005355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62653021392736696939336903 93979532089105045409005355)
    ·
      refine ⟨140969298133657568113508033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93979532089105045409005355 140969298133657568113508033)
      ·
        refine ⟨105726973600243176085131025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140969298133657568113508033 105726973600243176085131025)
        ·
          refine ⟨79295230200182382063848269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105726973600243176085131025 79295230200182382063848269)
          ·
            refine ⟨29735711325068393273943101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79295230200182382063848269 29735711325068393273943101)
            ·
              refine ⟨11150891746900647477728663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29735711325068393273943101 11150891746900647477728663)
              ·
                refine ⟨16726337620350971216592995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11150891746900647477728663 16726337620350971216592995)
                ·
                  refine ⟨25089506430526456824889493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16726337620350971216592995 25089506430526456824889493)
                  ·
                    refine ⟨1176070613930927663666695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25089506430526456824889493 1176070613930927663666695)
                    ·
                      rfl

theorem cell22_3435584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_3435584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435584 prefixEnd_3435584 := by exact prefixLift 3435584
  have htrace : WordTrace (prefixWord ++ tailWord_3435584) baseStart_3435584 baseEnd_3435584 := by
    simpa [prefixWord, tailWord_3435584, baseEnd_3435584] using wordTrace_append hprefix tailTrace_3435584
  have hstable : (prefixWord ++ tailWord_3435584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435584).length < 2 ^ (prefixWord ++ tailWord_3435584).sum := by decide
  have hdescent : baseEnd_3435584 < baseStart_3435584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435590 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3435590 : Nat := 118140960795 + 3435590 * 2 ^ 59
def prefixEnd_3435590 : Nat := 4983230072969 + 3 ^ 40 * 3435590 * 2
def baseEnd_3435590 : Nat := 1176072667853545648016677

theorem tailTrace_3435590 : CollatzResearch.WordTrace tailWord_3435590 prefixEnd_3435590 1176072667853545648016677 := by
  unfold tailWord_3435590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3915820675732864278231007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83537507748967771268928149 3915820675732864278231007)
  ·
    refine ⟨5873731013599296417346511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3915820675732864278231007 5873731013599296417346511)
    ·
      refine ⟨8810596520398944626019767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5873731013599296417346511 8810596520398944626019767)
      ·
        refine ⟨13215894780598416939029651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810596520398944626019767 13215894780598416939029651)
        ·
          refine ⟨19823842170897625408544477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13215894780598416939029651 19823842170897625408544477)
          ·
            refine ⟨7433940814086609528204179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19823842170897625408544477 7433940814086609528204179)
            ·
              refine ⟨11150911221129914292306269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7433940814086609528204179 11150911221129914292306269)
              ·
                refine ⟨4181591707923717859614851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11150911221129914292306269 4181591707923717859614851)
                ·
                  refine ⟨6272387561885576789422277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4181591707923717859614851 6272387561885576789422277)
                  ·
                    refine ⟨1176072667853545648016677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272387561885576789422277 1176072667853545648016677)
                    ·
                      rfl

theorem cell22_3435590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3435590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435590 prefixEnd_3435590 := by exact prefixLift 3435590
  have htrace : WordTrace (prefixWord ++ tailWord_3435590) baseStart_3435590 baseEnd_3435590 := by
    simpa [prefixWord, tailWord_3435590, baseEnd_3435590] using wordTrace_append hprefix tailTrace_3435590
  have hstable : (prefixWord ++ tailWord_3435590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435590).length < 2 ^ (prefixWord ++ tailWord_3435590).sum := by decide
  have hdescent : baseEnd_3435590 < baseStart_3435590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435631 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 3, 3]
def baseStart_3435631 : Nat := 118140960795 + 3435631 * 2 ^ 59
def prefixEnd_3435631 : Nat := 4983230072969 + 3 ^ 40 * 3435631 * 2
def baseEnd_3435631 : Nat := 1176086702991435207741551

theorem tailTrace_3435631 : CollatzResearch.WordTrace tailWord_3435631 prefixEnd_3435631 1176086702991435207741551 := by
  unfold tailWord_3435631
  simp only [CollatzResearch.WordTrace]
  refine ⟨125307757016303120905634747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83538504677535413937089831 125307757016303120905634747)
  ·
    refine ⟨187961635524454681358452121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125307757016303120905634747 187961635524454681358452121)
    ·
      refine ⟨140971226643341011018839091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187961635524454681358452121 140971226643341011018839091)
      ·
        refine ⟨211456839965011516528258637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140971226643341011018839091 211456839965011516528258637)
        ·
          refine ⟨79296314986879318698096989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211456839965011516528258637 79296314986879318698096989)
          ·
            refine ⟨29736118120079744511786371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79296314986879318698096989 29736118120079744511786371)
            ·
              refine ⟨44604177180119616767679557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29736118120079744511786371 44604177180119616767679557)
              ·
                refine ⟨8363283221272428143939917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44604177180119616767679557 8363283221272428143939917)
                ·
                  refine ⟨3136231207977160553977469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8363283221272428143939917 3136231207977160553977469)
                  ·
                    refine ⟨1176086702991435207741551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136231207977160553977469 1176086702991435207741551)
                    ·
                      rfl

theorem cell22_3435631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_3435631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435631 prefixEnd_3435631 := by exact prefixLift 3435631
  have htrace : WordTrace (prefixWord ++ tailWord_3435631) baseStart_3435631 baseEnd_3435631 := by
    simpa [prefixWord, tailWord_3435631, baseEnd_3435631] using wordTrace_append hprefix tailTrace_3435631
  have hstable : (prefixWord ++ tailWord_3435631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435631).length < 2 ^ (prefixWord ++ tailWord_3435631).sum := by decide
  have hdescent : baseEnd_3435631 < baseStart_3435631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435644 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_3435644 : Nat := 118140960795 + 3435644 * 2 ^ 59
def prefixEnd_3435644 : Nat := 4983230072969 + 3 ^ 40 * 3435644 * 2
def baseEnd_3435644 : Nat := 392030384385702502388837

theorem tailTrace_3435644 : CollatzResearch.WordTrace tailWord_3435644 prefixEnd_3435644 392030384385702502388837 := by
  unfold tailWord_3435644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62654115582628012062928993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83538820776837349417238657 62654115582628012062928993)
  ·
    refine ⟨46990586686971009047196745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62654115582628012062928993 46990586686971009047196745)
    ·
      refine ⟨35242940015228256785397559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46990586686971009047196745 35242940015228256785397559)
      ·
        refine ⟨52864410022842385178096339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35242940015228256785397559 52864410022842385178096339)
        ·
          refine ⟨79296615034263577767144509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52864410022842385178096339 79296615034263577767144509)
          ·
            refine ⟨29736230637848841662679191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79296615034263577767144509 29736230637848841662679191)
            ·
              refine ⟨44604345956773262494018787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29736230637848841662679191 44604345956773262494018787)
              ·
                refine ⟨66906518935159893741028181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44604345956773262494018787 66906518935159893741028181)
                ·
                  refine ⟨392030384385702502388837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66906518935159893741028181 392030384385702502388837)
                  ·
                    rfl

theorem cell22_3435644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_3435644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435644 prefixEnd_3435644 := by exact prefixLift 3435644
  have htrace : WordTrace (prefixWord ++ tailWord_3435644) baseStart_3435644 baseEnd_3435644 := by
    simpa [prefixWord, tailWord_3435644, baseEnd_3435644] using wordTrace_append hprefix tailTrace_3435644
  have hstable : (prefixWord ++ tailWord_3435644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435644).length < 2 ^ (prefixWord ++ tailWord_3435644).sum := by decide
  have hdescent : baseEnd_3435644 < baseStart_3435644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435659 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_3435659 : Nat := 118140960795 + 3435659 * 2 ^ 59
def prefixEnd_3435659 : Nat := 4983230072969 + 3 ^ 40 * 3435659 * 2
def baseEnd_3435659 : Nat := 1176096287963652468041465

theorem tailTrace_3435659 : CollatzResearch.WordTrace tailWord_3435659 prefixEnd_3435659 1176096287963652468041465 := by
  unfold tailWord_3435659
  simp only [CollatzResearch.WordTrace]
  refine ⟨125308778260201681687654031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83539185506801121125102687 125308778260201681687654031)
  ·
    refine ⟨187963167390302522531481047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125308778260201681687654031 187963167390302522531481047)
    ·
      refine ⟨281944751085453783797221571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187963167390302522531481047 281944751085453783797221571)
      ·
        refine ⟨422917126628180675695832357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281944751085453783797221571 422917126628180675695832357)
        ·
          refine ⟨79296961242783876692968567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422917126628180675695832357 79296961242783876692968567)
          ·
            refine ⟨118945441864175815039452851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79296961242783876692968567 118945441864175815039452851)
            ·
              refine ⟨178418162796263722559179277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118945441864175815039452851 178418162796263722559179277)
              ·
                refine ⟨66906811048598895959692229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178418162796263722559179277 66906811048598895959692229)
                ·
                  refine ⟨12545027071612292992442293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66906811048598895959692229 12545027071612292992442293)
                  ·
                    refine ⟨1176096287963652468041465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12545027071612292992442293 1176096287963652468041465)
                    ·
                      rfl

theorem cell22_3435659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_3435659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435659 prefixEnd_3435659 := by exact prefixLift 3435659
  have htrace : WordTrace (prefixWord ++ tailWord_3435659) baseStart_3435659 baseEnd_3435659 := by
    simpa [prefixWord, tailWord_3435659, baseEnd_3435659] using wordTrace_append hprefix tailTrace_3435659
  have hstable : (prefixWord ++ tailWord_3435659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435659).length < 2 ^ (prefixWord ++ tailWord_3435659).sum := by decide
  have hdescent : baseEnd_3435659 < baseStart_3435659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435716 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3435716 : Nat := 118140960795 + 3435716 * 2 ^ 59
def prefixEnd_3435716 : Nat := 4983230072969 + 3 ^ 40 * 3435716 * 2
def baseEnd_3435716 : Nat := 1176115800228523319366291

theorem tailTrace_3435716 : CollatzResearch.WordTrace tailWord_3435716 prefixEnd_3435716 1176115800228523319366291 := by
  unfold tailWord_3435716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62655428610497590211239501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83540571480663453614986001 62655428610497590211239501)
  ·
    refine ⟨23495785728936596329214813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62655428610497590211239501 23495785728936596329214813)
    ·
      refine ⟨8810919648351223623455555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23495785728936596329214813 8810919648351223623455555)
      ·
        refine ⟨13216379472526835435183333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8810919648351223623455555 13216379472526835435183333)
        ·
          refine ⟨2478071151098781644096875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13216379472526835435183333 2478071151098781644096875)
          ·
            refine ⟨3717106726648172466145313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478071151098781644096875 3717106726648172466145313)
            ·
              refine ⟨2787830044986129349608985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3717106726648172466145313 2787830044986129349608985)
              ·
                refine ⟨2090872533739597012206739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787830044986129349608985 2090872533739597012206739)
                ·
                  refine ⟨3136308800609395518310109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090872533739597012206739 3136308800609395518310109)
                  ·
                    refine ⟨1176115800228523319366291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136308800609395518310109 1176115800228523319366291)
                    ·
                      rfl

theorem cell22_3435716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3435716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435716 prefixEnd_3435716 := by exact prefixLift 3435716
  have htrace : WordTrace (prefixWord ++ tailWord_3435716) baseStart_3435716 baseEnd_3435716 := by
    simpa [prefixWord, tailWord_3435716, baseEnd_3435716] using wordTrace_append hprefix tailTrace_3435716
  have hstable : (prefixWord ++ tailWord_3435716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435716).length < 2 ^ (prefixWord ++ tailWord_3435716).sum := by decide
  have hdescent : baseEnd_3435716 < baseStart_3435716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435721 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 8, 3]
def baseStart_3435721 : Nat := 118140960795 + 3435721 * 2 ^ 59
def prefixEnd_3435721 : Nat := 4983230072969 + 3 ^ 40 * 3435721 * 2
def baseEnd_3435721 : Nat := 1176117511830704972991275

theorem tailTrace_3435721 : CollatzResearch.WordTrace tailWord_3435721 prefixEnd_3435721 1176117511830704972991275 := by
  unfold tailWord_3435721
  simp only [CollatzResearch.WordTrace]
  refine ⟨125311039585977066276411017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83540693057318044184274011 125311039585977066276411017)
  ·
    refine ⟨93983279689482799707308263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125311039585977066276411017 93983279689482799707308263)
    ·
      refine ⟨140974919534224199560962395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93983279689482799707308263 140974919534224199560962395)
      ·
        refine ⟨211462379301336299341443593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140974919534224199560962395 211462379301336299341443593)
        ·
          refine ⟨158596784476002224506082695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211462379301336299341443593 158596784476002224506082695)
          ·
            refine ⟨237895176714003336759124043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158596784476002224506082695 237895176714003336759124043)
            ·
              refine ⟨356842765071005005138686065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237895176714003336759124043 356842765071005005138686065)
              ·
                refine ⟨267632073803253753854014549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 356842765071005005138686065 267632073803253753854014549)
                ·
                  refine ⟨3136313364881879927976733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 267632073803253753854014549 3136313364881879927976733)
                  ·
                    refine ⟨1176117511830704972991275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136313364881879927976733 1176117511830704972991275)
                    ·
                      rfl

theorem cell22_3435721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 8, 3].length) (baseStart_3435721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435721 prefixEnd_3435721 := by exact prefixLift 3435721
  have htrace : WordTrace (prefixWord ++ tailWord_3435721) baseStart_3435721 baseEnd_3435721 := by
    simpa [prefixWord, tailWord_3435721, baseEnd_3435721] using wordTrace_append hprefix tailTrace_3435721
  have hstable : (prefixWord ++ tailWord_3435721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435721).length < 2 ^ (prefixWord ++ tailWord_3435721).sum := by decide
  have hdescent : baseEnd_3435721 < baseStart_3435721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435772 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_3435772 : Nat := 118140960795 + 3435772 * 2 ^ 59
def prefixEnd_3435772 : Nat := 4983230072969 + 3 ^ 40 * 3435772 * 2
def baseEnd_3435772 : Nat := 1176134970172957839966119

theorem tailTrace_3435772 : CollatzResearch.WordTrace tailWord_3435772 prefixEnd_3435772 1176134970172957839966119 := by
  unfold tailWord_3435772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62656449854396150993258785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83541933139194867991011713 62656449854396150993258785)
  ·
    refine ⟨46992337390797113244944089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62656449854396150993258785 46992337390797113244944089)
    ·
      refine ⟨35244253043097834933708067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46992337390797113244944089 35244253043097834933708067)
      ·
        refine ⟨52866379564646752400562101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35244253043097834933708067 52866379564646752400562101)
        ·
          refine ⟨4956223084185633037552697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52866379564646752400562101 4956223084185633037552697)
          ·
            refine ⟨3717167313139224778164523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4956223084185633037552697 3717167313139224778164523)
            ·
              refine ⟨5575750969708837167246785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717167313139224778164523 5575750969708837167246785)
              ·
                refine ⟨4181813227281627875435089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575750969708837167246785 4181813227281627875435089)
                ·
                  refine ⟨3136359920461220906576317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4181813227281627875435089 3136359920461220906576317)
                  ·
                    refine ⟨1176134970172957839966119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136359920461220906576317 1176134970172957839966119)
                    ·
                      rfl

theorem cell22_3435772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_3435772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435772 prefixEnd_3435772 := by exact prefixLift 3435772
  have htrace : WordTrace (prefixWord ++ tailWord_3435772) baseStart_3435772 baseEnd_3435772 := by
    simpa [prefixWord, tailWord_3435772, baseEnd_3435772] using wordTrace_append hprefix tailTrace_3435772
  have hstable : (prefixWord ++ tailWord_3435772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435772).length < 2 ^ (prefixWord ++ tailWord_3435772).sum := by decide
  have hdescent : baseEnd_3435772 < baseStart_3435772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435873 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 6, 3]
def baseStart_3435873 : Nat := 118140960795 + 3435873 * 2 ^ 59
def prefixEnd_3435873 : Nat := 4983230072969 + 3 ^ 40 * 3435873 * 2
def baseEnd_3435873 : Nat := 1176169544537027243190809

theorem tailTrace_3435873 : CollatzResearch.WordTrace tailWord_3435873 prefixEnd_3435873 1176169544537027243190809 := by
  unfold tailWord_3435873
  simp only [CollatzResearch.WordTrace]
  refine ⟨125316583481426396235944273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83544388987617597490629515 125316583481426396235944273)
  ·
    refine ⟨93987437611069797176958205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125316583481426396235944273 93987437611069797176958205)
    ·
      refine ⟨35245289104151173941359327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93987437611069797176958205 35245289104151173941359327)
      ·
        refine ⟨52867933656226760912038991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35245289104151173941359327 52867933656226760912038991)
        ·
          refine ⟨79301900484340141368058487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52867933656226760912038991 79301900484340141368058487)
          ·
            refine ⟨118952850726510212052087731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79301900484340141368058487 118952850726510212052087731)
            ·
              refine ⟨178429276089765318078131597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118952850726510212052087731 178429276089765318078131597)
              ·
                refine ⟨66910978533661994279299349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178429276089765318078131597 66910978533661994279299349)
                ·
                  refine ⟨3136452118765405981842157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66910978533661994279299349 3136452118765405981842157)
                  ·
                    refine ⟨1176169544537027243190809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136452118765405981842157 1176169544537027243190809)
                    ·
                      rfl

theorem cell22_3435873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_3435873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435873 prefixEnd_3435873 := by exact prefixLift 3435873
  have htrace : WordTrace (prefixWord ++ tailWord_3435873) baseStart_3435873 baseEnd_3435873 := by
    simpa [prefixWord, tailWord_3435873, baseEnd_3435873] using wordTrace_append hprefix tailTrace_3435873
  have hstable : (prefixWord ++ tailWord_3435873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435873).length < 2 ^ (prefixWord ++ tailWord_3435873).sum := by decide
  have hdescent : baseEnd_3435873 < baseStart_3435873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435888 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_3435888 : Nat := 118140960795 + 3435888 * 2 ^ 59
def prefixEnd_3435888 : Nat := 4983230072969 + 3 ^ 40 * 3435888 * 2
def baseEnd_3435888 : Nat := 1176174679343572204065763

theorem tailTrace_3435888 : CollatzResearch.WordTrace tailWord_3435888 prefixEnd_3435888 1176174679343572204065763 := by
  unfold tailWord_3435888
  simp only [CollatzResearch.WordTrace]
  refine ⟨62658565288186026898870159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83544753717581369198493545 62658565288186026898870159)
  ·
    refine ⟨93987847932279040348305239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62658565288186026898870159 93987847932279040348305239)
    ·
      refine ⟨140981771898418560522457859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93987847932279040348305239 140981771898418560522457859)
      ·
        refine ⟨211472657847627840783686789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140981771898418560522457859 211472657847627840783686789)
        ·
          refine ⟨39651123346430220146941273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211472657847627840783686789 39651123346430220146941273)
          ·
            refine ⟨29738342509822665110205955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39651123346430220146941273 29738342509822665110205955)
            ·
              refine ⟨44607513764733997665308933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29738342509822665110205955 44607513764733997665308933)
              ·
                refine ⟨8363908830887624562245425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44607513764733997665308933 8363908830887624562245425)
                ·
                  refine ⟨6272931623165718421684069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8363908830887624562245425 6272931623165718421684069)
                  ·
                    refine ⟨1176174679343572204065763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6272931623165718421684069 1176174679343572204065763)
                    ·
                      rfl

theorem cell22_3435888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_3435888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435888 prefixEnd_3435888 := by exact prefixLift 3435888
  have htrace : WordTrace (prefixWord ++ tailWord_3435888) baseStart_3435888 baseEnd_3435888 := by
    simpa [prefixWord, tailWord_3435888, baseEnd_3435888] using wordTrace_append hprefix tailTrace_3435888
  have hstable : (prefixWord ++ tailWord_3435888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435888).length < 2 ^ (prefixWord ++ tailWord_3435888).sum := by decide
  have hdescent : baseEnd_3435888 < baseStart_3435888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3435922 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3435922 : Nat := 118140960795 + 3435922 * 2 ^ 59
def prefixEnd_3435922 : Nat := 4983230072969 + 3 ^ 40 * 3435922 * 2
def baseEnd_3435922 : Nat := 1176186318238407448715659

theorem tailTrace_3435922 : CollatzResearch.WordTrace tailWord_3435922 prefixEnd_3435922 1176186318238407448715659 := by
  unfold tailWord_3435922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31329592664562219401119505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83545580438832585069652013 31329592664562219401119505)
  ·
    refine ⟨23497194498421664550839629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31329592664562219401119505 23497194498421664550839629)
    ·
      refine ⟨8811447936908124206564861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23497194498421664550839629 8811447936908124206564861)
      ·
        refine ⟨3304292976340546577461823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8811447936908124206564861 3304292976340546577461823)
        ·
          refine ⟨4956439464510819866192735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304292976340546577461823 4956439464510819866192735)
          ·
            refine ⟨7434659196766229799289103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956439464510819866192735 7434659196766229799289103)
            ·
              refine ⟨11151988795149344698933655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7434659196766229799289103 11151988795149344698933655)
              ·
                refine ⟨16727983192724017048400483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11151988795149344698933655 16727983192724017048400483)
                ·
                  refine ⟨25091974789086025572600725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16727983192724017048400483 25091974789086025572600725)
                  ·
                    refine ⟨1176186318238407448715659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25091974789086025572600725 1176186318238407448715659)
                    ·
                      rfl

theorem cell22_3435922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3435922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3435922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3435922 prefixEnd_3435922 := by exact prefixLift 3435922
  have htrace : WordTrace (prefixWord ++ tailWord_3435922) baseStart_3435922 baseEnd_3435922 := by
    simpa [prefixWord, tailWord_3435922, baseEnd_3435922] using wordTrace_append hprefix tailTrace_3435922
  have hstable : (prefixWord ++ tailWord_3435922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3435922).length < 2 ^ (prefixWord ++ tailWord_3435922).sum := by decide
  have hdescent : baseEnd_3435922 < baseStart_3435922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3435922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436023 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3436023 : Nat := 118140960795 + 3436023 * 2 ^ 59
def prefixEnd_3436023 : Nat := 4983230072969 + 3 ^ 40 * 3436023 * 2
def baseEnd_3436023 : Nat := 1176220892602476851940349

theorem tailTrace_3436023 : CollatzResearch.WordTrace tailWord_3436023 prefixEnd_3436023 1176220892602476851940349 := by
  unfold tailWord_3436023
  simp only [CollatzResearch.WordTrace]
  refine ⟨125322054430882971853904723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83548036287255314569269815 125322054430882971853904723)
  ·
    refine ⟨187983081646324457780857085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125322054430882971853904723 187983081646324457780857085)
    ·
      refine ⟨70493655617371671667821407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187983081646324457780857085 70493655617371671667821407)
      ·
        refine ⟨105740483426057507501732111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70493655617371671667821407 105740483426057507501732111)
        ·
          refine ⟨158610725139086261252598167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105740483426057507501732111 158610725139086261252598167)
          ·
            refine ⟨237916087708629391878897251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158610725139086261252598167 237916087708629391878897251)
            ·
              refine ⟨356874131562944087818345877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237916087708629391878897251 356874131562944087818345877)
              ·
                refine ⟨16728474917013004116484963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 356874131562944087818345877 16728474917013004116484963)
                ·
                  refine ⟨25092712375519506174727445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16728474917013004116484963 25092712375519506174727445)
                  ·
                    refine ⟨1176220892602476851940349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25092712375519506174727445 1176220892602476851940349)
                    ·
                      rfl

theorem cell22_3436023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3436023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436023 prefixEnd_3436023 := by exact prefixLift 3436023
  have htrace : WordTrace (prefixWord ++ tailWord_3436023) baseStart_3436023 baseEnd_3436023 := by
    simpa [prefixWord, tailWord_3436023, baseEnd_3436023] using wordTrace_append hprefix tailTrace_3436023
  have hstable : (prefixWord ++ tailWord_3436023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436023).length < 2 ^ (prefixWord ++ tailWord_3436023).sum := by decide
  have hdescent : baseEnd_3436023 < baseStart_3436023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436040 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_3436040 : Nat := 118140960795 + 3436040 * 2 ^ 59
def prefixEnd_3436040 : Nat := 4983230072969 + 3 ^ 40 * 3436040 * 2
def baseEnd_3436040 : Nat := 1176226712049894474265297

theorem tailTrace_3436040 : CollatzResearch.WordTrace tailWord_3436040 prefixEnd_3436040 1176226712049894474265297 := by
  unfold tailWord_3436040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62661337235910691878636787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83548449647880922504849049 62661337235910691878636787)
  ·
    refine ⟨93992005853866037817955181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62661337235910691878636787 93992005853866037817955181)
    ·
      refine ⟨35247002195199764181733193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93992005853866037817955181 35247002195199764181733193)
      ·
        refine ⟨26435251646399823136299895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35247002195199764181733193 26435251646399823136299895)
        ·
          refine ⟨39652877469599734704449843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26435251646399823136299895 39652877469599734704449843)
          ·
            refine ⟨59479316204399602056674765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39652877469599734704449843 59479316204399602056674765)
            ·
              refine ⟨22304743576649850771253037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59479316204399602056674765 22304743576649850771253037)
              ·
                refine ⟨8364278841243694039219889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22304743576649850771253037 8364278841243694039219889)
                ·
                  refine ⟨6273209130932770529414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8364278841243694039219889 6273209130932770529414917)
                  ·
                    refine ⟨1176226712049894474265297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273209130932770529414917 1176226712049894474265297)
                    ·
                      rfl

theorem cell22_3436040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_3436040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436040 prefixEnd_3436040 := by exact prefixLift 3436040
  have htrace : WordTrace (prefixWord ++ tailWord_3436040) baseStart_3436040 baseEnd_3436040 := by
    simpa [prefixWord, tailWord_3436040, baseEnd_3436040] using wordTrace_append hprefix tailTrace_3436040
  have hstable : (prefixWord ++ tailWord_3436040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436040).length < 2 ^ (prefixWord ++ tailWord_3436040).sum := by decide
  have hdescent : baseEnd_3436040 < baseStart_3436040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436087 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 3, 3]
def baseStart_3436087 : Nat := 118140960795 + 3436087 * 2 ^ 59
def prefixEnd_3436087 : Nat := 4983230072969 + 3 ^ 40 * 3436087 * 2
def baseEnd_3436087 : Nat := 1176242801110402018340153

theorem tailTrace_3436087 : CollatzResearch.WordTrace tailWord_3436087 prefixEnd_3436087 1176242801110402018340153 := by
  unfold tailWord_3436087
  simp only [CollatzResearch.WordTrace]
  refine ⟨125324388702651110784234515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83549592468434073856156343 125324388702651110784234515)
  ·
    refine ⟨187986583053976666176351773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125324388702651110784234515 187986583053976666176351773)
    ·
      refine ⟨70494968645241249816131915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187986583053976666176351773 70494968645241249816131915)
      ·
        refine ⟨105742452967861874724197873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70494968645241249816131915 105742452967861874724197873)
        ·
          refine ⟨79306839725896406043148405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105742452967861874724197873 79306839725896406043148405)
          ·
            refine ⟨7435016224302788066545163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79306839725896406043148405 7435016224302788066545163)
            ·
              refine ⟨11152524336454182099817745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435016224302788066545163 11152524336454182099817745)
              ·
                refine ⟨8364393252340636574863309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11152524336454182099817745 8364393252340636574863309)
                ·
                  refine ⟨3136647469627738715573741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8364393252340636574863309 3136647469627738715573741)
                  ·
                    refine ⟨1176242801110402018340153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3136647469627738715573741 1176242801110402018340153)
                    ·
                      rfl

theorem cell22_3436087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_3436087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436087 prefixEnd_3436087 := by exact prefixLift 3436087
  have htrace : WordTrace (prefixWord ++ tailWord_3436087) baseStart_3436087 baseEnd_3436087 := by
    simpa [prefixWord, tailWord_3436087, baseEnd_3436087] using wordTrace_append hprefix tailTrace_3436087
  have hstable : (prefixWord ++ tailWord_3436087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436087).length < 2 ^ (prefixWord ++ tailWord_3436087).sum := by decide
  have hdescent : baseEnd_3436087 < baseStart_3436087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436160 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_3436160 : Nat := 118140960795 + 3436160 * 2 ^ 59
def prefixEnd_3436160 : Nat := 4983230072969 + 3 ^ 40 * 3436160 * 2
def baseEnd_3436160 : Nat := 1176267790502254161264929

theorem tailTrace_3436160 : CollatzResearch.WordTrace tailWord_3436160 prefixEnd_3436160 1176267790502254161264929 := by
  unfold tailWord_3436160
  simp only [CollatzResearch.WordTrace]
  refine ⟨62663525615693322125820967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83551367487591096167761289 62663525615693322125820967)
  ·
    refine ⟨93995288423539983188731451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62663525615693322125820967 93995288423539983188731451)
    ·
      refine ⟨140992932635309974783097177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93995288423539983188731451 140992932635309974783097177)
      ·
        refine ⟨105744699476482481087322883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140992932635309974783097177 105744699476482481087322883)
        ·
          refine ⟨158617049214723721630984325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105744699476482481087322883 158617049214723721630984325)
          ·
            refine ⟨29740696727760697805809561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158617049214723721630984325 29740696727760697805809561)
            ·
              refine ⟨22305522545820523354357171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29740696727760697805809561 22305522545820523354357171)
              ·
                refine ⟨33458283818730785031535757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22305522545820523354357171 33458283818730785031535757)
                ·
                  refine ⟨12546856432024044386825909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33458283818730785031535757 12546856432024044386825909)
                  ·
                    refine ⟨1176267790502254161264929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12546856432024044386825909 1176267790502254161264929)
                    ·
                      rfl

theorem cell22_3436160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_3436160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436160 prefixEnd_3436160 := by exact prefixLift 3436160
  have htrace : WordTrace (prefixWord ++ tailWord_3436160) baseStart_3436160 baseEnd_3436160 := by
    simpa [prefixWord, tailWord_3436160, baseEnd_3436160] using wordTrace_append hprefix tailTrace_3436160
  have hstable : (prefixWord ++ tailWord_3436160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436160).length < 2 ^ (prefixWord ++ tailWord_3436160).sum := by decide
  have hdescent : baseEnd_3436160 < baseStart_3436160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436230 : List Nat := [6, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3436230 : Nat := 118140960795 + 3436230 * 2 ^ 59
def prefixEnd_3436230 : Nat := 4983230072969 + 3 ^ 40 * 3436230 * 2
def baseEnd_3436230 : Nat := 392097250977599104004905

theorem tailTrace_3436230 : CollatzResearch.WordTrace tailWord_3436230 prefixEnd_3436230 392097250977599104004905 := by
  unfold tailWord_3436230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916550135660407693959067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83553069560755364137793429 3916550135660407693959067)
  ·
    refine ⟨5874825203490611540938601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3916550135660407693959067 5874825203490611540938601)
    ·
      refine ⟨4406118902617958655703951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5874825203490611540938601 4406118902617958655703951)
      ·
        refine ⟨6609178353926937983555927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4406118902617958655703951 6609178353926937983555927)
        ·
          refine ⟨9913767530890406975333891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6609178353926937983555927 9913767530890406975333891)
          ·
            refine ⟨14870651296335610463000837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9913767530890406975333891 14870651296335610463000837)
            ·
              refine ⟨2788247118062926961812657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14870651296335610463000837 2788247118062926961812657)
              ·
                refine ⟨2091185338547195221359493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788247118062926961812657 2091185338547195221359493)
                ·
                  refine ⟨392097250977599104004905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091185338547195221359493 392097250977599104004905)
                  ·
                    rfl

theorem cell22_3436230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3436230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436230 prefixEnd_3436230 := by exact prefixLift 3436230
  have htrace : WordTrace (prefixWord ++ tailWord_3436230) baseStart_3436230 baseEnd_3436230 := by
    simpa [prefixWord, tailWord_3436230, baseEnd_3436230] using wordTrace_append hprefix tailTrace_3436230
  have hstable : (prefixWord ++ tailWord_3436230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436230).length < 2 ^ (prefixWord ++ tailWord_3436230).sum := by decide
  have hdescent : baseEnd_3436230 < baseStart_3436230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436235 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 7]
def baseStart_3436235 : Nat := 118140960795 + 3436235 * 2 ^ 59
def prefixEnd_3436235 : Nat := 4983230072969 + 3 ^ 40 * 3436235 * 2
def baseEnd_3436235 : Nat := 392097821511659655213233

theorem tailTrace_3436235 : CollatzResearch.WordTrace tailWord_3436235 prefixEnd_3436235 392097821511659655213233 := by
  unfold tailWord_3436235
  simp only [CollatzResearch.WordTrace]
  refine ⟨125329786706114932060622159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83553191137409954707081439 125329786706114932060622159)
  ·
    refine ⟨187994680059172398090933239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125329786706114932060622159 187994680059172398090933239)
    ·
      refine ⟨281992020088758597136399859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187994680059172398090933239 281992020088758597136399859)
      ·
        refine ⟨422988030133137895704599789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281992020088758597136399859 422988030133137895704599789)
        ·
          refine ⟨158620511299926710889224921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422988030133137895704599789 158620511299926710889224921)
          ·
            refine ⟨118965383474945033166918691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158620511299926710889224921 118965383474945033166918691)
            ·
              refine ⟨178448075212417549750378037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118965383474945033166918691 178448075212417549750378037)
              ·
                refine ⟨16729507051164145289097941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178448075212417549750378037 16729507051164145289097941)
                ·
                  refine ⟨392097821511659655213233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16729507051164145289097941 392097821511659655213233)
                  ·
                    rfl

theorem cell22_3436235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_3436235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436235 prefixEnd_3436235 := by exact prefixLift 3436235
  have htrace : WordTrace (prefixWord ++ tailWord_3436235) baseStart_3436235 baseEnd_3436235 := by
    simpa [prefixWord, tailWord_3436235, baseEnd_3436235] using wordTrace_append hprefix tailTrace_3436235
  have hstable : (prefixWord ++ tailWord_3436235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436235).length < 2 ^ (prefixWord ++ tailWord_3436235).sum := by decide
  have hdescent : baseEnd_3436235 < baseStart_3436235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436344 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_3436344 : Nat := 118140960795 + 3436344 * 2 ^ 59
def prefixEnd_3436344 : Nat := 4983230072969 + 3 ^ 40 * 3436344 * 2
def baseEnd_3436344 : Nat := 1176330777462539014664365

theorem tailTrace_3436344 : CollatzResearch.WordTrace tailWord_3436344 prefixEnd_3436344 1176330777462539014664365 := by
  unfold tailWord_3436344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62666881131360021838170043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83555841508480029117560057 62666881131360021838170043)
  ·
    refine ⟨94000321697040032757255065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62666881131360021838170043 94000321697040032757255065)
    ·
      refine ⟨70500241272780024567941299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94000321697040032757255065 70500241272780024567941299)
      ·
        refine ⟨105750361909170036851911949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70500241272780024567941299 105750361909170036851911949)
        ·
          refine ⟨39656385715938763819466981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105750361909170036851911949 39656385715938763819466981)
          ·
            refine ⟨7435572321738518216150059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39656385715938763819466981 7435572321738518216150059)
            ·
              refine ⟨11153358482607777324225089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435572321738518216150059 11153358482607777324225089)
              ·
                refine ⟨8365018861955832993168817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11153358482607777324225089 8365018861955832993168817)
                ·
                  refine ⟨6273764146466874744876613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365018861955832993168817 6273764146466874744876613)
                  ·
                    refine ⟨1176330777462539014664365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6273764146466874744876613 1176330777462539014664365)
                    ·
                      rfl

theorem cell22_3436344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_3436344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436344 prefixEnd_3436344 := by exact prefixLift 3436344
  have htrace : WordTrace (prefixWord ++ tailWord_3436344) baseStart_3436344 baseEnd_3436344 := by
    simpa [prefixWord, tailWord_3436344, baseEnd_3436344] using wordTrace_append hprefix tailTrace_3436344
  have hstable : (prefixWord ++ tailWord_3436344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436344).length < 2 ^ (prefixWord ++ tailWord_3436344).sum := by decide
  have hdescent : baseEnd_3436344 < baseStart_3436344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436419 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 2, 5]
def baseStart_3436419 : Nat := 118140960795 + 3436419 * 2 ^ 59
def prefixEnd_3436419 : Nat := 4983230072969 + 3 ^ 40 * 3436419 * 2
def baseEnd_3436419 : Nat := 1176356451495263819039135

theorem tailTrace_3436419 : CollatzResearch.WordTrace tailWord_3436419 prefixEnd_3436419 1176356451495263819039135 := by
  unfold tailWord_3436419
  simp only [CollatzResearch.WordTrace]
  refine ⟨125336497737448331485320311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83557665158298887656880207 125336497737448331485320311)
  ·
    refine ⟨188004746606172497227980467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125336497737448331485320311 188004746606172497227980467)
    ·
      refine ⟨282007119909258745841970701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188004746606172497227980467 282007119909258745841970701)
      ·
        refine ⟨105752669965972029690739013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282007119909258745841970701 105752669965972029690739013)
        ·
          refine ⟨19828625618619755567013565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105752669965972029690739013 19828625618619755567013565)
          ·
            refine ⟨7435734606982408337630087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19828625618619755567013565 7435734606982408337630087)
            ·
              refine ⟨11153601910473612506445131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7435734606982408337630087 11153601910473612506445131)
              ·
                refine ⟨16730402865710418759667697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11153601910473612506445131 16730402865710418759667697)
                ·
                  refine ⟨12547802149282814069750773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16730402865710418759667697 12547802149282814069750773)
                  ·
                    refine ⟨1176356451495263819039135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12547802149282814069750773 1176356451495263819039135)
                    ·
                      rfl

theorem cell22_3436419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_3436419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436419 prefixEnd_3436419 := by exact prefixLift 3436419
  have htrace : WordTrace (prefixWord ++ tailWord_3436419) baseStart_3436419 baseEnd_3436419 := by
    simpa [prefixWord, tailWord_3436419, baseEnd_3436419] using wordTrace_append hprefix tailTrace_3436419
  have hstable : (prefixWord ++ tailWord_3436419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436419).length < 2 ^ (prefixWord ++ tailWord_3436419).sum := by decide
  have hdescent : baseEnd_3436419 < baseStart_3436419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436432 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_3436432 : Nat := 118140960795 + 3436432 * 2 ^ 59
def prefixEnd_3436432 : Nat := 4983230072969 + 3 ^ 40 * 3436432 * 2
def baseEnd_3436432 : Nat := 392120300553645372821365

theorem tailTrace_3436432 : CollatzResearch.WordTrace tailWord_3436432 prefixEnd_3436432 392120300553645372821365 := by
  unfold tailWord_3436432
  simp only [CollatzResearch.WordTrace]
  refine ⟨62668485943200617352771775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83557981257600823137029033 62668485943200617352771775)
  ·
    refine ⟨94002728914800926029157663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62668485943200617352771775 94002728914800926029157663)
    ·
      refine ⟨141004093372201389043736495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94002728914800926029157663 141004093372201389043736495)
      ·
        refine ⟨211506140058302083565604743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141004093372201389043736495 211506140058302083565604743)
        ·
          refine ⟨317259210087453125348407115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211506140058302083565604743 317259210087453125348407115)
          ·
            refine ⟨475888815131179688022610673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317259210087453125348407115 475888815131179688022610673)
            ·
              refine ⟨356916611348384766016958005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475888815131179688022610673 356916611348384766016958005)
              ·
                refine ⟨33460932313911071814089813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 356916611348384766016958005 33460932313911071814089813)
                ·
                  refine ⟨392120300553645372821365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33460932313911071814089813 392120300553645372821365)
                  ·
                    rfl

theorem cell22_3436432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_3436432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436432 prefixEnd_3436432 := by exact prefixLift 3436432
  have htrace : WordTrace (prefixWord ++ tailWord_3436432) baseStart_3436432 baseEnd_3436432 := by
    simpa [prefixWord, tailWord_3436432, baseEnd_3436432] using wordTrace_append hprefix tailTrace_3436432
  have hstable : (prefixWord ++ tailWord_3436432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436432).length < 2 ^ (prefixWord ++ tailWord_3436432).sum := by decide
  have hdescent : baseEnd_3436432 < baseStart_3436432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436494 : List Nat := [4, 1, 1, 1, 2, 2, 3, 8]
def baseStart_3436494 : Nat := 118140960795 + 3436494 * 2 ^ 59
def prefixEnd_3436494 : Nat := 4983230072969 + 3 ^ 40 * 3436494 * 2
def baseEnd_3436494 : Nat := 130709125058665402601545

theorem tailTrace_3436494 : CollatzResearch.WordTrace tailWord_3436494 prefixEnd_3436494 130709125058665402601545 := by
  unfold tailWord_3436494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15667404151522077411787567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83559488808117746196200357 15667404151522077411787567)
  ·
    refine ⟨23501106227283116117681351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15667404151522077411787567 23501106227283116117681351)
    ·
      refine ⟨35251659340924674176522027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23501106227283116117681351 35251659340924674176522027)
      ·
        refine ⟨52877489011387011264783041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35251659340924674176522027 52877489011387011264783041)
        ·
          refine ⟨39658116758540258448587281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52877489011387011264783041 39658116758540258448587281)
          ·
            refine ⟨29743587568905193836440461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39658116758540258448587281 29743587568905193836440461)
            ·
              refine ⟨11153845338339447688665173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29743587568905193836440461 11153845338339447688665173)
              ·
                refine ⟨130709125058665402601545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11153845338339447688665173 130709125058665402601545)
                ·
                  rfl

theorem cell22_3436494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_3436494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436494 prefixEnd_3436494 := by exact prefixLift 3436494
  have htrace : WordTrace (prefixWord ++ tailWord_3436494) baseStart_3436494 baseEnd_3436494 := by
    simpa [prefixWord, tailWord_3436494, baseEnd_3436494] using wordTrace_append hprefix tailTrace_3436494
  have hstable : (prefixWord ++ tailWord_3436494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436494).length < 2 ^ (prefixWord ++ tailWord_3436494).sum := by decide
  have hdescent : baseEnd_3436494 < baseStart_3436494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436573 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 5]
def baseStart_3436573 : Nat := 118140960795 + 3436573 * 2 ^ 59
def prefixEnd_3436573 : Nat := 4983230072969 + 3 ^ 40 * 3436573 * 2
def baseEnd_3436573 : Nat := 392136389614152916896221

theorem tailTrace_3436573 : CollatzResearch.WordTrace tailWord_3436573 prefixEnd_3436573 392136389614152916896221 := by
  unfold tailWord_3436573
  simp only [CollatzResearch.WordTrace]
  refine ⟨125342114578890415786426373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83561409719260277190950915 125342114578890415786426373)
  ·
    refine ⟨23501646483541952959954945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125342114578890415786426373 23501646483541952959954945)
    ·
      refine ⟨17626234862656464719966209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23501646483541952959954945 17626234862656464719966209)
      ·
        refine ⟨13219676146992348539974657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17626234862656464719966209 13219676146992348539974657)
        ·
          refine ⟨9914757110244261404980993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13219676146992348539974657 9914757110244261404980993)
          ·
            refine ⟨7436067832683196053735745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9914757110244261404980993 7436067832683196053735745)
            ·
              refine ⟨5577050874512397040301809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7436067832683196053735745 5577050874512397040301809)
              ·
                refine ⟨4182788155884297780226357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5577050874512397040301809 4182788155884297780226357)
                ·
                  refine ⟨392136389614152916896221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182788155884297780226357 392136389614152916896221)
                  ·
                    rfl

theorem cell22_3436573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_3436573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436573 prefixEnd_3436573 := by exact prefixLift 3436573
  have htrace : WordTrace (prefixWord ++ tailWord_3436573) baseStart_3436573 baseEnd_3436573 := by
    simpa [prefixWord, tailWord_3436573, baseEnd_3436573] using wordTrace_append hprefix tailTrace_3436573
  have hstable : (prefixWord ++ tailWord_3436573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436573).length < 2 ^ (prefixWord ++ tailWord_3436573).sum := by decide
  have hdescent : baseEnd_3436573 < baseStart_3436573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436631 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 2, 4]
def baseStart_3436631 : Nat := 118140960795 + 3436631 * 2 ^ 59
def prefixEnd_3436631 : Nat := 4983230072969 + 3 ^ 40 * 3436631 * 2
def baseEnd_3436631 : Nat := 1176429023427765932738485

theorem tailTrace_3436631 : CollatzResearch.WordTrace tailWord_3436631 prefixEnd_3436631 1176429023427765932738485 := by
  unfold tailWord_3436631
  simp only [CollatzResearch.WordTrace]
  refine ⟨125344230012680291692037747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83562820008453527794691831 125344230012680291692037747)
  ·
    refine ⟨188016345019020437538056621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125344230012680291692037747 188016345019020437538056621)
    ·
      refine ⟨70506129382132664076771233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188016345019020437538056621 70506129382132664076771233)
      ·
        refine ⟨52879597036599498057578425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70506129382132664076771233 52879597036599498057578425)
        ·
          refine ⟨39659697777449623543183819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52879597036599498057578425 39659697777449623543183819)
          ·
            refine ⟨59489546666174435314775729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39659697777449623543183819 59489546666174435314775729)
            ·
              refine ⟨44617159999630826486081797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59489546666174435314775729 44617159999630826486081797)
              ·
                refine ⟨8365717499930779966140337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44617159999630826486081797 8365717499930779966140337)
                ·
                  refine ⟨6274288124948084974605253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8365717499930779966140337 6274288124948084974605253)
                  ·
                    refine ⟨1176429023427765932738485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6274288124948084974605253 1176429023427765932738485)
                    ·
                      rfl

theorem cell22_3436631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_3436631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436631 prefixEnd_3436631 := by exact prefixLift 3436631
  have htrace : WordTrace (prefixWord ++ tailWord_3436631) baseStart_3436631 baseEnd_3436631 := by
    simpa [prefixWord, tailWord_3436631, baseEnd_3436631] using wordTrace_append hprefix tailTrace_3436631
  have hstable : (prefixWord ++ tailWord_3436631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436631).length < 2 ^ (prefixWord ++ tailWord_3436631).sum := by decide
  have hdescent : baseEnd_3436631 < baseStart_3436631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436650 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_3436650 : Nat := 118140960795 + 3436650 * 2 ^ 59
def prefixEnd_3436650 : Nat := 4983230072969 + 3 ^ 40 * 3436650 * 2
def baseEnd_3436650 : Nat := 1176435527516056216513427

theorem tailTrace_3436650 : CollatzResearch.WordTrace tailWord_3436650 prefixEnd_3436650 1176435527516056216513427 := by
  unfold tailWord_3436650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31336230749902864484244851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83563281999740971957986269 31336230749902864484244851)
  ·
    refine ⟨47004346124854296726367277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31336230749902864484244851 47004346124854296726367277)
    ·
      refine ⟨17626629796820361272387729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47004346124854296726367277 17626629796820361272387729)
      ·
        refine ⟨13219972347615270954290797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17626629796820361272387729 13219972347615270954290797)
        ·
          refine ⟨4957489630355726607859049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13219972347615270954290797 4957489630355726607859049)
          ·
            refine ⟨3718117222766794955894287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4957489630355726607859049 3718117222766794955894287)
            ·
              refine ⟨5577175834150192433841431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718117222766794955894287 5577175834150192433841431)
              ·
                refine ⟨8365763751225288650762147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577175834150192433841431 8365763751225288650762147)
                ·
                  refine ⟨12548645626837932976143221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8365763751225288650762147 12548645626837932976143221)
                  ·
                    refine ⟨1176435527516056216513427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12548645626837932976143221 1176435527516056216513427)
                    ·
                      rfl

theorem cell22_3436650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_3436650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436650 prefixEnd_3436650 := by exact prefixLift 3436650
  have htrace : WordTrace (prefixWord ++ tailWord_3436650) baseStart_3436650 baseEnd_3436650 := by
    simpa [prefixWord, tailWord_3436650, baseEnd_3436650] using wordTrace_append hprefix tailTrace_3436650
  have hstable : (prefixWord ++ tailWord_3436650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436650).length < 2 ^ (prefixWord ++ tailWord_3436650).sum := by decide
  have hdescent : baseEnd_3436650 < baseStart_3436650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436663 : List Nat := [1, 1, 3, 1, 1, 7, 2, 6]
def baseStart_3436663 : Nat := 118140960795 + 3436663 * 2 ^ 59
def prefixEnd_3436663 : Nat := 4983230072969 + 3 ^ 40 * 3436663 * 2
def baseEnd_3436663 : Nat := 130715553075747612882043

theorem tailTrace_3436663 : CollatzResearch.WordTrace tailWord_3436663 prefixEnd_3436663 130715553075747612882043 := by
  unfold tailWord_3436663
  simp only [CollatzResearch.WordTrace]
  refine ⟨125345397148564361157202643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83563598099042907438135095 125345397148564361157202643)
  ·
    refine ⟨188018095722846541735803965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125345397148564361157202643 188018095722846541735803965)
    ·
      refine ⟨70506785896067453150926487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188018095722846541735803965 70506785896067453150926487)
      ·
        refine ⟨105760178844101179726389731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70506785896067453150926487 105760178844101179726389731)
        ·
          refine ⟨158640268266151769589584597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105760178844101179726389731 158640268266151769589584597)
          ·
            refine ⟨3718131287487932099755889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 158640268266151769589584597 3718131287487932099755889)
            ·
              refine ⟨2788598465615949074816917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718131287487932099755889 2788598465615949074816917)
              ·
                refine ⟨130715553075747612882043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2788598465615949074816917 130715553075747612882043)
                ·
                  rfl

theorem cell22_3436663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 6].length) (baseStart_3436663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436663 prefixEnd_3436663 := by exact prefixLift 3436663
  have htrace : WordTrace (prefixWord ++ tailWord_3436663) baseStart_3436663 baseEnd_3436663 := by
    simpa [prefixWord, tailWord_3436663, baseEnd_3436663] using wordTrace_append hprefix tailTrace_3436663
  have hstable : (prefixWord ++ tailWord_3436663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436663).length < 2 ^ (prefixWord ++ tailWord_3436663).sum := by decide
  have hdescent : baseEnd_3436663 < baseStart_3436663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436691 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 5]
def baseStart_3436691 : Nat := 118140960795 + 3436691 * 2 ^ 59
def prefixEnd_3436691 : Nat := 4983230072969 + 3 ^ 40 * 3436691 * 2
def baseEnd_3436691 : Nat := 392149854217981925412767

theorem tailTrace_3436691 : CollatzResearch.WordTrace tailWord_3436691 prefixEnd_3436691 392149854217981925412767 := by
  unfold tailWord_3436691
  simp only [CollatzResearch.WordTrace]
  refine ⟨125346418392462921939221927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83564278928308614626147951 125346418392462921939221927)
  ·
    refine ⟨188019627588694382908832891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125346418392462921939221927 188019627588694382908832891)
    ·
      refine ⟨282029441383041574363249337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188019627588694382908832891 282029441383041574363249337)
      ·
        refine ⟨211522081037281180772437003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282029441383041574363249337 211522081037281180772437003)
        ·
          refine ⟨317283121555921771158655505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211522081037281180772437003 317283121555921771158655505)
          ·
            refine ⟨237962341166941328368991629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317283121555921771158655505 237962341166941328368991629)
            ·
              refine ⟨89235877937602998138371861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237962341166941328368991629 89235877937602998138371861)
              ·
                refine ⟨4182931778325140537736181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89235877937602998138371861 4182931778325140537736181)
                ·
                  refine ⟨392149854217981925412767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4182931778325140537736181 392149854217981925412767)
                  ·
                    rfl

theorem cell22_3436691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 5].length) (baseStart_3436691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436691 prefixEnd_3436691 := by exact prefixLift 3436691
  have htrace : WordTrace (prefixWord ++ tailWord_3436691) baseStart_3436691 baseEnd_3436691 := by
    simpa [prefixWord, tailWord_3436691, baseEnd_3436691] using wordTrace_append hprefix tailTrace_3436691
  have hstable : (prefixWord ++ tailWord_3436691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436691).length < 2 ^ (prefixWord ++ tailWord_3436691).sum := by decide
  have hdescent : baseEnd_3436691 < baseStart_3436691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436751 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_3436751 : Nat := 118140960795 + 3436751 * 2 ^ 59
def prefixEnd_3436751 : Nat := 4983230072969 + 3 ^ 40 * 3436751 * 2
def baseEnd_3436751 : Nat := 1176470101880125619738117

theorem tailTrace_3436751 : CollatzResearch.WordTrace tailWord_3436751 prefixEnd_3436751 1176470101880125619738117 := by
  unfold tailWord_3436751
  simp only [CollatzResearch.WordTrace]
  refine ⟨125348606772245552186406107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83565737848163701457604071 125348606772245552186406107)
  ·
    refine ⟨188022910158368328279609161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125348606772245552186406107 188022910158368328279609161)
    ·
      refine ⟨141017182618776246209706871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188022910158368328279609161 141017182618776246209706871)
      ·
        refine ⟨211525773928164369314560307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141017182618776246209706871 211525773928164369314560307)
        ·
          refine ⟨317288660892246553971840461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211525773928164369314560307 317288660892246553971840461)
          ·
            refine ⟨118983247834592457739440173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317288660892246553971840461 118983247834592457739440173)
            ·
              refine ⟨44618717937972171652290065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118983247834592457739440173 44618717937972171652290065)
              ·
                refine ⟨33464038453479128739217549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44618717937972171652290065 33464038453479128739217549)
                ·
                  refine ⟨12549014420054673277206581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33464038453479128739217549 12549014420054673277206581)
                  ·
                    refine ⟨1176470101880125619738117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12549014420054673277206581 1176470101880125619738117)
                    ·
                      rfl

theorem cell22_3436751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_3436751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436751 prefixEnd_3436751 := by exact prefixLift 3436751
  have htrace : WordTrace (prefixWord ++ tailWord_3436751) baseStart_3436751 baseEnd_3436751 := by
    simpa [prefixWord, tailWord_3436751, baseEnd_3436751] using wordTrace_append hprefix tailTrace_3436751
  have hstable : (prefixWord ++ tailWord_3436751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436751).length < 2 ^ (prefixWord ++ tailWord_3436751).sum := by decide
  have hdescent : baseEnd_3436751 < baseStart_3436751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436768 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_3436768 : Nat := 118140960795 + 3436768 * 2 ^ 59
def prefixEnd_3436768 : Nat := 4983230072969 + 3 ^ 40 * 3436768 * 2
def baseEnd_3436768 : Nat := 1176475921327543242063065

theorem tailTrace_3436768 : CollatzResearch.WordTrace tailWord_3436768 prefixEnd_3436768 1176475921327543242063065 := by
  unfold tailWord_3436768
  simp only [CollatzResearch.WordTrace]
  refine ⟨62674613406591982044887479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83566151208789309393183305 62674613406591982044887479)
  ·
    refine ⟨94011920109887973067331219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62674613406591982044887479 94011920109887973067331219)
    ·
      refine ⟨141017880164831959600996829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94011920109887973067331219 141017880164831959600996829)
      ·
        refine ⟨52881705061811984850373811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141017880164831959600996829 52881705061811984850373811)
        ·
          refine ⟨79322557592717977275560717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52881705061811984850373811 79322557592717977275560717)
          ·
            refine ⟨29745959097269241478335269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79322557592717977275560717 29745959097269241478335269)
            ·
              refine ⟨5577367330737982777187863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29745959097269241478335269 5577367330737982777187863)
              ·
                refine ⟨8366050996106974165781795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577367330737982777187863 8366050996106974165781795)
                ·
                  refine ⟨12549076494160461248672693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8366050996106974165781795 12549076494160461248672693)
                  ·
                    refine ⟨1176475921327543242063065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12549076494160461248672693 1176475921327543242063065)
                    ·
                      rfl

theorem cell22_3436768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_3436768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436768 prefixEnd_3436768 := by exact prefixLift 3436768
  have htrace : WordTrace (prefixWord ++ tailWord_3436768) baseStart_3436768 baseEnd_3436768 := by
    simpa [prefixWord, tailWord_3436768, baseEnd_3436768] using wordTrace_append hprefix tailTrace_3436768
  have hstable : (prefixWord ++ tailWord_3436768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436768).length < 2 ^ (prefixWord ++ tailWord_3436768).sum := by decide
  have hdescent : baseEnd_3436768 < baseStart_3436768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436783 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 1, 6]
def baseStart_3436783 : Nat := 118140960795 + 3436783 * 2 ^ 59
def prefixEnd_3436783 : Nat := 4983230072969 + 3 ^ 40 * 3436783 * 2
def baseEnd_3436783 : Nat := 1176481056134088202938019

theorem tailTrace_3436783 : CollatzResearch.WordTrace tailWord_3436783 prefixEnd_3436783 1176481056134088202938019 := by
  unfold tailWord_3436783
  simp only [CollatzResearch.WordTrace]
  refine ⟨125349773908129621651571003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83566515938753081101047335 125349773908129621651571003)
  ·
    refine ⟨188024660862194432477356505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125349773908129621651571003 188024660862194432477356505)
    ·
      refine ⟨141018495646645824358017379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188024660862194432477356505 141018495646645824358017379)
      ·
        refine ⟨211527743469968736537026069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141018495646645824358017379 211527743469968736537026069)
        ·
          refine ⟨9915362975154784525173097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211527743469968736537026069 9915362975154784525173097)
          ·
            refine ⟨7436522231366088393879823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9915362975154784525173097 7436522231366088393879823)
            ·
              refine ⟨11154783347049132590819735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436522231366088393879823 11154783347049132590819735)
              ·
                refine ⟨16732175020573698886229603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11154783347049132590819735 16732175020573698886229603)
                ·
                  refine ⟨25098262530860548329344405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16732175020573698886229603 25098262530860548329344405)
                  ·
                    refine ⟨1176481056134088202938019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25098262530860548329344405 1176481056134088202938019)
                    ·
                      rfl

theorem cell22_3436783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_3436783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436783 prefixEnd_3436783 := by exact prefixLift 3436783
  have htrace : WordTrace (prefixWord ++ tailWord_3436783) baseStart_3436783 baseEnd_3436783 := by
    simpa [prefixWord, tailWord_3436783, baseEnd_3436783] using wordTrace_append hprefix tailTrace_3436783
  have hstable : (prefixWord ++ tailWord_3436783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436783).length < 2 ^ (prefixWord ++ tailWord_3436783).sum := by decide
  have hdescent : baseEnd_3436783 < baseStart_3436783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436798 : List Nat := [4, 2, 2, 1, 1, 1, 11]
def baseStart_3436798 : Nat := 118140960795 + 3436798 * 2 ^ 59
def prefixEnd_3436798 : Nat := 4983230072969 + 3 ^ 40 * 3436798 * 2
def baseEnd_3436798 : Nat := 43573562627430857918999

theorem tailTrace_3436798 : CollatzResearch.WordTrace tailWord_3436798 prefixEnd_3436798 43573562627430857918999 := by
  unfold tailWord_3436798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15668790125384409901670881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83566880668716852808911365 15668790125384409901670881)
  ·
    refine ⟨11751592594038307426253161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15668790125384409901670881 11751592594038307426253161)
    ·
      refine ⟨8813694445528730569689871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11751592594038307426253161 8813694445528730569689871)
      ·
        refine ⟨13220541668293095854534807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8813694445528730569689871 13220541668293095854534807)
        ·
          refine ⟨19830812502439643781802211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13220541668293095854534807 19830812502439643781802211)
          ·
            refine ⟨29746218753659465672703317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19830812502439643781802211 29746218753659465672703317)
            ·
              refine ⟨43573562627430857918999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29746218753659465672703317 43573562627430857918999)
              ·
                rfl

theorem cell22_3436798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 11].length) (baseStart_3436798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436798 prefixEnd_3436798 := by exact prefixLift 3436798
  have htrace : WordTrace (prefixWord ++ tailWord_3436798) baseStart_3436798 baseEnd_3436798 := by
    simpa [prefixWord, tailWord_3436798, baseEnd_3436798] using wordTrace_append hprefix tailTrace_3436798
  have hstable : (prefixWord ++ tailWord_3436798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436798).length < 2 ^ (prefixWord ++ tailWord_3436798).sum := by decide
  have hdescent : baseEnd_3436798 < baseStart_3436798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436802 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3436802 : Nat := 118140960795 + 3436802 * 2 ^ 59
def prefixEnd_3436802 : Nat := 4983230072969 + 3 ^ 40 * 3436802 * 2
def baseEnd_3436802 : Nat := 1176487560222378486712961

theorem tailTrace_3436802 : CollatzResearch.WordTrace tailWord_3436802 prefixEnd_3436802 1176487560222378486712961 := by
  unfold tailWord_3436802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31337616723765196974128165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83566977930040525264341773 31337616723765196974128165)
  ·
    refine ⟨5875803135705974432649031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31337616723765196974128165 5875803135705974432649031)
    ·
      refine ⟨8813704703558961648973547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5875803135705974432649031 8813704703558961648973547)
      ·
        refine ⟨13220557055338442473460321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8813704703558961648973547 13220557055338442473460321)
        ·
          refine ⟨9915417791503831855095241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13220557055338442473460321 9915417791503831855095241)
          ·
            refine ⟨7436563343627873891321431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9915417791503831855095241 7436563343627873891321431)
            ·
              refine ⟨11154845015441810836982147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436563343627873891321431 11154845015441810836982147)
              ·
                refine ⟨16732267523162716255473221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11154845015441810836982147 16732267523162716255473221)
                ·
                  refine ⟨3137300160593009297901229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16732267523162716255473221 3137300160593009297901229)
                  ·
                    refine ⟨1176487560222378486712961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137300160593009297901229 1176487560222378486712961)
                    ·
                      rfl

theorem cell22_3436802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3436802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436802 prefixEnd_3436802 := by exact prefixLift 3436802
  have htrace : WordTrace (prefixWord ++ tailWord_3436802) baseStart_3436802 baseEnd_3436802 := by
    simpa [prefixWord, tailWord_3436802, baseEnd_3436802] using wordTrace_append hprefix tailTrace_3436802
  have hstable : (prefixWord ++ tailWord_3436802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436802).length < 2 ^ (prefixWord ++ tailWord_3436802).sum := by decide
  have hdescent : baseEnd_3436802 < baseStart_3436802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436847 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 1, 3]
def baseStart_3436847 : Nat := 118140960795 + 3436847 * 2 ^ 59
def prefixEnd_3436847 : Nat := 4983230072969 + 3 ^ 40 * 3436847 * 2
def baseEnd_3436847 : Nat := 1176502964642013369337823

theorem tailTrace_3436847 : CollatzResearch.WordTrace tailWord_3436847 prefixEnd_3436847 1176502964642013369337823 := by
  unfold tailWord_3436847
  simp only [CollatzResearch.WordTrace]
  refine ⟨125352108179897760581900795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83568072119931840387933863 125352108179897760581900795)
  ·
    refine ⟨188028162269846640872851193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125352108179897760581900795 188028162269846640872851193)
    ·
      refine ⟨141021121702384980654638395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188028162269846640872851193 141021121702384980654638395)
      ·
        refine ⟨211531682553577470981957593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141021121702384980654638395 211531682553577470981957593)
        ·
          refine ⟨158648761915183103236468195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211531682553577470981957593 158648761915183103236468195)
          ·
            refine ⟨237973142872774654854702293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158648761915183103236468195 237973142872774654854702293)
            ·
              refine ⟨5577495536080655973157085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 237973142872774654854702293 5577495536080655973157085)
              ·
                refine ⟨2091560826030245989933907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5577495536080655973157085 2091560826030245989933907)
                ·
                  refine ⟨3137341239045368984900861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091560826030245989933907 3137341239045368984900861)
                  ·
                    refine ⟨1176502964642013369337823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137341239045368984900861 1176502964642013369337823)
                    ·
                      rfl

theorem cell22_3436847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_3436847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436847 prefixEnd_3436847 := by exact prefixLift 3436847
  have htrace : WordTrace (prefixWord ++ tailWord_3436847) baseStart_3436847 baseEnd_3436847 := by
    simpa [prefixWord, tailWord_3436847, baseEnd_3436847] using wordTrace_append hprefix tailTrace_3436847
  have hstable : (prefixWord ++ tailWord_3436847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436847).length < 2 ^ (prefixWord ++ tailWord_3436847).sum := by decide
  have hdescent : baseEnd_3436847 < baseStart_3436847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436873 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_3436873 : Nat := 118140960795 + 3436873 * 2 ^ 59
def prefixEnd_3436873 : Nat := 4983230072969 + 3 ^ 40 * 3436873 * 2
def baseEnd_3436873 : Nat := 1176511864973357968187743

theorem tailTrace_3436873 : CollatzResearch.WordTrace tailWord_3436873 prefixEnd_3436873 1176511864973357968187743 := by
  unfold tailWord_3436873
  simp only [CollatzResearch.WordTrace]
  refine ⟨125353056477803567022347273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83568704318535711348231515 125353056477803567022347273)
  ·
    refine ⟨94014792358352675266760455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125353056477803567022347273 94014792358352675266760455)
    ·
      refine ⟨141022188537529012900140683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94014792358352675266760455 141022188537529012900140683)
      ·
        refine ⟨211533282806293519350211025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141022188537529012900140683 211533282806293519350211025)
        ·
          refine ⟨158649962104720139512658269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211533282806293519350211025 158649962104720139512658269)
          ·
            refine ⟨59493735789270052317246851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158649962104720139512658269 59493735789270052317246851)
            ·
              refine ⟨89240603683905078475870277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59493735789270052317246851 89240603683905078475870277)
              ·
                refine ⟨16732613190732202214225677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89240603683905078475870277 16732613190732202214225677)
                ·
                  refine ⟨6274729946524575830334629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16732613190732202214225677 6274729946524575830334629)
                  ·
                    refine ⟨1176511864973357968187743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6274729946524575830334629 1176511864973357968187743)
                    ·
                      rfl

theorem cell22_3436873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_3436873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436873 prefixEnd_3436873 := by exact prefixLift 3436873
  have htrace : WordTrace (prefixWord ++ tailWord_3436873) baseStart_3436873 baseEnd_3436873 := by
    simpa [prefixWord, tailWord_3436873, baseEnd_3436873] using wordTrace_append hprefix tailTrace_3436873
  have hstable : (prefixWord ++ tailWord_3436873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436873).length < 2 ^ (prefixWord ++ tailWord_3436873).sum := by decide
  have hdescent : baseEnd_3436873 < baseStart_3436873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436905 : List Nat := [1, 2, 1, 1, 1, 3, 4, 5, 4]
def baseStart_3436905 : Nat := 118140960795 + 3436905 * 2 ^ 59
def prefixEnd_3436905 : Nat := 4983230072969 + 3 ^ 40 * 3436905 * 2
def baseEnd_3436905 : Nat := 392174273075773517129215

theorem tailTrace_3436905 : CollatzResearch.WordTrace tailWord_3436905 prefixEnd_3436905 392174273075773517129215 := by
  unfold tailWord_3436905
  simp only [CollatzResearch.WordTrace]
  refine ⟨125354223613687636487512169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83569482409125090991674779 125354223613687636487512169)
  ·
    refine ⟨94015667710265727365634127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125354223613687636487512169 94015667710265727365634127)
    ·
      refine ⟨141023501565398591048451191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94015667710265727365634127 141023501565398591048451191)
      ·
        refine ⟨211535252348097886572676787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141023501565398591048451191 211535252348097886572676787)
        ·
          refine ⟨317302878522146829859015181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211535252348097886572676787 317302878522146829859015181)
          ·
            refine ⟨118988579445805061197130693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317302878522146829859015181 118988579445805061197130693)
            ·
              refine ⟨22310358646088448974462005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118988579445805061197130693 22310358646088448974462005)
              ·
                refine ⟨2091596123070792091355813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22310358646088448974462005 2091596123070792091355813)
                ·
                  refine ⟨392174273075773517129215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091596123070792091355813 392174273075773517129215)
                  ·
                    rfl

theorem cell22_3436905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_3436905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436905 prefixEnd_3436905 := by exact prefixLift 3436905
  have htrace : WordTrace (prefixWord ++ tailWord_3436905) baseStart_3436905 baseEnd_3436905 := by
    simpa [prefixWord, tailWord_3436905, baseEnd_3436905] using wordTrace_append hprefix tailTrace_3436905
  have hstable : (prefixWord ++ tailWord_3436905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436905).length < 2 ^ (prefixWord ++ tailWord_3436905).sum := by decide
  have hdescent : baseEnd_3436905 < baseStart_3436905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436937 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_3436937 : Nat := 118140960795 + 3436937 * 2 ^ 59
def prefixEnd_3436937 : Nat := 4983230072969 + 3 ^ 40 * 3436937 * 2
def baseEnd_3436937 : Nat := 1176533773481283134587547

theorem tailTrace_3436937 : CollatzResearch.WordTrace tailWord_3436937 prefixEnd_3436937 1176533773481283134587547 := by
  unfold tailWord_3436937
  simp only [CollatzResearch.WordTrace]
  refine ⟨125355390749571705952677065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83570260499714470635118043 125355390749571705952677065)
  ·
    refine ⟨94016543062178779464507799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125355390749571705952677065 94016543062178779464507799)
    ·
      refine ⟨141024814593268169196761699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94016543062178779464507799 141024814593268169196761699)
      ·
        refine ⟨211537221889902253795142549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141024814593268169196761699 211537221889902253795142549)
        ·
          refine ⟨9915807276089168146647307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 211537221889902253795142549 9915807276089168146647307)
          ·
            refine ⟨14873710914133752219970961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915807276089168146647307 14873710914133752219970961)
            ·
              refine ⟨11155283185600314164978221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14873710914133752219970961 11155283185600314164978221)
              ·
                refine ⟨4183231194600117811866833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11155283185600314164978221 4183231194600117811866833)
                ·
                  refine ⟨3137423395950088358900125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4183231194600117811866833 3137423395950088358900125)
                  ·
                    refine ⟨1176533773481283134587547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137423395950088358900125 1176533773481283134587547)
                    ·
                      rfl

theorem cell22_3436937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_3436937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436937 prefixEnd_3436937 := by exact prefixLift 3436937
  have htrace : WordTrace (prefixWord ++ tailWord_3436937) baseStart_3436937 baseEnd_3436937 := by
    simpa [prefixWord, tailWord_3436937, baseEnd_3436937] using wordTrace_append hprefix tailTrace_3436937
  have hstable : (prefixWord ++ tailWord_3436937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436937).length < 2 ^ (prefixWord ++ tailWord_3436937).sum := by decide
  have hdescent : baseEnd_3436937 < baseStart_3436937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436952 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_3436952 : Nat := 118140960795 + 3436952 * 2 ^ 59
def prefixEnd_3436952 : Nat := 4983230072969 + 3 ^ 40 * 3436952 * 2
def baseEnd_3436952 : Nat := 1176538908287828095462501

theorem tailTrace_3436952 : CollatzResearch.WordTrace tailWord_3436952 prefixEnd_3436952 1176538908287828095462501 := by
  unfold tailWord_3436952
  simp only [CollatzResearch.WordTrace]
  refine ⟨62677968922258681757236555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83570625229678242342982073 62677968922258681757236555)
  ·
    refine ⟨94016953383388022635854833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62677968922258681757236555 94016953383388022635854833)
    ·
      refine ⟨70512715037541016976891125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94016953383388022635854833 70512715037541016976891125)
      ·
        refine ⟨6610567034769470341583543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70512715037541016976891125 6610567034769470341583543)
        ·
          refine ⟨9915850552154205512375315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6610567034769470341583543 9915850552154205512375315)
          ·
            refine ⟨14873775828231308268562973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9915850552154205512375315 14873775828231308268562973)
            ·
              refine ⟨5577665935586740600711115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14873775828231308268562973 5577665935586740600711115)
              ·
                refine ⟨8366498903380110901066673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5577665935586740600711115 8366498903380110901066673)
                ·
                  refine ⟨6274874177535083175800005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8366498903380110901066673 6274874177535083175800005)
                  ·
                    refine ⟨1176538908287828095462501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6274874177535083175800005 1176538908287828095462501)
                    ·
                      rfl

theorem cell22_3436952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_3436952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436952 prefixEnd_3436952 := by exact prefixLift 3436952
  have htrace : WordTrace (prefixWord ++ tailWord_3436952) baseStart_3436952 baseEnd_3436952 := by
    simpa [prefixWord, tailWord_3436952, baseEnd_3436952] using wordTrace_append hprefix tailTrace_3436952
  have hstable : (prefixWord ++ tailWord_3436952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436952).length < 2 ^ (prefixWord ++ tailWord_3436952).sum := by decide
  have hdescent : baseEnd_3436952 < baseStart_3436952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3436965 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_3436965 : Nat := 118140960795 + 3436965 * 2 ^ 59
def prefixEnd_3436965 : Nat := 4983230072969 + 3 ^ 40 * 3436965 * 2
def baseEnd_3436965 : Nat := 1176543358453500394887461

theorem tailTrace_3436965 : CollatzResearch.WordTrace tailWord_3436965 prefixEnd_3436965 1176543358453500394887461 := by
  unfold tailWord_3436965
  simp only [CollatzResearch.WordTrace]
  refine ⟨125356411993470266734696349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83570941328980177823130899 125356411993470266734696349)
  ·
    refine ⟨47008654497551350025511131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125356411993470266734696349 47008654497551350025511131)
    ·
      refine ⟨70512981746327025038266697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47008654497551350025511131 70512981746327025038266697)
      ·
        refine ⟨52884736309745268778700023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70512981746327025038266697 52884736309745268778700023)
        ·
          refine ⟨79327104464617903168050035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52884736309745268778700023 79327104464617903168050035)
          ·
            refine ⟨118990656696926854752075053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79327104464617903168050035 118990656696926854752075053)
            ·
              refine ⟨44621496261347570532028145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118990656696926854752075053 44621496261347570532028145)
              ·
                refine ⟨33466122196010677899021109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44621496261347570532028145 33466122196010677899021109)
                ·
                  refine ⟨3137448955876001053033229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33466122196010677899021109 3137448955876001053033229)
                  ·
                    refine ⟨1176543358453500394887461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137448955876001053033229 1176543358453500394887461)
                    ·
                      rfl

theorem cell22_3436965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_3436965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3436965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3436965 prefixEnd_3436965 := by exact prefixLift 3436965
  have htrace : WordTrace (prefixWord ++ tailWord_3436965) baseStart_3436965 baseEnd_3436965 := by
    simpa [prefixWord, tailWord_3436965, baseEnd_3436965] using wordTrace_append hprefix tailTrace_3436965
  have hstable : (prefixWord ++ tailWord_3436965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3436965).length < 2 ^ (prefixWord ++ tailWord_3436965).sum := by decide
  have hdescent : baseEnd_3436965 < baseStart_3436965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3436965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437055 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 1, 5]
def baseStart_3437055 : Nat := 118140960795 + 3437055 * 2 ^ 59
def prefixEnd_3437055 : Nat := 4983230072969 + 3 ^ 40 * 3437055 * 2
def baseEnd_3437055 : Nat := 1176574167292770160137185

theorem tailTrace_3437055 : CollatzResearch.WordTrace tailWord_3437055 prefixEnd_3437055 1176574167292770160137185 := by
  unfold tailWord_3437055
  simp only [CollatzResearch.WordTrace]
  refine ⟨125359694563144212105472619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83573129708762808070315079 125359694563144212105472619)
  ·
    refine ⟨188039541844716318158208929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125359694563144212105472619 188039541844716318158208929)
    ·
      refine ⟨141029656383537238618656697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188039541844716318158208929 141029656383537238618656697)
      ·
        refine ⟨105772242287652928963992523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141029656383537238618656697 105772242287652928963992523)
        ·
          refine ⟨158658363431479393445988785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105772242287652928963992523 158658363431479393445988785)
          ·
            refine ⟨118993772573609545084491589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158658363431479393445988785 118993772573609545084491589)
            ·
              refine ⟨22311332357551789703342173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118993772573609545084491589 22311332357551789703342173)
              ·
                refine ⟨8366749634081921138753315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22311332357551789703342173 8366749634081921138753315)
                ·
                  refine ⟨12550124451122881708129973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8366749634081921138753315 12550124451122881708129973)
                  ·
                    refine ⟨1176574167292770160137185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12550124451122881708129973 1176574167292770160137185)
                    ·
                      rfl

theorem cell22_3437055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_3437055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437055 prefixEnd_3437055 := by exact prefixLift 3437055
  have htrace : WordTrace (prefixWord ++ tailWord_3437055) baseStart_3437055 baseEnd_3437055 := by
    simpa [prefixWord, tailWord_3437055, baseEnd_3437055] using wordTrace_append hprefix tailTrace_3437055
  have hstable : (prefixWord ++ tailWord_3437055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437055).length < 2 ^ (prefixWord ++ tailWord_3437055).sum := by decide
  have hdescent : baseEnd_3437055 < baseStart_3437055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437085 : List Nat := [1, 4, 2, 2, 1, 12]
def baseStart_3437085 : Nat := 118140960795 + 3437085 * 2 ^ 59
def prefixEnd_3437085 : Nat := 4983230072969 + 3 ^ 40 * 3437085 * 2
def baseEnd_3437085 : Nat := 14525733788961235578853

theorem tailTrace_3437085 : CollatzResearch.WordTrace tailWord_3437085 prefixEnd_3437085 14525733788961235578853 := by
  unfold tailWord_3437085
  simp only [CollatzResearch.WordTrace]
  refine ⟨125360788753035527229064709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83573859168690351486043139 125360788753035527229064709)
  ·
    refine ⟨23505147891194161355449633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125360788753035527229064709 23505147891194161355449633)
    ·
      refine ⟨17628860918395621016587225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23505147891194161355449633 17628860918395621016587225)
      ·
        refine ⟨13221645688796715762440419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17628860918395621016587225 13221645688796715762440419)
        ·
          refine ⟨19832468533195073643660629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13221645688796715762440419 19832468533195073643660629)
          ·
            refine ⟨14525733788961235578853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19832468533195073643660629 14525733788961235578853)
            ·
              rfl

theorem cell22_3437085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 12].length) (baseStart_3437085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437085 prefixEnd_3437085 := by exact prefixLift 3437085
  have htrace : WordTrace (prefixWord ++ tailWord_3437085) baseStart_3437085 baseEnd_3437085 := by
    simpa [prefixWord, tailWord_3437085, baseEnd_3437085] using wordTrace_append hprefix tailTrace_3437085
  have hstable : (prefixWord ++ tailWord_3437085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437085).length < 2 ^ (prefixWord ++ tailWord_3437085).sum := by decide
  have hdescent : baseEnd_3437085 < baseStart_3437085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437089 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_3437089 : Nat := 118140960795 + 3437089 * 2 ^ 59
def prefixEnd_3437089 : Nat := 4983230072969 + 3 ^ 40 * 3437089 * 2
def baseEnd_3437089 : Nat := 1176585806187605404787081

theorem tailTrace_3437089 : CollatzResearch.WordTrace tailWord_3437089 prefixEnd_3437089 1176585806187605404787081 := by
  unfold tailWord_3437089
  simp only [CollatzResearch.WordTrace]
  refine ⟨125360934645021035912210321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83573956430014023941473547 125360934645021035912210321)
  ·
    refine ⟨94020700983765776934157741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125360934645021035912210321 94020700983765776934157741)
    ·
      refine ⟨35257762868912166350309153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94020700983765776934157741 35257762868912166350309153)
      ·
        refine ⟨26443322151684124762731865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35257762868912166350309153 26443322151684124762731865)
        ·
          refine ⟨19832491613763093572048899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26443322151684124762731865 19832491613763093572048899)
          ·
            refine ⟨29748737420644640358073349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19832491613763093572048899 29748737420644640358073349)
            ·
              refine ⟨5577888266370870067138753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29748737420644640358073349 5577888266370870067138753)
              ·
                refine ⟨4183416199778152550354065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5577888266370870067138753 4183416199778152550354065)
                ·
                  refine ⟨3137562149833614412765549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4183416199778152550354065 3137562149833614412765549)
                  ·
                    refine ⟨1176585806187605404787081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137562149833614412765549 1176585806187605404787081)
                    ·
                      rfl

theorem cell22_3437089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_3437089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437089 prefixEnd_3437089 := by exact prefixLift 3437089
  have htrace : WordTrace (prefixWord ++ tailWord_3437089) baseStart_3437089 baseEnd_3437089 := by
    simpa [prefixWord, tailWord_3437089, baseEnd_3437089] using wordTrace_append hprefix tailTrace_3437089
  have hstable : (prefixWord ++ tailWord_3437089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437089).length < 2 ^ (prefixWord ++ tailWord_3437089).sum := by decide
  have hdescent : baseEnd_3437089 < baseStart_3437089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437091 : List Nat := [1, 1, 1, 4, 4, 3, 2, 2, 4]
def baseStart_3437091 : Nat := 118140960795 + 3437091 * 2 ^ 59
def prefixEnd_3437091 : Nat := 4983230072969 + 3 ^ 40 * 3437091 * 2
def baseEnd_3437091 : Nat := 392195496942826022079025

theorem tailTrace_3437091 : CollatzResearch.WordTrace tailWord_3437091 prefixEnd_3437091 392195496942826022079025 := by
  unfold tailWord_3437091
  simp only [CollatzResearch.WordTrace]
  refine ⟨125361007591013790253783127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83574005060675860169188751 125361007591013790253783127)
  ·
    refine ⟨188041511386520685380674691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125361007591013790253783127 188041511386520685380674691)
    ·
      refine ⟨282062267079781028071012037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188041511386520685380674691 282062267079781028071012037)
      ·
        refine ⟨52886675077458942763314757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282062267079781028071012037 52886675077458942763314757)
        ·
          refine ⟨9916251577023551768121517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52886675077458942763314757 9916251577023551768121517)
          ·
            refine ⟨3718594341383831913045569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9916251577023551768121517 3718594341383831913045569)
            ·
              refine ⟨2788945756037873934784177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718594341383831913045569 2788945756037873934784177)
              ·
                refine ⟨2091709317028405451088133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2788945756037873934784177 2091709317028405451088133)
                ·
                  refine ⟨392195496942826022079025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091709317028405451088133 392195496942826022079025)
                  ·
                    rfl

theorem cell22_3437091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2, 4].length) (baseStart_3437091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437091 prefixEnd_3437091 := by exact prefixLift 3437091
  have htrace : WordTrace (prefixWord ++ tailWord_3437091) baseStart_3437091 baseEnd_3437091 := by
    simpa [prefixWord, tailWord_3437091, baseEnd_3437091] using wordTrace_append hprefix tailTrace_3437091
  have hstable : (prefixWord ++ tailWord_3437091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437091).length < 2 ^ (prefixWord ++ tailWord_3437091).sum := by decide
  have hdescent : baseEnd_3437091 < baseStart_3437091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437162 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3437162 : Nat := 118140960795 + 3437162 * 2 ^ 59
def prefixEnd_3437162 : Nat := 4983230072969 + 3 ^ 40 * 3437162 * 2
def baseEnd_3437162 : Nat := 1176610795579457547711857

theorem tailTrace_3437162 : CollatzResearch.WordTrace tailWord_3437162 prefixEnd_3437162 1176610795579457547711857 := by
  unfold tailWord_3437162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31340899293439142344904435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83575731449171046253078493 31340899293439142344904435)
  ·
    refine ⟨47011348940158713517356653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31340899293439142344904435 47011348940158713517356653)
    ·
      refine ⟨17629255852559517569008745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47011348940158713517356653 17629255852559517569008745)
      ·
        refine ⟨13221941889419638176756559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17629255852559517569008745 13221941889419638176756559)
        ·
          refine ⟨19832912834129457265134839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13221941889419638176756559 19832912834129457265134839)
          ·
            refine ⟨29749369251194185897702259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19832912834129457265134839 29749369251194185897702259)
            ·
              refine ⟨44624053876791278846553389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29749369251194185897702259 44624053876791278846553389)
              ·
                refine ⟨16734020203796729567457521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44624053876791278846553389 16734020203796729567457521)
                ·
                  refine ⟨12550515152847547175593141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16734020203796729567457521 12550515152847547175593141)
                  ·
                    refine ⟨1176610795579457547711857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12550515152847547175593141 1176610795579457547711857)
                    ·
                      rfl

theorem cell22_3437162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3437162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437162 prefixEnd_3437162 := by exact prefixLift 3437162
  have htrace : WordTrace (prefixWord ++ tailWord_3437162) baseStart_3437162 baseEnd_3437162 := by
    simpa [prefixWord, tailWord_3437162, baseEnd_3437162] using wordTrace_append hprefix tailTrace_3437162
  have hstable : (prefixWord ++ tailWord_3437162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437162).length < 2 ^ (prefixWord ++ tailWord_3437162).sum := by decide
  have hdescent : baseEnd_3437162 < baseStart_3437162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437297 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3437297 : Nat := 118140960795 + 3437297 * 2 ^ 59
def prefixEnd_3437297 : Nat := 4983230072969 + 3 ^ 40 * 3437297 * 2
def baseEnd_3437297 : Nat := 1176657008838362195586443

theorem tailTrace_3437297 : CollatzResearch.WordTrace tailWord_3437297 prefixEnd_3437297 1176657008838362195586443 := by
  unfold tailWord_3437297
  simp only [CollatzResearch.WordTrace]
  refine ⟨125368521028267487435782145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83579014018844991623854763 125368521028267487435782145)
  ·
    refine ⟨94026390771200615576836609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125368521028267487435782145 94026390771200615576836609)
    ·
      refine ⟨70519793078400461682627457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94026390771200615576836609 70519793078400461682627457)
      ·
        refine ⟨52889844808800346261970593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70519793078400461682627457 52889844808800346261970593)
        ·
          refine ⟨39667383606600259696477945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52889844808800346261970593 39667383606600259696477945)
          ·
            refine ⟨29750537704950194772358459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39667383606600259696477945 29750537704950194772358459)
            ·
              refine ⟨44625806557425292158537689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29750537704950194772358459 44625806557425292158537689)
              ·
                refine ⟨33469354918068969118903267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44625806557425292158537689 33469354918068969118903267)
                ·
                  refine ⟨50204032377103453678354901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33469354918068969118903267 50204032377103453678354901)
                  ·
                    refine ⟨1176657008838362195586443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50204032377103453678354901 1176657008838362195586443)
                    ·
                      rfl

theorem cell22_3437297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3437297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437297 prefixEnd_3437297 := by exact prefixLift 3437297
  have htrace : WordTrace (prefixWord ++ tailWord_3437297) baseStart_3437297 baseEnd_3437297 := by
    simpa [prefixWord, tailWord_3437297, baseEnd_3437297] using wordTrace_append hprefix tailTrace_3437297
  have hstable : (prefixWord ++ tailWord_3437297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437297).length < 2 ^ (prefixWord ++ tailWord_3437297).sum := by decide
  have hdescent : baseEnd_3437297 < baseStart_3437297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437344 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_3437344 : Nat := 118140960795 + 3437344 * 2 ^ 59
def prefixEnd_3437344 : Nat := 4983230072969 + 3 ^ 40 * 3437344 * 2
def baseEnd_3437344 : Nat := 392224365966289913220433

theorem tailTrace_3437344 : CollatzResearch.WordTrace tailWord_3437344 prefixEnd_3437344 392224365966289913220433 := by
  unfold tailWord_3437344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62685117629548607231371543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83580156839398142975162057 62685117629548607231371543)
  ·
    refine ⟨94027676444322910847057315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62685117629548607231371543 94027676444322910847057315)
    ·
      refine ⟨141041514666484366270585973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94027676444322910847057315 141041514666484366270585973)
      ·
        refine ⟨13222641999982909337867435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141041514666484366270585973 13222641999982909337867435)
        ·
          refine ⟨19833962999974364006801153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13222641999982909337867435 19833962999974364006801153)
          ·
            refine ⟨14875472249980773005100865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19833962999974364006801153 14875472249980773005100865)
            ·
              refine ⟨11156604187485579753825649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14875472249980773005100865 11156604187485579753825649)
              ·
                refine ⟨8367453140614184815369237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11156604187485579753825649 8367453140614184815369237)
                ·
                  refine ⟨392224365966289913220433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8367453140614184815369237 392224365966289913220433)
                  ·
                    rfl

theorem cell22_3437344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_3437344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437344 prefixEnd_3437344 := by exact prefixLift 3437344
  have htrace : WordTrace (prefixWord ++ tailWord_3437344) baseStart_3437344 baseEnd_3437344 := by
    simpa [prefixWord, tailWord_3437344, baseEnd_3437344] using wordTrace_append hprefix tailTrace_3437344
  have hstable : (prefixWord ++ tailWord_3437344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437344).length < 2 ^ (prefixWord ++ tailWord_3437344).sum := by decide
  have hdescent : baseEnd_3437344 < baseStart_3437344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437346 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3437346 : Nat := 118140960795 + 3437346 * 2 ^ 59
def prefixEnd_3437346 : Nat := 4983230072969 + 3 ^ 40 * 3437346 * 2
def baseEnd_3437346 : Nat := 1176673782539742401111293

theorem tailTrace_3437346 : CollatzResearch.WordTrace tailWord_3437346 prefixEnd_3437346 1176673782539742401111293 := by
  unfold tailWord_3437346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31342577051272492201078973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83580205470059979202877261 31342577051272492201078973)
  ·
    refine ⟨11753466394227184575404615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31342577051272492201078973 11753466394227184575404615)
    ·
      refine ⟨17630199591340776863106923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11753466394227184575404615 17630199591340776863106923)
      ·
        refine ⟨26445299387011165294660385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17630199591340776863106923 26445299387011165294660385)
        ·
          refine ⟨19833974540258373970995289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26445299387011165294660385 19833974540258373970995289)
          ·
            refine ⟨14875480905193780478246467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19833974540258373970995289 14875480905193780478246467)
            ·
              refine ⟨22313221357790670717369701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14875480905193780478246467 22313221357790670717369701)
              ·
                refine ⟨4183729004585750759506819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22313221357790670717369701 4183729004585750759506819)
                ·
                  refine ⟨6275593506878626139260229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4183729004585750759506819 6275593506878626139260229)
                  ·
                    refine ⟨1176673782539742401111293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6275593506878626139260229 1176673782539742401111293)
                    ·
                      rfl

theorem cell22_3437346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3437346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437346 prefixEnd_3437346 := by exact prefixLift 3437346
  have htrace : WordTrace (prefixWord ++ tailWord_3437346) baseStart_3437346 baseEnd_3437346 := by
    simpa [prefixWord, tailWord_3437346, baseEnd_3437346] using wordTrace_append hprefix tailTrace_3437346
  have hstable : (prefixWord ++ tailWord_3437346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437346).length < 2 ^ (prefixWord ++ tailWord_3437346).sum := by decide
  have hdescent : baseEnd_3437346 < baseStart_3437346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437354 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3437354 : Nat := 118140960795 + 3437354 * 2 ^ 59
def prefixEnd_3437354 : Nat := 4983230072969 + 3 ^ 40 * 3437354 * 2
def baseEnd_3437354 : Nat := 1176676521103233046911269

theorem tailTrace_3437354 : CollatzResearch.WordTrace tailWord_3437354 prefixEnd_3437354 1176676521103233046911269 := by
  unfold tailWord_3437354
  simp only [CollatzResearch.WordTrace]
  refine ⟨31342649997265246542651779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83580399992707324113738077 31342649997265246542651779)
  ·
    refine ⟨47013974995897869813977669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31342649997265246542651779 47013974995897869813977669)
    ·
      refine ⟨8815120311730850590120813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47013974995897869813977669 8815120311730850590120813)
      ·
        refine ⟨3305670116899068971295305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8815120311730850590120813 3305670116899068971295305)
        ·
          refine ⟨2479252587674301728471479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3305670116899068971295305 2479252587674301728471479)
          ·
            refine ⟨3718878881511452592707219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479252587674301728471479 3718878881511452592707219)
            ·
              refine ⟨5578318322267178889060829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718878881511452592707219 5578318322267178889060829)
              ·
                refine ⟨2091869370850192083397811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5578318322267178889060829 2091869370850192083397811)
                ·
                  refine ⟨3137804056275288125096717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091869370850192083397811 3137804056275288125096717)
                  ·
                    refine ⟨1176676521103233046911269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137804056275288125096717 1176676521103233046911269)
                    ·
                      rfl

theorem cell22_3437354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3437354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437354 prefixEnd_3437354 := by exact prefixLift 3437354
  have htrace : WordTrace (prefixWord ++ tailWord_3437354) baseStart_3437354 baseEnd_3437354 := by
    simpa [prefixWord, tailWord_3437354, baseEnd_3437354] using wordTrace_append hprefix tailTrace_3437354
  have hstable : (prefixWord ++ tailWord_3437354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437354).length < 2 ^ (prefixWord ++ tailWord_3437354).sum := by decide
  have hdescent : baseEnd_3437354 < baseStart_3437354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437393 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_3437393 : Nat := 118140960795 + 3437393 * 2 ^ 59
def prefixEnd_3437393 : Nat := 4983230072969 + 3 ^ 40 * 3437393 * 2
def baseEnd_3437393 : Nat := 1176689871600249945186149

theorem tailTrace_3437393 : CollatzResearch.WordTrace tailWord_3437393 prefixEnd_3437393 1176689871600249945186149 := by
  unfold tailWord_3437393
  simp only [CollatzResearch.WordTrace]
  refine ⟨125372022435919695831276833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83581348290613130554184555 125372022435919695831276833)
  ·
    refine ⟨94029016826939771873457625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125372022435919695831276833 94029016826939771873457625)
    ·
      refine ⟨70521762620204828905093219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94029016826939771873457625 70521762620204828905093219)
      ·
        refine ⟨105782643930307243357639829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70521762620204828905093219 105782643930307243357639829)
        ·
          refine ⟨4958561434233152032389367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105782643930307243357639829 4958561434233152032389367)
          ·
            refine ⟨7437842151349728048584051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958561434233152032389367 7437842151349728048584051)
            ·
              refine ⟨11156763227024592072876077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437842151349728048584051 11156763227024592072876077)
              ·
                refine ⟨4183786210134222027328529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11156763227024592072876077 4183786210134222027328529)
                ·
                  refine ⟨3137839657600666520496397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4183786210134222027328529 3137839657600666520496397)
                  ·
                    refine ⟨1176689871600249945186149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3137839657600666520496397 1176689871600249945186149)
                    ·
                      rfl

theorem cell22_3437393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_3437393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437393 prefixEnd_3437393 := by exact prefixLift 3437393
  have htrace : WordTrace (prefixWord ++ tailWord_3437393) baseStart_3437393 baseEnd_3437393 := by
    simpa [prefixWord, tailWord_3437393, baseEnd_3437393] using wordTrace_append hprefix tailTrace_3437393
  have hstable : (prefixWord ++ tailWord_3437393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437393).length < 2 ^ (prefixWord ++ tailWord_3437393).sum := by decide
  have hdescent : baseEnd_3437393 < baseStart_3437393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437449 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_3437449 : Nat := 118140960795 + 3437449 * 2 ^ 59
def prefixEnd_3437449 : Nat := 4983230072969 + 3 ^ 40 * 3437449 * 2
def baseEnd_3437449 : Nat := 1176709041544684465785977

theorem tailTrace_3437449 : CollatzResearch.WordTrace tailWord_3437449 prefixEnd_3437449 1176709041544684465785977 := by
  unfold tailWord_3437449
  simp only [CollatzResearch.WordTrace]
  refine ⟨125374064923716817395315401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83582709949144544930210267 125374064923716817395315401)
  ·
    refine ⟨94030548692787613046486551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125374064923716817395315401 94030548692787613046486551)
    ·
      refine ⟨141045823039181419569729827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94030548692787613046486551 141045823039181419569729827)
      ·
        refine ⟨211568734558772129354594741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141045823039181419569729827 211568734558772129354594741)
        ·
          refine ⟨19834568864884887126993257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211568734558772129354594741 19834568864884887126993257)
          ·
            refine ⟨14875926648663665345244943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19834568864884887126993257 14875926648663665345244943)
            ·
              refine ⟨22313889972995498017867415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14875926648663665345244943 22313889972995498017867415)
              ·
                refine ⟨33470834959493247026801123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22313889972995498017867415 33470834959493247026801123)
                ·
                  refine ⟨50206252439239870540201685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33470834959493247026801123 50206252439239870540201685)
                  ·
                    refine ⟨1176709041544684465785977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50206252439239870540201685 1176709041544684465785977)
                    ·
                      rfl

theorem cell22_3437449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_3437449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437449 prefixEnd_3437449 := by exact prefixLift 3437449
  have htrace : WordTrace (prefixWord ++ tailWord_3437449) baseStart_3437449 baseEnd_3437449 := by
    simpa [prefixWord, tailWord_3437449, baseEnd_3437449] using wordTrace_append hprefix tailTrace_3437449
  have hstable : (prefixWord ++ tailWord_3437449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437449).length < 2 ^ (prefixWord ++ tailWord_3437449).sum := by decide
  have hdescent : baseEnd_3437449 < baseStart_3437449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437481 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_3437481 : Nat := 118140960795 + 3437481 * 2 ^ 59
def prefixEnd_3437481 : Nat := 4983230072969 + 3 ^ 40 * 3437481 * 2
def baseEnd_3437481 : Nat := 1176719995798647048985879

theorem tailTrace_3437481 : CollatzResearch.WordTrace tailWord_3437481 prefixEnd_3437481 1176719995798647048985879 := by
  unfold tailWord_3437481
  simp only [CollatzResearch.WordTrace]
  refine ⟨125375232059600886860480297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83583488039733924573653531 125375232059600886860480297)
  ·
    refine ⟨94031424044700665145360223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125375232059600886860480297 94031424044700665145360223)
    ·
      refine ⟨141047136067050997718040335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94031424044700665145360223 141047136067050997718040335)
      ·
        refine ⟨211570704100576496577060503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141047136067050997718040335 211570704100576496577060503)
        ·
          refine ⟨317356056150864744865590755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211570704100576496577060503 317356056150864744865590755)
          ·
            refine ⟨476034084226297117298386133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317356056150864744865590755 476034084226297117298386133)
            ·
              refine ⟨11157048849053838686680925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 476034084226297117298386133 11157048849053838686680925)
              ·
                refine ⟨4183893318395189507505347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11157048849053838686680925 4183893318395189507505347)
                ·
                  refine ⟨6275839977592784261258021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4183893318395189507505347 6275839977592784261258021)
                  ·
                    refine ⟨1176719995798647048985879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6275839977592784261258021 1176719995798647048985879)
                    ·
                      rfl

theorem cell22_3437481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_3437481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437481 prefixEnd_3437481 := by exact prefixLift 3437481
  have htrace : WordTrace (prefixWord ++ tailWord_3437481) baseStart_3437481 baseEnd_3437481 := by
    simpa [prefixWord, tailWord_3437481, baseEnd_3437481] using wordTrace_append hprefix tailTrace_3437481
  have hstable : (prefixWord ++ tailWord_3437481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437481).length < 2 ^ (prefixWord ++ tailWord_3437481).sum := by decide
  have hdescent : baseEnd_3437481 < baseStart_3437481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437496 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_3437496 : Nat := 118140960795 + 3437496 * 2 ^ 59
def prefixEnd_3437496 : Nat := 4983230072969 + 3 ^ 40 * 3437496 * 2
def baseEnd_3437496 : Nat := 392241710201730669953611

theorem tailTrace_3437496 : CollatzResearch.WordTrace tailWord_3437496 prefixEnd_3437496 392241710201730669953611 := by
  unfold tailWord_3437496
  simp only [CollatzResearch.WordTrace]
  refine ⟨62687889577273272211138171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83583852769697696281517561 62687889577273272211138171)
  ·
    refine ⟨94031834365909908316707257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62687889577273272211138171 94031834365909908316707257)
    ·
      refine ⟨70523875774432431237530443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94031834365909908316707257 70523875774432431237530443)
      ·
        refine ⟨105785813661648646856295665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70523875774432431237530443 105785813661648646856295665)
        ·
          refine ⟨79339360246236485142221749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105785813661648646856295665 79339360246236485142221749)
          ·
            refine ⟨7438065023084670482083289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79339360246236485142221749 7438065023084670482083289)
            ·
              refine ⟨5578548767313502861562467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438065023084670482083289 5578548767313502861562467)
              ·
                refine ⟨8367823150970254292343701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578548767313502861562467 8367823150970254292343701)
                ·
                  refine ⟨392241710201730669953611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8367823150970254292343701 392241710201730669953611)
                  ·
                    rfl

theorem cell22_3437496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_3437496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437496 prefixEnd_3437496 := by exact prefixLift 3437496
  have htrace : WordTrace (prefixWord ++ tailWord_3437496) baseStart_3437496 baseEnd_3437496 := by
    simpa [prefixWord, tailWord_3437496, baseEnd_3437496] using wordTrace_append hprefix tailTrace_3437496
  have hstable : (prefixWord ++ tailWord_3437496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437496).length < 2 ^ (prefixWord ++ tailWord_3437496).sum := by decide
  have hdescent : baseEnd_3437496 < baseStart_3437496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437511 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3437511 : Nat := 118140960795 + 3437511 * 2 ^ 59
def prefixEnd_3437511 : Nat := 4983230072969 + 3 ^ 40 * 3437511 * 2
def baseEnd_3437511 : Nat := 1176730265411736970735787

theorem tailTrace_3437511 : CollatzResearch.WordTrace tailWord_3437511 prefixEnd_3437511 1176730265411736970735787 := by
  unfold tailWord_3437511
  simp only [CollatzResearch.WordTrace]
  refine ⟨125376326249492201984072387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83584217499661467989381591 125376326249492201984072387)
  ·
    refine ⟨188064489374238302976108581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125376326249492201984072387 188064489374238302976108581)
    ·
      refine ⟨35262091757669681808020359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188064489374238302976108581 35262091757669681808020359)
      ·
        refine ⟨52893137636504522712030539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35262091757669681808020359 52893137636504522712030539)
        ·
          refine ⟨79339706454756784068045809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52893137636504522712030539 79339706454756784068045809)
          ·
            refine ⟨59504779841067588051034357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79339706454756784068045809 59504779841067588051034357)
            ·
              refine ⟨5578573110100086379784471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59504779841067588051034357 5578573110100086379784471)
              ·
                refine ⟨8367859665150129569676707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578573110100086379784471 8367859665150129569676707)
                ·
                  refine ⟨12551789497725194354515061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8367859665150129569676707 12551789497725194354515061)
                  ·
                    refine ⟨1176730265411736970735787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12551789497725194354515061 1176730265411736970735787)
                    ·
                      rfl

theorem cell22_3437511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3437511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437511 prefixEnd_3437511 := by exact prefixLift 3437511
  have htrace : WordTrace (prefixWord ++ tailWord_3437511) baseStart_3437511 baseEnd_3437511 := by
    simpa [prefixWord, tailWord_3437511, baseEnd_3437511] using wordTrace_append hprefix tailTrace_3437511
  have hstable : (prefixWord ++ tailWord_3437511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437511).length < 2 ^ (prefixWord ++ tailWord_3437511).sum := by decide
  have hdescent : baseEnd_3437511 < baseStart_3437511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437530 : List Nat := [3, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_3437530 : Nat := 118140960795 + 3437530 * 2 ^ 59
def prefixEnd_3437530 : Nat := 4983230072969 + 3 ^ 40 * 3437530 * 2
def baseEnd_3437530 : Nat := 392245589833342418170243

theorem tailTrace_3437530 : CollatzResearch.WordTrace tailWord_3437530 prefixEnd_3437530 392245589833342418170243 := by
  unfold tailWord_3437530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31344254809105842057253511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83584679490948912152676029 31344254809105842057253511)
  ·
    refine ⟨47016382213658763085880267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31344254809105842057253511 47016382213658763085880267)
    ·
      refine ⟨70524573320488144628820401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47016382213658763085880267 70524573320488144628820401)
      ·
        refine ⟨52893429990366108471615301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70524573320488144628820401 52893429990366108471615301)
        ·
          refine ⟨9917518123193645338427869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52893429990366108471615301 9917518123193645338427869)
          ·
            refine ⟨3719069296197617001910451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9917518123193645338427869 3719069296197617001910451)
            ·
              refine ⟨5578603944296425502865677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719069296197617001910451 5578603944296425502865677)
              ·
                refine ⟨2091976479111159563574629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5578603944296425502865677 2091976479111159563574629)
                ·
                  refine ⟨392245589833342418170243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2091976479111159563574629 392245589833342418170243)
                  ·
                    rfl

theorem cell22_3437530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_3437530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437530 prefixEnd_3437530 := by exact prefixLift 3437530
  have htrace : WordTrace (prefixWord ++ tailWord_3437530) baseStart_3437530 baseEnd_3437530 := by
    simpa [prefixWord, tailWord_3437530, baseEnd_3437530] using wordTrace_append hprefix tailTrace_3437530
  have hstable : (prefixWord ++ tailWord_3437530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437530).length < 2 ^ (prefixWord ++ tailWord_3437530).sum := by decide
  have hdescent : baseEnd_3437530 < baseStart_3437530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437543 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3437543 : Nat := 118140960795 + 3437543 * 2 ^ 59
def prefixEnd_3437543 : Nat := 4983230072969 + 3 ^ 40 * 3437543 * 2
def baseEnd_3437543 : Nat := 1176741219665699553935689

theorem tailTrace_3437543 : CollatzResearch.WordTrace tailWord_3437543 prefixEnd_3437543 1176741219665699553935689 := by
  unfold tailWord_3437543
  simp only [CollatzResearch.WordTrace]
  refine ⟨125377493385376271449237283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83584995590250847632824855 125377493385376271449237283)
  ·
    refine ⟨188066240078064407173855925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125377493385376271449237283 188066240078064407173855925)
    ·
      refine ⟨17631210007318538172548993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188066240078064407173855925 17631210007318538172548993)
      ·
        refine ⟨13223407505488903629411745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17631210007318538172548993 13223407505488903629411745)
        ·
          refine ⟨9917555629116677722058809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13223407505488903629411745 9917555629116677722058809)
          ·
            refine ⟨7438166721837508291544107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917555629116677722058809 7438166721837508291544107)
            ·
              refine ⟨11157250082756262437316161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438166721837508291544107 11157250082756262437316161)
              ·
                refine ⟨8367937562067196827987121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11157250082756262437316161 8367937562067196827987121)
                ·
                  refine ⟨6275953171550397620990341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367937562067196827987121 6275953171550397620990341)
                  ·
                    refine ⟨1176741219665699553935689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6275953171550397620990341 1176741219665699553935689)
                    ·
                      rfl

theorem cell22_3437543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3437543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437543 prefixEnd_3437543 := by exact prefixLift 3437543
  have htrace : WordTrace (prefixWord ++ tailWord_3437543) baseStart_3437543 baseEnd_3437543 := by
    simpa [prefixWord, tailWord_3437543, baseEnd_3437543] using wordTrace_append hprefix tailTrace_3437543
  have hstable : (prefixWord ++ tailWord_3437543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437543).length < 2 ^ (prefixWord ++ tailWord_3437543).sum := by decide
  have hdescent : baseEnd_3437543 < baseStart_3437543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437558 : List Nat := [5, 1, 1, 1, 3, 2, 2, 7]
def baseStart_3437558 : Nat := 118140960795 + 3437558 * 2 ^ 59
def prefixEnd_3437558 : Nat := 4983230072969 + 3 ^ 40 * 3437558 * 2
def baseEnd_3437558 : Nat := 130749594941360501645627

theorem tailTrace_3437558 : CollatzResearch.WordTrace tailWord_3437558 prefixEnd_3437558 130749594941360501645627 := by
  unfold tailWord_3437558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836127530020120563189583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83585360320214619340688885 7836127530020120563189583)
  ·
    refine ⟨11754191295030180844784375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7836127530020120563189583 11754191295030180844784375)
    ·
      refine ⟨17631286942545271267176563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11754191295030180844784375 17631286942545271267176563)
      ·
        refine ⟨26446930413817906900764845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17631286942545271267176563 26446930413817906900764845)
        ·
          refine ⟨9917598905181715087786817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26446930413817906900764845 9917598905181715087786817)
          ·
            refine ⟨7438199178886286315840113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917598905181715087786817 7438199178886286315840113)
            ·
              refine ⟨5578649384164714736880085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438199178886286315840113 5578649384164714736880085)
              ·
                refine ⟨130749594941360501645627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5578649384164714736880085 130749594941360501645627)
                ·
                  rfl

theorem cell22_3437558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_3437558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437558 prefixEnd_3437558 := by exact prefixLift 3437558
  have htrace : WordTrace (prefixWord ++ tailWord_3437558) baseStart_3437558 baseEnd_3437558 := by
    simpa [prefixWord, tailWord_3437558, baseEnd_3437558] using wordTrace_append hprefix tailTrace_3437558
  have hstable : (prefixWord ++ tailWord_3437558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437558).length < 2 ^ (prefixWord ++ tailWord_3437558).sum := by decide
  have hdescent : baseEnd_3437558 < baseStart_3437558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437603 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 5]
def baseStart_3437603 : Nat := 118140960795 + 3437603 * 2 ^ 59
def prefixEnd_3437603 : Nat := 4983230072969 + 3 ^ 40 * 3437603 * 2
def baseEnd_3437603 : Nat := 392253919630626465811835

theorem tailTrace_3437603 : CollatzResearch.WordTrace tailWord_3437603 prefixEnd_3437603 392253919630626465811835 := by
  unfold tailWord_3437603
  simp only [CollatzResearch.WordTrace]
  refine ⟨125379681765158901696421463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83586454510105934464280975 125379681765158901696421463)
  ·
    refine ⟨188069522647738352544632195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125379681765158901696421463 188069522647738352544632195)
    ·
      refine ⟨282104283971607528816948293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188069522647738352544632195 282104283971607528816948293)
      ·
        refine ⟨52894553244676411653177805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282104283971607528816948293 52894553244676411653177805)
        ·
          refine ⟨19835457466753654369941677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52894553244676411653177805 19835457466753654369941677)
          ·
            refine ⟨7438296550032620388728129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19835457466753654369941677 7438296550032620388728129)
            ·
              refine ⟨5578722412524465291546097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7438296550032620388728129 5578722412524465291546097)
              ·
                refine ⟨4184041809393348968659573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5578722412524465291546097 4184041809393348968659573)
                ·
                  refine ⟨392253919630626465811835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184041809393348968659573 392253919630626465811835)
                  ·
                    rfl

theorem cell22_3437603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 5].length) (baseStart_3437603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437603 prefixEnd_3437603 := by exact prefixLift 3437603
  have htrace : WordTrace (prefixWord ++ tailWord_3437603) baseStart_3437603 baseEnd_3437603 := by
    simpa [prefixWord, tailWord_3437603, baseEnd_3437603] using wordTrace_append hprefix tailTrace_3437603
  have hstable : (prefixWord ++ tailWord_3437603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437603).length < 2 ^ (prefixWord ++ tailWord_3437603).sum := by decide
  have hdescent : baseEnd_3437603 < baseStart_3437603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437616 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_3437616 : Nat := 118140960795 + 3437616 * 2 ^ 59
def prefixEnd_3437616 : Nat := 4983230072969 + 3 ^ 40 * 3437616 * 2
def baseEnd_3437616 : Nat := 1176766209057551696860465

theorem tailTrace_3437616 : CollatzResearch.WordTrace tailWord_3437616 prefixEnd_3437616 1176766209057551696860465 := by
  unfold tailWord_3437616
  simp only [CollatzResearch.WordTrace]
  refine ⟨62690077957055902458322351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83586770609407869944429801 62690077957055902458322351)
  ·
    refine ⟨94035116935583853687483527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62690077957055902458322351 94035116935583853687483527)
    ·
      refine ⟨141052675403375780531225291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94035116935583853687483527 141052675403375780531225291)
      ·
        refine ⟨211579013105063670796837937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141052675403375780531225291 211579013105063670796837937)
        ·
          refine ⟨158684259828797753097628453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211579013105063670796837937 158684259828797753097628453)
          ·
            refine ⟨29753298717899578705805335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158684259828797753097628453 29753298717899578705805335)
            ·
              refine ⟨44629948076849368058708003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29753298717899578705805335 44629948076849368058708003)
              ·
                refine ⟨66944922115274052088062005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44629948076849368058708003 66944922115274052088062005)
                ·
                  refine ⟨6276086448306942383255813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66944922115274052088062005 6276086448306942383255813)
                  ·
                    refine ⟨1176766209057551696860465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276086448306942383255813 1176766209057551696860465)
                    ·
                      rfl

theorem cell22_3437616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_3437616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437616 prefixEnd_3437616 := by exact prefixLift 3437616
  have htrace : WordTrace (prefixWord ++ tailWord_3437616) baseStart_3437616 baseEnd_3437616 := by
    simpa [prefixWord, tailWord_3437616, baseEnd_3437616] using wordTrace_append hprefix tailTrace_3437616
  have hstable : (prefixWord ++ tailWord_3437616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437616).length < 2 ^ (prefixWord ++ tailWord_3437616).sum := by decide
  have hdescent : baseEnd_3437616 < baseStart_3437616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437620 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3437620 : Nat := 118140960795 + 3437620 * 2 ^ 59
def prefixEnd_3437620 : Nat := 4983230072969 + 3 ^ 40 * 3437620 * 2
def baseEnd_3437620 : Nat := 392255859446432339920151

theorem tailTrace_3437620 : CollatzResearch.WordTrace tailWord_3437620 prefixEnd_3437620 392255859446432339920151 := by
  unfold tailWord_3437620
  simp only [CollatzResearch.WordTrace]
  refine ⟨62690150903048656799895157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83586867870731542399860209 62690150903048656799895157)
  ·
    refine ⟨5877201647160811574990171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62690150903048656799895157 5877201647160811574990171)
    ·
      refine ⟨8815802470741217362485257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877201647160811574990171 8815802470741217362485257)
      ·
        refine ⟨6611851853055913021863943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8815802470741217362485257 6611851853055913021863943)
        ·
          refine ⟨9917777779583869532795915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611851853055913021863943 9917777779583869532795915)
          ·
            refine ⟨14876666669375804299193873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9917777779583869532795915 14876666669375804299193873)
            ·
              refine ⟨11157500002031853224395405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14876666669375804299193873 11157500002031853224395405)
              ·
                refine ⟨4184062500761944959148277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11157500002031853224395405 4184062500761944959148277)
                ·
                  refine ⟨392255859446432339920151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184062500761944959148277 392255859446432339920151)
                  ·
                    rfl

theorem cell22_3437620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3437620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437620 prefixEnd_3437620 := by exact prefixLift 3437620
  have htrace : WordTrace (prefixWord ++ tailWord_3437620) baseStart_3437620 baseEnd_3437620 := by
    simpa [prefixWord, tailWord_3437620, baseEnd_3437620] using wordTrace_append hprefix tailTrace_3437620
  have hstable : (prefixWord ++ tailWord_3437620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437620).length < 2 ^ (prefixWord ++ tailWord_3437620).sum := by decide
  have hdescent : baseEnd_3437620 < baseStart_3437620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437650 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3437650 : Nat := 118140960795 + 3437650 * 2 ^ 59
def prefixEnd_3437650 : Nat := 4983230072969 + 3 ^ 40 * 3437650 * 2
def baseEnd_3437650 : Nat := 1176777847952386941510361

theorem tailTrace_3437650 : CollatzResearch.WordTrace tailWord_3437650 prefixEnd_3437650 1176777847952386941510361 := by
  unfold tailWord_3437650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31345348998997157180845601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83587597330659085815588269 31345348998997157180845601)
  ·
    refine ⟨23509011749247867885634201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31345348998997157180845601 23509011749247867885634201)
    ·
      refine ⟨17631758811935900914225651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23509011749247867885634201 17631758811935900914225651)
      ·
        refine ⟨26447638217903851371338477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17631758811935900914225651 26447638217903851371338477)
        ·
          refine ⟨9917864331713944264251929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26447638217903851371338477 9917864331713944264251929)
          ·
            refine ⟨7438398248785458198188947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917864331713944264251929 7438398248785458198188947)
            ·
              refine ⟨11157597373178187297283421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438398248785458198188947 11157597373178187297283421)
              ·
                refine ⟨4184099014941820236481283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11157597373178187297283421 4184099014941820236481283)
                ·
                  refine ⟨6276148522412730354721925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4184099014941820236481283 6276148522412730354721925)
                  ·
                    refine ⟨1176777847952386941510361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276148522412730354721925 1176777847952386941510361)
                    ·
                      rfl

theorem cell22_3437650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3437650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437650 prefixEnd_3437650 := by exact prefixLift 3437650
  have htrace : WordTrace (prefixWord ++ tailWord_3437650) baseStart_3437650 baseEnd_3437650 := by
    simpa [prefixWord, tailWord_3437650, baseEnd_3437650] using wordTrace_append hprefix tailTrace_3437650
  have hstable : (prefixWord ++ tailWord_3437650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437650).length < 2 ^ (prefixWord ++ tailWord_3437650).sum := by decide
  have hdescent : baseEnd_3437650 < baseStart_3437650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437654 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3437654 : Nat := 118140960795 + 3437654 * 2 ^ 59
def prefixEnd_3437654 : Nat := 4983230072969 + 3 ^ 40 * 3437654 * 2
def baseEnd_3437654 : Nat := 392259739078044088136783

theorem tailTrace_3437654 : CollatzResearch.WordTrace tailWord_3437654 prefixEnd_3437654 392259739078044088136783 := by
  unfold tailWord_3437654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836346367998383587908001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83587694591982758271018677 7836346367998383587908001)
  ·
    refine ⟨5877259775998787690931001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7836346367998383587908001 5877259775998787690931001)
    ·
      refine ⟨4407944831999090768198251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5877259775998787690931001 4407944831999090768198251)
      ·
        refine ⟨6611917247998636152297377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407944831999090768198251 6611917247998636152297377)
        ·
          refine ⟨4958937935998977114223033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6611917247998636152297377 4958937935998977114223033)
          ·
            refine ⟨3719203451999232835667275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4958937935998977114223033 3719203451999232835667275)
            ·
              refine ⟨5578805177998849253500913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719203451999232835667275 5578805177998849253500913)
              ·
                refine ⟨4184103883499136940125685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5578805177998849253500913 4184103883499136940125685)
                ·
                  refine ⟨392259739078044088136783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184103883499136940125685 392259739078044088136783)
                  ·
                    rfl

theorem cell22_3437654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3437654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437654 prefixEnd_3437654 := by exact prefixLift 3437654
  have htrace : WordTrace (prefixWord ++ tailWord_3437654) baseStart_3437654 baseEnd_3437654 := by
    simpa [prefixWord, tailWord_3437654, baseEnd_3437654] using wordTrace_append hprefix tailTrace_3437654
  have hstable : (prefixWord ++ tailWord_3437654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437654).length < 2 ^ (prefixWord ++ tailWord_3437654).sum := by decide
  have hdescent : baseEnd_3437654 < baseStart_3437654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437663 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 4, 3]
def baseStart_3437663 : Nat := 118140960795 + 3437663 * 2 ^ 59
def prefixEnd_3437663 : Nat := 4983230072969 + 3 ^ 40 * 3437663 * 2
def baseEnd_3437663 : Nat := 1176782298118059240935321

theorem tailTrace_3437663 : CollatzResearch.WordTrace tailWord_3437663 prefixEnd_3437663 1176782298118059240935321 := by
  unfold tailWord_3437663
  simp only [CollatzResearch.WordTrace]
  refine ⟨125381870144941531943605643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83587913429961021295737095 125381870144941531943605643)
  ·
    refine ⟨188072805217412297915408465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125381870144941531943605643 188072805217412297915408465)
    ·
      refine ⟨141054603913059223436556349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188072805217412297915408465 141054603913059223436556349)
      ·
        refine ⟨52895476467397208788708631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141054603913059223436556349 52895476467397208788708631)
        ·
          refine ⟨79343214701095813183062947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52895476467397208788708631 79343214701095813183062947)
          ·
            refine ⟨119014822051643719774594421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79343214701095813183062947 119014822051643719774594421)
            ·
              refine ⟨11157639567341598728868227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119014822051643719774594421 11157639567341598728868227)
              ·
                refine ⟨16736459351012398093302341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11157639567341598728868227 16736459351012398093302341)
                ·
                  refine ⟨3138086128314824642494189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16736459351012398093302341 3138086128314824642494189)
                  ·
                    refine ⟨1176782298118059240935321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3138086128314824642494189 1176782298118059240935321)
                    ·
                      rfl

theorem cell22_3437663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_3437663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437663 prefixEnd_3437663 := by exact prefixLift 3437663
  have htrace : WordTrace (prefixWord ++ tailWord_3437663) baseStart_3437663 baseEnd_3437663 := by
    simpa [prefixWord, tailWord_3437663, baseEnd_3437663] using wordTrace_append hprefix tailTrace_3437663
  have hstable : (prefixWord ++ tailWord_3437663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437663).length < 2 ^ (prefixWord ++ tailWord_3437663).sum := by decide
  have hdescent : baseEnd_3437663 < baseStart_3437663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437676 : List Nat := [2, 2, 1, 1, 3, 2, 2, 9]
def baseStart_3437676 : Nat := 118140960795 + 3437676 * 2 ^ 59
def prefixEnd_3437676 : Nat := 4983230072969 + 3 ^ 40 * 3437676 * 2
def baseEnd_3437676 : Nat := 130754083142636837817809

theorem tailTrace_3437676 : CollatzResearch.WordTrace tailWord_3437676 prefixEnd_3437676 130754083142636837817809 := by
  unfold tailWord_3437676
  simp only [CollatzResearch.WordTrace]
  refine ⟨62691172146947217581914441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83588229529262956775885921 62691172146947217581914441)
  ·
    refine ⟨47018379110210413186435831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62691172146947217581914441 47018379110210413186435831)
    ·
      refine ⟨70527568665315619779653747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47018379110210413186435831 70527568665315619779653747)
      ·
        refine ⟨105791352997973429669480621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70527568665315619779653747 105791352997973429669480621)
        ·
          refine ⟨39671757374240036126055233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105791352997973429669480621 39671757374240036126055233)
          ·
            refine ⟨29753818030680027094541425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39671757374240036126055233 29753818030680027094541425)
            ·
              refine ⟨22315363523010020320906069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29753818030680027094541425 22315363523010020320906069)
              ·
                refine ⟨130754083142636837817809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22315363523010020320906069 130754083142636837817809)
                ·
                  rfl

theorem cell22_3437676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_3437676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437676 prefixEnd_3437676 := by exact prefixLift 3437676
  have htrace : WordTrace (prefixWord ++ tailWord_3437676) baseStart_3437676 baseEnd_3437676 := by
    simpa [prefixWord, tailWord_3437676, baseEnd_3437676] using wordTrace_append hprefix tailTrace_3437676
  have hstable : (prefixWord ++ tailWord_3437676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437676).length < 2 ^ (prefixWord ++ tailWord_3437676).sum := by decide
  have hdescent : baseEnd_3437676 < baseStart_3437676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437678 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3437678 : Nat := 118140960795 + 3437678 * 2 ^ 59
def prefixEnd_3437678 : Nat := 4983230072969 + 3 ^ 40 * 3437678 * 2
def baseEnd_3437678 : Nat := 1176787432924604201810275

theorem tailTrace_3437678 : CollatzResearch.WordTrace tailWord_3437678 prefixEnd_3437678 1176787432924604201810275 := by
  unfold tailWord_3437678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15672802154985898688175211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83588278159924793003601125 15672802154985898688175211)
  ·
    refine ⟨23509203232478848032262817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15672802154985898688175211 23509203232478848032262817)
    ·
      refine ⟨17631902424359136024197113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23509203232478848032262817 17631902424359136024197113)
      ·
        refine ⟨13223926818269352018147835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17631902424359136024197113 13223926818269352018147835)
        ·
          refine ⟨19835890227404028027221753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13223926818269352018147835 19835890227404028027221753)
          ·
            refine ⟨14876917670553021020416315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19835890227404028027221753 14876917670553021020416315)
            ·
              refine ⟨22315376505829531530624473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876917670553021020416315 22315376505829531530624473)
              ·
                refine ⟨16736532379372148647968355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22315376505829531530624473 16736532379372148647968355)
                ·
                  refine ⟨25104798569058222971952533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16736532379372148647968355 25104798569058222971952533)
                  ·
                    refine ⟨1176787432924604201810275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25104798569058222971952533 1176787432924604201810275)
                    ·
                      rfl

theorem cell22_3437678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3437678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437678 prefixEnd_3437678 := by exact prefixLift 3437678
  have htrace : WordTrace (prefixWord ++ tailWord_3437678) baseStart_3437678 baseEnd_3437678 := by
    simpa [prefixWord, tailWord_3437678, baseEnd_3437678] using wordTrace_append hprefix tailTrace_3437678
  have hstable : (prefixWord ++ tailWord_3437678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437678).length < 2 ^ (prefixWord ++ tailWord_3437678).sum := by decide
  have hdescent : baseEnd_3437678 < baseStart_3437678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437708 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_3437708 : Nat := 118140960795 + 3437708 * 2 ^ 59
def prefixEnd_3437708 : Nat := 4983230072969 + 3 ^ 40 * 3437708 * 2
def baseEnd_3437708 : Nat := 1176797702537694123560183

theorem tailTrace_3437708 : CollatzResearch.WordTrace tailWord_3437708 prefixEnd_3437708 1176797702537694123560183 := by
  unfold tailWord_3437708
  simp only [CollatzResearch.WordTrace]
  refine ⟨62691755714889252314496889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83589007619852336419329185 62691755714889252314496889)
  ·
    refine ⟨47018816786166939235872667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62691755714889252314496889 47018816786166939235872667)
    ·
      refine ⟨70528225179250408853809001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47018816786166939235872667 70528225179250408853809001)
      ·
        refine ⟨52896168884437806640356751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70528225179250408853809001 52896168884437806640356751)
        ·
          refine ⟨79344253326656709960535127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52896168884437806640356751 79344253326656709960535127)
          ·
            refine ⟨119016379989985064940802691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79344253326656709960535127 119016379989985064940802691)
            ·
              refine ⟨178524569984977597411204037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119016379989985064940802691 178524569984977597411204037)
              ·
                refine ⟨33473356872183299514600757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178524569984977597411204037 33473356872183299514600757)
                ·
                  refine ⟨3138127206767184329493821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33473356872183299514600757 3138127206767184329493821)
                  ·
                    refine ⟨1176797702537694123560183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3138127206767184329493821 1176797702537694123560183)
                    ·
                      rfl

theorem cell22_3437708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_3437708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437708 prefixEnd_3437708 := by exact prefixLift 3437708
  have htrace : WordTrace (prefixWord ++ tailWord_3437708) baseStart_3437708 baseEnd_3437708 := by
    simpa [prefixWord, tailWord_3437708, baseEnd_3437708] using wordTrace_append hprefix tailTrace_3437708
  have hstable : (prefixWord ++ tailWord_3437708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437708).length < 2 ^ (prefixWord ++ tailWord_3437708).sum := by decide
  have hdescent : baseEnd_3437708 < baseStart_3437708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437832 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_3437832 : Nat := 118140960795 + 3437832 * 2 ^ 59
def prefixEnd_3437832 : Nat := 4983230072969 + 3 ^ 40 * 3437832 * 2
def baseEnd_3437832 : Nat := 1176840150271799133459803

theorem tailTrace_3437832 : CollatzResearch.WordTrace tailWord_3437832 prefixEnd_3437832 1176840150271799133459803 := by
  unfold tailWord_3437832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62694017040664636903253875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83592022720886182537671833 62694017040664636903253875)
  ·
    refine ⟨94041025560996955354880813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62694017040664636903253875 94041025560996955354880813)
    ·
      refine ⟨35265384585373858258080305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94041025560996955354880813 35265384585373858258080305)
      ·
        refine ⟨26449038439030393693560229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35265384585373858258080305 26449038439030393693560229)
        ·
          refine ⟨4959194707318198817542543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26449038439030393693560229 4959194707318198817542543)
          ·
            refine ⟨7438792060977298226313815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959194707318198817542543 7438792060977298226313815)
            ·
              refine ⟨11158188091465947339470723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438792060977298226313815 11158188091465947339470723)
              ·
                refine ⟨16737282137198921009206085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11158188091465947339470723 16737282137198921009206085)
                ·
                  refine ⟨3138240400724797689226141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16737282137198921009206085 3138240400724797689226141)
                  ·
                    refine ⟨1176840150271799133459803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3138240400724797689226141 1176840150271799133459803)
                    ·
                      rfl

theorem cell22_3437832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_3437832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437832 prefixEnd_3437832 := by exact prefixLift 3437832
  have htrace : WordTrace (prefixWord ++ tailWord_3437832) baseStart_3437832 baseEnd_3437832 := by
    simpa [prefixWord, tailWord_3437832, baseEnd_3437832] using wordTrace_append hprefix tailTrace_3437832
  have hstable : (prefixWord ++ tailWord_3437832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437832).length < 2 ^ (prefixWord ++ tailWord_3437832).sum := by decide
  have hdescent : baseEnd_3437832 < baseStart_3437832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437954 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3437954 : Nat := 118140960795 + 3437954 * 2 ^ 59
def prefixEnd_3437954 : Nat := 4983230072969 + 3 ^ 40 * 3437954 * 2
def baseEnd_3437954 : Nat := 1176881913365031481909429

theorem tailTrace_3437954 : CollatzResearch.WordTrace tailWord_3437954 prefixEnd_3437954 1176881913365031481909429 := by
  unfold tailWord_3437954
  simp only [CollatzResearch.WordTrace]
  refine ⟨31348120946721822160612229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83594989191258192428299277 31348120946721822160612229)
  ·
    refine ⟨5877772677510341655114793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31348120946721822160612229 5877772677510341655114793)
    ·
      refine ⟨4408329508132756241336095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5877772677510341655114793 4408329508132756241336095)
      ·
        refine ⟨6612494262199134362004143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408329508132756241336095 6612494262199134362004143)
        ·
          refine ⟨9918741393298701543006215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612494262199134362004143 9918741393298701543006215)
          ·
            refine ⟨14878112089948052314509323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918741393298701543006215 14878112089948052314509323)
            ·
              refine ⟨22317168134922078471763985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14878112089948052314509323 22317168134922078471763985)
              ·
                refine ⟨16737876101191558853822989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22317168134922078471763985 16737876101191558853822989)
                ·
                  refine ⟨6276703537946834570183621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16737876101191558853822989 6276703537946834570183621)
                  ·
                    refine ⟨1176881913365031481909429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6276703537946834570183621 1176881913365031481909429)
                    ·
                      rfl

theorem cell22_3437954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3437954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437954 prefixEnd_3437954 := by exact prefixLift 3437954
  have htrace : WordTrace (prefixWord ++ tailWord_3437954) baseStart_3437954 baseEnd_3437954 := by
    simpa [prefixWord, tailWord_3437954, baseEnd_3437954] using wordTrace_append hprefix tailTrace_3437954
  have hstable : (prefixWord ++ tailWord_3437954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437954).length < 2 ^ (prefixWord ++ tailWord_3437954).sum := by decide
  have hdescent : baseEnd_3437954 < baseStart_3437954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3437997 : List Nat := [1, 5, 2, 2, 1, 2, 9]
def baseStart_3437997 : Nat := 118140960795 + 3437997 * 2 ^ 59
def prefixEnd_3437997 : Nat := 4983230072969 + 3 ^ 40 * 3437997 * 2
def baseEnd_3437997 : Nat := 43588764190510877892011

theorem tailTrace_3437997 : CollatzResearch.WordTrace tailWord_3437997 prefixEnd_3437997 43588764190510877892011 := by
  unfold tailWord_3437997
  simp only [CollatzResearch.WordTrace]
  refine ⟨125394052125731506986264245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83596034750487671324176163 125394052125731506986264245)
  ·
    refine ⟨11755692386787328779962273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125394052125731506986264245 11755692386787328779962273)
    ·
      refine ⟨8816769290090496584971705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11755692386787328779962273 8816769290090496584971705)
      ·
        refine ⟨6612576967567872438728779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816769290090496584971705 6612576967567872438728779)
        ·
          refine ⟨9918865451351808658093169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612576967567872438728779 9918865451351808658093169)
          ·
            refine ⟨7439149088513856493569877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9918865451351808658093169 7439149088513856493569877)
            ·
              refine ⟨43588764190510877892011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7439149088513856493569877 43588764190510877892011)
              ·
                rfl

theorem cell22_3437997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 9].length) (baseStart_3437997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3437997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3437997 prefixEnd_3437997 := by exact prefixLift 3437997
  have htrace : WordTrace (prefixWord ++ tailWord_3437997) baseStart_3437997 baseEnd_3437997 := by
    simpa [prefixWord, tailWord_3437997, baseEnd_3437997] using wordTrace_append hprefix tailTrace_3437997
  have hstable : (prefixWord ++ tailWord_3437997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3437997).length < 2 ^ (prefixWord ++ tailWord_3437997).sum := by decide
  have hdescent : baseEnd_3437997 < baseStart_3437997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3437997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438040 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_3438040 : Nat := 118140960795 + 3438040 * 2 ^ 59
def prefixEnd_3438040 : Nat := 4983230072969 + 3 ^ 40 * 3438040 * 2
def baseEnd_3438040 : Nat := 1176911352922555924259165

theorem tailTrace_3438040 : CollatzResearch.WordTrace tailWord_3438040 prefixEnd_3438040 1176911352922555924259165 := by
  unfold tailWord_3438040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62697810232287862665039787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83597080309717150220053049 62697810232287862665039787)
  ·
    refine ⟨94046715348431793997559681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62697810232287862665039787 94046715348431793997559681)
    ·
      refine ⟨70535036511323845498169761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94046715348431793997559681 70535036511323845498169761)
      ·
        refine ⟨52901277383492884123627321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70535036511323845498169761 52901277383492884123627321)
        ·
          refine ⟨39675958037619663092720491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52901277383492884123627321 39675958037619663092720491)
          ·
            refine ⟨59513937056429494639080737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39675958037619663092720491 59513937056429494639080737)
            ·
              refine ⟨44635452792322120979310553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59513937056429494639080737 44635452792322120979310553)
              ·
                refine ⟨33476589594241590734482915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44635452792322120979310553 33476589594241590734482915)
                ·
                  refine ⟨50214884391362386101724373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33476589594241590734482915 50214884391362386101724373)
                  ·
                    refine ⟨1176911352922555924259165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50214884391362386101724373 1176911352922555924259165)
                    ·
                      rfl

theorem cell22_3438040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_3438040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438040 prefixEnd_3438040 := by exact prefixLift 3438040
  have htrace : WordTrace (prefixWord ++ tailWord_3438040) baseStart_3438040 baseEnd_3438040 := by
    simpa [prefixWord, tailWord_3438040, baseEnd_3438040] using wordTrace_append hprefix tailTrace_3438040
  have hstable : (prefixWord ++ tailWord_3438040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438040).length < 2 ^ (prefixWord ++ tailWord_3438040).sum := by decide
  have hdescent : baseEnd_3438040 < baseStart_3438040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438110 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3438110 : Nat := 118140960795 + 3438110 * 2 ^ 59
def prefixEnd_3438110 : Nat := 4983230072969 + 3 ^ 40 * 3438110 * 2
def baseEnd_3438110 : Nat := 392311771784366358336317

theorem tailTrace_3438110 : CollatzResearch.WordTrace tailWord_3438110 prefixEnd_3438110 392311771784366358336317 := by
  unfold tailWord_3438110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15674771696790265910640973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83598782382881418190085189 15674771696790265910640973)
  ·
    refine ⟨5878039386296349716490365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15674771696790265910640973 5878039386296349716490365)
    ·
      refine ⟨2204264769861131143683887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5878039386296349716490365 2204264769861131143683887)
      ·
        refine ⟨3306397154791696715525831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204264769861131143683887 3306397154791696715525831)
        ·
          refine ⟨4959595732187545073288747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306397154791696715525831 4959595732187545073288747)
          ·
            refine ⟨7439393598281317609933121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959595732187545073288747 7439393598281317609933121)
            ·
              refine ⟨5579545198710988207449841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7439393598281317609933121 5579545198710988207449841)
              ·
                refine ⟨4184658899033241155587381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579545198710988207449841 4184658899033241155587381)
                ·
                  refine ⟨392311771784366358336317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184658899033241155587381 392311771784366358336317)
                  ·
                    rfl

theorem cell22_3438110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3438110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438110 prefixEnd_3438110 := by exact prefixLift 3438110
  have htrace : WordTrace (prefixWord ++ tailWord_3438110) baseStart_3438110 baseEnd_3438110 := by
    simpa [prefixWord, tailWord_3438110, baseEnd_3438110] using wordTrace_append hprefix tailTrace_3438110
  have hstable : (prefixWord ++ tailWord_3438110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438110).length < 2 ^ (prefixWord ++ tailWord_3438110).sum := by decide
  have hdescent : baseEnd_3438110 < baseStart_3438110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438115 : List Nat := [1, 1, 1, 4, 15]
def baseStart_3438115 : Nat := 118140960795 + 3438115 * 2 ^ 59
def prefixEnd_3438115 : Nat := 4983230072969 + 3 ^ 40 * 3438115 * 2
def baseEnd_3438115 : Nat := 4843362250844776661045

theorem tailTrace_3438115 : CollatzResearch.WordTrace tailWord_3438115 prefixEnd_3438115 4843362250844776661045 := by
  unfold tailWord_3438115
  simp only [CollatzResearch.WordTrace]
  refine ⟨125398355939304013139059799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83598903959536008759373199 125398355939304013139059799)
  ·
    refine ⟨188097533908956019708589699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125398355939304013139059799 188097533908956019708589699)
    ·
      refine ⟨282146300863434029562884549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188097533908956019708589699 282146300863434029562884549)
      ·
        refine ⟨52902431411893880543040853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282146300863434029562884549 52902431411893880543040853)
        ·
          refine ⟨4843362250844776661045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 52902431411893880543040853 4843362250844776661045)
          ·
            rfl

theorem cell22_3438115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 15].length) (baseStart_3438115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438115 prefixEnd_3438115 := by exact prefixLift 3438115
  have htrace : WordTrace (prefixWord ++ tailWord_3438115) baseStart_3438115 baseEnd_3438115 := by
    simpa [prefixWord, tailWord_3438115, baseEnd_3438115] using wordTrace_append hprefix tailTrace_3438115
  have hstable : (prefixWord ++ tailWord_3438115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438115).length < 2 ^ (prefixWord ++ tailWord_3438115).sum := by decide
  have hdescent : baseEnd_3438115 < baseStart_3438115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438151 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3438151 : Nat := 118140960795 + 3438151 * 2 ^ 59
def prefixEnd_3438151 : Nat := 4983230072969 + 3 ^ 40 * 3438151 * 2
def baseEnd_3438151 : Nat := 1176949350490988634733825

theorem tailTrace_3438151 : CollatzResearch.WordTrace tailWord_3438151 prefixEnd_3438151 1176949350490988634733825 := by
  unfold tailWord_3438151
  simp only [CollatzResearch.WordTrace]
  refine ⟨125399668967173591287370307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83599779311449060858246871 125399668967173591287370307)
  ·
    refine ⟨188099503450760386931055461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125399668967173591287370307 188099503450760386931055461)
    ·
      refine ⟨35268656897017572549572899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188099503450760386931055461 35268656897017572549572899)
      ·
        refine ⟨52902985345526358824359349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35268656897017572549572899 52902985345526358824359349)
        ·
          refine ⟨4959654876143096139783689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52902985345526358824359349 4959654876143096139783689)
          ·
            refine ⟨3719741157107322104837767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959654876143096139783689 3719741157107322104837767)
            ·
              refine ⟨5579611735660983157256651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719741157107322104837767 5579611735660983157256651)
              ·
                refine ⟨8369417603491474735884977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579611735660983157256651 8369417603491474735884977)
                ·
                  refine ⟨6277063202618606051913733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8369417603491474735884977 6277063202618606051913733)
                  ·
                    refine ⟨1176949350490988634733825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6277063202618606051913733 1176949350490988634733825)
                    ·
                      rfl

theorem cell22_3438151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3438151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438151 prefixEnd_3438151 := by exact prefixLift 3438151
  have htrace : WordTrace (prefixWord ++ tailWord_3438151) baseStart_3438151 baseEnd_3438151 := by
    simpa [prefixWord, tailWord_3438151, baseEnd_3438151] using wordTrace_append hprefix tailTrace_3438151
  have hstable : (prefixWord ++ tailWord_3438151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438151).length < 2 ^ (prefixWord ++ tailWord_3438151).sum := by decide
  have hdescent : baseEnd_3438151 < baseStart_3438151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438164 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3438164 : Nat := 118140960795 + 3438164 * 2 ^ 59
def prefixEnd_3438164 : Nat := 4983230072969 + 3 ^ 40 * 3438164 * 2
def baseEnd_3438164 : Nat := 1176953800656660934158785

theorem tailTrace_3438164 : CollatzResearch.WordTrace tailWord_3438164 prefixEnd_3438164 1176953800656660934158785 := by
  unfold tailWord_3438164
  simp only [CollatzResearch.WordTrace]
  refine ⟨62700071558063247253796773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83600095410750996338395697 62700071558063247253796773)
  ·
    refine ⟨11756263417136858860086895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62700071558063247253796773 11756263417136858860086895)
    ·
      refine ⟨17634395125705288290130343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11756263417136858860086895 17634395125705288290130343)
      ·
        refine ⟨26451592688557932435195515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17634395125705288290130343 26451592688557932435195515)
        ·
          refine ⟨39677389032836898652793273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26451592688557932435195515 39677389032836898652793273)
          ·
            refine ⟨29758041774627673989594955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39677389032836898652793273 29758041774627673989594955)
            ·
              refine ⟨44637062661941510984392433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29758041774627673989594955 44637062661941510984392433)
              ·
                refine ⟨33477796996456133238294325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44637062661941510984392433 33477796996456133238294325)
                ·
                  refine ⟨3138543468417762491090093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33477796996456133238294325 3138543468417762491090093)
                  ·
                    refine ⟨1176953800656660934158785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3138543468417762491090093 1176953800656660934158785)
                    ·
                      rfl

theorem cell22_3438164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3438164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438164 prefixEnd_3438164 := by exact prefixLift 3438164
  have htrace : WordTrace (prefixWord ++ tailWord_3438164) baseStart_3438164 baseEnd_3438164 := by
    simpa [prefixWord, tailWord_3438164, baseEnd_3438164] using wordTrace_append hprefix tailTrace_3438164
  have hstable : (prefixWord ++ tailWord_3438164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438164).length < 2 ^ (prefixWord ++ tailWord_3438164).sum := by decide
  have hdescent : baseEnd_3438164 < baseStart_3438164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438177 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 7]
def baseStart_3438177 : Nat := 118140960795 + 3438177 * 2 ^ 59
def prefixEnd_3438177 : Nat := 4983230072969 + 3 ^ 40 * 3438177 * 2
def baseEnd_3438177 : Nat := 392319416940777744527915

theorem tailTrace_3438177 : CollatzResearch.WordTrace tailWord_3438177 prefixEnd_3438177 392319416940777744527915 := by
  unfold tailWord_3438177
  simp only [CollatzResearch.WordTrace]
  refine ⟨125400617265079397727816785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83600411510052931818544523 125400617265079397727816785)
  ·
    refine ⟨94050462948809548295862589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125400617265079397727816785 94050462948809548295862589)
    ·
      refine ⟨35268923605803580610948471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94050462948809548295862589 35268923605803580610948471)
      ·
        refine ⟨52903385408705370916422707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35268923605803580610948471 52903385408705370916422707)
        ·
          refine ⟨79355078113058056374634061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52903385408705370916422707 79355078113058056374634061)
          ·
            refine ⟨29758154292396771140487773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79355078113058056374634061 29758154292396771140487773)
            ·
              refine ⟨11159307859648789177682915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29758154292396771140487773 11159307859648789177682915)
              ·
                refine ⟨16738961789473183766524373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11159307859648789177682915 16738961789473183766524373)
                ·
                  refine ⟨392319416940777744527915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16738961789473183766524373 392319416940777744527915)
                  ·
                    rfl

theorem cell22_3438177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_3438177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438177 prefixEnd_3438177 := by exact prefixLift 3438177
  have htrace : WordTrace (prefixWord ++ tailWord_3438177) baseStart_3438177 baseEnd_3438177 := by
    simpa [prefixWord, tailWord_3438177, baseEnd_3438177] using wordTrace_append hprefix tailTrace_3438177
  have hstable : (prefixWord ++ tailWord_3438177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438177).length < 2 ^ (prefixWord ++ tailWord_3438177).sum := by decide
  have hdescent : baseEnd_3438177 < baseStart_3438177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438181 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_3438181 : Nat := 118140960795 + 3438181 * 2 ^ 59
def prefixEnd_3438181 : Nat := 4983230072969 + 3 ^ 40 * 3438181 * 2
def baseEnd_3438181 : Nat := 1176959620104078556483733

theorem tailTrace_3438181 : CollatzResearch.WordTrace tailWord_3438181 prefixEnd_3438181 1176959620104078556483733 := by
  unfold tailWord_3438181
  simp only [CollatzResearch.WordTrace]
  refine ⟨125400763157064906410962397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83600508771376604273974931 125400763157064906410962397)
  ·
    refine ⟨47025286183899339904110899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125400763157064906410962397 47025286183899339904110899)
    ·
      refine ⟨70537929275849009856166349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47025286183899339904110899 70537929275849009856166349)
      ·
        refine ⟨26451723478443378696062381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70537929275849009856166349 26451723478443378696062381)
        ·
          refine ⟨9919396304416267011023393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26451723478443378696062381 9919396304416267011023393)
          ·
            refine ⟨7439547228312200258267545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9919396304416267011023393 7439547228312200258267545)
            ·
              refine ⟨5579660421234150193700659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7439547228312200258267545 5579660421234150193700659)
              ·
                refine ⟨8369490631851225290550989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579660421234150193700659 8369490631851225290550989)
                ·
                  refine ⟨3138558986944209483956621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8369490631851225290550989 3138558986944209483956621)
                  ·
                    refine ⟨1176959620104078556483733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3138558986944209483956621 1176959620104078556483733)
                    ·
                      rfl

theorem cell22_3438181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_3438181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438181 prefixEnd_3438181 := by exact prefixLift 3438181
  have htrace : WordTrace (prefixWord ++ tailWord_3438181) baseStart_3438181 baseEnd_3438181 := by
    simpa [prefixWord, tailWord_3438181, baseEnd_3438181] using wordTrace_append hprefix tailTrace_3438181
  have hstable : (prefixWord ++ tailWord_3438181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438181).length < 2 ^ (prefixWord ++ tailWord_3438181).sum := by decide
  have hdescent : baseEnd_3438181 < baseStart_3438181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 7, 4]
def baseStart_3438207 : Nat := 118140960795 + 3438207 * 2 ^ 59
def prefixEnd_3438207 : Nat := 4983230072969 + 3 ^ 40 * 3438207 * 2
def baseEnd_3438207 : Nat := 1176968520435423155333653

theorem tailTrace_3438207 : CollatzResearch.WordTrace tailWord_3438207 prefixEnd_3438207 1176968520435423155333653 := by
  unfold tailWord_3438207
  simp only [CollatzResearch.WordTrace]
  refine ⟨125401711454970712851408875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83601140969980475234272583 125401711454970712851408875)
  ·
    refine ⟨188102567182456069277113313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125401711454970712851408875 188102567182456069277113313)
    ·
      refine ⟨141076925386842051957834985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188102567182456069277113313 141076925386842051957834985)
      ·
        refine ⟨105807694040131538968376239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141076925386842051957834985 105807694040131538968376239)
        ·
          refine ⟨158711541060197308452564359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105807694040131538968376239 158711541060197308452564359)
          ·
            refine ⟨238067311590295962678846539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158711541060197308452564359 238067311590295962678846539)
            ·
              refine ⟨357100967385443944018269809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238067311590295962678846539 357100967385443944018269809)
              ·
                refine ⟨267825725539082958013702357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357100967385443944018269809 267825725539082958013702357)
                ·
                  refine ⟨6277165442322256828446149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 267825725539082958013702357 6277165442322256828446149)
                  ·
                    refine ⟨1176968520435423155333653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6277165442322256828446149 1176968520435423155333653)
                    ·
                      rfl

theorem cell22_3438207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_3438207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438207 prefixEnd_3438207 := by exact prefixLift 3438207
  have htrace : WordTrace (prefixWord ++ tailWord_3438207) baseStart_3438207 baseEnd_3438207 := by
    simpa [prefixWord, tailWord_3438207, baseEnd_3438207] using wordTrace_append hprefix tailTrace_3438207
  have hstable : (prefixWord ++ tailWord_3438207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438207).length < 2 ^ (prefixWord ++ tailWord_3438207).sum := by decide
  have hdescent : baseEnd_3438207 < baseStart_3438207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438284 : List Nat := [2, 2, 1, 5, 2, 10]
def baseStart_3438284 : Nat := 118140960795 + 3438284 * 2 ^ 59
def prefixEnd_3438284 : Nat := 4983230072969 + 3 ^ 40 * 3438284 * 2
def baseEnd_3438284 : Nat := 14530800976654575569857

theorem tailTrace_3438284 : CollatzResearch.WordTrace tailWord_3438284 prefixEnd_3438284 14530800976654575569857 := by
  unfold tailWord_3438284
  simp only [CollatzResearch.WordTrace]
  refine ⟨62702259937845877500980953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83603013250461170001307937 62702259937845877500980953)
  ·
    refine ⟨47026694953384408125735715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62702259937845877500980953 47026694953384408125735715)
    ·
      refine ⟨70540042430076612188603573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47026694953384408125735715 70540042430076612188603573)
      ·
        refine ⟨6613128977819682392681585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70540042430076612188603573 6613128977819682392681585)
        ·
          refine ⟨4959846733364761794511189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6613128977819682392681585 4959846733364761794511189)
          ·
            refine ⟨14530800976654575569857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4959846733364761794511189 14530800976654575569857)
            ·
              rfl

theorem cell22_3438284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 10].length) (baseStart_3438284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438284 prefixEnd_3438284 := by exact prefixLift 3438284
  have htrace : WordTrace (prefixWord ++ tailWord_3438284) baseStart_3438284 baseEnd_3438284 := by
    simpa [prefixWord, tailWord_3438284, baseEnd_3438284] using wordTrace_append hprefix tailTrace_3438284
  have hstable : (prefixWord ++ tailWord_3438284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438284).length < 2 ^ (prefixWord ++ tailWord_3438284).sum := by decide
  have hdescent : baseEnd_3438284 < baseStart_3438284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438290 : List Nat := [3, 2, 2, 2, 2, 3, 2, 2, 4]
def baseStart_3438290 : Nat := 118140960795 + 3438290 * 2 ^ 59
def prefixEnd_3438290 : Nat := 4983230072969 + 3 ^ 40 * 3438290 * 2
def baseEnd_3438290 : Nat := 392332311010546201836133

theorem tailTrace_3438290 : CollatzResearch.WordTrace tailWord_3438290 prefixEnd_3438290 392332311010546201836133 := by
  unfold tailWord_3438290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31351184678417504506670081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83603159142446678684453549 31351184678417504506670081)
  ·
    refine ⟨23513388508813128380002561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31351184678417504506670081 23513388508813128380002561)
    ·
      refine ⟨17635041381609846285001921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23513388508813128380002561 17635041381609846285001921)
      ·
        refine ⟨13226281036207384713751441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17635041381609846285001921 13226281036207384713751441)
        ·
          refine ⟨9919710777155538535313581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13226281036207384713751441 9919710777155538535313581)
          ·
            refine ⟨3719891541433326950742593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9919710777155538535313581 3719891541433326950742593)
            ·
              refine ⟨2789918656074995213056945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3719891541433326950742593 2789918656074995213056945)
              ·
                refine ⟨2092438992056246409792709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2789918656074995213056945 2092438992056246409792709)
                ·
                  refine ⟨392332311010546201836133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092438992056246409792709 392332311010546201836133)
                  ·
                    rfl

theorem cell22_3438290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_3438290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438290 prefixEnd_3438290 := by exact prefixLift 3438290
  have htrace : WordTrace (prefixWord ++ tailWord_3438290) baseStart_3438290 baseEnd_3438290 := by
    simpa [prefixWord, tailWord_3438290, baseEnd_3438290] using wordTrace_append hprefix tailTrace_3438290
  have hstable : (prefixWord ++ tailWord_3438290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438290).length < 2 ^ (prefixWord ++ tailWord_3438290).sum := by decide
  have hdescent : baseEnd_3438290 < baseStart_3438290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438344 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_3438344 : Nat := 118140960795 + 3438344 * 2 ^ 59
def prefixEnd_3438344 : Nat := 4983230072969 + 3 ^ 40 * 3438344 * 2
def baseEnd_3438344 : Nat := 1177015418335200464658233

theorem tailTrace_3438344 : CollatzResearch.WordTrace tailWord_3438344 prefixEnd_3438344 1177015418335200464658233 := by
  unfold tailWord_3438344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62703354127737192624573043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83604472170316256832764057 62703354127737192624573043)
  ·
    refine ⟨94055031191605788936859565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62703354127737192624573043 94055031191605788936859565)
    ·
      refine ⟨35270636696852170851322337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94055031191605788936859565 35270636696852170851322337)
      ·
        refine ⟨26452977522639128138491753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35270636696852170851322337 26452977522639128138491753)
        ·
          refine ⟨19839733141979346103868815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26452977522639128138491753 19839733141979346103868815)
          ·
            refine ⟨29759599712969019155803223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19839733141979346103868815 29759599712969019155803223)
            ·
              refine ⟨44639399569453528733704835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29759599712969019155803223 44639399569453528733704835)
              ·
                refine ⟨66959099354180293100557253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44639399569453528733704835 66959099354180293100557253)
                ·
                  refine ⟨12554831128908804956354485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66959099354180293100557253 12554831128908804956354485)
                  ·
                    refine ⟨1177015418335200464658233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12554831128908804956354485 1177015418335200464658233)
                    ·
                      rfl

theorem cell22_3438344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_3438344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438344 prefixEnd_3438344 := by exact prefixLift 3438344
  have htrace : WordTrace (prefixWord ++ tailWord_3438344) baseStart_3438344 baseEnd_3438344 := by
    simpa [prefixWord, tailWord_3438344, baseEnd_3438344] using wordTrace_append hprefix tailTrace_3438344
  have hstable : (prefixWord ++ tailWord_3438344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438344).length < 2 ^ (prefixWord ++ tailWord_3438344).sum := by decide
  have hdescent : baseEnd_3438344 < baseStart_3438344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438346 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_3438346 : Nat := 118140960795 + 3438346 * 2 ^ 59
def prefixEnd_3438346 : Nat := 4983230072969 + 3 ^ 40 * 3438346 * 2
def baseEnd_3438346 : Nat := 392338700992024375369409

theorem tailTrace_3438346 : CollatzResearch.WordTrace tailWord_3438346 prefixEnd_3438346 392338700992024375369409 := by
  unfold tailWord_3438346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31351695300366784897679723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83604520800978093060479261 31351695300366784897679723)
  ·
    refine ⟨47027542950550177346519585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31351695300366784897679723 47027542950550177346519585)
    ·
      refine ⟨35270657212912633009889689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47027542950550177346519585 35270657212912633009889689)
      ·
        refine ⟨26452992909684474757417267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35270657212912633009889689 26452992909684474757417267)
        ·
          refine ⟨39679489364526712136125901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26452992909684474757417267 39679489364526712136125901)
          ·
            refine ⟨14879808511697517051047213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39679489364526712136125901 14879808511697517051047213)
            ·
              refine ⟨5579928191886568894142705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14879808511697517051047213 5579928191886568894142705)
              ·
                refine ⟨4184946143914926670607029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579928191886568894142705 4184946143914926670607029)
                ·
                  refine ⟨392338700992024375369409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4184946143914926670607029 392338700992024375369409)
                  ·
                    rfl

theorem cell22_3438346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_3438346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438346 prefixEnd_3438346 := by exact prefixLift 3438346
  have htrace : WordTrace (prefixWord ++ tailWord_3438346) baseStart_3438346 baseEnd_3438346 := by
    simpa [prefixWord, tailWord_3438346, baseEnd_3438346] using wordTrace_append hprefix tailTrace_3438346
  have hstable : (prefixWord ++ tailWord_3438346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438346).length < 2 ^ (prefixWord ++ tailWord_3438346).sum := by decide
  have hdescent : baseEnd_3438346 < baseStart_3438346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438391 : List Nat := [1, 1, 3, 1, 2, 1, 2, 7, 4]
def baseStart_3438391 : Nat := 118140960795 + 3438391 * 2 ^ 59
def prefixEnd_3438391 : Nat := 4983230072969 + 3 ^ 40 * 3438391 * 2
def baseEnd_3438391 : Nat := 392343835798569336244363

theorem tailTrace_3438391 : CollatzResearch.WordTrace tailWord_3438391 prefixEnd_3438391 392343835798569336244363 := by
  unfold tailWord_3438391
  simp only [CollatzResearch.WordTrace]
  refine ⟨125408422486304112276107027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83605614990869408184071351 125408422486304112276107027)
  ·
    refine ⟨188112633729456168414160541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125408422486304112276107027 188112633729456168414160541)
    ·
      refine ⟨70542237648546063155310203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188112633729456168414160541 70542237648546063155310203)
      ·
        refine ⟨105813356472819094732965305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70542237648546063155310203 105813356472819094732965305)
        ·
          refine ⟨79360017354614321049723979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105813356472819094732965305 79360017354614321049723979)
          ·
            refine ⟨119040026031921481574585969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79360017354614321049723979 119040026031921481574585969)
            ·
              refine ⟨89280019523941111180939477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119040026031921481574585969 89280019523941111180939477)
              ·
                refine ⟨2092500457592369793303269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 89280019523941111180939477 2092500457592369793303269)
                ·
                  refine ⟨392343835798569336244363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092500457592369793303269 392343835798569336244363)
                  ·
                    rfl

theorem cell22_3438391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 7, 4].length) (baseStart_3438391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438391 prefixEnd_3438391 := by exact prefixLift 3438391
  have htrace : WordTrace (prefixWord ++ tailWord_3438391) baseStart_3438391 baseEnd_3438391 := by
    simpa [prefixWord, tailWord_3438391, baseEnd_3438391] using wordTrace_append hprefix tailTrace_3438391
  have hstable : (prefixWord ++ tailWord_3438391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438391).length < 2 ^ (prefixWord ++ tailWord_3438391).sum := by decide
  have hdescent : baseEnd_3438391 < baseStart_3438391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438481 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 5]
def baseStart_3438481 : Nat := 118140960795 + 3438481 * 2 ^ 59
def prefixEnd_3438481 : Nat := 4983230072969 + 3 ^ 40 * 3438481 * 2
def baseEnd_3438481 : Nat := 392354105411659257994271

theorem tailTrace_3438481 : CollatzResearch.WordTrace tailWord_3438481 prefixEnd_3438481 392354105411659257994271 := by
  unfold tailWord_3438481
  simp only [CollatzResearch.WordTrace]
  refine ⟨125411705055978057646883297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83607803370652038431255531 125411705055978057646883297)
  ·
    refine ⟨94058778791983543235162473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125411705055978057646883297 94058778791983543235162473)
    ·
      refine ⟨70544084093987657426371855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94058778791983543235162473 70544084093987657426371855)
      ·
        refine ⟨105816126140981486139557783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70544084093987657426371855 105816126140981486139557783)
        ·
          refine ⟨158724189211472229209336675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105816126140981486139557783 158724189211472229209336675)
          ·
            refine ⟨238086283817208343814005013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158724189211472229209336675 238086283817208343814005013)
            ·
              refine ⟨11160294553931641116281485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 238086283817208343814005013 11160294553931641116281485)
              ·
                refine ⟨4185110457724365418605557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11160294553931641116281485 4185110457724365418605557)
                ·
                  refine ⟨392354105411659257994271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4185110457724365418605557 392354105411659257994271)
                  ·
                    rfl

theorem cell22_3438481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_3438481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438481 prefixEnd_3438481 := by exact prefixLift 3438481
  have htrace : WordTrace (prefixWord ++ tailWord_3438481) baseStart_3438481 baseEnd_3438481 := by
    simpa [prefixWord, tailWord_3438481, baseEnd_3438481] using wordTrace_append hprefix tailTrace_3438481
  have hstable : (prefixWord ++ tailWord_3438481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438481).length < 2 ^ (prefixWord ++ tailWord_3438481).sum := by decide
  have hdescent : baseEnd_3438481 < baseStart_3438481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438577 : List Nat := [1, 2, 2, 2, 5, 1, 3, 2, 4]
def baseStart_3438577 : Nat := 118140960795 + 3438577 * 2 ^ 59
def prefixEnd_3438577 : Nat := 4983230072969 + 3 ^ 40 * 3438577 * 2
def baseEnd_3438577 : Nat := 392365059665621841194173

theorem tailTrace_3438577 : CollatzResearch.WordTrace tailWord_3438577 prefixEnd_3438577 392365059665621841194173 := by
  unfold tailWord_3438577
  simp only [CollatzResearch.WordTrace]
  refine ⟨125415206463630266042377985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83610137642420177361585323 125415206463630266042377985)
  ·
    refine ⟨94061404847722699531783489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125415206463630266042377985 94061404847722699531783489)
    ·
      refine ⟨70546053635792024648837617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94061404847722699531783489 70546053635792024648837617)
      ·
        refine ⟨52909540226844018486628213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70546053635792024648837617 52909540226844018486628213)
        ·
          refine ⟨4960269396266626733121395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52909540226844018486628213 4960269396266626733121395)
          ·
            refine ⟨7440404094399940099682093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960269396266626733121395 7440404094399940099682093)
            ·
              refine ⟨2790151535399977537380785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7440404094399940099682093 2790151535399977537380785)
              ·
                refine ⟨2092613651549983153035589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790151535399977537380785 2092613651549983153035589)
                ·
                  refine ⟨392365059665621841194173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092613651549983153035589 392365059665621841194173)
                  ·
                    rfl

theorem cell22_3438577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_3438577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438577 prefixEnd_3438577 := by exact prefixLift 3438577
  have htrace : WordTrace (prefixWord ++ tailWord_3438577) baseStart_3438577 baseEnd_3438577 := by
    simpa [prefixWord, tailWord_3438577, baseEnd_3438577] using wordTrace_append hprefix tailTrace_3438577
  have hstable : (prefixWord ++ tailWord_3438577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438577).length < 2 ^ (prefixWord ++ tailWord_3438577).sum := by decide
  have hdescent : baseEnd_3438577 < baseStart_3438577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438603 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 5, 3]
def baseStart_3438603 : Nat := 118140960795 + 3438603 * 2 ^ 59
def prefixEnd_3438603 : Nat := 4983230072969 + 3 ^ 40 * 3438603 * 2
def baseEnd_3438603 : Nat := 1177104079328210122432439

theorem tailTrace_3438603 : CollatzResearch.WordTrace tailWord_3438603 prefixEnd_3438603 1177104079328210122432439 := by
  unfold tailWord_3438603
  simp only [CollatzResearch.WordTrace]
  refine ⟨125416154761536072482824463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83610769841024048321882975 125416154761536072482824463)
  ·
    refine ⟨188124232142304108724236695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125416154761536072482824463 188124232142304108724236695)
    ·
      refine ⟨282186348213456163086355043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188124232142304108724236695 282186348213456163086355043)
      ·
        refine ⟨423279522320184244629532565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282186348213456163086355043 423279522320184244629532565)
        ·
          refine ⟨19841227608758636467009339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 423279522320184244629532565 19841227608758636467009339)
          ·
            refine ⟨29761841413137954700514009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19841227608758636467009339 29761841413137954700514009)
            ·
              refine ⟨22321381059853466025385507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29761841413137954700514009 22321381059853466025385507)
              ·
                refine ⟨33482071589780199038078261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22321381059853466025385507 33482071589780199038078261)
                ·
                  refine ⟨3138944211541893659819837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33482071589780199038078261 3138944211541893659819837)
                  ·
                    refine ⟨1177104079328210122432439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3138944211541893659819837 1177104079328210122432439)
                    ·
                      rfl

theorem cell22_3438603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 3].length) (baseStart_3438603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438603 prefixEnd_3438603 := by exact prefixLift 3438603
  have htrace : WordTrace (prefixWord ++ tailWord_3438603) baseStart_3438603 baseEnd_3438603 := by
    simpa [prefixWord, tailWord_3438603, baseEnd_3438603] using wordTrace_append hprefix tailTrace_3438603
  have hstable : (prefixWord ++ tailWord_3438603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438603).length < 2 ^ (prefixWord ++ tailWord_3438603).sum := by decide
  have hdescent : baseEnd_3438603 < baseStart_3438603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438663 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3438663 : Nat := 118140960795 + 3438663 * 2 ^ 59
def prefixEnd_3438663 : Nat := 4983230072969 + 3 ^ 40 * 3438663 * 2
def baseEnd_3438663 : Nat := 1177124618554389965932255

theorem tailTrace_3438663 : CollatzResearch.WordTrace tailWord_3438663 prefixEnd_3438663 1177124618554389965932255 := by
  unfold tailWord_3438663
  simp only [CollatzResearch.WordTrace]
  refine ⟨125418343141318702730008643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83612228760879135153339095 125418343141318702730008643)
  ·
    refine ⟨188127514711978054095012965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125418343141318702730008643 188127514711978054095012965)
    ·
      refine ⟨35273909008495885142814931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188127514711978054095012965 35273909008495885142814931)
      ·
        refine ⟨52910863512743827714222397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35273909008495885142814931 52910863512743827714222397)
        ·
          refine ⟨19841573817278935392833399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52910863512743827714222397 19841573817278935392833399)
          ·
            refine ⟨29762360725918403089250099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19841573817278935392833399 29762360725918403089250099)
            ·
              refine ⟨44643541088877604633875149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29762360725918403089250099 44643541088877604633875149)
              ·
                refine ⟨16741327908329101737703181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44643541088877604633875149 16741327908329101737703181)
                ·
                  refine ⟨6277997965623413151638693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16741327908329101737703181 6277997965623413151638693)
                  ·
                    refine ⟨1177124618554389965932255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6277997965623413151638693 1177124618554389965932255)
                    ·
                      rfl

theorem cell22_3438663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3438663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438663 prefixEnd_3438663 := by exact prefixLift 3438663
  have htrace : WordTrace (prefixWord ++ tailWord_3438663) baseStart_3438663 baseEnd_3438663 := by
    simpa [prefixWord, tailWord_3438663, baseEnd_3438663] using wordTrace_append hprefix tailTrace_3438663
  have hstable : (prefixWord ++ tailWord_3438663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438663).length < 2 ^ (prefixWord ++ tailWord_3438663).sum := by decide
  have hdescent : baseEnd_3438663 < baseStart_3438663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438680 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_3438680 : Nat := 118140960795 + 3438680 * 2 ^ 59
def prefixEnd_3438680 : Nat := 4983230072969 + 3 ^ 40 * 3438680 * 2
def baseEnd_3438680 : Nat := 1177130438001807588257203

theorem tailTrace_3438680 : CollatzResearch.WordTrace tailWord_3438680 prefixEnd_3438680 1177130438001807588257203 := by
  unfold tailWord_3438680
  simp only [CollatzResearch.WordTrace]
  refine ⟨62709481591128557316688747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83612642121504743088918329 62709481591128557316688747)
  ·
    refine ⟨94064222386692835975033121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62709481591128557316688747 94064222386692835975033121)
    ·
      refine ⟨70548166790019626981274841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94064222386692835975033121 70548166790019626981274841)
      ·
        refine ⟨52911125092514720235956131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70548166790019626981274841 52911125092514720235956131)
        ·
          refine ⟨79366687638772080353934197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52911125092514720235956131 79366687638772080353934197)
          ·
            refine ⟨7440626966134882533181331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79366687638772080353934197 7440626966134882533181331)
            ·
              refine ⟨11160940449202323799771997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440626966134882533181331 11160940449202323799771997)
              ·
                refine ⟨4185352668450871424914499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11160940449202323799771997 4185352668450871424914499)
                ·
                  refine ⟨6278029002676307137371749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185352668450871424914499 6278029002676307137371749)
                  ·
                    refine ⟨1177130438001807588257203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6278029002676307137371749 1177130438001807588257203)
                    ·
                      rfl

theorem cell22_3438680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_3438680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438680 prefixEnd_3438680 := by exact prefixLift 3438680
  have htrace : WordTrace (prefixWord ++ tailWord_3438680) baseStart_3438680 baseEnd_3438680 := by
    simpa [prefixWord, tailWord_3438680, baseEnd_3438680] using wordTrace_append hprefix tailTrace_3438680
  have hstable : (prefixWord ++ tailWord_3438680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438680).length < 2 ^ (prefixWord ++ tailWord_3438680).sum := by decide
  have hdescent : baseEnd_3438680 < baseStart_3438680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438695 : List Nat := [1, 1, 5, 1, 1, 2, 1, 6, 4]
def baseStart_3438695 : Nat := 118140960795 + 3438695 * 2 ^ 59
def prefixEnd_3438695 : Nat := 4983230072969 + 3 ^ 40 * 3438695 * 2
def baseEnd_3438695 : Nat := 392378524269450849710719

theorem tailTrace_3438695 : CollatzResearch.WordTrace tailWord_3438695 prefixEnd_3438695 392378524269450849710719 := by
  unfold tailWord_3438695
  simp only [CollatzResearch.WordTrace]
  refine ⟨125419510277202772195173539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83613006851468514796782359 125419510277202772195173539)
  ·
    refine ⟨188129265415804158292760309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125419510277202772195173539 188129265415804158292760309)
    ·
      refine ⟨17637118632731639839946279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188129265415804158292760309 17637118632731639839946279)
      ·
        refine ⟨26455677949097459759919419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17637118632731639839946279 26455677949097459759919419)
        ·
          refine ⟨39683516923646189639879129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26455677949097459759919419 39683516923646189639879129)
          ·
            refine ⟨29762637692734642229909347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39683516923646189639879129 29762637692734642229909347)
            ·
              refine ⟨44643956539101963344864021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29762637692734642229909347 44643956539101963344864021)
              ·
                refine ⟨2092685462770404531790501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44643956539101963344864021 2092685462770404531790501)
                ·
                  refine ⟨392378524269450849710719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092685462770404531790501 392378524269450849710719)
                  ·
                    rfl

theorem cell22_3438695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 6, 4].length) (baseStart_3438695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438695 prefixEnd_3438695 := by exact prefixLift 3438695
  have htrace : WordTrace (prefixWord ++ tailWord_3438695) baseStart_3438695 baseEnd_3438695 := by
    simpa [prefixWord, tailWord_3438695, baseEnd_3438695] using wordTrace_append hprefix tailTrace_3438695
  have hstable : (prefixWord ++ tailWord_3438695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438695).length < 2 ^ (prefixWord ++ tailWord_3438695).sum := by decide
  have hdescent : baseEnd_3438695 < baseStart_3438695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438723 : List Nat := [1, 1, 1, 3, 3, 4, 1, 8]
def baseStart_3438723 : Nat := 118140960795 + 3438723 * 2 ^ 59
def prefixEnd_3438723 : Nat := 4983230072969 + 3 ^ 40 * 3438723 * 2
def baseEnd_3438723 : Nat := 130793906420063312159119

theorem tailTrace_3438723 : CollatzResearch.WordTrace tailWord_3438723 prefixEnd_3438723 130793906420063312159119 := by
  unfold tailWord_3438723
  simp only [CollatzResearch.WordTrace]
  refine ⟨125420531521101332977192823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83613687680734221984795215 125420531521101332977192823)
  ·
    refine ⟨188130797281651999465789235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125420531521101332977192823 188130797281651999465789235)
    ·
      refine ⟨282196195922477999198683853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188130797281651999465789235 282196195922477999198683853)
      ·
        refine ⟨105823573470929249699506445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282196195922477999198683853 105823573470929249699506445)
        ·
          refine ⟨39683840051598468637314917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105823573470929249699506445 39683840051598468637314917)
          ·
            refine ⟨7440720009674712869496547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39683840051598468637314917 7440720009674712869496547)
            ·
              refine ⟨11161080014512069304244821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440720009674712869496547 11161080014512069304244821)
              ·
                refine ⟨130793906420063312159119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11161080014512069304244821 130793906420063312159119)
                ·
                  rfl

theorem cell22_3438723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 8].length) (baseStart_3438723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438723 prefixEnd_3438723 := by exact prefixLift 3438723
  have htrace : WordTrace (prefixWord ++ tailWord_3438723) baseStart_3438723 baseEnd_3438723 := by
    simpa [prefixWord, tailWord_3438723, baseEnd_3438723] using wordTrace_append hprefix tailTrace_3438723
  have hstable : (prefixWord ++ tailWord_3438723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438723).length < 2 ^ (prefixWord ++ tailWord_3438723).sum := by decide
  have hdescent : baseEnd_3438723 < baseStart_3438723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438783 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_3438783 : Nat := 118140960795 + 3438783 * 2 ^ 59
def prefixEnd_3438783 : Nat := 4983230072969 + 3 ^ 40 * 3438783 * 2
def baseEnd_3438783 : Nat := 1177165697006749652931887

theorem tailTrace_3438783 : CollatzResearch.WordTrace tailWord_3438783 prefixEnd_3438783 1177165697006749652931887 := by
  unfold tailWord_3438783
  simp only [CollatzResearch.WordTrace]
  refine ⟨125422719900883963224377003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83615146600589308816251335 125422719900883963224377003)
  ·
    refine ⟨188134079851325944836565505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125422719900883963224377003 188134079851325944836565505)
    ·
      refine ⟨141100559888494458627424129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188134079851325944836565505 141100559888494458627424129)
      ·
        refine ⟨105825419916370843970568097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141100559888494458627424129 105825419916370843970568097)
        ·
          refine ⟨79369064937278132977926073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105825419916370843970568097 79369064937278132977926073)
          ·
            refine ⟨59526798702958599733444555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79369064937278132977926073 59526798702958599733444555)
            ·
              refine ⟨89290198054437899600166833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59526798702958599733444555 89290198054437899600166833)
              ·
                refine ⟨66967648540828424700125125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89290198054437899600166833 66967648540828424700125125)
                ·
                  refine ⟨12556434101405329631273461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66967648540828424700125125 12556434101405329631273461)
                  ·
                    refine ⟨1177165697006749652931887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12556434101405329631273461 1177165697006749652931887)
                    ·
                      rfl

theorem cell22_3438783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_3438783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438783 prefixEnd_3438783 := by exact prefixLift 3438783
  have htrace : WordTrace (prefixWord ++ tailWord_3438783) baseStart_3438783 baseEnd_3438783 := by
    simpa [prefixWord, tailWord_3438783, baseEnd_3438783] using wordTrace_append hprefix tailTrace_3438783
  have hstable : (prefixWord ++ tailWord_3438783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438783).length < 2 ^ (prefixWord ++ tailWord_3438783).sum := by decide
  have hdescent : baseEnd_3438783 < baseStart_3438783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438802 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3438802 : Nat := 118140960795 + 3438802 * 2 ^ 59
def prefixEnd_3438802 : Nat := 4983230072969 + 3 ^ 40 * 3438802 * 2
def baseEnd_3438802 : Nat := 392390733698346645568943

theorem tailTrace_3438802 : CollatzResearch.WordTrace tailWord_3438802 prefixEnd_3438802 392390733698346645568943 := by
  unfold tailWord_3438802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31355853221953782367329665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83615608591876752979545773 31355853221953782367329665)
  ·
    refine ⟨23516889916465336775497249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31355853221953782367329665 23516889916465336775497249)
    ·
      refine ⟨17637667437349002581622937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23516889916465336775497249 17637667437349002581622937)
      ·
        refine ⟨13228250578011751936217203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17637667437349002581622937 13228250578011751936217203)
        ·
          refine ⟨19842375867017627904325805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13228250578011751936217203 19842375867017627904325805)
          ·
            refine ⟨7440890950131610464122177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19842375867017627904325805 7440890950131610464122177)
            ·
              refine ⟨5580668212598707848091633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7440890950131610464122177 5580668212598707848091633)
              ·
                refine ⟨4185501159449030886068725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5580668212598707848091633 4185501159449030886068725)
                ·
                  refine ⟨392390733698346645568943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4185501159449030886068725 392390733698346645568943)
                  ·
                    rfl

theorem cell22_3438802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3438802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438802 prefixEnd_3438802 := by exact prefixLift 3438802
  have htrace : WordTrace (prefixWord ++ tailWord_3438802) baseStart_3438802 baseEnd_3438802 := by
    simpa [prefixWord, tailWord_3438802, baseEnd_3438802] using wordTrace_append hprefix tailTrace_3438802
  have hstable : (prefixWord ++ tailWord_3438802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438802).length < 2 ^ (prefixWord ++ tailWord_3438802).sum := by decide
  have hdescent : baseEnd_3438802 < baseStart_3438802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438847 : List Nat := [1, 1, 2, 2, 1, 4, 4, 3, 4]
def baseStart_3438847 : Nat := 118140960795 + 3438847 * 2 ^ 59
def prefixEnd_3438847 : Nat := 4983230072969 + 3 ^ 40 * 3438847 * 2
def baseEnd_3438847 : Nat := 392395868504891606443897

theorem tailTrace_3438847 : CollatzResearch.WordTrace tailWord_3438847 prefixEnd_3438847 392395868504891606443897 := by
  unfold tailWord_3438847
  simp only [CollatzResearch.WordTrace]
  refine ⟨125425054172652102154706795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83616702781768068103137863 125425054172652102154706795)
  ·
    refine ⟨188137581258978153232060193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125425054172652102154706795 188137581258978153232060193)
    ·
      refine ⟨141103185944233614924045145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188137581258978153232060193 141103185944233614924045145)
      ·
        refine ⟨105827389458175211193033859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141103185944233614924045145 105827389458175211193033859)
        ·
          refine ⟨158741084187262816789550789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105827389458175211193033859 158741084187262816789550789)
          ·
            refine ⟨29763953285111778148040773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158741084187262816789550789 29763953285111778148040773)
            ·
              refine ⟨5580741240958458402757645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29763953285111778148040773 5580741240958458402757645)
              ·
                refine ⟨2092777965359421901034117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5580741240958458402757645 2092777965359421901034117)
                ·
                  refine ⟨392395868504891606443897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092777965359421901034117 392395868504891606443897)
                  ·
                    rfl

theorem cell22_3438847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 3, 4].length) (baseStart_3438847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438847 prefixEnd_3438847 := by exact prefixLift 3438847
  have htrace : WordTrace (prefixWord ++ tailWord_3438847) baseStart_3438847 baseEnd_3438847 := by
    simpa [prefixWord, tailWord_3438847, baseEnd_3438847] using wordTrace_append hprefix tailTrace_3438847
  have hstable : (prefixWord ++ tailWord_3438847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438847).length < 2 ^ (prefixWord ++ tailWord_3438847).sum := by decide
  have hdescent : baseEnd_3438847 < baseStart_3438847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438860 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_3438860 : Nat := 118140960795 + 3438860 * 2 ^ 59
def prefixEnd_3438860 : Nat := 4983230072969 + 3 ^ 40 * 3438860 * 2
def baseEnd_3438860 : Nat := 1177192055680347118756651

theorem tailTrace_3438860 : CollatzResearch.WordTrace tailWord_3438860 prefixEnd_3438860 1177192055680347118756651 := by
  unfold tailWord_3438860
  simp only [CollatzResearch.WordTrace]
  refine ⟨62712764160802502687465017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83617018881070003583286689 62712764160802502687465017)
  ·
    refine ⟨47034573120601877015598763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62712764160802502687465017 47034573120601877015598763)
    ·
      refine ⟨70551859680902815523398145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47034573120601877015598763 70551859680902815523398145)
      ·
        refine ⟨52913894760677111642548609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70551859680902815523398145 52913894760677111642548609)
        ·
          refine ⟨39685421070507833731911457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52913894760677111642548609 39685421070507833731911457)
          ·
            refine ⟨29764065802880875298933593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39685421070507833731911457 29764065802880875298933593)
            ·
              refine ⟨22323049352160656474200195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29764065802880875298933593 22323049352160656474200195)
              ·
                refine ⟨33484574028240984711300293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22323049352160656474200195 33484574028240984711300293)
                ·
                  refine ⟨6278357630295184633368805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33484574028240984711300293 6278357630295184633368805)
                  ·
                    refine ⟨1177192055680347118756651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6278357630295184633368805 1177192055680347118756651)
                    ·
                      rfl

theorem cell22_3438860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_3438860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438860 prefixEnd_3438860 := by exact prefixLift 3438860
  have htrace : WordTrace (prefixWord ++ tailWord_3438860) baseStart_3438860 baseEnd_3438860 := by
    simpa [prefixWord, tailWord_3438860, baseEnd_3438860] using wordTrace_append hprefix tailTrace_3438860
  have hstable : (prefixWord ++ tailWord_3438860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438860).length < 2 ^ (prefixWord ++ tailWord_3438860).sum := by decide
  have hdescent : baseEnd_3438860 < baseStart_3438860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438862 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3438862 : Nat := 118140960795 + 3438862 * 2 ^ 59
def prefixEnd_3438862 : Nat := 4983230072969 + 3 ^ 40 * 3438862 * 2
def baseEnd_3438862 : Nat := 1177192740321219780206645

theorem tailTrace_3438862 : CollatzResearch.WordTrace tailWord_3438862 prefixEnd_3438862 1177192740321219780206645 := by
  unfold tailWord_3438862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15678200158449719964562855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83617067511731839811001893 15678200158449719964562855)
  ·
    refine ⟨23517300237674579946844283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15678200158449719964562855 23517300237674579946844283)
    ·
      refine ⟨35275950356511869920266425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23517300237674579946844283 35275950356511869920266425)
      ·
        refine ⟨26456962767383902440199819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35275950356511869920266425 26456962767383902440199819)
        ·
          refine ⟨39685444151075853660299729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26456962767383902440199819 39685444151075853660299729)
          ·
            refine ⟨29764083113306890245224797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39685444151075853660299729 29764083113306890245224797)
            ·
              refine ⟨11161531167490083841959299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29764083113306890245224797 11161531167490083841959299)
              ·
                refine ⟨16742296751235125762938949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161531167490083841959299 16742296751235125762938949)
                ·
                  refine ⟨3139180640856586080551053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16742296751235125762938949 3139180640856586080551053)
                  ·
                    refine ⟨1177192740321219780206645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139180640856586080551053 1177192740321219780206645)
                    ·
                      rfl

theorem cell22_3438862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3438862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438862 prefixEnd_3438862 := by exact prefixLift 3438862
  have htrace : WordTrace (prefixWord ++ tailWord_3438862) baseStart_3438862 baseEnd_3438862 := by
    simpa [prefixWord, tailWord_3438862, baseEnd_3438862] using wordTrace_append hprefix tailTrace_3438862
  have hstable : (prefixWord ++ tailWord_3438862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438862).length < 2 ^ (prefixWord ++ tailWord_3438862).sum := by decide
  have hdescent : baseEnd_3438862 < baseStart_3438862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438920 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_3438920 : Nat := 118140960795 + 3438920 * 2 ^ 59
def prefixEnd_3438920 : Nat := 4983230072969 + 3 ^ 40 * 3438920 * 2
def baseEnd_3438920 : Nat := 392404198302175654085489

theorem tailTrace_3438920 : CollatzResearch.WordTrace tailWord_3438920 prefixEnd_3438920 392404198302175654085489 := by
  unfold tailWord_3438920
  simp only [CollatzResearch.WordTrace]
  refine ⟨62713858350693817811057107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83618477800925090414742809 62713858350693817811057107)
  ·
    refine ⟨94070787526040726716585661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62713858350693817811057107 94070787526040726716585661)
    ·
      refine ⟨35276545322265272518719623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94070787526040726716585661 35276545322265272518719623)
      ·
        refine ⟨52914817983397908778079435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35276545322265272518719623 52914817983397908778079435)
        ·
          refine ⟨79372226975096863167119153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52914817983397908778079435 79372226975096863167119153)
          ·
            refine ⟨59529170231322647375339365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79372226975096863167119153 59529170231322647375339365)
            ·
              refine ⟨11161719418372996382876131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59529170231322647375339365 11161719418372996382876131)
              ·
                refine ⟨16742579127559494574314197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161719418372996382876131 16742579127559494574314197)
                ·
                  refine ⟨392404198302175654085489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16742579127559494574314197 392404198302175654085489)
                  ·
                    rfl

theorem cell22_3438920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_3438920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438920 prefixEnd_3438920 := by exact prefixLift 3438920
  have htrace : WordTrace (prefixWord ++ tailWord_3438920) baseStart_3438920 baseEnd_3438920 := by
    simpa [prefixWord, tailWord_3438920, baseEnd_3438920] using wordTrace_append hprefix tailTrace_3438920
  have hstable : (prefixWord ++ tailWord_3438920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438920).length < 2 ^ (prefixWord ++ tailWord_3438920).sum := by decide
  have hdescent : baseEnd_3438920 < baseStart_3438920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438935 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_3438935 : Nat := 118140960795 + 3438935 * 2 ^ 59
def prefixEnd_3438935 : Nat := 4983230072969 + 3 ^ 40 * 3438935 * 2
def baseEnd_3438935 : Nat := 1177217729713071923131421

theorem tailTrace_3438935 : CollatzResearch.WordTrace tailWord_3438935 prefixEnd_3438935 1177217729713071923131421 := by
  unfold tailWord_3438935
  simp only [CollatzResearch.WordTrace]
  refine ⟨125428263796333293183910259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83618842530888862122606839 125428263796333293183910259)
  ·
    refine ⟨188142395694499939775865389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125428263796333293183910259 188142395694499939775865389)
    ·
      refine ⟨70553398385437477415949521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188142395694499939775865389 70553398385437477415949521)
      ·
        refine ⟨52915048789078108061962141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70553398385437477415949521 52915048789078108061962141)
        ·
          refine ⟨19843143295904290523235803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52915048789078108061962141 19843143295904290523235803)
          ·
            refine ⟨29764714943856435784853705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843143295904290523235803 29764714943856435784853705)
            ·
              refine ⟨22323536207892326838640279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29764714943856435784853705 22323536207892326838640279)
              ·
                refine ⟨33485304311838490257960419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22323536207892326838640279 33485304311838490257960419)
                ·
                  refine ⟨50227956467757735386940629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33485304311838490257960419 50227956467757735386940629)
                  ·
                    refine ⟨1177217729713071923131421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50227956467757735386940629 1177217729713071923131421)
                    ·
                      rfl

theorem cell22_3438935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_3438935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438935 prefixEnd_3438935 := by exact prefixLift 3438935
  have htrace : WordTrace (prefixWord ++ tailWord_3438935) baseStart_3438935 baseEnd_3438935 := by
    simpa [prefixWord, tailWord_3438935, baseEnd_3438935] using wordTrace_append hprefix tailTrace_3438935
  have hstable : (prefixWord ++ tailWord_3438935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438935).length < 2 ^ (prefixWord ++ tailWord_3438935).sum := by decide
  have hdescent : baseEnd_3438935 < baseStart_3438935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3438997 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3438997 : Nat := 118140960795 + 3438997 * 2 ^ 59
def prefixEnd_3438997 : Nat := 4983230072969 + 3 ^ 40 * 3438997 * 2
def baseEnd_3438997 : Nat := 1177238953580124428081231

theorem tailTrace_3438997 : CollatzResearch.WordTrace tailWord_3438997 prefixEnd_3438997 1177238953580124428081231 := by
  unfold tailWord_3438997
  simp only [CollatzResearch.WordTrace]
  refine ⟨125430525122108677772667245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83620350081405785181778163 125430525122108677772667245)
  ·
    refine ⟨47036446920790754164750217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125430525122108677772667245 47036446920790754164750217)
    ·
      refine ⟨35277335190593065623562663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47036446920790754164750217 35277335190593065623562663)
      ·
        refine ⟨52916002785889598435343995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35277335190593065623562663 52916002785889598435343995)
        ·
          refine ⟨79374004178834397653015993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52916002785889598435343995 79374004178834397653015993)
          ·
            refine ⟨59530503134125798239761995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79374004178834397653015993 59530503134125798239761995)
            ·
              refine ⟨89295754701188697359642993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59530503134125798239761995 89295754701188697359642993)
              ·
                refine ⟨66971816025891523019732245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89295754701188697359642993 66971816025891523019732245)
                ·
                  refine ⟨3139303876213665141549949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66971816025891523019732245 3139303876213665141549949)
                  ·
                    refine ⟨1177238953580124428081231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139303876213665141549949 1177238953580124428081231)
                    ·
                      rfl

theorem cell22_3438997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3438997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3438997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3438997 prefixEnd_3438997 := by exact prefixLift 3438997
  have htrace : WordTrace (prefixWord ++ tailWord_3438997) baseStart_3438997 baseEnd_3438997 := by
    simpa [prefixWord, tailWord_3438997, baseEnd_3438997] using wordTrace_append hprefix tailTrace_3438997
  have hstable : (prefixWord ++ tailWord_3438997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3438997).length < 2 ^ (prefixWord ++ tailWord_3438997).sum := by decide
  have hdescent : baseEnd_3438997 < baseStart_3438997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3438997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439016 : List Nat := [2, 1, 6, 1, 1, 1, 1, 5, 4]
def baseStart_3439016 : Nat := 118140960795 + 3439016 * 2 ^ 59
def prefixEnd_3439016 : Nat := 4983230072969 + 3 ^ 40 * 3439016 * 2
def baseEnd_3439016 : Nat := 392415152556138237285391

theorem tailTrace_3439016 : CollatzResearch.WordTrace tailWord_3439016 prefixEnd_3439016 392415152556138237285391 := by
  unfold tailWord_3439016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62715609054519922008804451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83620812072693229345072601 62715609054519922008804451)
  ·
    refine ⟨94073413581779883013206677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62715609054519922008804451 94073413581779883013206677)
    ·
      refine ⟨4409691261645932016244063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94073413581779883013206677 4409691261645932016244063)
      ·
        refine ⟨6614536892468898024366095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409691261645932016244063 6614536892468898024366095)
        ·
          refine ⟨9921805338703347036549143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6614536892468898024366095 9921805338703347036549143)
          ·
            refine ⟨14882708008055020554823715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9921805338703347036549143 14882708008055020554823715)
            ·
              refine ⟨22324062012082530832235573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14882708008055020554823715 22324062012082530832235573)
              ·
                refine ⟨2092880813632737265522085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22324062012082530832235573 2092880813632737265522085)
                ·
                  refine ⟨392415152556138237285391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2092880813632737265522085 392415152556138237285391)
                  ·
                    rfl

theorem cell22_3439016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5, 4].length) (baseStart_3439016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439016 prefixEnd_3439016 := by exact prefixLift 3439016
  have htrace : WordTrace (prefixWord ++ tailWord_3439016) baseStart_3439016 baseEnd_3439016 := by
    simpa [prefixWord, tailWord_3439016, baseEnd_3439016] using wordTrace_append hprefix tailTrace_3439016
  have hstable : (prefixWord ++ tailWord_3439016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439016).length < 2 ^ (prefixWord ++ tailWord_3439016).sum := by decide
  have hdescent : baseEnd_3439016 < baseStart_3439016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439031 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 2, 3]
def baseStart_3439031 : Nat := 118140960795 + 3439031 * 2 ^ 59
def prefixEnd_3439031 : Nat := 4983230072969 + 3 ^ 40 * 3439031 * 2
def baseEnd_3439031 : Nat := 1177250592474959672731127

theorem tailTrace_3439031 : CollatzResearch.WordTrace tailWord_3439031 prefixEnd_3439031 1177250592474959672731127 := by
  unfold tailWord_3439031
  simp only [CollatzResearch.WordTrace]
  refine ⟨125431765203985501579404947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83621176802657001052936631 125431765203985501579404947)
  ·
    refine ⟨188147647805978252369107421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125431765203985501579404947 188147647805978252369107421)
    ·
      refine ⟨70555367927241844638415283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188147647805978252369107421 70555367927241844638415283)
      ·
        refine ⟨105833051890862766957622925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70555367927241844638415283 105833051890862766957622925)
        ·
          refine ⟨39687394459073537609108597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105833051890862766957622925 39687394459073537609108597)
          ·
            refine ⟨3720693230538144150853931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39687394459073537609108597 3720693230538144150853931)
            ·
              refine ⟨5581039845807216226280897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720693230538144150853931 5581039845807216226280897)
              ·
                refine ⟨4185779884355412169710673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581039845807216226280897 4185779884355412169710673)
                ·
                  refine ⟨3139334913266559127283005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4185779884355412169710673 3139334913266559127283005)
                  ·
                    refine ⟨1177250592474959672731127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139334913266559127283005 1177250592474959672731127)
                    ·
                      rfl

theorem cell22_3439031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_3439031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439031 prefixEnd_3439031 := by exact prefixLift 3439031
  have htrace : WordTrace (prefixWord ++ tailWord_3439031) baseStart_3439031 baseEnd_3439031 := by
    simpa [prefixWord, tailWord_3439031, baseEnd_3439031] using wordTrace_append hprefix tailTrace_3439031
  have hstable : (prefixWord ++ tailWord_3439031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439031).length < 2 ^ (prefixWord ++ tailWord_3439031).sum := by decide
  have hdescent : baseEnd_3439031 < baseStart_3439031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439181 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3439181 : Nat := 118140960795 + 3439181 * 2 ^ 59
def prefixEnd_3439181 : Nat := 4983230072969 + 3 ^ 40 * 3439181 * 2
def baseEnd_3439181 : Nat := 1177301940540409281480667

theorem tailTrace_3439181 : CollatzResearch.WordTrace tailWord_3439181 prefixEnd_3439181 1177301940540409281480667 := by
  unfold tailWord_3439181
  simp only [CollatzResearch.WordTrace]
  refine ⟨125437236153442077197365397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83624824102294718131576931 125437236153442077197365397)
  ·
    refine ⟨5879870444692597368626503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125437236153442077197365397 5879870444692597368626503)
    ·
      refine ⟨8819805667038896052939755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5879870444692597368626503 8819805667038896052939755)
      ·
        refine ⟨13229708500558344079409633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8819805667038896052939755 13229708500558344079409633)
        ·
          refine ⟨9922281375418758059557225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13229708500558344079409633 9922281375418758059557225)
          ·
            refine ⟨7441711031564068544667919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9922281375418758059557225 7441711031564068544667919)
            ·
              refine ⟨11162566547346102817001879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441711031564068544667919 11162566547346102817001879)
              ·
                refine ⟨16743849821019154225502819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11162566547346102817001879 16743849821019154225502819)
                ·
                  refine ⟨25115774731528731338254229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16743849821019154225502819 25115774731528731338254229)
                  ·
                    refine ⟨1177301940540409281480667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25115774731528731338254229 1177301940540409281480667)
                    ·
                      rfl

theorem cell22_3439181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3439181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439181 prefixEnd_3439181 := by exact prefixLift 3439181
  have htrace : WordTrace (prefixWord ++ tailWord_3439181) baseStart_3439181 baseEnd_3439181 := by
    simpa [prefixWord, tailWord_3439181, baseEnd_3439181] using wordTrace_append hprefix tailTrace_3439181
  have hstable : (prefixWord ++ tailWord_3439181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439181).length < 2 ^ (prefixWord ++ tailWord_3439181).sum := by decide
  have hdescent : baseEnd_3439181 < baseStart_3439181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439262 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3439262 : Nat := 118140960795 + 3439262 * 2 ^ 59
def prefixEnd_3439262 : Nat := 4983230072969 + 3 ^ 40 * 3439262 * 2
def baseEnd_3439262 : Nat := 1177329668495752070205419

theorem tailTrace_3439262 : CollatzResearch.WordTrace tailWord_3439262 prefixEnd_3439262 1177329668495752070205419 := by
  unfold tailWord_3439262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680023808268578503883005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83626793644099085354042693 15680023808268578503883005)
  ·
    refine ⟨5880008928100716938956127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15680023808268578503883005 5880008928100716938956127)
    ·
      refine ⟨8820013392151075408434191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5880008928100716938956127 8820013392151075408434191)
      ·
        refine ⟨13230020088226613112651287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8820013392151075408434191 13230020088226613112651287)
        ·
          refine ⟨19845030132339919668976931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13230020088226613112651287 19845030132339919668976931)
          ·
            refine ⟨29767545198509879503465397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19845030132339919668976931 29767545198509879503465397)
            ·
              refine ⟨2790707362360301203449881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29767545198509879503465397 2790707362360301203449881)
              ·
                refine ⟨2093030521770225902587411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790707362360301203449881 2093030521770225902587411)
                ·
                  refine ⟨3139545782655338853881117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093030521770225902587411 3139545782655338853881117)
                  ·
                    refine ⟨1177329668495752070205419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3139545782655338853881117 1177329668495752070205419)
                    ·
                      rfl

theorem cell22_3439262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3439262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439262 prefixEnd_3439262 := by exact prefixLift 3439262
  have htrace : WordTrace (prefixWord ++ tailWord_3439262) baseStart_3439262 baseEnd_3439262 := by
    simpa [prefixWord, tailWord_3439262, baseEnd_3439262] using wordTrace_append hprefix tailTrace_3439262
  have hstable : (prefixWord ++ tailWord_3439262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439262).length < 2 ^ (prefixWord ++ tailWord_3439262).sum := by decide
  have hdescent : baseEnd_3439262 < baseStart_3439262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439314 : List Nat := [3, 2, 2, 2, 13]
def baseStart_3439314 : Nat := 118140960795 + 3439314 * 2 ^ 59
def prefixEnd_3439314 : Nat := 4983230072969 + 3 ^ 40 * 3439314 * 2
def baseEnd_3439314 : Nat := 4845051313409223324713

theorem tailTrace_3439314 : CollatzResearch.WordTrace tailWord_3439314 prefixEnd_3439314 4845051313409223324713 := by
  unfold tailWord_3439314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31360521765490060227989249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83628058041306827274637997 31360521765490060227989249)
  ·
    refine ⟨23520391324117545170991937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31360521765490060227989249 23520391324117545170991937)
    ·
      refine ⟨17640293493088158878243953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23520391324117545170991937 17640293493088158878243953)
      ·
        refine ⟨13230220119816119158682965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17640293493088158878243953 13230220119816119158682965)
        ·
          refine ⟨4845051313409223324713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13230220119816119158682965 4845051313409223324713)
          ·
            rfl

theorem cell22_3439314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 13].length) (baseStart_3439314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439314 prefixEnd_3439314 := by exact prefixLift 3439314
  have htrace : WordTrace (prefixWord ++ tailWord_3439314) baseStart_3439314 baseEnd_3439314 := by
    simpa [prefixWord, tailWord_3439314, baseEnd_3439314] using wordTrace_append hprefix tailTrace_3439314
  have hstable : (prefixWord ++ tailWord_3439314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439314).length < 2 ^ (prefixWord ++ tailWord_3439314).sum := by decide
  have hdescent : baseEnd_3439314 < baseStart_3439314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439320 : List Nat := [2, 1, 2, 2, 3, 4, 2, 2, 4]
def baseStart_3439320 : Nat := 118140960795 + 3439320 * 2 ^ 59
def prefixEnd_3439320 : Nat := 4983230072969 + 3 ^ 40 * 3439320 * 2
def baseEnd_3439320 : Nat := 392449841027019750751747

theorem tailTrace_3439320 : CollatzResearch.WordTrace tailWord_3439320 prefixEnd_3439320 392449841027019750751747 := by
  unfold tailWord_3439320
  simp only [CollatzResearch.WordTrace]
  refine ⟨62721152949969251968337707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83628203933292335957783609 62721152949969251968337707)
  ·
    refine ⟨94081729424953877952506561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62721152949969251968337707 94081729424953877952506561)
    ·
      refine ⟨70561297068715408464379921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94081729424953877952506561 70561297068715408464379921)
      ·
        refine ⟨52920972801536556348284941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70561297068715408464379921 52920972801536556348284941)
        ·
          refine ⟨19845364800576208630606853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52920972801536556348284941 19845364800576208630606853)
          ·
            refine ⟨3721005900108039118238785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19845364800576208630606853 3721005900108039118238785)
            ·
              refine ⟨2790754425081029338679089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3721005900108039118238785 2790754425081029338679089)
              ·
                refine ⟨2093065818810772004009317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2790754425081029338679089 2093065818810772004009317)
                ·
                  refine ⟨392449841027019750751747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093065818810772004009317 392449841027019750751747)
                  ·
                    rfl

theorem cell22_3439320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 4].length) (baseStart_3439320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439320 prefixEnd_3439320 := by exact prefixLift 3439320
  have htrace : WordTrace (prefixWord ++ tailWord_3439320) baseStart_3439320 baseEnd_3439320 := by
    simpa [prefixWord, tailWord_3439320, baseEnd_3439320] using wordTrace_append hprefix tailTrace_3439320
  have hstable : (prefixWord ++ tailWord_3439320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439320).length < 2 ^ (prefixWord ++ tailWord_3439320).sum := by decide
  have hdescent : baseEnd_3439320 < baseStart_3439320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439331 : List Nat := [1, 1, 1, 7, 1, 1, 3, 7]
def baseStart_3439331 : Nat := 118140960795 + 3439331 * 2 ^ 59
def prefixEnd_3439331 : Nat := 4983230072969 + 3 ^ 40 * 3439331 * 2
def baseEnd_3439331 : Nat := 130817032067317654470023

theorem tailTrace_3439331 : CollatzResearch.WordTrace tailWord_3439331 prefixEnd_3439331 130817032067317654470023 := by
  unfold tailWord_3439331
  simp only [CollatzResearch.WordTrace]
  refine ⟨125442707102898652815325847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83628471401932435210217231 125442707102898652815325847)
  ·
    refine ⟨188164060654347979222988771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125442707102898652815325847 188164060654347979222988771)
    ·
      refine ⟨282246090981521968834483157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188164060654347979222988771 282246090981521968834483157)
      ·
        refine ⟨6615142757379421144558199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 282246090981521968834483157 6615142757379421144558199)
        ·
          refine ⟨9922714136069131716837299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615142757379421144558199 9922714136069131716837299)
          ·
            refine ⟨14884071204103697575255949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922714136069131716837299 14884071204103697575255949)
            ·
              refine ⟨5581526701538886590720981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14884071204103697575255949 5581526701538886590720981)
              ·
                refine ⟨130817032067317654470023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5581526701538886590720981 130817032067317654470023)
                ·
                  rfl

theorem cell22_3439331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 7].length) (baseStart_3439331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439331 prefixEnd_3439331 := by exact prefixLift 3439331
  have htrace : WordTrace (prefixWord ++ tailWord_3439331) baseStart_3439331 baseEnd_3439331 := by
    simpa [prefixWord, tailWord_3439331, baseEnd_3439331] using wordTrace_append hprefix tailTrace_3439331
  have hstable : (prefixWord ++ tailWord_3439331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439331).length < 2 ^ (prefixWord ++ tailWord_3439331).sum := by decide
  have hdescent : baseEnd_3439331 < baseStart_3439331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439344 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_3439344 : Nat := 118140960795 + 3439344 * 2 ^ 59
def prefixEnd_3439344 : Nat := 4983230072969 + 3 ^ 40 * 3439344 * 2
def baseEnd_3439344 : Nat := 1177357738771531189655167

theorem tailTrace_3439344 : CollatzResearch.WordTrace tailWord_3439344 prefixEnd_3439344 1177357738771531189655167 := by
  unfold tailWord_3439344
  simp only [CollatzResearch.WordTrace]
  refine ⟨62721590625925778017774543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83628787501234370690366057 62721590625925778017774543)
  ·
    refine ⟨94082385938888667026661815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62721590625925778017774543 94082385938888667026661815)
    ·
      refine ⟨141123578908333000539992723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94082385938888667026661815 141123578908333000539992723)
      ·
        refine ⟨211685368362499500809989085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141123578908333000539992723 211685368362499500809989085)
        ·
          refine ⟨79382013135937312803745907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211685368362499500809989085 79382013135937312803745907)
          ·
            refine ⟨119073019703905969205618861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79382013135937312803745907 119073019703905969205618861)
            ·
              refine ⟨44652382388964738452107073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119073019703905969205618861 44652382388964738452107073)
              ·
                refine ⟨33489286791723553839080305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44652382388964738452107073 33489286791723553839080305)
                ·
                  refine ⟨25116965093792665379310229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33489286791723553839080305 25116965093792665379310229)
                  ·
                    refine ⟨1177357738771531189655167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25116965093792665379310229 1177357738771531189655167)
                    ·
                      rfl

theorem cell22_3439344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_3439344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439344 prefixEnd_3439344 := by exact prefixLift 3439344
  have htrace : WordTrace (prefixWord ++ tailWord_3439344) baseStart_3439344 baseEnd_3439344 := by
    simpa [prefixWord, tailWord_3439344, baseEnd_3439344] using wordTrace_append hprefix tailTrace_3439344
  have hstable : (prefixWord ++ tailWord_3439344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439344).length < 2 ^ (prefixWord ++ tailWord_3439344).sum := by decide
  have hdescent : baseEnd_3439344 < baseStart_3439344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439359 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 7]
def baseStart_3439359 : Nat := 118140960795 + 3439359 * 2 ^ 59
def prefixEnd_3439359 : Nat := 4983230072969 + 3 ^ 40 * 3439359 * 2
def baseEnd_3439359 : Nat := 392454291192692050176707

theorem tailTrace_3439359 : CollatzResearch.WordTrace tailWord_3439359 prefixEnd_3439359 392454291192692050176707 := by
  unfold tailWord_3439359
  simp only [CollatzResearch.WordTrace]
  refine ⟨125443728346797213597345131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83629152231198142398230087 125443728346797213597345131)
  ·
    refine ⟨188165592520195820396017697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125443728346797213597345131 188165592520195820396017697)
    ·
      refine ⟨141124194390146865297013273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188165592520195820396017697 141124194390146865297013273)
      ·
        refine ⟨105843145792610148972759955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141124194390146865297013273 105843145792610148972759955)
        ·
          refine ⟨158764718688915223459139933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105843145792610148972759955 158764718688915223459139933)
          ·
            refine ⟨59536769508343208797177475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158764718688915223459139933 59536769508343208797177475)
            ·
              refine ⟨89305154262514813195766213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59536769508343208797177475 89305154262514813195766213)
              ·
                refine ⟨16744716424221527474206165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89305154262514813195766213 16744716424221527474206165)
                ·
                  refine ⟨392454291192692050176707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16744716424221527474206165 392454291192692050176707)
                  ·
                    rfl

theorem cell22_3439359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 7].length) (baseStart_3439359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439359 prefixEnd_3439359 := by exact prefixLift 3439359
  have htrace : WordTrace (prefixWord ++ tailWord_3439359) baseStart_3439359 baseEnd_3439359 := by
    simpa [prefixWord, tailWord_3439359, baseEnd_3439359] using wordTrace_append hprefix tailTrace_3439359
  have hstable : (prefixWord ++ tailWord_3439359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439359).length < 2 ^ (prefixWord ++ tailWord_3439359).sum := by decide
  have hdescent : baseEnd_3439359 < baseStart_3439359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439391 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 2, 5]
def baseStart_3439391 : Nat := 118140960795 + 3439391 * 2 ^ 59
def prefixEnd_3439391 : Nat := 4983230072969 + 3 ^ 40 * 3439391 * 2
def baseEnd_3439391 : Nat := 1177373827832038733730023

theorem tailTrace_3439391 : CollatzResearch.WordTrace tailWord_3439391 prefixEnd_3439391 1177373827832038733730023 := by
  unfold tailWord_3439391
  simp only [CollatzResearch.WordTrace]
  refine ⟨125444895482681283062510027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83629930321787522041673351 125444895482681283062510027)
  ·
    refine ⟨188167343224021924593765041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125444895482681283062510027 188167343224021924593765041)
    ·
      refine ⟨141125507418016443445323781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188167343224021924593765041 141125507418016443445323781)
      ·
        refine ⟨26461032640878083145998209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141125507418016443445323781 26461032640878083145998209)
        ·
          refine ⟨19845774480658562359498657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26461032640878083145998209 19845774480658562359498657)
          ·
            refine ⟨14884330860493921769623993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19845774480658562359498657 14884330860493921769623993)
            ·
              refine ⟨11163248145370441327217995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14884330860493921769623993 11163248145370441327217995)
              ·
                refine ⟨16744872218055661990826993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163248145370441327217995 16744872218055661990826993)
                ·
                  refine ⟨12558654163541746493120245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16744872218055661990826993 12558654163541746493120245)
                  ·
                    refine ⟨1177373827832038733730023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12558654163541746493120245 1177373827832038733730023)
                    ·
                      rfl

theorem cell22_3439391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 5].length) (baseStart_3439391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439391 prefixEnd_3439391 := by exact prefixLift 3439391
  have htrace : WordTrace (prefixWord ++ tailWord_3439391) baseStart_3439391 baseEnd_3439391 := by
    simpa [prefixWord, tailWord_3439391, baseEnd_3439391] using wordTrace_append hprefix tailTrace_3439391
  have hstable : (prefixWord ++ tailWord_3439391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439391).length < 2 ^ (prefixWord ++ tailWord_3439391).sum := by decide
  have hdescent : baseEnd_3439391 < baseStart_3439391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439393 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 5]
def baseStart_3439393 : Nat := 118140960795 + 3439393 * 2 ^ 59
def prefixEnd_3439393 : Nat := 4983230072969 + 3 ^ 40 * 3439393 * 2
def baseEnd_3439393 : Nat := 392458170824303798393339

theorem tailTrace_3439393 : CollatzResearch.WordTrace tailWord_3439393 prefixEnd_3439393 392458170824303798393339 := by
  unfold tailWord_3439393
  simp only [CollatzResearch.WordTrace]
  refine ⟨125444968428674037404082833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83629978952449358269388555 125444968428674037404082833)
  ·
    refine ⟨94083726321505528053062125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125444968428674037404082833 94083726321505528053062125)
    ·
      refine ⟨35281397370564573019898297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94083726321505528053062125 35281397370564573019898297)
      ·
        refine ⟨26461048027923429764923723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35281397370564573019898297 26461048027923429764923723)
        ·
          refine ⟨39691572041885144647385585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461048027923429764923723 39691572041885144647385585)
          ·
            refine ⟨29768679031413858485539189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39691572041885144647385585 29768679031413858485539189)
            ·
              refine ⟨2790813659195049233019299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29768679031413858485539189 2790813659195049233019299)
              ·
                refine ⟨4186220488792573849528949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2790813659195049233019299 4186220488792573849528949)
                ·
                  refine ⟨392458170824303798393339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186220488792573849528949 392458170824303798393339)
                  ·
                    rfl

theorem cell22_3439393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_3439393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439393 prefixEnd_3439393 := by exact prefixLift 3439393
  have htrace : WordTrace (prefixWord ++ tailWord_3439393) baseStart_3439393 baseEnd_3439393 := by
    simpa [prefixWord, tailWord_3439393, baseEnd_3439393] using wordTrace_append hprefix tailTrace_3439393
  have hstable : (prefixWord ++ tailWord_3439393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439393).length < 2 ^ (prefixWord ++ tailWord_3439393).sum := by decide
  have hdescent : baseEnd_3439393 < baseStart_3439393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439423 : List Nat := [1, 1, 2, 2, 5, 1, 2, 3, 1, 4]
def baseStart_3439423 : Nat := 118140960795 + 3439423 * 2 ^ 59
def prefixEnd_3439423 : Nat := 4983230072969 + 3 ^ 40 * 3439423 * 2
def baseEnd_3439423 : Nat := 1177384782086001316929925

theorem tailTrace_3439423 : CollatzResearch.WordTrace tailWord_3439423 prefixEnd_3439423 1177384782086001316929925 := by
  unfold tailWord_3439423
  simp only [CollatzResearch.WordTrace]
  refine ⟨125446062618565352527674923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83630708412376901685116615 125446062618565352527674923)
  ·
    refine ⟨188169093927848028791512385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125446062618565352527674923 188169093927848028791512385)
    ·
      refine ⟨141126820445886021593634289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188169093927848028791512385 141126820445886021593634289)
      ·
        refine ⟨105845115334414516195225717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141126820445886021593634289 105845115334414516195225717)
        ·
          refine ⟨9922979562601360893302411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105845115334414516195225717 9922979562601360893302411)
          ·
            refine ⟨14884469343902041339953617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922979562601360893302411 14884469343902041339953617)
            ·
              refine ⟨11163352007926531004965213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14884469343902041339953617 11163352007926531004965213)
              ·
                refine ⟨4186257002972449126861955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11163352007926531004965213 4186257002972449126861955)
                ·
                  refine ⟨6279385504458673690292933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186257002972449126861955 6279385504458673690292933)
                  ·
                    refine ⟨1177384782086001316929925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6279385504458673690292933 1177384782086001316929925)
                    ·
                      rfl

theorem cell22_3439423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 4].length) (baseStart_3439423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439423 prefixEnd_3439423 := by exact prefixLift 3439423
  have htrace : WordTrace (prefixWord ++ tailWord_3439423) baseStart_3439423 baseEnd_3439423 := by
    simpa [prefixWord, tailWord_3439423, baseEnd_3439423] using wordTrace_append hprefix tailTrace_3439423
  have hstable : (prefixWord ++ tailWord_3439423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439423).length < 2 ^ (prefixWord ++ tailWord_3439423).sum := by decide
  have hdescent : baseEnd_3439423 < baseStart_3439423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439438 : List Nat := [4, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_3439438 : Nat := 118140960795 + 3439438 * 2 ^ 59
def prefixEnd_3439438 : Nat := 4983230072969 + 3 ^ 40 * 3439438 * 2
def baseEnd_3439438 : Nat := 392463305630848759268293

theorem tailTrace_3439438 : CollatzResearch.WordTrace tailWord_3439438 prefixEnd_3439438 392463305630848759268293 := by
  unfold tailWord_3439438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680826214188876261183871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83631073142340673392980645 15680826214188876261183871)
  ·
    refine ⟨23521239321283314391775807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15680826214188876261183871 23521239321283314391775807)
    ·
      refine ⟨35281858981924971587663711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23521239321283314391775807 35281858981924971587663711)
      ·
        refine ⟨52922788472887457381495567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35281858981924971587663711 52922788472887457381495567)
        ·
          refine ⟨79384182709331186072243351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52922788472887457381495567 79384182709331186072243351)
          ·
            refine ⟨119076274063996779108365027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79384182709331186072243351 119076274063996779108365027)
            ·
              refine ⟨178614411095995168662547541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119076274063996779108365027 178614411095995168662547541)
              ·
                refine ⟨2093137630031193382764229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 178614411095995168662547541 2093137630031193382764229)
                ·
                  refine ⟨392463305630848759268293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093137630031193382764229 392463305630848759268293)
                  ·
                    rfl

theorem cell22_3439438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_3439438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439438 prefixEnd_3439438 := by exact prefixLift 3439438
  have htrace : WordTrace (prefixWord ++ tailWord_3439438) baseStart_3439438 baseEnd_3439438 := by
    simpa [prefixWord, tailWord_3439438, baseEnd_3439438] using wordTrace_append hprefix tailTrace_3439438
  have hstable : (prefixWord ++ tailWord_3439438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439438).length < 2 ^ (prefixWord ++ tailWord_3439438).sum := by decide
  have hdescent : baseEnd_3439438 < baseStart_3439438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439468 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_3439468 : Nat := 118140960795 + 3439468 * 2 ^ 59
def prefixEnd_3439468 : Nat := 4983230072969 + 3 ^ 40 * 3439468 * 2
def baseEnd_3439468 : Nat := 1177400186505636199554787

theorem tailTrace_3439468 : CollatzResearch.WordTrace tailWord_3439468 prefixEnd_3439468 1177400186505636199554787 := by
  unfold tailWord_3439468
  simp only [CollatzResearch.WordTrace]
  refine ⟨62723851951701162606531529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83631802602268216808708705 62723851951701162606531529)
  ·
    refine ⟨47042888963775871954898647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62723851951701162606531529 47042888963775871954898647)
    ·
      refine ⟨70564333445663807932347971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47042888963775871954898647 70564333445663807932347971)
      ·
        refine ⟨105846500168495711898521957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70564333445663807932347971 105846500168495711898521957)
        ·
          refine ⟨19846218781592945980972867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105846500168495711898521957 19846218781592945980972867)
          ·
            refine ⟨29769328172389418971459301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19846218781592945980972867 29769328172389418971459301)
            ·
              refine ⟨5581749032323016057148619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29769328172389418971459301 5581749032323016057148619)
              ·
                refine ⟨8372623548484524085722929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581749032323016057148619 8372623548484524085722929)
                ·
                  refine ⟨6279467661363393064292197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8372623548484524085722929 6279467661363393064292197)
                  ·
                    refine ⟨1177400186505636199554787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6279467661363393064292197 1177400186505636199554787)
                    ·
                      rfl

theorem cell22_3439468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_3439468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439468 prefixEnd_3439468 := by exact prefixLift 3439468
  have htrace : WordTrace (prefixWord ++ tailWord_3439468) baseStart_3439468 baseEnd_3439468 := by
    simpa [prefixWord, tailWord_3439468, baseEnd_3439468] using wordTrace_append hprefix tailTrace_3439468
  have hstable : (prefixWord ++ tailWord_3439468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439468).length < 2 ^ (prefixWord ++ tailWord_3439468).sum := by decide
  have hdescent : baseEnd_3439468 < baseStart_3439468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439470 : List Nat := [4, 1, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3439470 : Nat := 118140960795 + 3439470 * 2 ^ 59
def prefixEnd_3439470 : Nat := 4983230072969 + 3 ^ 40 * 3439470 * 2
def baseEnd_3439470 : Nat := 1177400871146508861004781

theorem tailTrace_3439470 : CollatzResearch.WordTrace tailWord_3439470 prefixEnd_3439470 1177400871146508861004781 := by
  unfold tailWord_3439470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680972106174384944329483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83631851232930053036423909 15680972106174384944329483)
  ·
    refine ⟨23521458159261577416494225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15680972106174384944329483 23521458159261577416494225)
    ·
      refine ⟨17641093619446183062370669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23521458159261577416494225 17641093619446183062370669)
      ·
        refine ⟨6615410107292318648389001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17641093619446183062370669 6615410107292318648389001)
        ·
          refine ⟨4961557580469238986291751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615410107292318648389001 4961557580469238986291751)
          ·
            refine ⟨7442336370703858479437627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961557580469238986291751 7442336370703858479437627)
            ·
              refine ⟨11163504556055787719156441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442336370703858479437627 11163504556055787719156441)
              ·
                refine ⟨8372628417041840789367331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11163504556055787719156441 8372628417041840789367331)
                ·
                  refine ⟨12558942625562761184050997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372628417041840789367331 12558942625562761184050997)
                  ·
                    refine ⟨1177400871146508861004781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12558942625562761184050997 1177400871146508861004781)
                    ·
                      rfl

theorem cell22_3439470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3439470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439470 prefixEnd_3439470 := by exact prefixLift 3439470
  have htrace : WordTrace (prefixWord ++ tailWord_3439470) baseStart_3439470 baseEnd_3439470 := by
    simpa [prefixWord, tailWord_3439470, baseEnd_3439470] using wordTrace_append hprefix tailTrace_3439470
  have hstable : (prefixWord ++ tailWord_3439470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439470).length < 2 ^ (prefixWord ++ tailWord_3439470).sum := by decide
  have hdescent : baseEnd_3439470 < baseStart_3439470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439545 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 5]
def baseStart_3439545 : Nat := 118140960795 + 3439545 * 2 ^ 59
def prefixEnd_3439545 : Nat := 4983230072969 + 3 ^ 40 * 3439545 * 2
def baseEnd_3439545 : Nat := 392475515059744555126517

theorem tailTrace_3439545 : CollatzResearch.WordTrace tailWord_3439545 prefixEnd_3439545 392475515059744555126517 := by
  unfold tailWord_3439545
  simp only [CollatzResearch.WordTrace]
  refine ⟨125450512324123367363616089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83633674882748911575744059 125450512324123367363616089)
  ·
    refine ⟨94087884243092525522712067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125450512324123367363616089 94087884243092525522712067)
    ·
      refine ⟨141131826364638788284068101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94087884243092525522712067 141131826364638788284068101)
      ·
        refine ⟨26462217443369772803262769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141131826364638788284068101 26462217443369772803262769)
        ·
          refine ⟨19846663082527329602447077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26462217443369772803262769 19846663082527329602447077)
          ·
            refine ⟨3721249327973874300458827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19846663082527329602447077 3721249327973874300458827)
            ·
              refine ⟨5581873991960811450688241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721249327973874300458827 5581873991960811450688241)
              ·
                refine ⟨4186405493970608588016181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581873991960811450688241 4186405493970608588016181)
                ·
                  refine ⟨392475515059744555126517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186405493970608588016181 392475515059744555126517)
                  ·
                    rfl

theorem cell22_3439545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_3439545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439545 prefixEnd_3439545 := by exact prefixLift 3439545
  have htrace : WordTrace (prefixWord ++ tailWord_3439545) baseStart_3439545 baseEnd_3439545 := by
    simpa [prefixWord, tailWord_3439545, baseEnd_3439545] using wordTrace_append hprefix tailTrace_3439545
  have hstable : (prefixWord ++ tailWord_3439545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439545).length < 2 ^ (prefixWord ++ tailWord_3439545).sum := by decide
  have hdescent : baseEnd_3439545 < baseStart_3439545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439714 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3439714 : Nat := 118140960795 + 3439714 * 2 ^ 59
def prefixEnd_3439714 : Nat := 4983230072969 + 3 ^ 40 * 3439714 * 2
def baseEnd_3439714 : Nat := 392494799110991185968011

theorem tailTrace_3439714 : CollatzResearch.WordTrace tailWord_3439714 prefixEnd_3439714 392494799110991185968011 := by
  unfold tailWord_3439714
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364169065127777306629549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83637784173674072817678797 31364169065127777306629549)
  ·
    refine ⟨11761563399422916489986081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31364169065127777306629549 11761563399422916489986081)
    ·
      refine ⟨8821172549567187367489561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11761563399422916489986081 8821172549567187367489561)
      ·
        refine ⟨6615879412175390525617171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8821172549567187367489561 6615879412175390525617171)
        ·
          refine ⟨9923819118263085788425757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615879412175390525617171 9923819118263085788425757)
          ·
            refine ⟨3721432169348657170659659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9923819118263085788425757 3721432169348657170659659)
            ·
              refine ⟨5582148254022985755989489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721432169348657170659659 5582148254022985755989489)
              ·
                refine ⟨4186611190517239316992117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5582148254022985755989489 4186611190517239316992117)
                ·
                  refine ⟨392494799110991185968011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186611190517239316992117 392494799110991185968011)
                  ·
                    rfl

theorem cell22_3439714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3439714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439714 prefixEnd_3439714 := by exact prefixLift 3439714
  have htrace : WordTrace (prefixWord ++ tailWord_3439714) baseStart_3439714 baseEnd_3439714 := by
    simpa [prefixWord, tailWord_3439714, baseEnd_3439714] using wordTrace_append hprefix tailTrace_3439714
  have hstable : (prefixWord ++ tailWord_3439714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439714).length < 2 ^ (prefixWord ++ tailWord_3439714).sum := by decide
  have hdescent : baseEnd_3439714 < baseStart_3439714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439725 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3439725 : Nat := 118140960795 + 3439725 * 2 ^ 59
def prefixEnd_3439725 : Nat := 4983230072969 + 3 ^ 40 * 3439725 * 2
def baseEnd_3439725 : Nat := 392496054285924398626333

theorem tailTrace_3439725 : CollatzResearch.WordTrace tailWord_3439725 prefixEnd_3439725 392496054285924398626333 := by
  unfold tailWord_3439725
  simp only [CollatzResearch.WordTrace]
  refine ⟨125457077463471258105168629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83638051642314172070112419 125457077463471258105168629)
  ·
    refine ⟨11761601012200430447359559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125457077463471258105168629 11761601012200430447359559)
    ·
      refine ⟨17642401518300645671039339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11761601012200430447359559 17642401518300645671039339)
      ·
        refine ⟨26463602277450968506559009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17642401518300645671039339 26463602277450968506559009)
        ·
          refine ⟨19847701708088226379919257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26463602277450968506559009 19847701708088226379919257)
          ·
            refine ⟨14885776281066169784939443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19847701708088226379919257 14885776281066169784939443)
            ·
              refine ⟨22328664421599254677409165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14885776281066169784939443 22328664421599254677409165)
              ·
                refine ⟨8373249158099720504028437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22328664421599254677409165 8373249158099720504028437)
                ·
                  refine ⟨392496054285924398626333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8373249158099720504028437 392496054285924398626333)
                  ·
                    rfl

theorem cell22_3439725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3439725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439725 prefixEnd_3439725 := by exact prefixLift 3439725
  have htrace : WordTrace (prefixWord ++ tailWord_3439725) baseStart_3439725 baseEnd_3439725 := by
    simpa [prefixWord, tailWord_3439725, baseEnd_3439725] using wordTrace_append hprefix tailTrace_3439725
  have hstable : (prefixWord ++ tailWord_3439725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439725).length < 2 ^ (prefixWord ++ tailWord_3439725).sum := by decide
  have hdescent : baseEnd_3439725 < baseStart_3439725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439770 : List Nat := [3, 1, 1, 5, 1, 1, 10]
def baseStart_3439770 : Nat := 118140960795 + 3439770 * 2 ^ 59
def prefixEnd_3439770 : Nat := 4983230072969 + 3 ^ 40 * 3439770 * 2
def baseEnd_3439770 : Nat := 43611243232496595500143

theorem tailTrace_3439770 : CollatzResearch.WordTrace tailWord_3439770 prefixEnd_3439770 43611243232496595500143 := by
  unfold tailWord_3439770
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364679687077057697639191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83639145832205487193704509 31364679687077057697639191)
  ·
    refine ⟨47047019530615586546458787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31364679687077057697639191 47047019530615586546458787)
    ·
      refine ⟨70570529295923379819688181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47047019530615586546458787 70570529295923379819688181)
      ·
        refine ⟨6615987121492816858095767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70570529295923379819688181 6615987121492816858095767)
        ·
          refine ⟨9923980682239225287143651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615987121492816858095767 9923980682239225287143651)
          ·
            refine ⟨14885971023358837930715477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9923980682239225287143651 14885971023358837930715477)
            ·
              refine ⟨43611243232496595500143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14885971023358837930715477 43611243232496595500143)
              ·
                rfl

theorem cell22_3439770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 10].length) (baseStart_3439770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439770 prefixEnd_3439770 := by exact prefixLift 3439770
  have htrace : WordTrace (prefixWord ++ tailWord_3439770) baseStart_3439770 baseEnd_3439770 := by
    simpa [prefixWord, tailWord_3439770, baseEnd_3439770] using wordTrace_append hprefix tailTrace_3439770
  have hstable : (prefixWord ++ tailWord_3439770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439770).length < 2 ^ (prefixWord ++ tailWord_3439770).sum := by decide
  have hdescent : baseEnd_3439770 < baseStart_3439770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439772 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3439772 : Nat := 118140960795 + 3439772 * 2 ^ 59
def prefixEnd_3439772 : Nat := 4983230072969 + 3 ^ 40 * 3439772 * 2
def baseEnd_3439772 : Nat := 1177504251918280739953855

theorem tailTrace_3439772 : CollatzResearch.WordTrace tailWord_3439772 prefixEnd_3439772 1177504251918280739953855 := by
  unfold tailWord_3439772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62729395847150492566064785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83639194462867323421419713 62729395847150492566064785)
  ·
    refine ⟨47047046885362869424548589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62729395847150492566064785 47047046885362869424548589)
    ·
      refine ⟨17642642582011076034205721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47047046885362869424548589 17642642582011076034205721)
      ·
        refine ⟨13231981936508307025654291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17642642582011076034205721 13231981936508307025654291)
        ·
          refine ⟨19847972904762460538481437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13231981936508307025654291 19847972904762460538481437)
          ·
            refine ⟨7442989839285922701930539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19847972904762460538481437 7442989839285922701930539)
            ·
              refine ⟨11164484758928884052895809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442989839285922701930539 11164484758928884052895809)
              ·
                refine ⟨8373363569196663039671857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164484758928884052895809 8373363569196663039671857)
                ·
                  refine ⟨6280022676897497279753893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373363569196663039671857 6280022676897497279753893)
                  ·
                    refine ⟨1177504251918280739953855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280022676897497279753893 1177504251918280739953855)
                    ·
                      rfl

theorem cell22_3439772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3439772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439772 prefixEnd_3439772 := by exact prefixLift 3439772
  have htrace : WordTrace (prefixWord ++ tailWord_3439772) baseStart_3439772 baseEnd_3439772 := by
    simpa [prefixWord, tailWord_3439772, baseEnd_3439772] using wordTrace_append hprefix tailTrace_3439772
  have hstable : (prefixWord ++ tailWord_3439772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439772).length < 2 ^ (prefixWord ++ tailWord_3439772).sum := by decide
  have hdescent : baseEnd_3439772 < baseStart_3439772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439774 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3439774 : Nat := 118140960795 + 3439774 * 2 ^ 59
def prefixEnd_3439774 : Nat := 4983230072969 + 3 ^ 40 * 3439774 * 2
def baseEnd_3439774 : Nat := 1177504936559153401403849

theorem tailTrace_3439774 : CollatzResearch.WordTrace tailWord_3439774 prefixEnd_3439774 1177504936559153401403849 := by
  unfold tailWord_3439774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682358080036717434212797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83639243093529159649134917 15682358080036717434212797)
  ·
    refine ⟨5880884280013769037829799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15682358080036717434212797 5880884280013769037829799)
    ·
      refine ⟨8821326420020653556744699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5880884280013769037829799 8821326420020653556744699)
      ·
        refine ⟨13231989630030980335117049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821326420020653556744699 13231989630030980335117049)
        ·
          refine ⟨9923992222523235251337787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13231989630030980335117049 9923992222523235251337787)
          ·
            refine ⟨14885988333784852877006681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9923992222523235251337787 14885988333784852877006681)
            ·
              refine ⟨11164491250338639657755011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14885988333784852877006681 11164491250338639657755011)
              ·
                refine ⟨16746736875507959486632517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164491250338639657755011 16746736875507959486632517)
                ·
                  refine ⟨3140013164157742403743597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16746736875507959486632517 3140013164157742403743597)
                  ·
                    refine ⟨1177504936559153401403849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140013164157742403743597 1177504936559153401403849)
                    ·
                      rfl

theorem cell22_3439774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3439774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439774 prefixEnd_3439774 := by exact prefixLift 3439774
  have htrace : WordTrace (prefixWord ++ tailWord_3439774) baseStart_3439774 baseEnd_3439774 := by
    simpa [prefixWord, tailWord_3439774, baseEnd_3439774] using wordTrace_append hprefix tailTrace_3439774
  have hstable : (prefixWord ++ tailWord_3439774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439774).length < 2 ^ (prefixWord ++ tailWord_3439774).sum := by decide
  have hdescent : baseEnd_3439774 < baseStart_3439774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439785 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_3439785 : Nat := 118140960795 + 3439785 * 2 ^ 59
def prefixEnd_3439785 : Nat := 4983230072969 + 3 ^ 40 * 3439785 * 2
def baseEnd_3439785 : Nat := 1177508702083953039378815

theorem tailTrace_3439785 : CollatzResearch.WordTrace tailWord_3439785 prefixEnd_3439785 1177508702083953039378815 := by
  unfold tailWord_3439785
  simp only [CollatzResearch.WordTrace]
  refine ⟨125459265843253888352352809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83639510562169258901568539 125459265843253888352352809)
  ·
    refine ⟨94094449382440416264264607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125459265843253888352352809 94094449382440416264264607)
    ·
      refine ⟨141141674073660624396396911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94094449382440416264264607 141141674073660624396396911)
      ·
        refine ⟨211712511110490936594595367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141141674073660624396396911 211712511110490936594595367)
        ·
          refine ⟨317568766665736404891893051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211712511110490936594595367 317568766665736404891893051)
          ·
            refine ⟨476353149998604607337839577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317568766665736404891893051 476353149998604607337839577)
            ·
              refine ⟨357264862498953455503379683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476353149998604607337839577 357264862498953455503379683)
              ·
                refine ⟨535897293748430183255069525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357264862498953455503379683 535897293748430183255069525)
                ·
                  refine ⟨3140023205557208105010173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 535897293748430183255069525 3140023205557208105010173)
                  ·
                    refine ⟨1177508702083953039378815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140023205557208105010173 1177508702083953039378815)
                    ·
                      rfl

theorem cell22_3439785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_3439785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439785 prefixEnd_3439785 := by exact prefixLift 3439785
  have htrace : WordTrace (prefixWord ++ tailWord_3439785) baseStart_3439785 baseEnd_3439785 := by
    simpa [prefixWord, tailWord_3439785, baseEnd_3439785] using wordTrace_append hprefix tailTrace_3439785
  have hstable : (prefixWord ++ tailWord_3439785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439785).length < 2 ^ (prefixWord ++ tailWord_3439785).sum := by decide
  have hdescent : baseEnd_3439785 < baseStart_3439785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439905 : List Nat := [1, 2, 3, 2, 1, 1, 1, 11]
def baseStart_3439905 : Nat := 118140960795 + 3439905 * 2 ^ 59
def prefixEnd_3439905 : Nat := 4983230072969 + 3 ^ 40 * 3439905 * 2
def baseEnd_3439905 : Nat := 130838864504034747375383

theorem tailTrace_3439905 : CollatzResearch.WordTrace tailWord_3439905 prefixEnd_3439905 130838864504034747375383 := by
  unfold tailWord_3439905
  simp only [CollatzResearch.WordTrace]
  refine ⟨125463642602819148846721169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83642428401879432564480779 125463642602819148846721169)
  ·
    refine ⟨94097731952114361635040877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125463642602819148846721169 94097731952114361635040877)
    ·
      refine ⟨35286649482042885613140329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94097731952114361635040877 35286649482042885613140329)
      ·
        refine ⟨26464987111532164209855247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35286649482042885613140329 26464987111532164209855247)
        ·
          refine ⟨39697480667298246314782871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26464987111532164209855247 39697480667298246314782871)
          ·
            refine ⟨59546221000947369472174307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39697480667298246314782871 59546221000947369472174307)
            ·
              refine ⟨89319331501421054208261461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59546221000947369472174307 89319331501421054208261461)
              ·
                refine ⟨130838864504034747375383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 89319331501421054208261461 130838864504034747375383)
                ·
                  rfl

theorem cell22_3439905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 11].length) (baseStart_3439905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439905 prefixEnd_3439905 := by exact prefixLift 3439905
  have htrace : WordTrace (prefixWord ++ tailWord_3439905) baseStart_3439905 baseEnd_3439905 := by
    simpa [prefixWord, tailWord_3439905, baseEnd_3439905] using wordTrace_append hprefix tailTrace_3439905
  have hstable : (prefixWord ++ tailWord_3439905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439905).length < 2 ^ (prefixWord ++ tailWord_3439905).sum := by decide
  have hdescent : baseEnd_3439905 < baseStart_3439905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439909 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_3439909 : Nat := 118140960795 + 3439909 * 2 ^ 59
def prefixEnd_3439909 : Nat := 4983230072969 + 3 ^ 40 * 3439909 * 2
def baseEnd_3439909 : Nat := 1177551149818058049278435

theorem tailTrace_3439909 : CollatzResearch.WordTrace tailWord_3439909 prefixEnd_3439909 1177551149818058049278435 := by
  unfold tailWord_3439909
  simp only [CollatzResearch.WordTrace]
  refine ⟨125463788494804657529866781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83642525663203105019911187 125463788494804657529866781)
  ·
    refine ⟨47048920685551746573700043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125463788494804657529866781 47048920685551746573700043)
    ·
      refine ⟨70573381028327619860550065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47048920685551746573700043 70573381028327619860550065)
      ·
        refine ⟨52930035771245714895412549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70573381028327619860550065 52930035771245714895412549)
        ·
          refine ⟨9924381707108571542889853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52930035771245714895412549 9924381707108571542889853)
          ·
            refine ⟨3721643140165714328583695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9924381707108571542889853 3721643140165714328583695)
            ·
              refine ⟨5582464710248571492875543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3721643140165714328583695 5582464710248571492875543)
              ·
                refine ⟨8373697065372857239313315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582464710248571492875543 8373697065372857239313315)
                ·
                  refine ⟨12560545598059285858969973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8373697065372857239313315 12560545598059285858969973)
                  ·
                    refine ⟨1177551149818058049278435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12560545598059285858969973 1177551149818058049278435)
                    ·
                      rfl

theorem cell22_3439909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_3439909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439909 prefixEnd_3439909 := by exact prefixLift 3439909
  have htrace : WordTrace (prefixWord ++ tailWord_3439909) baseStart_3439909 baseEnd_3439909 := by
    simpa [prefixWord, tailWord_3439909, baseEnd_3439909] using wordTrace_append hprefix tailTrace_3439909
  have hstable : (prefixWord ++ tailWord_3439909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439909).length < 2 ^ (prefixWord ++ tailWord_3439909).sum := by decide
  have hdescent : baseEnd_3439909 < baseStart_3439909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439920 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_3439920 : Nat := 118140960795 + 3439920 * 2 ^ 59
def prefixEnd_3439920 : Nat := 4983230072969 + 3 ^ 40 * 3439920 * 2
def baseEnd_3439920 : Nat := 1177554915342857687253401

theorem tailTrace_3439920 : CollatzResearch.WordTrace tailWord_3439920 prefixEnd_3439920 1177554915342857687253401 := by
  unfold tailWord_3439920
  simp only [CollatzResearch.WordTrace]
  refine ⟨62732094848882403204258607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83642793131843204272344809 62732094848882403204258607)
  ·
    refine ⟨94098142273323604806387911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62732094848882403204258607 94098142273323604806387911)
    ·
      refine ⟨141147213409985407209581867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94098142273323604806387911 141147213409985407209581867)
      ·
        refine ⟨211720820114978110814372801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141147213409985407209581867 211720820114978110814372801)
        ·
          refine ⟨158790615086233583110779601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211720820114978110814372801 158790615086233583110779601)
          ·
            refine ⟨119092961314675187333084701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158790615086233583110779601 119092961314675187333084701)
            ·
              refine ⟨44659860493003195249906763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119092961314675187333084701 44659860493003195249906763)
              ·
                refine ⟨66989790739504792874860145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44659860493003195249906763 66989790739504792874860145)
                ·
                  refine ⟨50242343054628594656145109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66989790739504792874860145 50242343054628594656145109)
                  ·
                    refine ⟨1177554915342857687253401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50242343054628594656145109 1177554915342857687253401)
                    ·
                      rfl

theorem cell22_3439920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_3439920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439920 prefixEnd_3439920 := by exact prefixLift 3439920
  have htrace : WordTrace (prefixWord ++ tailWord_3439920) baseStart_3439920 baseEnd_3439920 := by
    simpa [prefixWord, tailWord_3439920, baseEnd_3439920] using wordTrace_append hprefix tailTrace_3439920
  have hstable : (prefixWord ++ tailWord_3439920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439920).length < 2 ^ (prefixWord ++ tailWord_3439920).sum := by decide
  have hdescent : baseEnd_3439920 < baseStart_3439920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439922 : List Nat := [3, 2, 1, 1, 4, 2, 1, 8]
def baseStart_3439922 : Nat := 118140960795 + 3439922 * 2 ^ 59
def prefixEnd_3439922 : Nat := 4983230072969 + 3 ^ 40 * 3439922 * 2
def baseEnd_3439922 : Nat := 130839511109303372078155

theorem tailTrace_3439922 : CollatzResearch.WordTrace tailWord_3439922 prefixEnd_3439922 130839511109303372078155 := by
  unfold tailWord_3439922
  simp only [CollatzResearch.WordTrace]
  refine ⟨31366065660939390187522505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83642841762505040500060013 31366065660939390187522505)
  ·
    refine ⟨23524549245704542640641879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31366065660939390187522505 23524549245704542640641879)
    ·
      refine ⟨35286823868556813960962819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23524549245704542640641879 35286823868556813960962819)
      ·
        refine ⟨52930235802835220941444229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35286823868556813960962819 52930235802835220941444229)
        ·
          refine ⟨9924419213031603926520793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52930235802835220941444229 9924419213031603926520793)
          ·
            refine ⟨7443314409773702944890595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9924419213031603926520793 7443314409773702944890595)
            ·
              refine ⟨11164971614660554417335893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443314409773702944890595 11164971614660554417335893)
              ·
                refine ⟨130839511109303372078155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11164971614660554417335893 130839511109303372078155)
                ·
                  rfl

theorem cell22_3439922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_3439922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439922 prefixEnd_3439922 := by exact prefixLift 3439922
  have htrace : WordTrace (prefixWord ++ tailWord_3439922) baseStart_3439922 baseEnd_3439922 := by
    simpa [prefixWord, tailWord_3439922, baseEnd_3439922] using wordTrace_append hprefix tailTrace_3439922
  have hstable : (prefixWord ++ tailWord_3439922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439922).length < 2 ^ (prefixWord ++ tailWord_3439922).sum := by decide
  have hdescent : baseEnd_3439922 < baseStart_3439922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3439924 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3439924 : Nat := 118140960795 + 3439924 * 2 ^ 59
def prefixEnd_3439924 : Nat := 4983230072969 + 3 ^ 40 * 3439924 * 2
def baseEnd_3439924 : Nat := 1177556284624603010153389

theorem tailTrace_3439924 : CollatzResearch.WordTrace tailWord_3439924 prefixEnd_3439924 1177556284624603010153389 := by
  unfold tailWord_3439924
  simp only [CollatzResearch.WordTrace]
  refine ⟨62732167794875157545831413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83642890393166876727775217 62732167794875157545831413)
  ·
    refine ⟨5881140730769546019921695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62732167794875157545831413 5881140730769546019921695)
    ·
      refine ⟨8821711096154319029882543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5881140730769546019921695 8821711096154319029882543)
      ·
        refine ⟨13232566644231478544823815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821711096154319029882543 13232566644231478544823815)
        ·
          refine ⟨19848849966347217817235723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232566644231478544823815 19848849966347217817235723)
          ·
            refine ⟨29773274949520826725853585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19848849966347217817235723 29773274949520826725853585)
            ·
              refine ⟨22329956212140620044390189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29773274949520826725853585 22329956212140620044390189)
              ·
                refine ⟨8373733579552732516646321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22329956212140620044390189 8373733579552732516646321)
                ·
                  refine ⟨6280300184664549387484741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373733579552732516646321 6280300184664549387484741)
                  ·
                    refine ⟨1177556284624603010153389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280300184664549387484741 1177556284624603010153389)
                    ·
                      rfl

theorem cell22_3439924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3439924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3439924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3439924 prefixEnd_3439924 := by exact prefixLift 3439924
  have htrace : WordTrace (prefixWord ++ tailWord_3439924) baseStart_3439924 baseEnd_3439924 := by
    simpa [prefixWord, tailWord_3439924, baseEnd_3439924] using wordTrace_append hprefix tailTrace_3439924
  have hstable : (prefixWord ++ tailWord_3439924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3439924).length < 2 ^ (prefixWord ++ tailWord_3439924).sum := by decide
  have hdescent : baseEnd_3439924 < baseStart_3439924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3439924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440001 : List Nat := [1, 2, 4, 3, 2, 1, 2, 2, 5]
def baseStart_3440001 : Nat := 118140960795 + 3440001 * 2 ^ 59
def prefixEnd_3440001 : Nat := 4983230072969 + 3 ^ 40 * 3440001 * 2
def baseEnd_3440001 : Nat := 392527547766066825326051

theorem tailTrace_3440001 : CollatzResearch.WordTrace tailWord_3440001 prefixEnd_3440001 392527547766066825326051 := by
  unfold tailWord_3440001
  simp only [CollatzResearch.WordTrace]
  refine ⟨125467144010471357242215857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83644762673647571494810571 125467144010471357242215857)
  ·
    refine ⟨94100358007853517931661893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125467144010471357242215857 94100358007853517931661893)
    ·
      refine ⟨17643817126472534612186605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94100358007853517931661893 17643817126472534612186605)
      ·
        refine ⟨6616431422427200479569977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17643817126472534612186605 6616431422427200479569977)
        ·
          refine ⟨4962323566820400359677483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6616431422427200479569977 4962323566820400359677483)
          ·
            refine ⟨7443485350230600539516225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962323566820400359677483 7443485350230600539516225)
            ·
              refine ⟨5582614012672950404637169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443485350230600539516225 5582614012672950404637169)
              ·
                refine ⟨4186960509504712803477877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5582614012672950404637169 4186960509504712803477877)
                ·
                  refine ⟨392527547766066825326051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186960509504712803477877 392527547766066825326051)
                  ·
                    rfl

theorem cell22_3440001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_3440001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440001 prefixEnd_3440001 := by exact prefixLift 3440001
  have htrace : WordTrace (prefixWord ++ tailWord_3440001) baseStart_3440001 baseEnd_3440001 := by
    simpa [prefixWord, tailWord_3440001, baseEnd_3440001] using wordTrace_append hprefix tailTrace_3440001
  have hstable : (prefixWord ++ tailWord_3440001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440001).length < 2 ^ (prefixWord ++ tailWord_3440001).sum := by decide
  have hdescent : baseEnd_3440001 < baseStart_3440001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440012 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 6]
def baseStart_3440012 : Nat := 118140960795 + 3440012 * 2 ^ 59
def prefixEnd_3440012 : Nat := 4983230072969 + 3 ^ 40 * 3440012 * 2
def baseEnd_3440012 : Nat := 392528802941000037984373

theorem tailTrace_3440012 : CollatzResearch.WordTrace tailWord_3440012 prefixEnd_3440012 392528802941000037984373 := by
  unfold tailWord_3440012
  simp only [CollatzResearch.WordTrace]
  refine ⟨62733772606715753060433145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83645030142287670747244193 62733772606715753060433145)
  ·
    refine ⟨47050329455036814795324859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62733772606715753060433145 47050329455036814795324859)
    ·
      refine ⟨70575494182555222192987289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47050329455036814795324859 70575494182555222192987289)
      ·
        refine ⟨52931620636916416644740467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70575494182555222192987289 52931620636916416644740467)
        ·
          refine ⟨79397430955374624967110701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52931620636916416644740467 79397430955374624967110701)
          ·
            refine ⟨29774036608265484362666513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79397430955374624967110701 29774036608265484362666513)
            ·
              refine ⟨22330527456199113271999885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29774036608265484362666513 22330527456199113271999885)
              ·
                refine ⟨8373947796074667476999957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22330527456199113271999885 8373947796074667476999957)
                ·
                  refine ⟨392528802941000037984373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8373947796074667476999957 392528802941000037984373)
                  ·
                    rfl

theorem cell22_3440012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_3440012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440012 prefixEnd_3440012 := by exact prefixLift 3440012
  have htrace : WordTrace (prefixWord ++ tailWord_3440012) baseStart_3440012 baseEnd_3440012 := by
    simpa [prefixWord, tailWord_3440012, baseEnd_3440012] using wordTrace_append hprefix tailTrace_3440012
  have hstable : (prefixWord ++ tailWord_3440012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440012).length < 2 ^ (prefixWord ++ tailWord_3440012).sum := by decide
  have hdescent : baseEnd_3440012 < baseStart_3440012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440029 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 6]
def baseStart_3440029 : Nat := 118140960795 + 3440029 * 2 ^ 59
def prefixEnd_3440029 : Nat := 4983230072969 + 3 ^ 40 * 3440029 * 2
def baseEnd_3440029 : Nat := 392530742756805912092689

theorem tailTrace_3440029 : CollatzResearch.WordTrace tailWord_3440029 prefixEnd_3440029 392530742756805912092689 := by
  unfold tailWord_3440029
  simp only [CollatzResearch.WordTrace]
  refine ⟨125468165254369918024235141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83645443502913278682823427 125468165254369918024235141)
  ·
    refine ⟨23525280985194359629544089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125468165254369918024235141 23525280985194359629544089)
    ·
      refine ⟨17643960738895769722158067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23525280985194359629544089 17643960738895769722158067)
      ·
        refine ⟨26465941108343654583237101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17643960738895769722158067 26465941108343654583237101)
        ·
          refine ⟨9924727915628870468713913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26465941108343654583237101 9924727915628870468713913)
          ·
            refine ⟨7443545936721652851535435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9924727915628870468713913 7443545936721652851535435)
            ·
              refine ⟨11165318905082479277303153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443545936721652851535435 11165318905082479277303153)
              ·
                refine ⟨8373989178811859457977365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11165318905082479277303153 8373989178811859457977365)
                ·
                  refine ⟨392530742756805912092689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8373989178811859457977365 392530742756805912092689)
                  ·
                    rfl

theorem cell22_3440029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_3440029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440029 prefixEnd_3440029 := by exact prefixLift 3440029
  have htrace : WordTrace (prefixWord ++ tailWord_3440029) baseStart_3440029 baseEnd_3440029 := by
    simpa [prefixWord, tailWord_3440029, baseEnd_3440029] using wordTrace_append hprefix tailTrace_3440029
  have hstable : (prefixWord ++ tailWord_3440029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440029).length < 2 ^ (prefixWord ++ tailWord_3440029).sum := by decide
  have hdescent : baseEnd_3440029 < baseStart_3440029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440087 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 2, 6]
def baseStart_3440087 : Nat := 118140960795 + 3440087 * 2 ^ 59
def prefixEnd_3440087 : Nat := 4983230072969 + 3 ^ 40 * 3440087 * 2
def baseEnd_3440087 : Nat := 1177612082855724918327889

theorem tailTrace_3440087 : CollatzResearch.WordTrace tailWord_3440087 prefixEnd_3440087 1177612082855724918327889 := by
  unfold tailWord_3440087
  simp only [CollatzResearch.WordTrace]
  refine ⟨125470280688159793929846515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83646853792106529286564343 125470280688159793929846515)
  ·
    refine ⟨188205421032239690894769773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125470280688159793929846515 188205421032239690894769773)
    ·
      refine ⟨70577032887089884085538665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188205421032239690894769773 70577032887089884085538665)
      ·
        refine ⟨52932774665317413064153999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70577032887089884085538665 52932774665317413064153999)
        ·
          refine ⟨79399161997976119596230999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52932774665317413064153999 79399161997976119596230999)
          ·
            refine ⟨119098742996964179394346499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79399161997976119596230999 119098742996964179394346499)
            ·
              refine ⟨178648114495446269091519749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119098742996964179394346499 178648114495446269091519749)
              ·
                refine ⟨33496521467896175454659953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178648114495446269091519749 33496521467896175454659953)
                ·
                  refine ⟨25122391100922131590994965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33496521467896175454659953 25122391100922131590994965)
                  ·
                    refine ⟨1177612082855724918327889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25122391100922131590994965 1177612082855724918327889)
                    ·
                      rfl

theorem cell22_3440087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3440087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440087 prefixEnd_3440087 := by exact prefixLift 3440087
  have htrace : WordTrace (prefixWord ++ tailWord_3440087) baseStart_3440087 baseEnd_3440087 := by
    simpa [prefixWord, tailWord_3440087, baseEnd_3440087] using wordTrace_append hprefix tailTrace_3440087
  have hstable : (prefixWord ++ tailWord_3440087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440087).length < 2 ^ (prefixWord ++ tailWord_3440087).sum := by decide
  have hdescent : baseEnd_3440087 < baseStart_3440087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440136 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 5]
def baseStart_3440136 : Nat := 118140960795 + 3440136 * 2 ^ 59
def prefixEnd_3440136 : Nat := 4983230072969 + 3 ^ 40 * 3440136 * 2
def baseEnd_3440136 : Nat := 392542952185701707950913

theorem tailTrace_3440136 : CollatzResearch.WordTrace tailWord_3440136 prefixEnd_3440136 392542952185701707950913 := by
  unfold tailWord_3440136
  simp only [CollatzResearch.WordTrace]
  refine ⟨62736033932491137649190131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83648045243321516865586841 62736033932491137649190131)
  ·
    refine ⟨94104050898736706473785197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62736033932491137649190131 94104050898736706473785197)
    ·
      refine ⟨35289019087026264927669449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94104050898736706473785197 35289019087026264927669449)
      ·
        refine ⟨26466764315269698695752087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35289019087026264927669449 26466764315269698695752087)
        ·
          refine ⟨39700146472904548043628131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26466764315269698695752087 39700146472904548043628131)
          ·
            refine ⟨59550219709356822065442197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39700146472904548043628131 59550219709356822065442197)
            ·
              refine ⟨2791416548876101034317603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59550219709356822065442197 2791416548876101034317603)
              ·
                refine ⟨4187124823314151551476405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2791416548876101034317603 4187124823314151551476405)
                ·
                  refine ⟨392542952185701707950913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4187124823314151551476405 392542952185701707950913)
                  ·
                    rfl

theorem cell22_3440136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_3440136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440136 prefixEnd_3440136 := by exact prefixLift 3440136
  have htrace : WordTrace (prefixWord ++ tailWord_3440136) baseStart_3440136 baseEnd_3440136 := by
    simpa [prefixWord, tailWord_3440136, baseEnd_3440136] using wordTrace_append hprefix tailTrace_3440136
  have hstable : (prefixWord ++ tailWord_3440136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440136).length < 2 ^ (prefixWord ++ tailWord_3440136).sum := by decide
  have hdescent : baseEnd_3440136 < baseStart_3440136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440260 : List Nat := [2, 3, 2, 1, 5, 1, 2, 6]
def baseStart_3440260 : Nat := 118140960795 + 3440260 * 2 ^ 59
def prefixEnd_3440260 : Nat := 4983230072969 + 3 ^ 40 * 3440260 * 2
def baseEnd_3440260 : Nat := 130852367143467792639151

theorem tailTrace_3440260 : CollatzResearch.WordTrace tailWord_3440260 prefixEnd_3440260 130852367143467792639151 := by
  unfold tailWord_3440260
  simp only [CollatzResearch.WordTrace]
  refine ⟨62738295258266522237947117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83651060344355362983929489 62738295258266522237947117)
  ·
    refine ⟨23526860721849945839230169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62738295258266522237947117 23526860721849945839230169)
    ·
      refine ⟨17645145541387459379422627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23526860721849945839230169 17645145541387459379422627)
      ·
        refine ⟨26467718312081189069133941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17645145541387459379422627 26467718312081189069133941)
        ·
          refine ⟨2481348591757611475231307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26467718312081189069133941 2481348591757611475231307)
          ·
            refine ⟨3722022887636417212846961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481348591757611475231307 3722022887636417212846961)
            ·
              refine ⟨2791517165727312909635221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722022887636417212846961 2791517165727312909635221)
              ·
                refine ⟨130852367143467792639151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2791517165727312909635221 130852367143467792639151)
                ·
                  rfl

theorem cell22_3440260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 6].length) (baseStart_3440260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440260 prefixEnd_3440260 := by exact prefixLift 3440260
  have htrace : WordTrace (prefixWord ++ tailWord_3440260) baseStart_3440260 baseEnd_3440260 := by
    simpa [prefixWord, tailWord_3440260, baseEnd_3440260] using wordTrace_append hprefix tailTrace_3440260
  have hstable : (prefixWord ++ tailWord_3440260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440260).length < 2 ^ (prefixWord ++ tailWord_3440260).sum := by decide
  have hdescent : baseEnd_3440260 < baseStart_3440260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440292 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_3440292 : Nat := 118140960795 + 3440292 * 2 ^ 59
def prefixEnd_3440292 : Nat := 4983230072969 + 3 ^ 40 * 3440292 * 2
def baseEnd_3440292 : Nat := 1177682258545172716952261

theorem tailTrace_3440292 : CollatzResearch.WordTrace tailWord_3440292 prefixEnd_3440292 1177682258545172716952261 := by
  unfold tailWord_3440292
  simp only [CollatzResearch.WordTrace]
  refine ⟨62738878826208556970529565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83651838434944742627372753 62738878826208556970529565)
  ·
    refine ⟨23527079559828208863948587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62738878826208556970529565 23527079559828208863948587)
    ·
      refine ⟨35290619339742313295922881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23527079559828208863948587 35290619339742313295922881)
      ·
        refine ⟨26467964504806734971942161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35290619339742313295922881 26467964504806734971942161)
        ·
          refine ⟨19850973378605051228956621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26467964504806734971942161 19850973378605051228956621)
          ·
            refine ⟨7444115016976894210858733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19850973378605051228956621 7444115016976894210858733)
            ·
              refine ⟨2791543131366335329072025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7444115016976894210858733 2791543131366335329072025)
              ·
                refine ⟨2093657348524751496804019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791543131366335329072025 2093657348524751496804019)
                ·
                  refine ⟨3140486022787127245206029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093657348524751496804019 3140486022787127245206029)
                  ·
                    refine ⟨1177682258545172716952261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140486022787127245206029 1177682258545172716952261)
                    ·
                      rfl

theorem cell22_3440292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_3440292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440292 prefixEnd_3440292 := by exact prefixLift 3440292
  have htrace : WordTrace (prefixWord ++ tailWord_3440292) baseStart_3440292 baseEnd_3440292 := by
    simpa [prefixWord, tailWord_3440292, baseEnd_3440292] using wordTrace_append hprefix tailTrace_3440292
  have hstable : (prefixWord ++ tailWord_3440292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440292).length < 2 ^ (prefixWord ++ tailWord_3440292).sum := by decide
  have hdescent : baseEnd_3440292 < baseStart_3440292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440318 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3440318 : Nat := 118140960795 + 3440318 * 2 ^ 59
def prefixEnd_3440318 : Nat := 4983230072969 + 3 ^ 40 * 3440318 * 2
def baseEnd_3440318 : Nat := 1177691158876517315802181

theorem tailTrace_3440318 : CollatzResearch.WordTrace tailWord_3440318 prefixEnd_3440318 1177691158876517315802181 := by
  unfold tailWord_3440318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15684838243790365047688201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83652470633548613587670405 15684838243790365047688201)
  ·
    refine ⟨11763628682842773785766151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15684838243790365047688201 11763628682842773785766151)
    ·
      refine ⟨17645443024264160678649227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11763628682842773785766151 17645443024264160678649227)
      ·
        refine ⟨26468164536396241017973841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17645443024264160678649227 26468164536396241017973841)
        ·
          refine ⟨19851123402297180763480381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26468164536396241017973841 19851123402297180763480381)
          ·
            refine ⟨7444171275861442786305143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19851123402297180763480381 7444171275861442786305143)
            ·
              refine ⟨11166256913792164179457715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444171275861442786305143 11166256913792164179457715)
              ·
                refine ⟨16749385370688246269186573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166256913792164179457715 16749385370688246269186573)
                ·
                  refine ⟨6281019514008092350944965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16749385370688246269186573 6281019514008092350944965)
                  ·
                    refine ⟨1177691158876517315802181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281019514008092350944965 1177691158876517315802181)
                    ·
                      rfl

theorem cell22_3440318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3440318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440318 prefixEnd_3440318 := by exact prefixLift 3440318
  have htrace : WordTrace (prefixWord ++ tailWord_3440318) baseStart_3440318 baseEnd_3440318 := by
    simpa [prefixWord, tailWord_3440318, baseEnd_3440318] using wordTrace_append hprefix tailTrace_3440318
  have hstable : (prefixWord ++ tailWord_3440318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440318).length < 2 ^ (prefixWord ++ tailWord_3440318).sum := by decide
  have hdescent : baseEnd_3440318 < baseStart_3440318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440331 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 6, 3]
def baseStart_3440331 : Nat := 118140960795 + 3440331 * 2 ^ 59
def prefixEnd_3440331 : Nat := 4983230072969 + 3 ^ 40 * 3440331 * 2
def baseEnd_3440331 : Nat := 1177695609042189615227141

theorem tailTrace_3440331 : CollatzResearch.WordTrace tailWord_3440331 prefixEnd_3440331 1177695609042189615227141 := by
  unfold tailWord_3440331
  simp only [CollatzResearch.WordTrace]
  refine ⟨125479180099275823601728847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83652786732850549067819231 125479180099275823601728847)
  ·
    refine ⟨188218770148913735402593271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125479180099275823601728847 188218770148913735402593271)
    ·
      refine ⟨282328155223370603103889907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188218770148913735402593271 282328155223370603103889907)
      ·
        refine ⟨423492232835055904655834861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282328155223370603103889907 423492232835055904655834861)
        ·
          refine ⟨158809587313145964245938073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423492232835055904655834861 158809587313145964245938073)
          ·
            refine ⟨119107190484859473184453555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158809587313145964245938073 119107190484859473184453555)
            ·
              refine ⟨178660785727289209776680333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119107190484859473184453555 178660785727289209776680333)
              ·
                refine ⟨66997794647733453666255125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178660785727289209776680333 66997794647733453666255125)
                ·
                  refine ⟨3140521624112505640605709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66997794647733453666255125 3140521624112505640605709)
                  ·
                    refine ⟨1177695609042189615227141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140521624112505640605709 1177695609042189615227141)
                    ·
                      rfl

theorem cell22_3440331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 3].length) (baseStart_3440331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440331 prefixEnd_3440331 := by exact prefixLift 3440331
  have htrace : WordTrace (prefixWord ++ tailWord_3440331) baseStart_3440331 baseEnd_3440331 := by
    simpa [prefixWord, tailWord_3440331, baseEnd_3440331] using wordTrace_append hprefix tailTrace_3440331
  have hstable : (prefixWord ++ tailWord_3440331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440331).length < 2 ^ (prefixWord ++ tailWord_3440331).sum := by decide
  have hdescent : baseEnd_3440331 < baseStart_3440331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440365 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_3440365 : Nat := 118140960795 + 3440365 * 2 ^ 59
def prefixEnd_3440365 : Nat := 4983230072969 + 3 ^ 40 * 3440365 * 2
def baseEnd_3440365 : Nat := 1177707247937024859877037

theorem tailTrace_3440365 : CollatzResearch.WordTrace tailWord_3440365 prefixEnd_3440365 1177707247937024859877037 := by
  unfold tailWord_3440365
  simp only [CollatzResearch.WordTrace]
  refine ⟨125480420181152647408466549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83653613454101764938977699 125480420181152647408466549)
  ·
    refine ⟨11763789391983060694543739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125480420181152647408466549 11763789391983060694543739)
    ·
      refine ⟨17645684087974591041815609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11763789391983060694543739 17645684087974591041815609)
      ·
        refine ⟨13234263065980943281361707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17645684087974591041815609 13234263065980943281361707)
        ·
          refine ⟨19851394598971414922042561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234263065980943281361707 19851394598971414922042561)
          ·
            refine ⟨14888545949228561191531921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19851394598971414922042561 14888545949228561191531921)
            ·
              refine ⟨11166409461921420893648941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14888545949228561191531921 11166409461921420893648941)
              ·
                refine ⟨4187403548220532835118353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11166409461921420893648941 4187403548220532835118353)
                ·
                  refine ⟨3140552661165399626338765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187403548220532835118353 3140552661165399626338765)
                  ·
                    refine ⟨1177707247937024859877037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140552661165399626338765 1177707247937024859877037)
                    ·
                      rfl

theorem cell22_3440365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_3440365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440365 prefixEnd_3440365 := by exact prefixLift 3440365
  have htrace : WordTrace (prefixWord ++ tailWord_3440365) baseStart_3440365 baseEnd_3440365 := by
    simpa [prefixWord, tailWord_3440365, baseEnd_3440365] using wordTrace_append hprefix tailTrace_3440365
  have hstable : (prefixWord ++ tailWord_3440365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440365).length < 2 ^ (prefixWord ++ tailWord_3440365).sum := by decide
  have hdescent : baseEnd_3440365 < baseStart_3440365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440410 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_3440410 : Nat := 118140960795 + 3440410 * 2 ^ 59
def prefixEnd_3440410 : Nat := 4983230072969 + 3 ^ 40 * 3440410 * 2
def baseEnd_3440410 : Nat := 1177722652356659742501899

theorem tailTrace_3440410 : CollatzResearch.WordTrace tailWord_3440410 prefixEnd_3440410 1177722652356659742501899 := by
  unfold tailWord_3440410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31370515366497405023463671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83654707643993080062569789 31370515366497405023463671)
  ·
    refine ⟨47055773049746107535195507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31370515366497405023463671 47055773049746107535195507)
    ·
      refine ⟨70583659574619161302793261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47055773049746107535195507 70583659574619161302793261)
      ·
        refine ⟨26468872340482185488547473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70583659574619161302793261 26468872340482185488547473)
        ·
          refine ⟨19851654255361639116410605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26468872340482185488547473 19851654255361639116410605)
          ·
            refine ⟨7444370345760614668653977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19851654255361639116410605 7444370345760614668653977)
            ·
              refine ⟨5583277759320461001490483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7444370345760614668653977 5583277759320461001490483)
              ·
                refine ⟨8374916638980691502235725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583277759320461001490483 8374916638980691502235725)
                ·
                  refine ⟨3140593739617759313338397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8374916638980691502235725 3140593739617759313338397)
                  ·
                    refine ⟨1177722652356659742501899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140593739617759313338397 1177722652356659742501899)
                    ·
                      rfl

theorem cell22_3440410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_3440410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440410 prefixEnd_3440410 := by exact prefixLift 3440410
  have htrace : WordTrace (prefixWord ++ tailWord_3440410) baseStart_3440410 baseEnd_3440410 := by
    simpa [prefixWord, tailWord_3440410, baseEnd_3440410] using wordTrace_append hprefix tailTrace_3440410
  have hstable : (prefixWord ++ tailWord_3440410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440410).length < 2 ^ (prefixWord ++ tailWord_3440410).sum := by decide
  have hdescent : baseEnd_3440410 < baseStart_3440410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440453 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_3440453 : Nat := 118140960795 + 3440453 * 2 ^ 59
def prefixEnd_3440453 : Nat := 4983230072969 + 3 ^ 40 * 3440453 * 2
def baseEnd_3440453 : Nat := 1177737372135421963676767

theorem tailTrace_3440453 : CollatzResearch.WordTrace tailWord_3440453 prefixEnd_3440453 1177737372135421963676767 := by
  unfold tailWord_3440453
  simp only [CollatzResearch.WordTrace]
  refine ⟨125483629804833838437670013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83655753203222558958446675 125483629804833838437670013)
  ·
    refine ⟨47056361176812689414126255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125483629804833838437670013 47056361176812689414126255)
    ·
      refine ⟨70584541765219034121189383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47056361176812689414126255 70584541765219034121189383)
      ·
        refine ⟨105876812647828551181784075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70584541765219034121189383 105876812647828551181784075)
        ·
          refine ⟨158815218971742826772676113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105876812647828551181784075 158815218971742826772676113)
          ·
            refine ⟨119111414228807120079507085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158815218971742826772676113 119111414228807120079507085)
            ·
              refine ⟨44666780335802670029815157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119111414228807120079507085 44666780335802670029815157)
              ·
                refine ⟨4187510656481500315295171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44666780335802670029815157 4187510656481500315295171)
                ·
                  refine ⟨6281265984722250472942757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187510656481500315295171 6281265984722250472942757)
                  ·
                    refine ⟨1177737372135421963676767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281265984722250472942757 1177737372135421963676767)
                    ·
                      rfl

theorem cell22_3440453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_3440453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440453 prefixEnd_3440453 := by exact prefixLift 3440453
  have htrace : WordTrace (prefixWord ++ tailWord_3440453) baseStart_3440453 baseEnd_3440453 := by
    simpa [prefixWord, tailWord_3440453, baseEnd_3440453] using wordTrace_append hprefix tailTrace_3440453
  have hstable : (prefixWord ++ tailWord_3440453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440453).length < 2 ^ (prefixWord ++ tailWord_3440453).sum := by decide
  have hdescent : baseEnd_3440453 < baseStart_3440453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440461 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3440461 : Nat := 118140960795 + 3440461 * 2 ^ 59
def prefixEnd_3440461 : Nat := 4983230072969 + 3 ^ 40 * 3440461 * 2
def baseEnd_3440461 : Nat := 1177740110698912609476743

theorem tailTrace_3440461 : CollatzResearch.WordTrace tailWord_3440461 prefixEnd_3440461 1177740110698912609476743 := by
  unfold tailWord_3440461
  simp only [CollatzResearch.WordTrace]
  refine ⟨125483921588804855803961237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83655947725869903869307491 125483921588804855803961237)
  ·
    refine ⟨5882058824475227615810683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125483921588804855803961237 5882058824475227615810683)
    ·
      refine ⟨8823088236712841423716025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5882058824475227615810683 8823088236712841423716025)
      ·
        refine ⟨6617316177534631067787019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8823088236712841423716025 6617316177534631067787019)
        ·
          refine ⟨9925974266301946601680529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617316177534631067787019 9925974266301946601680529)
          ·
            refine ⟨7444480699726459951260397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9925974266301946601680529 7444480699726459951260397)
            ·
              refine ⟨2791680262397422481722649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7444480699726459951260397 2791680262397422481722649)
              ·
                refine ⟨2093760196798066861291987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791680262397422481722649 2093760196798066861291987)
                ·
                  refine ⟨3140640295197100291937981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2093760196798066861291987 3140640295197100291937981)
                  ·
                    refine ⟨1177740110698912609476743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140640295197100291937981 1177740110698912609476743)
                    ·
                      rfl

theorem cell22_3440461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3440461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440461 prefixEnd_3440461 := by exact prefixLift 3440461
  have htrace : WordTrace (prefixWord ++ tailWord_3440461) baseStart_3440461 baseEnd_3440461 := by
    simpa [prefixWord, tailWord_3440461, baseEnd_3440461] using wordTrace_append hprefix tailTrace_3440461
  have hstable : (prefixWord ++ tailWord_3440461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440461).length < 2 ^ (prefixWord ++ tailWord_3440461).sum := by decide
  have hdescent : baseEnd_3440461 < baseStart_3440461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440513 : List Nat := [1, 2, 4, 4, 11]
def baseStart_3440513 : Nat := 118140960795 + 3440513 * 2 ^ 59
def prefixEnd_3440513 : Nat := 4983230072969 + 3 ^ 40 * 3440513 * 2
def baseEnd_3440513 : Nat := 4846740375973669988381

theorem tailTrace_3440513 : CollatzResearch.WordTrace tailWord_3440513 prefixEnd_3440513 4846740375973669988381 := by
  unfold tailWord_3440513
  simp only [CollatzResearch.WordTrace]
  refine ⟨125485818184616468684854193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83657212123077645789902795 125485818184616468684854193)
  ·
    refine ⟨94114363638462351513640645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125485818184616468684854193 94114363638462351513640645)
    ·
      refine ⟨17646443182211690908807621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94114363638462351513640645 17646443182211690908807621)
      ·
        refine ⟨3308708096664692045401429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17646443182211690908807621 3308708096664692045401429)
        ·
          refine ⟨4846740375973669988381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3308708096664692045401429 4846740375973669988381)
          ·
            rfl

theorem cell22_3440513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 11].length) (baseStart_3440513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440513 prefixEnd_3440513 := by exact prefixLift 3440513
  have htrace : WordTrace (prefixWord ++ tailWord_3440513) baseStart_3440513 baseEnd_3440513 := by
    simpa [prefixWord, tailWord_3440513, baseEnd_3440513] using wordTrace_append hprefix tailTrace_3440513
  have hstable : (prefixWord ++ tailWord_3440513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440513).length < 2 ^ (prefixWord ++ tailWord_3440513).sum := by decide
  have hdescent : baseEnd_3440513 < baseStart_3440513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440519 : List Nat := [1, 1, 4, 2, 4, 2, 2, 2, 4]
def baseStart_3440519 : Nat := 118140960795 + 3440519 * 2 ^ 59
def prefixEnd_3440519 : Nat := 4983230072969 + 3 ^ 40 * 3440519 * 2
def baseEnd_3440519 : Nat := 392586655094739930508855

theorem tailTrace_3440519 : CollatzResearch.WordTrace tailWord_3440519 prefixEnd_3440519 392586655094739930508855 := by
  unfold tailWord_3440519
  simp only [CollatzResearch.WordTrace]
  refine ⟨125486037022594731709572611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83657358015063154473048407 125486037022594731709572611)
  ·
    refine ⟨188229055533892097564358917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125486037022594731709572611 188229055533892097564358917)
    ·
      refine ⟨35292947912604768293317297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188229055533892097564358917 35292947912604768293317297)
      ·
        refine ⟨26469710934453576219987973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35292947912604768293317297 26469710934453576219987973)
        ·
          refine ⟨4963070800210045541247745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26469710934453576219987973 4963070800210045541247745)
          ·
            refine ⟨3722303100157534155935809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4963070800210045541247745 3722303100157534155935809)
            ·
              refine ⟨2791727325118150616951857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722303100157534155935809 2791727325118150616951857)
              ·
                refine ⟨2093795493838612962713893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2791727325118150616951857 2093795493838612962713893)
                ·
                  refine ⟨392586655094739930508855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2093795493838612962713893 392586655094739930508855)
                  ·
                    rfl

theorem cell22_3440519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 2, 4].length) (baseStart_3440519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440519 prefixEnd_3440519 := by exact prefixLift 3440519
  have htrace : WordTrace (prefixWord ++ tailWord_3440519) baseStart_3440519 baseEnd_3440519 := by
    simpa [prefixWord, tailWord_3440519, baseEnd_3440519] using wordTrace_append hprefix tailTrace_3440519
  have hstable : (prefixWord ++ tailWord_3440519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440519).length < 2 ^ (prefixWord ++ tailWord_3440519).sum := by decide
  have hdescent : baseEnd_3440519 < baseStart_3440519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440530 : List Nat := [3, 2, 3, 2, 1, 1, 3, 7]
def baseStart_3440530 : Nat := 118140960795 + 3440530 * 2 ^ 59
def prefixEnd_3440530 : Nat := 4983230072969 + 3 ^ 40 * 3440530 * 2
def baseEnd_3440530 : Nat := 130862636756557714389059

theorem tailTrace_3440530 : CollatzResearch.WordTrace tailWord_3440530 prefixEnd_3440530 130862636756557714389059 := by
  unfold tailWord_3440530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31371609556388720147055761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83657625483703253725482029 31371609556388720147055761)
  ·
    refine ⟨23528707167291540110291821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31371609556388720147055761 23528707167291540110291821)
    ·
      refine ⟨8823265187734327541359433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23528707167291540110291821 8823265187734327541359433)
      ·
        refine ⟨6617448890800745656019575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8823265187734327541359433 6617448890800745656019575)
        ·
          refine ⟨9926173336201118484029363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617448890800745656019575 9926173336201118484029363)
          ·
            refine ⟨14889260004301677726044045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926173336201118484029363 14889260004301677726044045)
            ·
              refine ⟨5583472501613129147266517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14889260004301677726044045 5583472501613129147266517)
              ·
                refine ⟨130862636756557714389059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5583472501613129147266517 130862636756557714389059)
                ·
                  rfl

theorem cell22_3440530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_3440530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440530 prefixEnd_3440530 := by exact prefixLift 3440530
  have htrace : WordTrace (prefixWord ++ tailWord_3440530) baseStart_3440530 baseEnd_3440530 := by
    simpa [prefixWord, tailWord_3440530, baseEnd_3440530] using wordTrace_append hprefix tailTrace_3440530
  have hstable : (prefixWord ++ tailWord_3440530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440530).length < 2 ^ (prefixWord ++ tailWord_3440530).sum := by decide
  have hdescent : baseEnd_3440530 < baseStart_3440530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440622 : List Nat := [4, 1, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3440622 : Nat := 118140960795 + 3440622 * 2 ^ 59
def prefixEnd_3440622 : Nat := 4983230072969 + 3 ^ 40 * 3440622 * 2
def baseEnd_3440622 : Nat := 1177795224289161856201249

theorem tailTrace_3440622 : CollatzResearch.WordTrace tailWord_3440622 prefixEnd_3440622 1177795224289161856201249 := by
  unfold tailWord_3440622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15686224217652697537571515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83659862494147720200381413 15686224217652697537571515)
  ·
    refine ⟨23529336326479046306357273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15686224217652697537571515 23529336326479046306357273)
    ·
      refine ⟨17647002244859284729767955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23529336326479046306357273 17647002244859284729767955)
      ·
        refine ⟨26470503367288927094651933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17647002244859284729767955 26470503367288927094651933)
        ·
          refine ⟨9926438762733347660494475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26470503367288927094651933 9926438762733347660494475)
          ·
            refine ⟨14889658144100021490741713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926438762733347660494475 14889658144100021490741713)
            ·
              refine ⟨11167243608075016118056285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14889658144100021490741713 11167243608075016118056285)
              ·
                refine ⟨4187716353028131044271107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11167243608075016118056285 4187716353028131044271107)
                ·
                  refine ⟨6281574529542196566406661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187716353028131044271107 6281574529542196566406661)
                  ·
                    refine ⟨1177795224289161856201249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281574529542196566406661 1177795224289161856201249)
                    ·
                      rfl

theorem cell22_3440622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3440622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440622 prefixEnd_3440622 := by exact prefixLift 3440622
  have htrace : WordTrace (prefixWord ++ tailWord_3440622) baseStart_3440622 baseEnd_3440622 := by
    simpa [prefixWord, tailWord_3440622, baseEnd_3440622] using wordTrace_append hprefix tailTrace_3440622
  have hstable : (prefixWord ++ tailWord_3440622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440622).length < 2 ^ (prefixWord ++ tailWord_3440622).sum := by decide
  have hdescent : baseEnd_3440622 < baseStart_3440622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440635 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 4, 3]
def baseStart_3440635 : Nat := 118140960795 + 3440635 * 2 ^ 59
def prefixEnd_3440635 : Nat := 4983230072969 + 3 ^ 40 * 3440635 * 2
def baseEnd_3440635 : Nat := 1177799674454834155626209

theorem tailTrace_3440635 : CollatzResearch.WordTrace tailWord_3440635 prefixEnd_3440635 1177799674454834155626209 := by
  unfold tailWord_3440635
  simp only [CollatzResearch.WordTrace]
  refine ⟨125490267890174483520795359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83660178593449655680530239 125490267890174483520795359)
  ·
    refine ⟨188235401835261725281193039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125490267890174483520795359 188235401835261725281193039)
    ·
      refine ⟨282353102752892587921789559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188235401835261725281193039 282353102752892587921789559)
      ·
        refine ⟨423529654129338881882684339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282353102752892587921789559 423529654129338881882684339)
        ·
          refine ⟨635294481194008322824026509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423529654129338881882684339 635294481194008322824026509)
          ·
            refine ⟨238235430447753121059009941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 635294481194008322824026509 238235430447753121059009941)
            ·
              refine ⟨11167285802238427549641091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 238235430447753121059009941 11167285802238427549641091)
              ·
                refine ⟨16750928703357641324461637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11167285802238427549641091 16750928703357641324461637)
                ·
                  refine ⟨3140799131879557748336557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16750928703357641324461637 3140799131879557748336557)
                  ·
                    refine ⟨1177799674454834155626209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140799131879557748336557 1177799674454834155626209)
                    ·
                      rfl

theorem cell22_3440635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 3].length) (baseStart_3440635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440635 prefixEnd_3440635 := by exact prefixLift 3440635
  have htrace : WordTrace (prefixWord ++ tailWord_3440635) baseStart_3440635 baseEnd_3440635 := by
    simpa [prefixWord, tailWord_3440635, baseEnd_3440635] using wordTrace_append hprefix tailTrace_3440635
  have hstable : (prefixWord ++ tailWord_3440635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440635).length < 2 ^ (prefixWord ++ tailWord_3440635).sum := by decide
  have hdescent : baseEnd_3440635 < baseStart_3440635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440652 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_3440652 : Nat := 118140960795 + 3440652 * 2 ^ 59
def prefixEnd_3440652 : Nat := 4983230072969 + 3 ^ 40 * 3440652 * 2
def baseEnd_3440652 : Nat := 1177805493902251777951157

theorem tailTrace_3440652 : CollatzResearch.WordTrace tailWord_3440652 prefixEnd_3440652 1177805493902251777951157 := by
  unfold tailWord_3440652
  simp only [CollatzResearch.WordTrace]
  refine ⟨62745443965556447712082105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83660591954075263616109473 62745443965556447712082105)
  ·
    refine ⟨47059082974167335784061579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62745443965556447712082105 47059082974167335784061579)
    ·
      refine ⟨70588624461251003676092369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47059082974167335784061579 70588624461251003676092369)
      ·
        refine ⟨52941468345938252757069277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70588624461251003676092369 52941468345938252757069277)
        ·
          refine ⟨19853050629726844783900979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52941468345938252757069277 19853050629726844783900979)
          ·
            refine ⟨29779575944590267175851469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19853050629726844783900979 29779575944590267175851469)
            ·
              refine ⟨11167340979221350190944301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29779575944590267175851469 11167340979221350190944301)
              ·
                refine ⟨4187752867208006321604113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11167340979221350190944301 4187752867208006321604113)
                ·
                  refine ⟨3140814650406004741203085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4187752867208006321604113 3140814650406004741203085)
                  ·
                    refine ⟨1177805493902251777951157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3140814650406004741203085 1177805493902251777951157)
                    ·
                      rfl

theorem cell22_3440652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_3440652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440652 prefixEnd_3440652 := by exact prefixLift 3440652
  have htrace : WordTrace (prefixWord ++ tailWord_3440652) baseStart_3440652 baseEnd_3440652 := by
    simpa [prefixWord, tailWord_3440652, baseEnd_3440652] using wordTrace_append hprefix tailTrace_3440652
  have hstable : (prefixWord ++ tailWord_3440652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440652).length < 2 ^ (prefixWord ++ tailWord_3440652).sum := by decide
  have hdescent : baseEnd_3440652 < baseStart_3440652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440785 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_3440785 : Nat := 118140960795 + 3440785 * 2 ^ 59
def prefixEnd_3440785 : Nat := 4983230072969 + 3 ^ 40 * 3440785 * 2
def baseEnd_3440785 : Nat := 1177851022520283764375749

theorem tailTrace_3440785 : CollatzResearch.WordTrace tailWord_3440785 prefixEnd_3440785 1177851022520283764375749 := by
  unfold tailWord_3440785
  simp only [CollatzResearch.WordTrace]
  refine ⟨125495738839631059138755809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83663825893087372759170539 125495738839631059138755809)
  ·
    refine ⟨94121804129723294354066857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125495738839631059138755809 94121804129723294354066857)
    ·
      refine ⟨70591353097292470765550143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94121804129723294354066857 70591353097292470765550143)
      ·
        refine ⟨105887029645938706148325215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70591353097292470765550143 105887029645938706148325215)
        ·
          refine ⟨158830544468908059222487823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105887029645938706148325215 158830544468908059222487823)
          ·
            refine ⟨238245816703362088833731735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158830544468908059222487823 238245816703362088833731735)
            ·
              refine ⟨357368725055043133250597603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238245816703362088833731735 357368725055043133250597603)
              ·
                refine ⟨536053087582564699875896405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357368725055043133250597603 536053087582564699875896405)
                ·
                  refine ⟨6281872120108180076670661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 536053087582564699875896405 6281872120108180076670661)
                  ·
                    refine ⟨1177851022520283764375749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281872120108180076670661 1177851022520283764375749)
                    ·
                      rfl

theorem cell22_3440785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_3440785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440785 prefixEnd_3440785 := by exact prefixLift 3440785
  have htrace : WordTrace (prefixWord ++ tailWord_3440785) baseStart_3440785 baseEnd_3440785 := by
    simpa [prefixWord, tailWord_3440785, baseEnd_3440785] using wordTrace_append hprefix tailTrace_3440785
  have hstable : (prefixWord ++ tailWord_3440785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440785).length < 2 ^ (prefixWord ++ tailWord_3440785).sum := by decide
  have hdescent : baseEnd_3440785 < baseStart_3440785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440800 : List Nat := [2, 1, 1, 4, 2, 2, 10]
def baseStart_3440800 : Nat := 118140960795 + 3440800 * 2 ^ 59
def prefixEnd_3440800 : Nat := 4983230072969 + 3 ^ 40 * 3440800 * 2
def baseEnd_3440800 : Nat := 43624302123215878712989

theorem tailTrace_3440800 : CollatzResearch.WordTrace tailWord_3440800 prefixEnd_3440800 43624302123215878712989 := by
  unfold tailWord_3440800
  simp only [CollatzResearch.WordTrace]
  refine ⟨62748142967288358350275927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83664190623051144467034569 62748142967288358350275927)
  ·
    refine ⟨94122214450932537525413891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62748142967288358350275927 94122214450932537525413891)
    ·
      refine ⟨141183321676398806288120837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94122214450932537525413891 141183321676398806288120837)
      ·
        refine ⟨26471872814324776179022657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141183321676398806288120837 26471872814324776179022657)
        ·
          refine ⟨19853904610743582134266993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26471872814324776179022657 19853904610743582134266993)
          ·
            refine ⟨14890428458057686600700245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19853904610743582134266993 14890428458057686600700245)
            ·
              refine ⟨43624302123215878712989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14890428458057686600700245 43624302123215878712989)
              ·
                rfl

theorem cell22_3440800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 10].length) (baseStart_3440800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440800 prefixEnd_3440800 := by exact prefixLift 3440800
  have htrace : WordTrace (prefixWord ++ tailWord_3440800) baseStart_3440800 baseEnd_3440800 := by
    simpa [prefixWord, tailWord_3440800, baseEnd_3440800] using wordTrace_append hprefix tailTrace_3440800
  have hstable : (prefixWord ++ tailWord_3440800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440800).length < 2 ^ (prefixWord ++ tailWord_3440800).sum := by decide
  have hdescent : baseEnd_3440800 < baseStart_3440800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440958 : List Nat := [4, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3440958 : Nat := 118140960795 + 3440958 * 2 ^ 59
def prefixEnd_3440958 : Nat := 4983230072969 + 3 ^ 40 * 3440958 * 2
def baseEnd_3440958 : Nat := 392636747985256326600073

theorem tailTrace_3440958 : CollatzResearch.WordTrace tailWord_3440958 prefixEnd_3440958 392636747985256326600073 := by
  unfold tailWord_3440958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15687756083500538710600441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83668032445336206456535685 15687756083500538710600441)
  ·
    refine ⟨11765817062625404032950331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15687756083500538710600441 11765817062625404032950331)
    ·
      refine ⟨17648725593938106049425497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11765817062625404032950331 17648725593938106049425497)
      ·
        refine ⟨13236544195453579537069123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17648725593938106049425497 13236544195453579537069123)
        ·
          refine ⟨19854816293180369305603685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13236544195453579537069123 19854816293180369305603685)
          ·
            refine ⟨3722778054971319244800691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19854816293180369305603685 3722778054971319244800691)
            ·
              refine ⟨5584167082456978867201037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722778054971319244800691 5584167082456978867201037)
              ·
                refine ⟨2094062655921367075200389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5584167082456978867201037 2094062655921367075200389)
                ·
                  refine ⟨392636747985256326600073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094062655921367075200389 392636747985256326600073)
                  ·
                    rfl

theorem cell22_3440958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3440958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440958 prefixEnd_3440958 := by exact prefixLift 3440958
  have htrace : WordTrace (prefixWord ++ tailWord_3440958) baseStart_3440958 baseEnd_3440958 := by
    simpa [prefixWord, tailWord_3440958, baseEnd_3440958] using wordTrace_append hprefix tailTrace_3440958
  have hstable : (prefixWord ++ tailWord_3440958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440958).length < 2 ^ (prefixWord ++ tailWord_3440958).sum := by decide
  have hdescent : baseEnd_3440958 < baseStart_3440958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3440984 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_3440984 : Nat := 118140960795 + 3440984 * 2 ^ 59
def prefixEnd_3440984 : Nat := 4983230072969 + 3 ^ 40 * 3440984 * 2
def baseEnd_3440984 : Nat := 1177919144287113578650139

theorem tailTrace_3440984 : CollatzResearch.WordTrace tailWord_3440984 prefixEnd_3440984 1177919144287113578650139 := by
  unfold tailWord_3440984
  simp only [CollatzResearch.WordTrace]
  refine ⟨62751498482955058062625003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83668664643940077416833337 62751498482955058062625003)
  ·
    refine ⟨94127247724432587093937505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62751498482955058062625003 94127247724432587093937505)
    ·
      refine ⟨70595435793324440320453129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94127247724432587093937505 70595435793324440320453129)
      ·
        refine ⟨52946576844993330240339847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70595435793324440320453129 52946576844993330240339847)
        ·
          refine ⟨79419865267489995360509771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52946576844993330240339847 79419865267489995360509771)
          ·
            refine ⟨119129797901234993040764657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79419865267489995360509771 119129797901234993040764657)
            ·
              refine ⟨89347348425926244780573493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119129797901234993040764657 89347348425926244780573493)
              ·
                refine ⟨8376313914930585448178765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89347348425926244780573493 8376313914930585448178765)
                ·
                  refine ⟨3141117718098969543067037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8376313914930585448178765 3141117718098969543067037)
                  ·
                    refine ⟨1177919144287113578650139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141117718098969543067037 1177919144287113578650139)
                    ·
                      rfl

theorem cell22_3440984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_3440984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3440984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3440984 prefixEnd_3440984 := by exact prefixLift 3440984
  have htrace : WordTrace (prefixWord ++ tailWord_3440984) baseStart_3440984 baseEnd_3440984 := by
    simpa [prefixWord, tailWord_3440984, baseEnd_3440984] using wordTrace_append hprefix tailTrace_3440984
  have hstable : (prefixWord ++ tailWord_3440984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3440984).length < 2 ^ (prefixWord ++ tailWord_3440984).sum := by decide
  have hdescent : baseEnd_3440984 < baseStart_3440984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3440984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441035 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 1, 3]
def baseStart_3441035 : Nat := 118140960795 + 3441035 * 2 ^ 59
def prefixEnd_3441035 : Nat := 4983230072969 + 3 ^ 40 * 3441035 * 2
def baseEnd_3441035 : Nat := 1177936602629366445624983

theorem tailTrace_3441035 : CollatzResearch.WordTrace tailWord_3441035 prefixEnd_3441035 1177936602629366445624983 := by
  unfold tailWord_3441035
  simp only [CollatzResearch.WordTrace]
  refine ⟨125504857088725351835356559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83669904725816901223571039 125504857088725351835356559)
  ·
    refine ⟨188257285633088027753034839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125504857088725351835356559 188257285633088027753034839)
    ·
      refine ⟨282385928449632041629552259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188257285633088027753034839 282385928449632041629552259)
      ·
        refine ⟨423578892674448062444328389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282385928449632041629552259 423578892674448062444328389)
        ·
          refine ⟨79421042376459011708311573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423578892674448062444328389 79421042376459011708311573)
          ·
            refine ⟨3722861361396516173827105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79421042376459011708311573 3722861361396516173827105)
            ·
              refine ⟨2792146021047387130370329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3722861361396516173827105 2792146021047387130370329)
              ·
                refine ⟨2094109515785540347777747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2792146021047387130370329 2094109515785540347777747)
                ·
                  refine ⟨3141164273678310521666621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094109515785540347777747 3141164273678310521666621)
                  ·
                    refine ⟨1177936602629366445624983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141164273678310521666621 1177936602629366445624983)
                    ·
                      rfl

theorem cell22_3441035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 1, 3].length) (baseStart_3441035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441035 prefixEnd_3441035 := by exact prefixLift 3441035
  have htrace : WordTrace (prefixWord ++ tailWord_3441035) baseStart_3441035 baseEnd_3441035 := by
    simpa [prefixWord, tailWord_3441035, baseEnd_3441035] using wordTrace_append hprefix tailTrace_3441035
  have hstable : (prefixWord ++ tailWord_3441035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441035).length < 2 ^ (prefixWord ++ tailWord_3441035).sum := by decide
  have hdescent : baseEnd_3441035 < baseStart_3441035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441059 : List Nat := [1, 1, 1, 4, 1, 5, 1, 2, 6]
def baseStart_3441059 : Nat := 118140960795 + 3441059 * 2 ^ 59
def prefixEnd_3441059 : Nat := 4983230072969 + 3 ^ 40 * 3441059 * 2
def baseEnd_3441059 : Nat := 392648272773279461008303

theorem tailTrace_3441059 : CollatzResearch.WordTrace tailWord_3441059 prefixEnd_3441059 392648272773279461008303 := by
  unfold tailWord_3441059
  simp only [CollatzResearch.WordTrace]
  refine ⟨125505732440638403934230231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83670488293758935956153487 125505732440638403934230231)
  ·
    refine ⟨188258598660957605901345347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125505732440638403934230231 188258598660957605901345347)
    ·
      refine ⟨282387897991436408852018021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188258598660957605901345347 282387897991436408852018021)
      ·
        refine ⟨52947730873394326659753379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282387897991436408852018021 52947730873394326659753379)
        ·
          refine ⟨79421596310091489989630069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52947730873394326659753379 79421596310091489989630069)
          ·
            refine ⟨7445774654071077186527819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79421596310091489989630069 7445774654071077186527819)
            ·
              refine ⟨11168661981106615779791729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445774654071077186527819 11168661981106615779791729)
              ·
                refine ⟨8376496485829961834843797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11168661981106615779791729 8376496485829961834843797)
                ·
                  refine ⟨392648272773279461008303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8376496485829961834843797 392648272773279461008303)
                  ·
                    rfl

theorem cell22_3441059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 2, 6].length) (baseStart_3441059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441059 prefixEnd_3441059 := by exact prefixLift 3441059
  have htrace : WordTrace (prefixWord ++ tailWord_3441059) baseStart_3441059 baseEnd_3441059 := by
    simpa [prefixWord, tailWord_3441059, baseEnd_3441059] using wordTrace_append hprefix tailTrace_3441059
  have hstable : (prefixWord ++ tailWord_3441059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441059).length < 2 ^ (prefixWord ++ tailWord_3441059).sum := by decide
  have hdescent : baseEnd_3441059 < baseStart_3441059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441074 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_3441074 : Nat := 118140960795 + 3441074 * 2 ^ 59
def prefixEnd_3441074 : Nat := 4983230072969 + 3 ^ 40 * 3441074 * 2
def baseEnd_3441074 : Nat := 1177949953126383343899863

theorem tailTrace_3441074 : CollatzResearch.WordTrace tailWord_3441074 prefixEnd_3441074 1177949953126383343899863 := by
  unfold tailWord_3441074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31376569883896015374006569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83670853023722707664017517 31376569883896015374006569)
  ·
    refine ⟨23532427412922011530504927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31376569883896015374006569 23532427412922011530504927)
    ·
      refine ⟨35298641119383017295757391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23532427412922011530504927 35298641119383017295757391)
      ·
        refine ⟨52947961679074525943636087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35298641119383017295757391 52947961679074525943636087)
        ·
          refine ⟨79421942518611788915454131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52947961679074525943636087 79421942518611788915454131)
          ·
            refine ⟨119132913777917683373181197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79421942518611788915454131 119132913777917683373181197)
            ·
              refine ⟨44674842666719131264942949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119132913777917683373181197 44674842666719131264942949)
              ·
                refine ⟨8376533000009837112176803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44674842666719131264942949 8376533000009837112176803)
                ·
                  refine ⟨12564799500014755668265205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376533000009837112176803 12564799500014755668265205)
                  ·
                    refine ⟨1177949953126383343899863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12564799500014755668265205 1177949953126383343899863)
                    ·
                      rfl

theorem cell22_3441074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_3441074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441074 prefixEnd_3441074 := by exact prefixLift 3441074
  have htrace : WordTrace (prefixWord ++ tailWord_3441074) baseStart_3441074 baseEnd_3441074 := by
    simpa [prefixWord, tailWord_3441074, baseEnd_3441074] using wordTrace_append hprefix tailTrace_3441074
  have hstable : (prefixWord ++ tailWord_3441074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441074).length < 2 ^ (prefixWord ++ tailWord_3441074).sum := by decide
  have hdescent : baseEnd_3441074 < baseStart_3441074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441108 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3441108 : Nat := 118140960795 + 3441108 * 2 ^ 59
def prefixEnd_3441108 : Nat := 4983230072969 + 3 ^ 40 * 3441108 * 2
def baseEnd_3441108 : Nat := 1177961592021218588549759

theorem tailTrace_3441108 : CollatzResearch.WordTrace tailWord_3441108 prefixEnd_3441108 1177961592021218588549759 := by
  unfold tailWord_3441108
  simp only [CollatzResearch.WordTrace]
  refine ⟨62753759808730442651381989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83671679744973923535175985 62753759808730442651381989)
  ·
    refine ⟨11766329964136957997134123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62753759808730442651381989 11766329964136957997134123)
    ·
      refine ⟨17649494946205436995701185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11766329964136957997134123 17649494946205436995701185)
      ·
        refine ⟨13237121209654077746775889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17649494946205436995701185 13237121209654077746775889)
        ·
          refine ⟨9927840907240558310081917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13237121209654077746775889 9927840907240558310081917)
          ·
            refine ⟨3722940340215209366280719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9927840907240558310081917 3722940340215209366280719)
            ·
              refine ⟨5584410510322814049421079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722940340215209366280719 5584410510322814049421079)
              ·
                refine ⟨8376615765484221074131619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584410510322814049421079 8376615765484221074131619)
                ·
                  refine ⟨12564923648226331611197429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376615765484221074131619 12564923648226331611197429)
                  ·
                    refine ⟨1177961592021218588549759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12564923648226331611197429 1177961592021218588549759)
                    ·
                      rfl

theorem cell22_3441108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3441108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441108 prefixEnd_3441108 := by exact prefixLift 3441108
  have htrace : WordTrace (prefixWord ++ tailWord_3441108) baseStart_3441108 baseEnd_3441108 := by
    simpa [prefixWord, tailWord_3441108, baseEnd_3441108] using wordTrace_append hprefix tailTrace_3441108
  have hstable : (prefixWord ++ tailWord_3441108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441108).length < 2 ^ (prefixWord ++ tailWord_3441108).sum := by decide
  have hdescent : baseEnd_3441108 < baseStart_3441108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441138 : List Nat := [3, 2, 1, 4, 3, 1, 8]
def baseStart_3441138 : Nat := 118140960795 + 3441138 * 2 ^ 59
def prefixEnd_3441138 : Nat := 4983230072969 + 3 ^ 40 * 3441138 * 2
def baseEnd_3441138 : Nat := 43628587467937352233321

theorem tailTrace_3441138 : CollatzResearch.WordTrace tailWord_3441138 prefixEnd_3441138 43628587467937352233321 := by
  unfold tailWord_3441138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31377153451838050106589017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83672409204901466950904045 31377153451838050106589017)
  ·
    refine ⟨23532865088878537579941763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31377153451838050106589017 23532865088878537579941763)
    ·
      refine ⟨35299297633317806369912645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23532865088878537579941763 35299297633317806369912645)
      ·
        refine ⟨6618618306247088694358621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35299297633317806369912645 6618618306247088694358621)
        ·
          refine ⟨2481981864842658260384483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6618618306247088694358621 2481981864842658260384483)
          ·
            refine ⟨3722972797263987390576725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481981864842658260384483 3722972797263987390576725)
            ·
              refine ⟨43628587467937352233321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3722972797263987390576725 43628587467937352233321)
              ·
                rfl

theorem cell22_3441138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 8].length) (baseStart_3441138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441138 prefixEnd_3441138 := by exact prefixLift 3441138
  have htrace : WordTrace (prefixWord ++ tailWord_3441138) baseStart_3441138 baseEnd_3441138 := by
    simpa [prefixWord, tailWord_3441138, baseEnd_3441138] using wordTrace_append hprefix tailTrace_3441138
  have hstable : (prefixWord ++ tailWord_3441138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441138).length < 2 ^ (prefixWord ++ tailWord_3441138).sum := by decide
  have hdescent : baseEnd_3441138 < baseStart_3441138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441149 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 7]
def baseStart_3441149 : Nat := 118140960795 + 3441149 * 2 ^ 59
def prefixEnd_3441149 : Nat := 4983230072969 + 3 ^ 40 * 3441149 * 2
def baseEnd_3441149 : Nat := 392658542386369382758211

theorem tailTrace_3441149 : CollatzResearch.WordTrace tailWord_3441149 prefixEnd_3441149 392658542386369382758211 := by
  unfold tailWord_3441149
  simp only [CollatzResearch.WordTrace]
  refine ⟨125509015010312349305006501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83672676673541566203337667 125509015010312349305006501)
  ·
    refine ⟨23532940314433565494688719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125509015010312349305006501 23532940314433565494688719)
    ·
      refine ⟨35299410471650348242033079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23532940314433565494688719 35299410471650348242033079)
      ·
        refine ⟨52949115707475522363049619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35299410471650348242033079 52949115707475522363049619)
        ·
          refine ⟨79423673561213283544574429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52949115707475522363049619 79423673561213283544574429)
          ·
            refine ⟨29783877585454981329215411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79423673561213283544574429 29783877585454981329215411)
            ·
              refine ⟨44675816378182471993823117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29783877585454981329215411 44675816378182471993823117)
              ·
                refine ⟨16753431141818426997683669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44675816378182471993823117 16753431141818426997683669)
                ·
                  refine ⟨392658542386369382758211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16753431141818426997683669 392658542386369382758211)
                  ·
                    rfl

theorem cell22_3441149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_3441149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441149 prefixEnd_3441149 := by exact prefixLift 3441149
  have htrace : WordTrace (prefixWord ++ tailWord_3441149) baseStart_3441149 baseEnd_3441149 := by
    simpa [prefixWord, tailWord_3441149, baseEnd_3441149] using wordTrace_append hprefix tailTrace_3441149
  have hstable : (prefixWord ++ tailWord_3441149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441149).length < 2 ^ (prefixWord ++ tailWord_3441149).sum := by decide
  have hdescent : baseEnd_3441149 < baseStart_3441149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441153 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3441153 : Nat := 118140960795 + 3441153 * 2 ^ 59
def prefixEnd_3441153 : Nat := 4983230072969 + 3 ^ 40 * 3441153 * 2
def baseEnd_3441153 : Nat := 1177976996440853471174621

theorem tailTrace_3441153 : CollatzResearch.WordTrace tailWord_3441153 prefixEnd_3441153 1177976996440853471174621 := by
  unfold tailWord_3441153
  simp only [CollatzResearch.WordTrace]
  refine ⟨125509160902297857988152113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83672773934865238658768075 125509160902297857988152113)
  ·
    refine ⟨94131870676723393491114085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125509160902297857988152113 94131870676723393491114085)
    ·
      refine ⟨17649725751885636279583891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94131870676723393491114085 17649725751885636279583891)
      ·
        refine ⟨26474588627828454419375837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17649725751885636279583891 26474588627828454419375837)
        ·
          refine ⟨9927970735435670407265939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26474588627828454419375837 9927970735435670407265939)
          ·
            refine ⟨14891956103153505610898909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9927970735435670407265939 14891956103153505610898909)
            ·
              refine ⟨5584483538682564604087091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14891956103153505610898909 5584483538682564604087091)
              ·
                refine ⟨8376725308023846906130637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584483538682564604087091 8376725308023846906130637)
                ·
                  refine ⟨3141271990508942589798989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8376725308023846906130637 3141271990508942589798989)
                  ·
                    refine ⟨1177976996440853471174621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141271990508942589798989 1177976996440853471174621)
                    ·
                      rfl

theorem cell22_3441153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3441153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441153 prefixEnd_3441153 := by exact prefixLift 3441153
  have htrace : WordTrace (prefixWord ++ tailWord_3441153) baseStart_3441153 baseEnd_3441153 := by
    simpa [prefixWord, tailWord_3441153, baseEnd_3441153] using wordTrace_append hprefix tailTrace_3441153
  have hstable : (prefixWord ++ tailWord_3441153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441153).length < 2 ^ (prefixWord ++ tailWord_3441153).sum := by decide
  have hdescent : baseEnd_3441153 < baseStart_3441153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441196 : List Nat := [2, 2, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_3441196 : Nat := 118140960795 + 3441196 * 2 ^ 59
def prefixEnd_3441196 : Nat := 4983230072969 + 3 ^ 40 * 3441196 * 2
def baseEnd_3441196 : Nat := 1177991716219615692349489

theorem tailTrace_3441196 : CollatzResearch.WordTrace tailWord_3441196 prefixEnd_3441196 1177991716219615692349489 := by
  unfold tailWord_3441196
  simp only [CollatzResearch.WordTrace]
  refine ⟨62755364620571038165983721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83673819494094717554644961 62755364620571038165983721)
  ·
    refine ⟨47066523465428278624487791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62755364620571038165983721 47066523465428278624487791)
    ·
      refine ⟨70599785198142417936731687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47066523465428278624487791 70599785198142417936731687)
      ·
        refine ⟨105899677797213626905097531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70599785198142417936731687 105899677797213626905097531)
        ·
          refine ⟨158849516695820440357646297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105899677797213626905097531 158849516695820440357646297)
          ·
            refine ⟨119137137521865330268234723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158849516695820440357646297 119137137521865330268234723)
            ·
              refine ⟨178705706282797995402352085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119137137521865330268234723 178705706282797995402352085)
              ·
                refine ⟨4188414991003078017242627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 178705706282797995402352085 4188414991003078017242627)
                ·
                  refine ⟨6282622486504617025863941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188414991003078017242627 6282622486504617025863941)
                  ·
                    refine ⟨1177991716219615692349489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6282622486504617025863941 1177991716219615692349489)
                    ·
                      rfl

theorem cell22_3441196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_3441196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441196 prefixEnd_3441196 := by exact prefixLift 3441196
  have htrace : WordTrace (prefixWord ++ tailWord_3441196) baseStart_3441196 baseEnd_3441196 := by
    simpa [prefixWord, tailWord_3441196, baseEnd_3441196] using wordTrace_append hprefix tailTrace_3441196
  have hstable : (prefixWord ++ tailWord_3441196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441196).length < 2 ^ (prefixWord ++ tailWord_3441196).sum := by decide
  have hdescent : baseEnd_3441196 < baseStart_3441196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441204 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3441204 : Nat := 118140960795 + 3441204 * 2 ^ 59
def prefixEnd_3441204 : Nat := 4983230072969 + 3 ^ 40 * 3441204 * 2
def baseEnd_3441204 : Nat := 1177994454783106338149465

theorem tailTrace_3441204 : CollatzResearch.WordTrace tailWord_3441204 prefixEnd_3441204 1177994454783106338149465 := by
  unfold tailWord_3441204
  simp only [CollatzResearch.WordTrace]
  refine ⟨62755510512556546849129333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83674014016742062465505777 62755510512556546849129333)
  ·
    refine ⟨5883329110552176267105875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62755510512556546849129333 5883329110552176267105875)
    ·
      refine ⟨8824993665828264400658813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5883329110552176267105875 8824993665828264400658813)
      ·
        refine ⟨3309372624685599150247055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8824993665828264400658813 3309372624685599150247055)
        ·
          refine ⟨4964058937028398725370583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3309372624685599150247055 4964058937028398725370583)
          ·
            refine ⟨7446088405542598088055875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964058937028398725370583 7446088405542598088055875)
            ·
              refine ⟨11169132608313897132083813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446088405542598088055875 11169132608313897132083813)
              ·
                refine ⟨2094212364058855712265715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11169132608313897132083813 2094212364058855712265715)
                ·
                  refine ⟨3141318546088283568398573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2094212364058855712265715 3141318546088283568398573)
                  ·
                    refine ⟨1177994454783106338149465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141318546088283568398573 1177994454783106338149465)
                    ·
                      rfl

theorem cell22_3441204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3441204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441204 prefixEnd_3441204 := by exact prefixLift 3441204
  have htrace : WordTrace (prefixWord ++ tailWord_3441204) baseStart_3441204 baseEnd_3441204 := by
    simpa [prefixWord, tailWord_3441204, baseEnd_3441204] using wordTrace_append hprefix tailTrace_3441204
  have hstable : (prefixWord ++ tailWord_3441204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441204).length < 2 ^ (prefixWord ++ tailWord_3441204).sum := by decide
  have hdescent : baseEnd_3441204 < baseStart_3441204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441226 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_3441226 : Nat := 118140960795 + 3441226 * 2 ^ 59
def prefixEnd_3441226 : Nat := 4983230072969 + 3 ^ 40 * 3441226 * 2
def baseEnd_3441226 : Nat := 1178001985832705614099397

theorem tailTrace_3441226 : CollatzResearch.WordTrace tailWord_3441226 prefixEnd_3441226 1178001985832705614099397 := by
  unfold tailWord_3441226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31377955857758347863889883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83674548954022260970373021 31377955857758347863889883)
  ·
    refine ⟨47066933786637521795834825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31377955857758347863889883 47066933786637521795834825)
    ·
      refine ⟨35300200339978141346876119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47066933786637521795834825 35300200339978141346876119)
      ·
        refine ⟨52950300509967212020314179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35300200339978141346876119 52950300509967212020314179)
        ·
          refine ⟨79425450764950818030471269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52950300509967212020314179 79425450764950818030471269)
          ·
            refine ⟨14892272018428278380713363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79425450764950818030471269 14892272018428278380713363)
            ·
              refine ⟨22338408027642417571070045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14892272018428278380713363 22338408027642417571070045)
              ·
                refine ⟨8376903010365906589151267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22338408027642417571070045 8376903010365906589151267)
                ·
                  refine ⟨12565354515548859883726901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376903010365906589151267 12565354515548859883726901)
                  ·
                    refine ⟨1178001985832705614099397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12565354515548859883726901 1178001985832705614099397)
                    ·
                      rfl

theorem cell22_3441226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_3441226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441226 prefixEnd_3441226 := by exact prefixLift 3441226
  have htrace : WordTrace (prefixWord ++ tailWord_3441226) baseStart_3441226 baseEnd_3441226 := by
    simpa [prefixWord, tailWord_3441226, baseEnd_3441226] using wordTrace_append hprefix tailTrace_3441226
  have hstable : (prefixWord ++ tailWord_3441226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441226).length < 2 ^ (prefixWord ++ tailWord_3441226).sum := by decide
  have hdescent : baseEnd_3441226 < baseStart_3441226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441277 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_3441277 : Nat := 118140960795 + 3441277 * 2 ^ 59
def prefixEnd_3441277 : Nat := 4983230072969 + 3 ^ 40 * 3441277 * 2
def baseEnd_3441277 : Nat := 1178019444174958481074241

theorem tailTrace_3441277 : CollatzResearch.WordTrace tailWord_3441277 prefixEnd_3441277 1178019444174958481074241 := by
  unfold tailWord_3441277
  simp only [CollatzResearch.WordTrace]
  refine ⟨125513683553848627165666085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83675789035899084777110723 125513683553848627165666085)
  ·
    refine ⟨23533815666346617593562391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125513683553848627165666085 23533815666346617593562391)
    ·
      refine ⟨35300723499519926390343587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23533815666346617593562391 35300723499519926390343587)
      ·
        refine ⟨52951085249279889585515381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35300723499519926390343587 52951085249279889585515381)
        ·
          refine ⟨4964164242119989648642067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52951085249279889585515381 4964164242119989648642067)
          ·
            refine ⟨7446246363179984472963101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964164242119989648642067 7446246363179984472963101)
            ·
              refine ⟨2792342386192494177361163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7446246363179984472963101 2792342386192494177361163)
              ·
                refine ⟨4188513579288741266041745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2792342386192494177361163 4188513579288741266041745)
                ·
                  refine ⟨3141385184466555949531309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4188513579288741266041745 3141385184466555949531309)
                  ·
                    refine ⟨1178019444174958481074241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141385184466555949531309 1178019444174958481074241)
                    ·
                      rfl

theorem cell22_3441277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_3441277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441277 prefixEnd_3441277 := by exact prefixLift 3441277
  have htrace : WordTrace (prefixWord ++ tailWord_3441277) baseStart_3441277 baseEnd_3441277 := by
    simpa [prefixWord, tailWord_3441277, baseEnd_3441277] using wordTrace_append hprefix tailTrace_3441277
  have hstable : (prefixWord ++ tailWord_3441277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441277).length < 2 ^ (prefixWord ++ tailWord_3441277).sum := by decide
  have hdescent : baseEnd_3441277 < baseStart_3441277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441290 : List Nat := [3, 1, 2, 3, 3, 2, 2, 6]
def baseStart_3441290 : Nat := 118140960795 + 3441290 * 2 ^ 59
def prefixEnd_3441290 : Nat := 4983230072969 + 3 ^ 40 * 3441290 * 2
def baseEnd_3441290 : Nat := 130891543815625642277689

theorem tailTrace_3441290 : CollatzResearch.WordTrace tailWord_3441290 prefixEnd_3441290 130891543815625642277689 := by
  unfold tailWord_3441290
  simp only [CollatzResearch.WordTrace]
  refine ⟨31378539425700382596472331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83676105135201020257259549 31378539425700382596472331)
  ·
    refine ⟨47067809138550573894708497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31378539425700382596472331 47067809138550573894708497)
    ·
      refine ⟨35300856853912930421031373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47067809138550573894708497 35300856853912930421031373)
      ·
        refine ⟨13237821320217348907886765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35300856853912930421031373 13237821320217348907886765)
        ·
          refine ⟨4964182995081505840457537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13237821320217348907886765 4964182995081505840457537)
          ·
            refine ⟨3723137246311129380343153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4964182995081505840457537 3723137246311129380343153)
            ·
              refine ⟨2792352934733347035257365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3723137246311129380343153 2792352934733347035257365)
              ·
                refine ⟨130891543815625642277689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2792352934733347035257365 130891543815625642277689)
                ·
                  rfl

theorem cell22_3441290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_3441290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441290 prefixEnd_3441290 := by exact prefixLift 3441290
  have htrace : WordTrace (prefixWord ++ tailWord_3441290) baseStart_3441290 baseEnd_3441290 := by
    simpa [prefixWord, tailWord_3441290, baseEnd_3441290] using wordTrace_append hprefix tailTrace_3441290
  have hstable : (prefixWord ++ tailWord_3441290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441290).length < 2 ^ (prefixWord ++ tailWord_3441290).sum := by decide
  have hdescent : baseEnd_3441290 < baseStart_3441290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441376 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_3441376 : Nat := 118140960795 + 3441376 * 2 ^ 59
def prefixEnd_3441376 : Nat := 4983230072969 + 3 ^ 40 * 3441376 * 2
def baseEnd_3441376 : Nat := 1178053333898155222848937

theorem tailTrace_3441376 : CollatzResearch.WordTrace tailWord_3441376 prefixEnd_3441376 1178053333898155222848937 := by
  unfold tailWord_3441376
  simp only [CollatzResearch.WordTrace]
  refine ⟨62758647190244983536759991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83678196253659978049013321 62758647190244983536759991)
  ·
    refine ⟨94137970785367475305139987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62758647190244983536759991 94137970785367475305139987)
    ·
      refine ⟨141206956178051212957709981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94137970785367475305139987 141206956178051212957709981)
      ·
        refine ⟨52952608566769204859141243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141206956178051212957709981 52952608566769204859141243)
        ·
          refine ⟨79428912850153807288711865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52952608566769204859141243 79428912850153807288711865)
          ·
            refine ⟨59571684637615355466533899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79428912850153807288711865 59571684637615355466533899)
            ·
              refine ⟨89357526956423033199800849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59571684637615355466533899 89357526956423033199800849)
              ·
                refine ⟨67018145217317274899850637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89357526956423033199800849 67018145217317274899850637)
                ·
                  refine ⟨25131804456493978087443989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67018145217317274899850637 25131804456493978087443989)
                  ·
                    refine ⟨1178053333898155222848937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25131804456493978087443989 1178053333898155222848937)
                    ·
                      rfl

theorem cell22_3441376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_3441376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441376 prefixEnd_3441376 := by exact prefixLift 3441376
  have htrace : WordTrace (prefixWord ++ tailWord_3441376) baseStart_3441376 baseEnd_3441376 := by
    simpa [prefixWord, tailWord_3441376, baseEnd_3441376] using wordTrace_append hprefix tailTrace_3441376
  have hstable : (prefixWord ++ tailWord_3441376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441376).length < 2 ^ (prefixWord ++ tailWord_3441376).sum := by decide
  have hdescent : baseEnd_3441376 < baseStart_3441376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441380 : List Nat := [2, 3, 1, 1, 1, 5, 1, 4, 4]
def baseStart_3441380 : Nat := 118140960795 + 3441380 * 2 ^ 59
def prefixEnd_3441380 : Nat := 4983230072969 + 3 ^ 40 * 3441380 * 2
def baseEnd_3441380 : Nat := 392684901059966848582975

theorem tailTrace_3441380 : CollatzResearch.WordTrace tailWord_3441380 prefixEnd_3441380 392684901059966848582975 := by
  unfold tailWord_3441380
  simp only [CollatzResearch.WordTrace]
  refine ⟨62758720136237737878332797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83678293514983650504443729 62758720136237737878332797)
  ·
    refine ⟨23534520051089151704374799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62758720136237737878332797 23534520051089151704374799)
    ·
      refine ⟨35301780076633727556562199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23534520051089151704374799 35301780076633727556562199)
      ·
        refine ⟨52952670114950591334843299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35301780076633727556562199 52952670114950591334843299)
        ·
          refine ⟨79429005172425887002264949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52952670114950591334843299 79429005172425887002264949)
          ·
            refine ⟨7446469234914926906462339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79429005172425887002264949 7446469234914926906462339)
            ·
              refine ⟨11169703852372390359693509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446469234914926906462339 11169703852372390359693509)
              ·
                refine ⟨2094319472319823192442533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11169703852372390359693509 2094319472319823192442533)
                ·
                  refine ⟨392684901059966848582975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094319472319823192442533 392684901059966848582975)
                  ·
                    rfl

theorem cell22_3441380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_3441380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441380 prefixEnd_3441380 := by exact prefixLift 3441380
  have htrace : WordTrace (prefixWord ++ tailWord_3441380) baseStart_3441380 baseEnd_3441380 := by
    simpa [prefixWord, tailWord_3441380, baseEnd_3441380] using wordTrace_append hprefix tailTrace_3441380
  have hstable : (prefixWord ++ tailWord_3441380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441380).length < 2 ^ (prefixWord ++ tailWord_3441380).sum := by decide
  have hdescent : baseEnd_3441380 < baseStart_3441380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441410 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3441410 : Nat := 118140960795 + 3441410 * 2 ^ 59
def prefixEnd_3441410 : Nat := 4983230072969 + 3 ^ 40 * 3441410 * 2
def baseEnd_3441410 : Nat := 1178064972792990467498833

theorem tailTrace_3441410 : CollatzResearch.WordTrace tailWord_3441410 prefixEnd_3441410 1178064972792990467498833 := by
  unfold tailWord_3441410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379633615591697720064421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83679022974911193920171789 31379633615591697720064421)
  ·
    refine ⟨5883681302923443322512079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31379633615591697720064421 5883681302923443322512079)
    ·
      refine ⟨8825521954385164983768119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5883681302923443322512079 8825521954385164983768119)
      ·
        refine ⟨13238282931577747475652179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8825521954385164983768119 13238282931577747475652179)
        ·
          refine ⟨19857424397366621213478269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13238282931577747475652179 19857424397366621213478269)
          ·
            refine ⟨7446534149012482955054351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19857424397366621213478269 7446534149012482955054351)
            ·
              refine ⟨11169801223518724432581527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446534149012482955054351 11169801223518724432581527)
              ·
                refine ⟨16754701835278086648872291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11169801223518724432581527 16754701835278086648872291)
                ·
                  refine ⟨25132052752917129973308437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16754701835278086648872291 25132052752917129973308437)
                  ·
                    refine ⟨1178064972792990467498833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25132052752917129973308437 1178064972792990467498833)
                    ·
                      rfl

theorem cell22_3441410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3441410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441410 prefixEnd_3441410 := by exact prefixLift 3441410
  have htrace : WordTrace (prefixWord ++ tailWord_3441410) baseStart_3441410 baseEnd_3441410 := by
    simpa [prefixWord, tailWord_3441410, baseEnd_3441410] using wordTrace_append hprefix tailTrace_3441410
  have hstable : (prefixWord ++ tailWord_3441410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441410).length < 2 ^ (prefixWord ++ tailWord_3441410).sum := by decide
  have hdescent : baseEnd_3441410 < baseStart_3441410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441423 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 5, 3]
def baseStart_3441423 : Nat := 118140960795 + 3441423 * 2 ^ 59
def prefixEnd_3441423 : Nat := 4983230072969 + 3 ^ 40 * 3441423 * 2
def baseEnd_3441423 : Nat := 1178069422958662766923793

theorem tailTrace_3441423 : CollatzResearch.WordTrace tailWord_3441423 prefixEnd_3441423 1178069422958662766923793 := by
  unfold tailWord_3441423
  simp only [CollatzResearch.WordTrace]
  refine ⟨125519008611319694100480923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83679339074213129400320615 125519008611319694100480923)
  ·
    refine ⟨188278512916979541150721385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125519008611319694100480923 188278512916979541150721385)
    ·
      refine ⟨141208884687734655863041039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188278512916979541150721385 141208884687734655863041039)
      ·
        refine ⟨211813327031601983794561559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141208884687734655863041039 211813327031601983794561559)
        ·
          refine ⟨317719990547402975691842339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211813327031601983794561559 317719990547402975691842339)
          ·
            refine ⟨476579985821104463537763509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317719990547402975691842339 476579985821104463537763509)
            ·
              refine ⟨44679373670728543456665329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476579985821104463537763509 44679373670728543456665329)
              ·
                refine ⟨33509530253046407592498997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44679373670728543456665329 33509530253046407592498997)
                ·
                  refine ⟨3141518461223100711796781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33509530253046407592498997 3141518461223100711796781)
                  ·
                    refine ⟨1178069422958662766923793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141518461223100711796781 1178069422958662766923793)
                    ·
                      rfl

theorem cell22_3441423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_3441423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441423 prefixEnd_3441423 := by exact prefixLift 3441423
  have htrace : WordTrace (prefixWord ++ tailWord_3441423) baseStart_3441423 baseEnd_3441423 := by
    simpa [prefixWord, tailWord_3441423, baseEnd_3441423] using wordTrace_append hprefix tailTrace_3441423
  have hstable : (prefixWord ++ tailWord_3441423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441423).length < 2 ^ (prefixWord ++ tailWord_3441423).sum := by decide
  have hdescent : baseEnd_3441423 < baseStart_3441423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441440 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_3441440 : Nat := 118140960795 + 3441440 * 2 ^ 59
def prefixEnd_3441440 : Nat := 4983230072969 + 3 ^ 40 * 3441440 * 2
def baseEnd_3441440 : Nat := 1178075242406080389248741

theorem tailTrace_3441440 : CollatzResearch.WordTrace tailWord_3441440 prefixEnd_3441440 1178075242406080389248741 := by
  unfold tailWord_3441440
  simp only [CollatzResearch.WordTrace]
  refine ⟨62759814326129053001924887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83679752434838737335899849 62759814326129053001924887)
  ·
    refine ⟨94139721489193579502887331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62759814326129053001924887 94139721489193579502887331)
    ·
      refine ⟨141209582233790369254330997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94139721489193579502887331 141209582233790369254330997)
      ·
        refine ⟨13238398334417847117593531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141209582233790369254330997 13238398334417847117593531)
        ·
          refine ⟨19857597501626770676390297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13238398334417847117593531 19857597501626770676390297)
          ·
            refine ⟨14893198126220078007292723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19857597501626770676390297 14893198126220078007292723)
            ·
              refine ⟨22339797189330117010939085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14893198126220078007292723 22339797189330117010939085)
              ·
                refine ⟨8377423945998793879102157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22339797189330117010939085 8377423945998793879102157)
                ·
                  refine ⟨3141533979749547704663309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8377423945998793879102157 3141533979749547704663309)
                  ·
                    refine ⟨1178075242406080389248741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141533979749547704663309 1178075242406080389248741)
                    ·
                      rfl

theorem cell22_3441440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_3441440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441440 prefixEnd_3441440 := by exact prefixLift 3441440
  have htrace : WordTrace (prefixWord ++ tailWord_3441440) baseStart_3441440 baseEnd_3441440 := by
    simpa [prefixWord, tailWord_3441440, baseEnd_3441440] using wordTrace_append hprefix tailTrace_3441440
  have hstable : (prefixWord ++ tailWord_3441440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441440).length < 2 ^ (prefixWord ++ tailWord_3441440).sum := by decide
  have hdescent : baseEnd_3441440 < baseStart_3441440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441543 : List Nat := [1, 1, 4, 2, 3, 11]
def baseStart_3441543 : Nat := 118140960795 + 3441543 * 2 ^ 59
def prefixEnd_3441543 : Nat := 4983230072969 + 3 ^ 40 * 3441543 * 2
def baseEnd_3441543 : Nat := 14544574091494104369425

theorem tailTrace_3441543 : CollatzResearch.WordTrace tailWord_3441543 prefixEnd_3441543 14544574091494104369425 := by
  unfold tailWord_3441543
  simp only [CollatzResearch.WordTrace]
  refine ⟨125523385370884954594849283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83682256913923303063232855 125523385370884954594849283)
  ·
    refine ⟨188285078056327431892273925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125523385370884954594849283 188285078056327431892273925)
    ·
      refine ⟨35303452135561393479801361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188285078056327431892273925 35303452135561393479801361)
      ·
        refine ⟨26477589101671045109851021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35303452135561393479801361 26477589101671045109851021)
        ·
          refine ⟨9929095913126641916194133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26477589101671045109851021 9929095913126641916194133)
          ·
            refine ⟨14544574091494104369425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9929095913126641916194133 14544574091494104369425)
            ·
              rfl

theorem cell22_3441543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 11].length) (baseStart_3441543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441543 prefixEnd_3441543 := by exact prefixLift 3441543
  have htrace : WordTrace (prefixWord ++ tailWord_3441543) baseStart_3441543 baseEnd_3441543 := by
    simpa [prefixWord, tailWord_3441543, baseEnd_3441543] using wordTrace_append hprefix tailTrace_3441543
  have hstable : (prefixWord ++ tailWord_3441543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441543).length < 2 ^ (prefixWord ++ tailWord_3441543).sum := by decide
  have hdescent : baseEnd_3441543 < baseStart_3441543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441545 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 2, 4]
def baseStart_3441545 : Nat := 118140960795 + 3441545 * 2 ^ 59
def prefixEnd_3441545 : Nat := 4983230072969 + 3 ^ 40 * 3441545 * 2
def baseEnd_3441545 : Nat := 1178111186051895115373419

theorem tailTrace_3441545 : CollatzResearch.WordTrace tailWord_3441545 prefixEnd_3441545 1178111186051895115373419 := by
  unfold tailWord_3441545
  simp only [CollatzResearch.WordTrace]
  refine ⟨125523458316877708936422089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83682305544585139290948059 125523458316877708936422089)
  ·
    refine ⟨94142593737658281702316567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125523458316877708936422089 94142593737658281702316567)
    ·
      refine ⟨141213890606487422553474851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94142593737658281702316567 141213890606487422553474851)
      ·
        refine ⟨211820835909731133830212277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141213890606487422553474851 211820835909731133830212277)
        ·
          refine ⟨19858203366537293796582401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211820835909731133830212277 19858203366537293796582401)
          ·
            refine ⟨14893652524902970347436801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19858203366537293796582401 14893652524902970347436801)
            ·
              refine ⟨11170239393677227760577601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14893652524902970347436801 11170239393677227760577601)
              ·
                refine ⟨8377679545257920820433201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11170239393677227760577601 8377679545257920820433201)
                ·
                  refine ⟨6283259658943440615324901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8377679545257920820433201 6283259658943440615324901)
                  ·
                    refine ⟨1178111186051895115373419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283259658943440615324901 1178111186051895115373419)
                    ·
                      rfl

theorem cell22_3441545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 4].length) (baseStart_3441545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441545 prefixEnd_3441545 := by exact prefixLift 3441545
  have htrace : WordTrace (prefixWord ++ tailWord_3441545) baseStart_3441545 baseEnd_3441545 := by
    simpa [prefixWord, tailWord_3441545, baseEnd_3441545] using wordTrace_append hprefix tailTrace_3441545
  have hstable : (prefixWord ++ tailWord_3441545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441545).length < 2 ^ (prefixWord ++ tailWord_3441545).sum := by decide
  have hdescent : baseEnd_3441545 < baseStart_3441545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441603 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 7]
def baseStart_3441603 : Nat := 118140960795 + 3441603 * 2 ^ 59
def prefixEnd_3441603 : Nat := 4983230072969 + 3 ^ 40 * 3441603 * 2
def baseEnd_3441603 : Nat := 1178131040637202297423241

theorem tailTrace_3441603 : CollatzResearch.WordTrace tailWord_3441603 prefixEnd_3441603 1178131040637202297423241 := by
  unfold tailWord_3441603
  simp only [CollatzResearch.WordTrace]
  refine ⟨125525573750667584842033463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83683715833778389894688975 125525573750667584842033463)
  ·
    refine ⟨188288360626001377263050195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125525573750667584842033463 188288360626001377263050195)
    ·
      refine ⟨282432540939002065894575293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188288360626001377263050195 282432540939002065894575293)
      ·
        refine ⟨105912202852125774710465735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282432540939002065894575293 105912202852125774710465735)
        ·
          refine ⟨158868304278188662065698603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105912202852125774710465735 158868304278188662065698603)
          ·
            refine ⟨238302456417282993098547905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158868304278188662065698603 238302456417282993098547905)
            ·
              refine ⟨178726842312962244823910929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238302456417282993098547905 178726842312962244823910929)
              ·
                refine ⟨134045131734721683617933197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178726842312962244823910929 134045131734721683617933197)
                ·
                  refine ⟨50266924400520631356724949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134045131734721683617933197 50266924400520631356724949)
                  ·
                    refine ⟨1178131040637202297423241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50266924400520631356724949 1178131040637202297423241)
                    ·
                      rfl

theorem cell22_3441603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_3441603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441603 prefixEnd_3441603 := by exact prefixLift 3441603
  have htrace : WordTrace (prefixWord ++ tailWord_3441603) baseStart_3441603 baseEnd_3441603 := by
    simpa [prefixWord, tailWord_3441603, baseEnd_3441603] using wordTrace_append hprefix tailTrace_3441603
  have hstable : (prefixWord ++ tailWord_3441603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441603).length < 2 ^ (prefixWord ++ tailWord_3441603).sum := by decide
  have hdescent : baseEnd_3441603 < baseStart_3441603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441695 : List Nat := [1, 1, 2, 4, 1, 3, 2, 8]
def baseStart_3441695 : Nat := 118140960795 + 3441695 * 2 ^ 59
def prefixEnd_3441695 : Nat := 4983230072969 + 3 ^ 40 * 3441695 * 2
def baseEnd_3441695 : Nat := 130906948235260524902551

theorem tailTrace_3441695 : CollatzResearch.WordTrace tailWord_3441695 prefixEnd_3441695 130906948235260524902551 := by
  unfold tailWord_3441695
  simp only [CollatzResearch.WordTrace]
  refine ⟨125528929266334284554382539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83685952844222856369588359 125528929266334284554382539)
  ·
    refine ⟨188293393899501426831573809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125528929266334284554382539 188293393899501426831573809)
    ·
      refine ⟨141220045424626070123680357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188293393899501426831573809 141220045424626070123680357)
      ·
        refine ⟨26478758517117388148190067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141220045424626070123680357 26478758517117388148190067)
        ·
          refine ⟨39718137775676082222285101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26478758517117388148190067 39718137775676082222285101)
          ·
            refine ⟨14894301665878530833356913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39718137775676082222285101 14894301665878530833356913)
            ·
              refine ⟨11170726249408898125017685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14894301665878530833356913 11170726249408898125017685)
              ·
                refine ⟨130906948235260524902551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11170726249408898125017685 130906948235260524902551)
                ·
                  rfl

theorem cell22_3441695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 8].length) (baseStart_3441695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441695 prefixEnd_3441695 := by exact prefixLift 3441695
  have htrace : WordTrace (prefixWord ++ tailWord_3441695) baseStart_3441695 baseEnd_3441695 := by
    simpa [prefixWord, tailWord_3441695, baseEnd_3441695] using wordTrace_append hprefix tailTrace_3441695
  have hstable : (prefixWord ++ tailWord_3441695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441695).length < 2 ^ (prefixWord ++ tailWord_3441695).sum := by decide
  have hdescent : baseEnd_3441695 < baseStart_3441695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441697 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3441697 : Nat := 118140960795 + 3441697 * 2 ^ 59
def prefixEnd_3441697 : Nat := 4983230072969 + 3 ^ 40 * 3441697 * 2
def baseEnd_3441697 : Nat := 1178163218758217385572953

theorem tailTrace_3441697 : CollatzResearch.WordTrace tailWord_3441697 prefixEnd_3441697 1178163218758217385572953 := by
  unfold tailWord_3441697
  simp only [CollatzResearch.WordTrace]
  refine ⟨125529002212327038895955345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83686001474884692597303563 125529002212327038895955345)
  ·
    refine ⟨94146751659245279171966509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125529002212327038895955345 94146751659245279171966509)
    ·
      refine ⟨35305031872216979689487441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94146751659245279171966509 35305031872216979689487441)
      ·
        refine ⟨26478773904162734767115581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35305031872216979689487441 26478773904162734767115581)
        ·
          refine ⟨9929540214061025537668343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26478773904162734767115581 9929540214061025537668343)
          ·
            refine ⟨14894310321091538306502515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929540214061025537668343 14894310321091538306502515)
            ·
              refine ⟨22341465481637307459753773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14894310321091538306502515 22341465481637307459753773)
              ·
                refine ⟨8378049555613990297407665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22341465481637307459753773 8378049555613990297407665)
                ·
                  refine ⟨6283537166710492723055749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8378049555613990297407665 6283537166710492723055749)
                  ·
                    refine ⟨1178163218758217385572953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283537166710492723055749 1178163218758217385572953)
                    ·
                      rfl

theorem cell22_3441697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3441697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441697 prefixEnd_3441697 := by exact prefixLift 3441697
  have htrace : WordTrace (prefixWord ++ tailWord_3441697) baseStart_3441697 baseEnd_3441697 := by
    simpa [prefixWord, tailWord_3441697, baseEnd_3441697] using wordTrace_append hprefix tailTrace_3441697
  have hstable : (prefixWord ++ tailWord_3441697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441697).length < 2 ^ (prefixWord ++ tailWord_3441697).sum := by decide
  have hdescent : baseEnd_3441697 < baseStart_3441697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441716 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3441716 : Nat := 118140960795 + 3441716 * 2 ^ 59
def prefixEnd_3441716 : Nat := 4983230072969 + 3 ^ 40 * 3441716 * 2
def baseEnd_3441716 : Nat := 1178169722846507669347895

theorem tailTrace_3441716 : CollatzResearch.WordTrace tailWord_3441716 prefixEnd_3441716 1178169722846507669347895 := by
  unfold tailWord_3441716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62764847599629102570448501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83686463466172136760598001 62764847599629102570448501)
  ·
    refine ⟨5884204462465228365979547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62764847599629102570448501 5884204462465228365979547)
    ·
      refine ⟨8826306693697842548969321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884204462465228365979547 8826306693697842548969321)
      ·
        refine ⟨6619730020273381911726991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8826306693697842548969321 6619730020273381911726991)
        ·
          refine ⟨9929595030410072867590487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619730020273381911726991 9929595030410072867590487)
          ·
            refine ⟨14894392545615109301385731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929595030410072867590487 14894392545615109301385731)
            ·
              refine ⟨22341588818422663952078597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14894392545615109301385731 22341588818422663952078597)
              ·
                refine ⟨4189047903454249491014737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22341588818422663952078597 4189047903454249491014737)
                ·
                  refine ⟨3141785927590687118261053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4189047903454249491014737 3141785927590687118261053)
                  ·
                    refine ⟨1178169722846507669347895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3141785927590687118261053 1178169722846507669347895)
                    ·
                      rfl

theorem cell22_3441716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3441716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441716 prefixEnd_3441716 := by exact prefixLift 3441716
  have htrace : WordTrace (prefixWord ++ tailWord_3441716) baseStart_3441716 baseEnd_3441716 := by
    simpa [prefixWord, tailWord_3441716, baseEnd_3441716] using wordTrace_append hprefix tailTrace_3441716
  have hstable : (prefixWord ++ tailWord_3441716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441716).length < 2 ^ (prefixWord ++ tailWord_3441716).sum := by decide
  have hdescent : baseEnd_3441716 < baseStart_3441716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3441718 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3441718 : Nat := 118140960795 + 3441718 * 2 ^ 59
def prefixEnd_3441718 : Nat := 4983230072969 + 3 ^ 40 * 3441718 * 2
def baseEnd_3441718 : Nat := 392723469162460110265963

theorem tailTrace_3441718 : CollatzResearch.WordTrace tailWord_3441718 prefixEnd_3441718 392723469162460110265963 := by
  unfold tailWord_3441718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845610509078184967654363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83686512096833972988313205 7845610509078184967654363)
  ·
    refine ⟨11768415763617277451481545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7845610509078184967654363 11768415763617277451481545)
    ·
      refine ⟨8826311822712958088611159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11768415763617277451481545 8826311822712958088611159)
      ·
        refine ⟨13239467734069437132916739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8826311822712958088611159 13239467734069437132916739)
        ·
          refine ⟨19859201601104155699375109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13239467734069437132916739 19859201601104155699375109)
          ·
            refine ⟨3723600300207029193632833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19859201601104155699375109 3723600300207029193632833)
            ·
              refine ⟨2792700225155271895224625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3723600300207029193632833 2792700225155271895224625)
              ·
                refine ⟨2094525168866453921418469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2792700225155271895224625 2094525168866453921418469)
                ·
                  refine ⟨392723469162460110265963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2094525168866453921418469 392723469162460110265963)
                  ·
                    rfl

theorem cell22_3441718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3441718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3441718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3441718 prefixEnd_3441718 := by exact prefixLift 3441718
  have htrace : WordTrace (prefixWord ++ tailWord_3441718) baseStart_3441718 baseEnd_3441718 := by
    simpa [prefixWord, tailWord_3441718, baseEnd_3441718] using wordTrace_append hprefix tailTrace_3441718
  have hstable : (prefixWord ++ tailWord_3441718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3441718).length < 2 ^ (prefixWord ++ tailWord_3441718).sum := by decide
  have hdescent : baseEnd_3441718 < baseStart_3441718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3441718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
