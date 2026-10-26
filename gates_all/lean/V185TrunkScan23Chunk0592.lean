import V185TrunkScan23Chunk0591

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3500594 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_3500594 : Nat := 118140960795 + 3500594 * 2 ^ 59
def prefixEnd_3500594 : Nat := 4983230072969 + 3 ^ 40 * 3500594 * 2
def baseEnd_3500594 : Nat := 599162432748394047858689

theorem tailTrace_3500594 : CollatzResearch.WordTrace tailWord_3500594 prefixEnd_3500594 599162432748394047858689 := by
  unfold tailWord_3500594
  simp only [CollatzResearch.WordTrace]
  refine ⟨31919288069988316675683209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85118101519968844468488557 31919288069988316675683209)
  ·
    refine ⟨23939466052491237506762407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31919288069988316675683209 23939466052491237506762407)
    ·
      refine ⟨35909199078736856260143611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23939466052491237506762407 35909199078736856260143611)
      ·
        refine ⟨53863798618105284390215417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35909199078736856260143611 53863798618105284390215417)
        ·
          refine ⟨40397848963578963292661563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53863798618105284390215417 40397848963578963292661563)
          ·
            refine ⟨60596773445368444938992345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40397848963578963292661563 60596773445368444938992345)
            ·
              refine ⟨45447580084026333704244259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60596773445368444938992345 45447580084026333704244259)
              ·
                refine ⟨68171370126039500556366389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45447580084026333704244259 68171370126039500556366389)
                ·
                  refine ⟨6391065949316203177159349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68171370126039500556366389 6391065949316203177159349)
                  ·
                    refine ⟨599162432748394047858689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6391065949316203177159349 599162432748394047858689)
                    ·
                      rfl

theorem cell23_3500594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_3500594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500594 prefixEnd_3500594 := by exact prefixLift 3500594
  have htrace : WordTrace (prefixWord ++ tailWord_3500594) baseStart_3500594 baseEnd_3500594 := by
    simpa [prefixWord, tailWord_3500594, baseEnd_3500594] using wordTrace_append hprefix tailTrace_3500594
  have hstable : (prefixWord ++ tailWord_3500594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500594).length < 2 ^ (prefixWord ++ tailWord_3500594).sum := by decide
  have hdescent : baseEnd_3500594 < baseStart_3500594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500601 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3500601 : Nat := 118140960795 + 3500601 * 2 ^ 59
def prefixEnd_3500601 : Nat := 4983230072969 + 3 ^ 40 * 3500601 * 2
def baseEnd_3500601 : Nat := 1797490892609763616188535

theorem tailTrace_3500601 : CollatzResearch.WordTrace tailWord_3500601 prefixEnd_3500601 1797490892609763616188535 := by
  unfold tailWord_3500601
  simp only [CollatzResearch.WordTrace]
  refine ⟨127677407590927906898237657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85118271727285271265491771 127677407590927906898237657)
  ·
    refine ⟨95758055693195930173678243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127677407590927906898237657 95758055693195930173678243)
    ·
      refine ⟨143637083539793895260517365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95758055693195930173678243 143637083539793895260517365)
      ·
        refine ⟨13465976581855677680673503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143637083539793895260517365 13465976581855677680673503)
        ·
          refine ⟨20198964872783516521010255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13465976581855677680673503 20198964872783516521010255)
          ·
            refine ⟨30298447309175274781515383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20198964872783516521010255 30298447309175274781515383)
            ·
              refine ⟨45447670963762912172273075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30298447309175274781515383 45447670963762912172273075)
              ·
                refine ⟨68171506445644368258409613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45447670963762912172273075 68171506445644368258409613)
                ·
                  refine ⟨25564314917116638096903605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68171506445644368258409613 25564314917116638096903605)
                  ·
                    refine ⟨2396654523479684821584713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25564314917116638096903605 2396654523479684821584713)
                    ·
                      refine ⟨1797490892609763616188535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396654523479684821584713 1797490892609763616188535)
                      ·
                        rfl

theorem cell23_3500601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3500601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500601 prefixEnd_3500601 := by exact prefixLift 3500601
  have htrace : WordTrace (prefixWord ++ tailWord_3500601) baseStart_3500601 baseEnd_3500601 := by
    simpa [prefixWord, tailWord_3500601, baseEnd_3500601] using wordTrace_append hprefix tailTrace_3500601
  have hstable : (prefixWord ++ tailWord_3500601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500601).length < 2 ^ (prefixWord ++ tailWord_3500601).sum := by decide
  have hdescent : baseEnd_3500601 < baseStart_3500601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500625 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 1, 1, 3]
def baseStart_3500625 : Nat := 118140960795 + 3500625 * 2 ^ 59
def prefixEnd_3500625 : Nat := 4983230072969 + 3 ^ 40 * 3500625 * 2
def baseEnd_3500625 : Nat := 1797503216145471522288425

theorem tailTrace_3500625 : CollatzResearch.WordTrace tailWord_3500625 prefixEnd_3500625 1797503216145471522288425 := by
  unfold tailWord_3500625
  simp only [CollatzResearch.WordTrace]
  refine ⟨127678282942840958997111329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85118855295227305998074219 127678282942840958997111329)
  ·
    refine ⟨95758712207130719247833497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127678282942840958997111329 95758712207130719247833497)
    ·
      refine ⟨71819034155348039435875123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95758712207130719247833497 71819034155348039435875123)
      ·
        refine ⟨107728551233022059153812685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71819034155348039435875123 107728551233022059153812685)
        ·
          refine ⟨40398206712383272182679757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107728551233022059153812685 40398206712383272182679757)
          ·
            refine ⟨15149327517143727068504909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40398206712383272182679757 15149327517143727068504909)
            ·
              refine ⟨5680997818928897650689341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15149327517143727068504909 5680997818928897650689341)
              ·
                refine ⟨2130374182098336619008503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5680997818928897650689341 2130374182098336619008503)
                ·
                  refine ⟨3195561273147504928512755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130374182098336619008503 3195561273147504928512755)
                  ·
                    refine ⟨4793341909721257392769133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195561273147504928512755 4793341909721257392769133)
                    ·
                      refine ⟨1797503216145471522288425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4793341909721257392769133 1797503216145471522288425)
                      ·
                        rfl

theorem cell23_3500625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 1, 3].length) (baseStart_3500625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500625 prefixEnd_3500625 := by exact prefixLift 3500625
  have htrace : WordTrace (prefixWord ++ tailWord_3500625) baseStart_3500625 baseEnd_3500625 := by
    simpa [prefixWord, tailWord_3500625, baseEnd_3500625] using wordTrace_append hprefix tailTrace_3500625
  have hstable : (prefixWord ++ tailWord_3500625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500625).length < 2 ^ (prefixWord ++ tailWord_3500625).sum := by decide
  have hdescent : baseEnd_3500625 < baseStart_3500625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500631 : List Nat := [1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_3500631 : Nat := 118140960795 + 3500631 * 2 ^ 59
def prefixEnd_3500631 : Nat := 4983230072969 + 3 ^ 40 * 3500631 * 2
def baseEnd_3500631 : Nat := 1797506297029398498813397

theorem tailTrace_3500631 : CollatzResearch.WordTrace tailWord_3500631 prefixEnd_3500631 1797506297029398498813397 := by
  unfold tailWord_3500631
  simp only [CollatzResearch.WordTrace]
  refine ⟨127678501780819222021829747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85119001187212814681219831 127678501780819222021829747)
  ·
    refine ⟨191517752671228833032744621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127678501780819222021829747 191517752671228833032744621)
    ·
      refine ⟨71819157251710812387279233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191517752671228833032744621 71819157251710812387279233)
      ·
        refine ⟨53864367938783109290459425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71819157251710812387279233 53864367938783109290459425)
        ·
          refine ⟨40398275954087331967844569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53864367938783109290459425 40398275954087331967844569)
          ·
            refine ⟨30298706965565498975883427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40398275954087331967844569 30298706965565498975883427)
            ·
              refine ⟨45448060448348248463825141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30298706965565498975883427 45448060448348248463825141)
              ·
                refine ⟨4260755667032648293483607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45448060448348248463825141 4260755667032648293483607)
                ·
                  refine ⟨6391133500548972440225411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260755667032648293483607 6391133500548972440225411)
                  ·
                    refine ⟨9586700250823458660338117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6391133500548972440225411 9586700250823458660338117)
                    ·
                      refine ⟨1797506297029398498813397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9586700250823458660338117 1797506297029398498813397)
                      ·
                        rfl

theorem cell23_3500631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_3500631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500631 prefixEnd_3500631 := by exact prefixLift 3500631
  have htrace : WordTrace (prefixWord ++ tailWord_3500631) baseStart_3500631 baseEnd_3500631 := by
    simpa [prefixWord, tailWord_3500631, baseEnd_3500631] using wordTrace_append hprefix tailTrace_3500631
  have hstable : (prefixWord ++ tailWord_3500631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500631).length < 2 ^ (prefixWord ++ tailWord_3500631).sum := by decide
  have hdescent : baseEnd_3500631 < baseStart_3500631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500641 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 4, 4]
def baseStart_3500641 : Nat := 118140960795 + 3500641 * 2 ^ 59
def prefixEnd_3500641 : Nat := 4983230072969 + 3 ^ 40 * 3500641 * 2
def baseEnd_3500641 : Nat := 599170477278647819896117

theorem tailTrace_3500641 : CollatzResearch.WordTrace tailWord_3500641 prefixEnd_3500641 599170477278647819896117 := by
  unfold tailWord_3500641
  simp only [CollatzResearch.WordTrace]
  refine ⟨127678866510782993729693777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85119244340521995819795851 127678866510782993729693777)
  ·
    refine ⟨95759149883087245297270333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127678866510782993729693777 95759149883087245297270333)
    ·
      refine ⟨35909681206157716986476375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95759149883087245297270333 35909681206157716986476375)
      ·
        refine ⟨53864521809236575479714563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35909681206157716986476375 53864521809236575479714563)
        ·
          refine ⟨80796782713854863219571845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53864521809236575479714563 80796782713854863219571845)
          ·
            refine ⟨15149396758847786853669721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80796782713854863219571845 15149396758847786853669721)
            ·
              refine ⟨11362047569135840140252291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15149396758847786853669721 11362047569135840140252291)
              ·
                refine ⟨17043071353703760210378437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11362047569135840140252291 17043071353703760210378437)
                ·
                  refine ⟨3195575878819455039445957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17043071353703760210378437 3195575878819455039445957)
                  ·
                    refine ⟨599170477278647819896117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3195575878819455039445957 599170477278647819896117)
                    ·
                      rfl

theorem cell23_3500641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_3500641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500641 prefixEnd_3500641 := by exact prefixLift 3500641
  have htrace : WordTrace (prefixWord ++ tailWord_3500641) baseStart_3500641 baseEnd_3500641 := by
    simpa [prefixWord, tailWord_3500641, baseEnd_3500641] using wordTrace_append hprefix tailTrace_3500641
  have hstable : (prefixWord ++ tailWord_3500641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500641).length < 2 ^ (prefixWord ++ tailWord_3500641).sum := by decide
  have hdescent : baseEnd_3500641 < baseStart_3500641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500644 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6]
def baseStart_3500644 : Nat := 118140960795 + 3500644 * 2 ^ 59
def prefixEnd_3500644 : Nat := 4983230072969 + 3 ^ 40 * 3500644 * 2
def baseEnd_3500644 : Nat := 1797512972277906947950837

theorem tailTrace_3500644 : CollatzResearch.WordTrace tailWord_3500644 prefixEnd_3500644 1797512972277906947950837 := by
  unfold tailWord_3500644
  simp only [CollatzResearch.WordTrace]
  refine ⟨63839487964886062621026493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85119317286514750161368657 63839487964886062621026493)
  ·
    refine ⟨23939807986832273482884935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63839487964886062621026493 23939807986832273482884935)
    ·
      refine ⟨35909711980248410224327403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23939807986832273482884935 35909711980248410224327403)
      ·
        refine ⟨53864567970372615336491105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35909711980248410224327403 53864567970372615336491105)
        ·
          refine ⟨40398425977779461502368329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53864567970372615336491105 40398425977779461502368329)
          ·
            refine ⟨30298819483334596126776247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40398425977779461502368329 30298819483334596126776247)
            ·
              refine ⟨45448229225001894190164371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30298819483334596126776247 45448229225001894190164371)
              ·
                refine ⟨68172343837502841285246557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45448229225001894190164371 68172343837502841285246557)
                ·
                  refine ⟨25564628939063565481967459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68172343837502841285246557 25564628939063565481967459)
                  ·
                    refine ⟨38346943408595348222951189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25564628939063565481967459 38346943408595348222951189)
                    ·
                      refine ⟨1797512972277906947950837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38346943408595348222951189 1797512972277906947950837)
                      ·
                        rfl

theorem cell23_3500644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_3500644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500644 prefixEnd_3500644 := by exact prefixLift 3500644
  have htrace : WordTrace (prefixWord ++ tailWord_3500644) baseStart_3500644 baseEnd_3500644 := by
    simpa [prefixWord, tailWord_3500644, baseEnd_3500644] using wordTrace_append hprefix tailTrace_3500644
  have hstable : (prefixWord ++ tailWord_3500644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500644).length < 2 ^ (prefixWord ++ tailWord_3500644).sum := by decide
  have hdescent : baseEnd_3500644 < baseStart_3500644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500662 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_3500662 : Nat := 118140960795 + 3500662 * 2 ^ 59
def prefixEnd_3500662 : Nat := 4983230072969 + 3 ^ 40 * 3500662 * 2
def baseEnd_3500662 : Nat := 599174071643229292508585

theorem tailTrace_3500662 : CollatzResearch.WordTrace tailWord_3500662 prefixEnd_3500662 599174071643229292508585 := by
  unfold tailWord_3500662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979977027731682144763015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85119754962471276210805493 7979977027731682144763015)
  ·
    refine ⟨11969965541597523217144523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7979977027731682144763015 11969965541597523217144523)
    ·
      refine ⟨17954948312396284825716785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11969965541597523217144523 17954948312396284825716785)
      ·
        refine ⟨13466211234297213619287589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17954948312396284825716785 13466211234297213619287589)
        ·
          refine ⟨2524914606430727553616423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13466211234297213619287589 2524914606430727553616423)
          ·
            refine ⟨3787371909646091330424635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2524914606430727553616423 3787371909646091330424635)
            ·
              refine ⟨5681057864469136995636953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787371909646091330424635 5681057864469136995636953)
              ·
                refine ⟨4260793398351852746727715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5681057864469136995636953 4260793398351852746727715)
                ·
                  refine ⟨6391190097527779120091573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260793398351852746727715 6391190097527779120091573)
                  ·
                    refine ⟨599174071643229292508585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6391190097527779120091573 599174071643229292508585)
                    ·
                      rfl

theorem cell23_3500662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_3500662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500662 prefixEnd_3500662 := by exact prefixLift 3500662
  have htrace : WordTrace (prefixWord ++ tailWord_3500662) baseStart_3500662 baseEnd_3500662 := by
    simpa [prefixWord, tailWord_3500662, baseEnd_3500662] using wordTrace_append hprefix tailTrace_3500662
  have hstable : (prefixWord ++ tailWord_3500662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500662).length < 2 ^ (prefixWord ++ tailWord_3500662).sum := by decide
  have hdescent : baseEnd_3500662 < baseStart_3500662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500668 : List Nat := [2, 2, 2, 1, 1, 2, 5, 2, 1, 2, 3]
def baseStart_3500668 : Nat := 118140960795 + 3500668 * 2 ^ 59
def prefixEnd_3500668 : Nat := 4983230072969 + 3 ^ 40 * 3500668 * 2
def baseEnd_3500668 : Nat := 1797525295813614854050727

theorem tailTrace_3500668 : CollatzResearch.WordTrace tailWord_3500668 prefixEnd_3500668 1797525295813614854050727 := by
  unfold tailWord_3500668
  simp only [CollatzResearch.WordTrace]
  refine ⟨63839925640842588670463329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85119900854456784893951105 63839925640842588670463329)
  ·
    refine ⟨47879944230631941502847497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63839925640842588670463329 47879944230631941502847497)
    ·
      refine ⟨35909958172973956127135623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47879944230631941502847497 35909958172973956127135623)
      ·
        refine ⟨53864937259460934190703435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35909958172973956127135623 53864937259460934190703435)
        ·
          refine ⟨80797405889191401286055153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53864937259460934190703435 80797405889191401286055153)
          ·
            refine ⟨60598054416893550964541365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80797405889191401286055153 60598054416893550964541365)
            ·
              refine ⟨5681067601583770402925753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60598054416893550964541365 5681067601583770402925753)
              ·
                refine ⟨4260800701187827802194315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5681067601583770402925753 4260800701187827802194315)
                ·
                  refine ⟨6391201051781741703291473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4260800701187827802194315 6391201051781741703291473)
                  ·
                    refine ⟨4793400788836306277468605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6391201051781741703291473 4793400788836306277468605)
                    ·
                      refine ⟨1797525295813614854050727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4793400788836306277468605 1797525295813614854050727)
                      ·
                        rfl

theorem cell23_3500668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_3500668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500668 prefixEnd_3500668 := by exact prefixLift 3500668
  have htrace : WordTrace (prefixWord ++ tailWord_3500668) baseStart_3500668 baseEnd_3500668 := by
    simpa [prefixWord, tailWord_3500668, baseEnd_3500668] using wordTrace_append hprefix tailTrace_3500668
  have hstable : (prefixWord ++ tailWord_3500668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500668).length < 2 ^ (prefixWord ++ tailWord_3500668).sum := by decide
  have hdescent : baseEnd_3500668 < baseStart_3500668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500708 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 5, 3, 2]
def baseStart_3500708 : Nat := 118140960795 + 3500708 * 2 ^ 59
def prefixEnd_3500708 : Nat := 4983230072969 + 3 ^ 40 * 3500708 * 2
def baseEnd_3500708 : Nat := 1797545835039794697550543

theorem tailTrace_3500708 : CollatzResearch.WordTrace tailWord_3500708 prefixEnd_3500708 1797545835039794697550543 := by
  unfold tailWord_3500708
  simp only [CollatzResearch.WordTrace]
  refine ⟨63840655100770132086191389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85120873467693509448255185 63840655100770132086191389)
  ·
    refine ⟨23940245662788799532321771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63840655100770132086191389 23940245662788799532321771)
    ·
      refine ⟨35910368494183199298482657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23940245662788799532321771 35910368494183199298482657)
      ·
        refine ⟨26932776370637399473861993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35910368494183199298482657 26932776370637399473861993)
        ·
          refine ⟨20199582277978049605396495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26932776370637399473861993 20199582277978049605396495)
          ·
            refine ⟨30299373416967074408094743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20199582277978049605396495 30299373416967074408094743)
            ·
              refine ⟨45449060125450611612142115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30299373416967074408094743 45449060125450611612142115)
              ·
                refine ⟨68173590188175917418213173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45449060125450611612142115 68173590188175917418213173)
                ·
                  refine ⟨6391274080141492257957485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68173590188175917418213173 6391274080141492257957485)
                  ·
                    refine ⟨2396727780053059596734057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6391274080141492257957485 2396727780053059596734057)
                    ·
                      refine ⟨1797545835039794697550543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396727780053059596734057 1797545835039794697550543)
                      ·
                        rfl

theorem cell23_3500708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_3500708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500708 prefixEnd_3500708 := by exact prefixLift 3500708
  have htrace : WordTrace (prefixWord ++ tailWord_3500708) baseStart_3500708 baseEnd_3500708 := by
    simpa [prefixWord, tailWord_3500708, baseEnd_3500708] using wordTrace_append hprefix tailTrace_3500708
  have hstable : (prefixWord ++ tailWord_3500708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500708).length < 2 ^ (prefixWord ++ tailWord_3500708).sum := by decide
  have hdescent : baseEnd_3500708 < baseStart_3500708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500725 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_3500725 : Nat := 118140960795 + 3500725 * 2 ^ 59
def prefixEnd_3500725 : Nat := 4983230072969 + 3 ^ 40 * 3500725 * 2
def baseEnd_3500725 : Nat := 1797554564210921131037965

theorem tailTrace_3500725 : CollatzResearch.WordTrace tailWord_3500725 prefixEnd_3500725 1797554564210921131037965 := by
  unfold tailWord_3500725
  simp only [CollatzResearch.WordTrace]
  refine ⟨127681930242478676075751629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85121286828319117383834419 127681930242478676075751629)
  ·
    refine ⟨47880723840929503528406861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127681930242478676075751629 47880723840929503528406861)
    ·
      refine ⟨17955271440348563823152573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47880723840929503528406861 17955271440348563823152573)
      ·
        refine ⟨6733226790130711433682215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17955271440348563823152573 6733226790130711433682215)
        ·
          refine ⟨10099840185196067150523323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733226790130711433682215 10099840185196067150523323)
          ·
            refine ⟨15149760277794100725784985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10099840185196067150523323 15149760277794100725784985)
            ·
              refine ⟨11362320208345575544338739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15149760277794100725784985 11362320208345575544338739)
              ·
                refine ⟨17043480312518363316508109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11362320208345575544338739 17043480312518363316508109)
                ·
                  refine ⟨6391305117194386243690541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17043480312518363316508109 6391305117194386243690541)
                  ·
                    refine ⟨2396739418947894841383953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6391305117194386243690541 2396739418947894841383953)
                    ·
                      refine ⟨1797554564210921131037965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396739418947894841383953 1797554564210921131037965)
                      ·
                        rfl

theorem cell23_3500725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_3500725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500725 prefixEnd_3500725 := by exact prefixLift 3500725
  have htrace : WordTrace (prefixWord ++ tailWord_3500725) baseStart_3500725 baseEnd_3500725 := by
    simpa [prefixWord, tailWord_3500725, baseEnd_3500725] using wordTrace_append hprefix tailTrace_3500725
  have hstable : (prefixWord ++ tailWord_3500725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500725).length < 2 ^ (prefixWord ++ tailWord_3500725).sum := by decide
  have hdescent : baseEnd_3500725 < baseStart_3500725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500761 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 7]
def baseStart_3500761 : Nat := 118140960795 + 3500761 * 2 ^ 59
def prefixEnd_3500761 : Nat := 4983230072969 + 3 ^ 40 * 3500761 * 2
def baseEnd_3500761 : Nat := 199730338834942554465311

theorem tailTrace_3500761 : CollatzResearch.WordTrace tailWord_3500761 prefixEnd_3500761 199730338834942554465311 := by
  unfold tailWord_3500761
  simp only [CollatzResearch.WordTrace]
  refine ⟨127683243270348254224062137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85122162180232169482708091 127683243270348254224062137)
  ·
    refine ⟨95762432452761190668046603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127683243270348254224062137 95762432452761190668046603)
    ·
      refine ⟨143643648679141786002069905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95762432452761190668046603 143643648679141786002069905)
      ·
        refine ⟨107732736509356339501552429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143643648679141786002069905 107732736509356339501552429)
        ·
          refine ⟨40399776191008627313082161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107732736509356339501552429 40399776191008627313082161)
          ·
            refine ⟨30299832143256470484811621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40399776191008627313082161 30299832143256470484811621)
            ·
              refine ⟨5681218526860588215902179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30299832143256470484811621 5681218526860588215902179)
              ·
                refine ⟨8521827790290882323853269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681218526860588215902179 8521827790290882323853269)
                ·
                  refine ⟨199730338834942554465311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8521827790290882323853269 199730338834942554465311)
                  ·
                    rfl

theorem cell23_3500761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_3500761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500761 prefixEnd_3500761 := by exact prefixLift 3500761
  have htrace : WordTrace (prefixWord ++ tailWord_3500761) baseStart_3500761 baseEnd_3500761 := by
    simpa [prefixWord, tailWord_3500761, baseEnd_3500761] using wordTrace_append hprefix tailTrace_3500761
  have hstable : (prefixWord ++ tailWord_3500761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500761).length < 2 ^ (prefixWord ++ tailWord_3500761).sum := by decide
  have hdescent : baseEnd_3500761 < baseStart_3500761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500791 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 2, 5]
def baseStart_3500791 : Nat := 118140960795 + 3500791 * 2 ^ 59
def prefixEnd_3500791 : Nat := 4983230072969 + 3 ^ 40 * 3500791 * 2
def baseEnd_3500791 : Nat := 599196151311372624270887

theorem tailTrace_3500791 : CollatzResearch.WordTrace tailWord_3500791 prefixEnd_3500791 599196151311372624270887 := by
  unfold tailWord_3500791
  simp only [CollatzResearch.WordTrace]
  refine ⟨127684337460239569347654227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85122891640159712898436151 127684337460239569347654227)
  ·
    refine ⟨191526506190359354021481341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127684337460239569347654227 191526506190359354021481341)
    ·
      refine ⟨71822439821384757758055503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191526506190359354021481341 71822439821384757758055503)
      ·
        refine ⟨107733659732077136637083255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71822439821384757758055503 107733659732077136637083255)
        ·
          refine ⟨161600489598115704955624883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107733659732077136637083255 161600489598115704955624883)
          ·
            refine ⟨242400734397173557433437325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161600489598115704955624883 242400734397173557433437325)
            ·
              refine ⟨90900275398940084037538997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242400734397173557433437325 90900275398940084037538997)
              ·
                refine ⟨8521900818650632878519281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90900275398940084037538997 8521900818650632878519281)
                ·
                  refine ⟨6391425613987974658889461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8521900818650632878519281 6391425613987974658889461)
                  ·
                    refine ⟨599196151311372624270887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6391425613987974658889461 599196151311372624270887)
                    ·
                      rfl

theorem cell23_3500791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_3500791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500791 prefixEnd_3500791 := by exact prefixLift 3500791
  have htrace : WordTrace (prefixWord ++ tailWord_3500791) baseStart_3500791 baseEnd_3500791 := by
    simpa [prefixWord, tailWord_3500791, baseEnd_3500791] using wordTrace_append hprefix tailTrace_3500791
  have hstable : (prefixWord ++ tailWord_3500791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500791).length < 2 ^ (prefixWord ++ tailWord_3500791).sum := by decide
  have hdescent : baseEnd_3500791 < baseStart_3500791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500801 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3500801 : Nat := 118140960795 + 3500801 * 2 ^ 59
def prefixEnd_3500801 : Nat := 4983230072969 + 3 ^ 40 * 3500801 * 2
def baseEnd_3500801 : Nat := 1797593588740662833687615

theorem tailTrace_3500801 : CollatzResearch.WordTrace tailWord_3500801 prefixEnd_3500801 1797593588740662833687615 := by
  unfold tailWord_3500801
  simp only [CollatzResearch.WordTrace]
  refine ⟨127684702190203341055518257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85123134793468894037012171 127684702190203341055518257)
  ·
    refine ⟨95763526642652505791638693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127684702190203341055518257 95763526642652505791638693)
    ·
      refine ⟨17955661245497344835932255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95763526642652505791638693 17955661245497344835932255)
      ·
        refine ⟨26933491868246017253898383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17955661245497344835932255 26933491868246017253898383)
        ·
          refine ⟨40400237802369025880847575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26933491868246017253898383 40400237802369025880847575)
          ·
            refine ⟨60600356703553538821271363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40400237802369025880847575 60600356703553538821271363)
            ·
              refine ⟨90900535055330308231907045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60600356703553538821271363 90900535055330308231907045)
              ·
                refine ⟨17043850322874432793482571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90900535055330308231907045 17043850322874432793482571)
                ·
                  refine ⟨25565775484311649190223857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17043850322874432793482571 25565775484311649190223857)
                  ·
                    refine ⟨19174331613233736892667893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25565775484311649190223857 19174331613233736892667893)
                    ·
                      refine ⟨1797593588740662833687615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19174331613233736892667893 1797593588740662833687615)
                      ·
                        rfl

theorem cell23_3500801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3500801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500801 prefixEnd_3500801 := by exact prefixLift 3500801
  have htrace : WordTrace (prefixWord ++ tailWord_3500801) baseStart_3500801 baseEnd_3500801 := by
    simpa [prefixWord, tailWord_3500801, baseEnd_3500801] using wordTrace_append hprefix tailTrace_3500801
  have hstable : (prefixWord ++ tailWord_3500801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500801).length < 2 ^ (prefixWord ++ tailWord_3500801).sum := by decide
  have hdescent : baseEnd_3500801 < baseStart_3500801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500808 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_3500808 : Nat := 118140960795 + 3500808 * 2 ^ 59
def prefixEnd_3500808 : Nat := 4983230072969 + 3 ^ 40 * 3500808 * 2
def baseEnd_3500808 : Nat := 599199061035081435433361

theorem tailTrace_3500808 : CollatzResearch.WordTrace tailWord_3500808 prefixEnd_3500808 599199061035081435433361 := by
  unfold tailWord_3500808
  simp only [CollatzResearch.WordTrace]
  refine ⟨63842478750588990625511539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85123305000785320834015385 63842478750588990625511539)
  ·
    refine ⟨95763718125883485938267309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63842478750588990625511539 95763718125883485938267309)
    ·
      refine ⟨35911394297206307226850241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95763718125883485938267309 35911394297206307226850241)
      ·
        refine ⟨26933545722904730420137681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35911394297206307226850241 26933545722904730420137681)
        ·
          refine ⟨20200159292178547815103261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26933545722904730420137681 20200159292178547815103261)
          ·
            refine ⟨7575059734566955430663723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20200159292178547815103261 7575059734566955430663723)
            ·
              refine ⟨11362589601850433145995585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7575059734566955430663723 11362589601850433145995585)
              ·
                refine ⟨8521942201387824859496689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11362589601850433145995585 8521942201387824859496689)
                ·
                  refine ⟨6391456651040868644622517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8521942201387824859496689 6391456651040868644622517)
                  ·
                    refine ⟨599199061035081435433361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6391456651040868644622517 599199061035081435433361)
                    ·
                      rfl

theorem cell23_3500808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_3500808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500808 prefixEnd_3500808 := by exact prefixLift 3500808
  have htrace : WordTrace (prefixWord ++ tailWord_3500808) baseStart_3500808 baseEnd_3500808 := by
    simpa [prefixWord, tailWord_3500808, baseEnd_3500808] using wordTrace_append hprefix tailTrace_3500808
  have hstable : (prefixWord ++ tailWord_3500808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500808).length < 2 ^ (prefixWord ++ tailWord_3500808).sum := by decide
  have hdescent : baseEnd_3500808 < baseStart_3500808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500842 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3500842 : Nat := 118140960795 + 3500842 * 2 ^ 59
def prefixEnd_3500842 : Nat := 4983230072969 + 3 ^ 40 * 3500842 * 2
def baseEnd_3500842 : Nat := 599204880482499057758309

theorem tailTrace_3500842 : CollatzResearch.WordTrace tailWord_3500842 prefixEnd_3500842 599204880482499057758309 := by
  unfold tailWord_3500842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31921549395763701264440195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85124131722036536705173853 31921549395763701264440195)
  ·
    refine ⟨47882324093645551896660293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31921549395763701264440195 47882324093645551896660293)
    ·
      refine ⟨8977935767558540980623805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47882324093645551896660293 8977935767558540980623805)
      ·
        refine ⟨3366725912834452867733927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8977935767558540980623805 3366725912834452867733927)
        ·
          refine ⟨5050088869251679301600891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3366725912834452867733927 5050088869251679301600891)
          ·
            refine ⟨7575133303877518952401337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050088869251679301600891 7575133303877518952401337)
            ·
              refine ⟨5681349977908139214301003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7575133303877518952401337 5681349977908139214301003)
              ·
                refine ⟨8522024966862208821451505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681349977908139214301003 8522024966862208821451505)
                ·
                  refine ⟨6391518725146656616088629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522024966862208821451505 6391518725146656616088629)
                  ·
                    refine ⟨599204880482499057758309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6391518725146656616088629 599204880482499057758309)
                    ·
                      rfl

theorem cell23_3500842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3500842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500842 prefixEnd_3500842 := by exact prefixLift 3500842
  have htrace : WordTrace (prefixWord ++ tailWord_3500842) baseStart_3500842 baseEnd_3500842 := by
    simpa [prefixWord, tailWord_3500842, baseEnd_3500842] using wordTrace_append hprefix tailTrace_3500842
  have hstable : (prefixWord ++ tailWord_3500842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500842).length < 2 ^ (prefixWord ++ tailWord_3500842).sum := by decide
  have hdescent : baseEnd_3500842 < baseStart_3500842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500855 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 1, 4]
def baseStart_3500855 : Nat := 118140960795 + 3500855 * 2 ^ 59
def prefixEnd_3500855 : Nat := 4983230072969 + 3 ^ 40 * 3500855 * 2
def baseEnd_3500855 : Nat := 599207105565335207470789

theorem tailTrace_3500855 : CollatzResearch.WordTrace tailWord_3500855 prefixEnd_3500855 599207105565335207470789 := by
  unfold tailWord_3500855
  simp only [CollatzResearch.WordTrace]
  refine ⟨127686671732007708277984019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85124447821338472185322679 127686671732007708277984019)
  ·
    refine ⟨191530007598011562416976029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127686671732007708277984019 191530007598011562416976029)
    ·
      refine ⟨71823752849254335906366011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191530007598011562416976029 71823752849254335906366011)
      ·
        refine ⟨107735629273881503859549017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71823752849254335906366011 107735629273881503859549017)
        ·
          refine ⟨80801721955411127894661763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107735629273881503859549017 80801721955411127894661763)
          ·
            refine ⟨121202582933116691841992645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80801721955411127894661763 121202582933116691841992645)
            ·
              refine ⟨22725484299959379720373621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121202582933116691841992645 22725484299959379720373621)
              ·
                refine ⟨2130514153121191848785027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22725484299959379720373621 2130514153121191848785027)
                ·
                  refine ⟨3195771229681787773177541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130514153121191848785027 3195771229681787773177541)
                  ·
                    refine ⟨599207105565335207470789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3195771229681787773177541 599207105565335207470789)
                    ·
                      rfl

theorem cell23_3500855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_3500855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500855 prefixEnd_3500855 := by exact prefixLift 3500855
  have htrace : WordTrace (prefixWord ++ tailWord_3500855) baseStart_3500855 baseEnd_3500855 := by
    simpa [prefixWord, tailWord_3500855, baseEnd_3500855] using wordTrace_append hprefix tailTrace_3500855
  have hstable : (prefixWord ++ tailWord_3500855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500855).length < 2 ^ (prefixWord ++ tailWord_3500855).sum := by decide
  have hdescent : baseEnd_3500855 < baseStart_3500855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500871 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3500871 : Nat := 118140960795 + 3500871 * 2 ^ 59
def prefixEnd_3500871 : Nat := 4983230072969 + 3 ^ 40 * 3500871 * 2
def baseEnd_3500871 : Nat := 1797629532386477559812293

theorem tailTrace_3500871 : CollatzResearch.WordTrace tailWord_3500871 prefixEnd_3500871 1797629532386477559812293 := by
  unfold tailWord_3500871
  simp only [CollatzResearch.WordTrace]
  refine ⟨127687255299949743010566467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85124836866633162007044311 127687255299949743010566467)
  ·
    refine ⟨191530882949924614515849701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127687255299949743010566467 191530882949924614515849701)
    ·
      refine ⟨35912040553110865221721819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191530882949924614515849701 35912040553110865221721819)
      ·
        refine ⟨53868060829666297832582729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35912040553110865221721819 53868060829666297832582729)
        ·
          refine ⟨40401045622249723374437047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53868060829666297832582729 40401045622249723374437047)
          ·
            refine ⟨60601568433374585061655571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40401045622249723374437047 60601568433374585061655571)
            ·
              refine ⟨90902352650061877592483357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60601568433374585061655571 90902352650061877592483357)
              ·
                refine ⟨34088382243773204097181259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90902352650061877592483357 34088382243773204097181259)
                ·
                  refine ⟨51132573365659806145771889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34088382243773204097181259 51132573365659806145771889)
                  ·
                    refine ⟨38349430024244854609328917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51132573365659806145771889 38349430024244854609328917)
                    ·
                      refine ⟨1797629532386477559812293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38349430024244854609328917 1797629532386477559812293)
                      ·
                        rfl

theorem cell23_3500871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3500871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500871 prefixEnd_3500871 := by exact prefixLift 3500871
  have htrace : WordTrace (prefixWord ++ tailWord_3500871) baseStart_3500871 baseEnd_3500871 := by
    simpa [prefixWord, tailWord_3500871, baseEnd_3500871] using wordTrace_append hprefix tailTrace_3500871
  have hstable : (prefixWord ++ tailWord_3500871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500871).length < 2 ^ (prefixWord ++ tailWord_3500871).sum := by decide
  have hdescent : baseEnd_3500871 < baseStart_3500871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500895 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 3]
def baseStart_3500895 : Nat := 118140960795 + 3500895 * 2 ^ 59
def prefixEnd_3500895 : Nat := 4983230072969 + 3 ^ 40 * 3500895 * 2
def baseEnd_3500895 : Nat := 1797641855922185465912183

theorem tailTrace_3500895 : CollatzResearch.WordTrace tailWord_3500895 prefixEnd_3500895 1797641855922185465912183 := by
  unfold tailWord_3500895
  simp only [CollatzResearch.WordTrace]
  refine ⟨127688130651862795109440139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85125420434575196739626759 127688130651862795109440139)
  ·
    refine ⟨191532195977794192664160209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127688130651862795109440139 191532195977794192664160209)
    ·
      refine ⟨143649146983345644498120157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191532195977794192664160209 143649146983345644498120157)
      ·
        refine ⟨53868430118754616686795059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143649146983345644498120157 53868430118754616686795059)
        ·
          refine ⟨80802645178131925030192589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53868430118754616686795059 80802645178131925030192589)
          ·
            refine ⟨30300991941799471886322221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80802645178131925030192589 30300991941799471886322221)
            ·
              refine ⟨11362871978174801957370833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30300991941799471886322221 11362871978174801957370833)
              ·
                refine ⟨8522153983631101468028125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11362871978174801957370833 8522153983631101468028125)
                ·
                  refine ⟨3195807743861663050510547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8522153983631101468028125 3195807743861663050510547)
                  ·
                    refine ⟨4793711615792494575765821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195807743861663050510547 4793711615792494575765821)
                    ·
                      refine ⟨1797641855922185465912183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4793711615792494575765821 1797641855922185465912183)
                      ·
                        rfl

theorem cell23_3500895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_3500895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500895 prefixEnd_3500895 := by exact prefixLift 3500895
  have htrace : WordTrace (prefixWord ++ tailWord_3500895) baseStart_3500895 baseEnd_3500895 := by
    simpa [prefixWord, tailWord_3500895, baseEnd_3500895] using wordTrace_append hprefix tailTrace_3500895
  have hstable : (prefixWord ++ tailWord_3500895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500895).length < 2 ^ (prefixWord ++ tailWord_3500895).sum := by decide
  have hdescent : baseEnd_3500895 < baseStart_3500895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500912 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 1, 1, 3]
def baseStart_3500912 : Nat := 118140960795 + 3500912 * 2 ^ 59
def prefixEnd_3500912 : Nat := 4983230072969 + 3 ^ 40 * 3500912 * 2
def baseEnd_3500912 : Nat := 1797650585093311899399605

theorem tailTrace_3500912 : CollatzResearch.WordTrace tailWord_3500912 prefixEnd_3500912 1797650585093311899399605 := by
  unfold tailWord_3500912
  simp only [CollatzResearch.WordTrace]
  refine ⟨63844375346400603506404495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85125833795200804675205993 63844375346400603506404495)
  ·
    refine ⟨95766563019600905259606743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63844375346400603506404495 95766563019600905259606743)
    ·
      refine ⟨143649844529401357889410115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95766563019600905259606743 143649844529401357889410115)
      ·
        refine ⟨215474766794102036834115173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143649844529401357889410115 215474766794102036834115173)
        ·
          refine ⟨40401518773894131906396595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215474766794102036834115173 40401518773894131906396595)
          ·
            refine ⟨60602278160841197859594893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40401518773894131906396595 60602278160841197859594893)
            ·
              refine ⟨22725854310315449197348085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60602278160841197859594893 22725854310315449197348085)
              ·
                refine ⟨2130548841592073362251383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22725854310315449197348085 2130548841592073362251383)
                ·
                  refine ⟨3195823262388110043377075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130548841592073362251383 3195823262388110043377075)
                  ·
                    refine ⟨4793734893582165065065613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3195823262388110043377075 4793734893582165065065613)
                    ·
                      refine ⟨1797650585093311899399605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4793734893582165065065613 1797650585093311899399605)
                      ·
                        rfl

theorem cell23_3500912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 1, 1, 3].length) (baseStart_3500912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500912 prefixEnd_3500912 := by exact prefixLift 3500912
  have htrace : WordTrace (prefixWord ++ tailWord_3500912) baseStart_3500912 baseEnd_3500912 := by
    simpa [prefixWord, tailWord_3500912, baseEnd_3500912] using wordTrace_append hprefix tailTrace_3500912
  have hstable : (prefixWord ++ tailWord_3500912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500912).length < 2 ^ (prefixWord ++ tailWord_3500912).sum := by decide
  have hdescent : baseEnd_3500912 < baseStart_3500912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500915 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 1, 5]
def baseStart_3500915 : Nat := 118140960795 + 3500915 * 2 ^ 59
def prefixEnd_3500915 : Nat := 4983230072969 + 3 ^ 40 * 3500915 * 2
def baseEnd_3500915 : Nat := 599217375178425129220697

theorem tailTrace_3500915 : CollatzResearch.WordTrace tailWord_3500915 prefixEnd_3500915 599217375178425129220697 := by
  unfold tailWord_3500915
  simp only [CollatzResearch.WordTrace]
  refine ⟨127688860111790338525168199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85125906741193559016778799 127688860111790338525168199)
  ·
    refine ⟨191533290167685507787752299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127688860111790338525168199 191533290167685507787752299)
    ·
      refine ⟨287299935251528261681628449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191533290167685507787752299 287299935251528261681628449)
      ·
        refine ⟨215474951438646196261221337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287299935251528261681628449 215474951438646196261221337)
        ·
          refine ⟨161606213578984647195916003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215474951438646196261221337 161606213578984647195916003)
          ·
            refine ⟨242409320368476970793874005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161606213578984647195916003 242409320368476970793874005)
            ·
              refine ⟨2840734223068089501490711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 242409320368476970793874005 2840734223068089501490711)
              ·
                refine ⟨4261101334602134252236067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2840734223068089501490711 4261101334602134252236067)
                ·
                  refine ⟨6391652001903201378354101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4261101334602134252236067 6391652001903201378354101)
                  ·
                    refine ⟨599217375178425129220697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6391652001903201378354101 599217375178425129220697)
                    ·
                      rfl

theorem cell23_3500915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 1, 5].length) (baseStart_3500915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500915 prefixEnd_3500915 := by exact prefixLift 3500915
  have htrace : WordTrace (prefixWord ++ tailWord_3500915) baseStart_3500915 baseEnd_3500915 := by
    simpa [prefixWord, tailWord_3500915, baseEnd_3500915] using wordTrace_append hprefix tailTrace_3500915
  have hstable : (prefixWord ++ tailWord_3500915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500915).length < 2 ^ (prefixWord ++ tailWord_3500915).sum := by decide
  have hdescent : baseEnd_3500915 < baseStart_3500915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500986 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2]
def baseStart_3500986 : Nat := 118140960795 + 3500986 * 2 ^ 59
def prefixEnd_3500986 : Nat := 4983230072969 + 3 ^ 40 * 3500986 * 2
def baseEnd_3500986 : Nat := 1797688582661744609874265

theorem tailTrace_3500986 : CollatzResearch.WordTrace tailWord_3500986 prefixEnd_3500986 1797688582661744609874265 := by
  unfold tailWord_3500986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31922862423633279412750703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85127633129688745100668541 31922862423633279412750703)
  ·
    refine ⟨47884293635449919119126055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31922862423633279412750703 47884293635449919119126055)
    ·
      refine ⟨71826440453174878678689083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47884293635449919119126055 71826440453174878678689083)
      ·
        refine ⟨107739660679762318018033625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71826440453174878678689083 107739660679762318018033625)
        ·
          refine ⟨80804745509821738513525219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107739660679762318018033625 80804745509821738513525219)
          ·
            refine ⟨121207118264732607770287829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80804745509821738513525219 121207118264732607770287829)
            ·
              refine ⟨2840791834329670494616121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121207118264732607770287829 2840791834329670494616121)
              ·
                refine ⟨2130593875747252870962091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2840791834329670494616121 2130593875747252870962091)
                ·
                  refine ⟨3195890813620879306443137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130593875747252870962091 3195890813620879306443137)
                  ·
                    refine ⟨2396918110215659479832353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3195890813620879306443137 2396918110215659479832353)
                    ·
                      refine ⟨1797688582661744609874265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396918110215659479832353 1797688582661744609874265)
                      ·
                        rfl

theorem cell23_3500986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_3500986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500986 prefixEnd_3500986 := by exact prefixLift 3500986
  have htrace : WordTrace (prefixWord ++ tailWord_3500986) baseStart_3500986 baseEnd_3500986 := by
    simpa [prefixWord, tailWord_3500986, baseEnd_3500986] using wordTrace_append hprefix tailTrace_3500986
  have hstable : (prefixWord ++ tailWord_3500986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500986).length < 2 ^ (prefixWord ++ tailWord_3500986).sum := by decide
  have hdescent : baseEnd_3500986 < baseStart_3500986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3500995 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 5, 3, 2]
def baseStart_3500995 : Nat := 118140960795 + 3500995 * 2 ^ 59
def prefixEnd_3500995 : Nat := 4983230072969 + 3 ^ 40 * 3500995 * 2
def baseEnd_3500995 : Nat := 1797693203987635074661723

theorem tailTrace_3500995 : CollatzResearch.WordTrace tailWord_3500995 prefixEnd_3500995 1797693203987635074661723 := by
  unfold tailWord_3500995
  simp only [CollatzResearch.WordTrace]
  refine ⟨127691777951500512188080439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85127851967667008125386959 127691777951500512188080439)
  ·
    refine ⟨191537666927250768282120659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127691777951500512188080439 191537666927250768282120659)
    ·
      refine ⟨287306500390876152423180989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191537666927250768282120659 287306500390876152423180989)
      ·
        refine ⟨107739937646578557158692871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287306500390876152423180989 107739937646578557158692871)
        ·
          refine ⟨161609906469867835738039307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107739937646578557158692871 161609906469867835738039307)
          ·
            refine ⟨242414859704801753607058961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161609906469867835738039307 242414859704801753607058961)
            ·
              refine ⟨181811144778601315205294221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242414859704801753607058961 181811144778601315205294221)
              ·
                refine ⟨68179179291975493201985333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181811144778601315205294221 68179179291975493201985333)
                ·
                  refine ⟨6391798058622702487686125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68179179291975493201985333 6391798058622702487686125)
                  ·
                    refine ⟨2396924271983513432882297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6391798058622702487686125 2396924271983513432882297)
                    ·
                      refine ⟨1797693203987635074661723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2396924271983513432882297 1797693203987635074661723)
                      ·
                        rfl

theorem cell23_3500995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_3500995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3500995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3500995 prefixEnd_3500995 := by exact prefixLift 3500995
  have htrace : WordTrace (prefixWord ++ tailWord_3500995) baseStart_3500995 baseEnd_3500995 := by
    simpa [prefixWord, tailWord_3500995, baseEnd_3500995] using wordTrace_append hprefix tailTrace_3500995
  have hstable : (prefixWord ++ tailWord_3500995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3500995).length < 2 ^ (prefixWord ++ tailWord_3500995).sum := by decide
  have hdescent : baseEnd_3500995 < baseStart_3500995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3500995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501028 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 1, 3, 5]
def baseStart_3501028 : Nat := 118140960795 + 3501028 * 2 ^ 59
def prefixEnd_3501028 : Nat := 4983230072969 + 3 ^ 40 * 3501028 * 2
def baseEnd_3501028 : Nat := 1797710148849233445549071

theorem tailTrace_3501028 : CollatzResearch.WordTrace tailWord_3501028 prefixEnd_3501028 1797710148849233445549071 := by
  unfold tailWord_3501028
  simp only [CollatzResearch.WordTrace]
  refine ⟨63846490780190479412015869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85128654373587305882687825 63846490780190479412015869)
  ·
    refine ⟨23942434042571429779505951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63846490780190479412015869 23942434042571429779505951)
    ·
      refine ⟨35913651063857144669258927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23942434042571429779505951 35913651063857144669258927)
      ·
        refine ⟨53870476595785717003888391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35913651063857144669258927 53870476595785717003888391)
        ·
          refine ⟨80805714893678575505832587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53870476595785717003888391 80805714893678575505832587)
          ·
            refine ⟨121208572340517863258748881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80805714893678575505832587 121208572340517863258748881)
            ·
              refine ⟨90906429255388397444061661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121208572340517863258748881 90906429255388397444061661)
              ·
                refine ⟨34089910970770649041523123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90906429255388397444061661 34089910970770649041523123)
                ·
                  refine ⟨51134866456155973562284685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34089910970770649041523123 51134866456155973562284685)
                  ·
                    refine ⟨19175574921058490085856757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51134866456155973562284685 19175574921058490085856757)
                    ·
                      refine ⟨1797710148849233445549071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19175574921058490085856757 1797710148849233445549071)
                      ·
                        rfl

theorem cell23_3501028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_3501028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501028 prefixEnd_3501028 := by exact prefixLift 3501028
  have htrace : WordTrace (prefixWord ++ tailWord_3501028) baseStart_3501028 baseEnd_3501028 := by
    simpa [prefixWord, tailWord_3501028, baseEnd_3501028] using wordTrace_append hprefix tailTrace_3501028
  have hstable : (prefixWord ++ tailWord_3501028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501028).length < 2 ^ (prefixWord ++ tailWord_3501028).sum := by decide
  have hdescent : baseEnd_3501028 < baseStart_3501028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501048 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 7]
def baseStart_3501048 : Nat := 118140960795 + 3501048 * 2 ^ 59
def prefixEnd_3501048 : Nat := 4983230072969 + 3 ^ 40 * 3501048 * 2
def baseEnd_3501048 : Nat := 199746713162480374144331

theorem tailTrace_3501048 : CollatzResearch.WordTrace tailWord_3501048 prefixEnd_3501048 199746713162480374144331 := by
  unfold tailWord_3501048
  simp only [CollatzResearch.WordTrace]
  refine ⟨63846855510154251119879899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85129140680205668159839865 63846855510154251119879899)
  ·
    refine ⟨95770283265231376679819849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63846855510154251119879899 95770283265231376679819849)
    ·
      refine ⟨71827712448923532509864887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95770283265231376679819849 71827712448923532509864887)
      ·
        refine ⟨107741568673385298764797331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71827712448923532509864887 107741568673385298764797331)
        ·
          refine ⟨161612353010077948147195997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107741568673385298764797331 161612353010077948147195997)
          ·
            refine ⟨60604632378779230555198499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161612353010077948147195997 60604632378779230555198499)
            ·
              refine ⟨90906948568168845832797749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60604632378779230555198499 90906948568168845832797749)
              ·
                refine ⟨8522526428265829296824789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90906948568168845832797749 8522526428265829296824789)
                ·
                  refine ⟨199746713162480374144331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8522526428265829296824789 199746713162480374144331)
                  ·
                    rfl

theorem cell23_3501048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_3501048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501048 prefixEnd_3501048 := by exact prefixLift 3501048
  have htrace : WordTrace (prefixWord ++ tailWord_3501048) baseStart_3501048 baseEnd_3501048 := by
    simpa [prefixWord, tailWord_3501048, baseEnd_3501048] using wordTrace_append hprefix tailTrace_3501048
  have hstable : (prefixWord ++ tailWord_3501048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501048).length < 2 ^ (prefixWord ++ tailWord_3501048).sum := by decide
  have hdescent : baseEnd_3501048 < baseStart_3501048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501082 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_3501082 : Nat := 118140960795 + 3501082 * 2 ^ 59
def prefixEnd_3501082 : Nat := 4983230072969 + 3 ^ 40 * 3501082 * 2
def baseEnd_3501082 : Nat := 199748652978286248252647

theorem tailTrace_3501082 : CollatzResearch.WordTrace tailWord_3501082 prefixEnd_3501082 199748652978286248252647 := by
  unfold tailWord_3501082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31923737775546331511624375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85129967401456884030998333 31923737775546331511624375)
  ·
    refine ⟨47885606663319497267436563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31923737775546331511624375 47885606663319497267436563)
    ·
      refine ⟨71828409994979245901154845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47885606663319497267436563 71828409994979245901154845)
      ·
        refine ⟨26935653748117217212933067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71828409994979245901154845 26935653748117217212933067)
        ·
          refine ⟨40403480622175825819399601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26935653748117217212933067 40403480622175825819399601)
          ·
            refine ⟨30302610466631869364549701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40403480622175825819399601 30302610466631869364549701)
            ·
              refine ⟨5681739462493475505853069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30302610466631869364549701 5681739462493475505853069)
              ·
                refine ⟨2130652298435053314694901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5681739462493475505853069 2130652298435053314694901)
                ·
                  refine ⟨199748652978286248252647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130652298435053314694901 199748652978286248252647)
                  ·
                    rfl

theorem cell23_3501082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_3501082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501082 prefixEnd_3501082 := by exact prefixLift 3501082
  have htrace : WordTrace (prefixWord ++ tailWord_3501082) baseStart_3501082 baseEnd_3501082 := by
    simpa [prefixWord, tailWord_3501082, baseEnd_3501082] using wordTrace_append hprefix tailTrace_3501082
  have hstable : (prefixWord ++ tailWord_3501082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501082).length < 2 ^ (prefixWord ++ tailWord_3501082).sum := by decide
  have hdescent : baseEnd_3501082 < baseStart_3501082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501092 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3501092 : Nat := 118140960795 + 3501092 * 2 ^ 59
def prefixEnd_3501092 : Nat := 4983230072969 + 3 ^ 40 * 3501092 * 2
def baseEnd_3501092 : Nat := 1797743011611121195148777

theorem tailTrace_3501092 : CollatzResearch.WordTrace tailWord_3501092 prefixEnd_3501092 1797743011611121195148777 := by
  unfold tailWord_3501092
  simp only [CollatzResearch.WordTrace]
  refine ⟨63847657916074548877180765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85130210554766065169574353 63847657916074548877180765)
  ·
    refine ⟨23942871718527955828942787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63847657916074548877180765 23942871718527955828942787)
    ·
      refine ⟨35914307577791933743414181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23942871718527955828942787 35914307577791933743414181)
      ·
        refine ⟨6733932670835987576890159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35914307577791933743414181 6733932670835987576890159)
        ·
          refine ⟨10100899006253981365335239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6733932670835987576890159 10100899006253981365335239)
          ·
            refine ⟨15151348509380972048002859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10100899006253981365335239 15151348509380972048002859)
            ·
              refine ⟨22727022764071458072004289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15151348509380972048002859 22727022764071458072004289)
              ·
                refine ⟨17045267073053593554003217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22727022764071458072004289 17045267073053593554003217)
                ·
                  refine ⟨12783950304790195165502413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17045267073053593554003217 12783950304790195165502413)
                  ·
                    refine ⟨4793981364296323187063405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12783950304790195165502413 4793981364296323187063405)
                    ·
                      refine ⟨1797743011611121195148777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4793981364296323187063405 1797743011611121195148777)
                      ·
                        rfl

theorem cell23_3501092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3501092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501092 prefixEnd_3501092 := by exact prefixLift 3501092
  have htrace : WordTrace (prefixWord ++ tailWord_3501092) baseStart_3501092 baseEnd_3501092 := by
    simpa [prefixWord, tailWord_3501092, baseEnd_3501092] using wordTrace_append hprefix tailTrace_3501092
  have hstable : (prefixWord ++ tailWord_3501092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501092).length < 2 ^ (prefixWord ++ tailWord_3501092).sum := by decide
  have hdescent : baseEnd_3501092 < baseStart_3501092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501152 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_3501152 : Nat := 118140960795 + 3501152 * 2 ^ 59
def prefixEnd_3501152 : Nat := 4983230072969 + 3 ^ 40 * 3501152 * 2
def baseEnd_3501152 : Nat := 1797773820450390960398501

theorem tailTrace_3501152 : CollatzResearch.WordTrace tailWord_3501152 prefixEnd_3501152 1797773820450390960398501 := by
  unfold tailWord_3501152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63848752105965864000772855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85131669474621152001030473 63848752105965864000772855)
  ·
    refine ⟨95773128158948796001159283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63848752105965864000772855 95773128158948796001159283)
    ·
      refine ⟨143659692238423194001738925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95773128158948796001159283 143659692238423194001738925)
      ·
        refine ⟨53872384589408697750652097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143659692238423194001738925 53872384589408697750652097)
        ·
          refine ⟨40404288442056523312989073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53872384589408697750652097 40404288442056523312989073)
          ·
            refine ⟨30303216331542392484741805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40404288442056523312989073 30303216331542392484741805)
            ·
              refine ⟨11363706124328397181778177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30303216331542392484741805 11363706124328397181778177)
              ·
                refine ⟨8522779593246297886333633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11363706124328397181778177 8522779593246297886333633)
                ·
                  refine ⟨6392084694934723414750225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8522779593246297886333633 6392084694934723414750225)
                  ·
                    refine ⟨4794063521201042561062669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6392084694934723414750225 4794063521201042561062669)
                    ·
                      refine ⟨1797773820450390960398501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4794063521201042561062669 1797773820450390960398501)
                      ·
                        rfl

theorem cell23_3501152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_3501152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501152 prefixEnd_3501152 := by exact prefixLift 3501152
  have htrace : WordTrace (prefixWord ++ tailWord_3501152) baseStart_3501152 baseEnd_3501152 := by
    simpa [prefixWord, tailWord_3501152, baseEnd_3501152] using wordTrace_append hprefix tailTrace_3501152
  have hstable : (prefixWord ++ tailWord_3501152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501152).length < 2 ^ (prefixWord ++ tailWord_3501152).sum := by decide
  have hdescent : baseEnd_3501152 < baseStart_3501152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501155 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 6]
def baseStart_3501155 : Nat := 118140960795 + 3501155 * 2 ^ 59
def prefixEnd_3501155 : Nat := 4983230072969 + 3 ^ 40 * 3501155 * 2
def baseEnd_3501155 : Nat := 199752817876928272073443

theorem tailTrace_3501155 : CollatzResearch.WordTrace tailWord_3501155 prefixEnd_3501155 199752817876928272073443 := by
  unfold tailWord_3501155
  simp only [CollatzResearch.WordTrace]
  refine ⟨127697613630920859513904919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85131742420613906342603279 127697613630920859513904919)
  ·
    refine ⟨191546420446381289270857379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127697613630920859513904919 191546420446381289270857379)
    ·
      refine ⟨287319630669571933906286069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191546420446381289270857379 287319630669571933906286069)
      ·
        refine ⟨26936215375272368803714319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 287319630669571933906286069 26936215375272368803714319)
        ·
          refine ⟨40404323062908553205571479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26936215375272368803714319 40404323062908553205571479)
          ·
            refine ⟨60606484594362829808357219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40404323062908553205571479 60606484594362829808357219)
            ·
              refine ⟨90909726891544244712535829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60606484594362829808357219 90909726891544244712535829)
              ·
                refine ⟨4261393448041136470900117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90909726891544244712535829 4261393448041136470900117)
                ·
                  refine ⟨199752817876928272073443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4261393448041136470900117 199752817876928272073443)
                  ·
                    rfl

theorem cell23_3501155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 6].length) (baseStart_3501155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501155 prefixEnd_3501155 := by exact prefixLift 3501155
  have htrace : WordTrace (prefixWord ++ tailWord_3501155) baseStart_3501155 baseEnd_3501155 := by
    simpa [prefixWord, tailWord_3501155, baseEnd_3501155] using wordTrace_append hprefix tailTrace_3501155
  have hstable : (prefixWord ++ tailWord_3501155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501155).length < 2 ^ (prefixWord ++ tailWord_3501155).sum := by decide
  have hdescent : baseEnd_3501155 < baseStart_3501155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501159 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3501159 : Nat := 118140960795 + 3501159 * 2 ^ 59
def prefixEnd_3501159 : Nat := 4983230072969 + 3 ^ 40 * 3501159 * 2
def baseEnd_3501159 : Nat := 599259138271657477670323

theorem tailTrace_3501159 : CollatzResearch.WordTrace tailWord_3501159 prefixEnd_3501159 599259138271657477670323 := by
  unfold tailWord_3501159
  simp only [CollatzResearch.WordTrace]
  refine ⟨127697759522906368197050531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85131839681937578798033687 127697759522906368197050531)
  ·
    refine ⟨191546639284359552295575797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127697759522906368197050531 191546639284359552295575797)
    ·
      refine ⟨17957497432908708027710231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191546639284359552295575797 17957497432908708027710231)
      ·
        refine ⟨26936246149363062041565347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17957497432908708027710231 26936246149363062041565347)
        ·
          refine ⟨40404369224044593062348021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26936246149363062041565347 40404369224044593062348021)
          ·
            refine ⟨3787909614754180599595127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40404369224044593062348021 3787909614754180599595127)
            ·
              refine ⟨5681864422131270899392691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787909614754180599595127 5681864422131270899392691)
              ·
                refine ⟨8522796633196906349089037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5681864422131270899392691 8522796633196906349089037)
                ·
                  refine ⟨3196048737448839880908389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8522796633196906349089037 3196048737448839880908389)
                  ·
                    refine ⟨599259138271657477670323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196048737448839880908389 599259138271657477670323)
                    ·
                      rfl

theorem cell23_3501159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3501159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501159 prefixEnd_3501159 := by exact prefixLift 3501159
  have htrace : WordTrace (prefixWord ++ tailWord_3501159) baseStart_3501159 baseEnd_3501159 := by
    simpa [prefixWord, tailWord_3501159, baseEnd_3501159] using wordTrace_append hprefix tailTrace_3501159
  have hstable : (prefixWord ++ tailWord_3501159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501159).length < 2 ^ (prefixWord ++ tailWord_3501159).sum := by decide
  have hdescent : baseEnd_3501159 < baseStart_3501159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501216 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 1, 1, 3]
def baseStart_3501216 : Nat := 118140960795 + 3501216 * 2 ^ 59
def prefixEnd_3501216 : Nat := 4983230072969 + 3 ^ 40 * 3501216 * 2
def baseEnd_3501216 : Nat := 1797806683212278709998207

theorem tailTrace_3501216 : CollatzResearch.WordTrace tailWord_3501216 prefixEnd_3501216 1797806683212278709998207 := by
  unfold tailWord_3501216
  simp only [CollatzResearch.WordTrace]
  refine ⟨63849919241849933465937751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85133225655799911287917001 63849919241849933465937751)
  ·
    refine ⟨95774878862774900198906627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63849919241849933465937751 95774878862774900198906627)
    ·
      refine ⟨143662318294162350298359941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95774878862774900198906627 143662318294162350298359941)
      ·
        refine ⟨26936684680155440680942489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143662318294162350298359941 26936684680155440680942489)
        ·
          refine ⟨20202513510116580510706867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26936684680155440680942489 20202513510116580510706867)
          ·
            refine ⟨30303770265174870766060301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20202513510116580510706867 30303770265174870766060301)
            ·
              refine ⟨11363913849440576537272613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30303770265174870766060301 11363913849440576537272613)
              ·
                refine ⟨2130733846770108100738615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11363913849440576537272613 2130733846770108100738615)
                ·
                  refine ⟨3196100770155162151107923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130733846770108100738615 3196100770155162151107923)
                  ·
                    refine ⟨4794151155232743226661885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196100770155162151107923 4794151155232743226661885)
                    ·
                      refine ⟨1797806683212278709998207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4794151155232743226661885 1797806683212278709998207)
                      ·
                        rfl

theorem cell23_3501216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_3501216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501216 prefixEnd_3501216 := by exact prefixLift 3501216
  have htrace : WordTrace (prefixWord ++ tailWord_3501216) baseStart_3501216 baseEnd_3501216 := by
    simpa [prefixWord, tailWord_3501216, baseEnd_3501216] using wordTrace_append hprefix tailTrace_3501216
  have hstable : (prefixWord ++ tailWord_3501216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501216).length < 2 ^ (prefixWord ++ tailWord_3501216).sum := by decide
  have hdescent : baseEnd_3501216 < baseStart_3501216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501235 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6]
def baseStart_3501235 : Nat := 118140960795 + 3501235 * 2 ^ 59
def prefixEnd_3501235 : Nat := 4983230072969 + 3 ^ 40 * 3501235 * 2
def baseEnd_3501235 : Nat := 1797816439344714135660619

theorem tailTrace_3501235 : CollatzResearch.WordTrace tailWord_3501235 prefixEnd_3501235 1797816439344714135660619 := by
  unfold tailWord_3501235
  simp only [CollatzResearch.WordTrace]
  refine ⟨127700531470631033176817159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85133687647087355451211439 127700531470631033176817159)
  ·
    refine ⟨191550797205946549765225739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127700531470631033176817159 191550797205946549765225739)
    ·
      refine ⟨287326195808919824647838609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191550797205946549765225739 287326195808919824647838609)
      ·
        refine ⟨215494646856689868485878957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287326195808919824647838609 215494646856689868485878957)
        ·
          refine ⟨80810492571258700682204609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215494646856689868485878957 80810492571258700682204609)
          ·
            refine ⟨60607869428444025511653457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80810492571258700682204609 60607869428444025511653457)
            ·
              refine ⟨45455902071333019133740093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60607869428444025511653457 45455902071333019133740093)
              ·
                refine ⟨17045963276749882175152535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45455902071333019133740093 17045963276749882175152535)
                ·
                  refine ⟨25568944915124823262728803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17045963276749882175152535 25568944915124823262728803)
                  ·
                    refine ⟨38353417372687234894093205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25568944915124823262728803 38353417372687234894093205)
                    ·
                      refine ⟨1797816439344714135660619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38353417372687234894093205 1797816439344714135660619)
                      ·
                        rfl

theorem cell23_3501235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_3501235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501235 prefixEnd_3501235 := by exact prefixLift 3501235
  have htrace : WordTrace (prefixWord ++ tailWord_3501235) baseStart_3501235 baseEnd_3501235 := by
    simpa [prefixWord, tailWord_3501235, baseEnd_3501235] using wordTrace_append hprefix tailTrace_3501235
  have hstable : (prefixWord ++ tailWord_3501235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501235).length < 2 ^ (prefixWord ++ tailWord_3501235).sum := by decide
  have hdescent : baseEnd_3501235 < baseStart_3501235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501245 : List Nat := [1, 4, 1, 2, 1, 1, 2, 11]
def baseStart_3501245 : Nat := 118140960795 + 3501245 * 2 ^ 59
def prefixEnd_3501245 : Nat := 4983230072969 + 3 ^ 40 * 3501245 * 2
def baseEnd_3501245 : Nat := 66585984227824410982799

theorem tailTrace_3501245 : CollatzResearch.WordTrace tailWord_3501245 prefixEnd_3501245 66585984227824410982799 := by
  unfold tailWord_3501245
  simp only [CollatzResearch.WordTrace]
  refine ⟨127700896200594804884681189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85133930800396536589787459 127700896200594804884681189)
  ·
    refine ⟨23943918037611525915877723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127700896200594804884681189 23943918037611525915877723)
    ·
      refine ⟨35915877056417288873816585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23943918037611525915877723 35915877056417288873816585)
      ·
        refine ⟨26936907792312966655362439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35915877056417288873816585 26936907792312966655362439)
        ·
          refine ⟨40405361688469449983043659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26936907792312966655362439 40405361688469449983043659)
          ·
            refine ⟨60608042532704174974565489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40405361688469449983043659 60608042532704174974565489)
            ·
              refine ⟨45456031899528131230924117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60608042532704174974565489 45456031899528131230924117)
              ·
                refine ⟨66585984227824410982799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 45456031899528131230924117 66585984227824410982799)
                ·
                  rfl

theorem cell23_3501245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 11].length) (baseStart_3501245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501245 prefixEnd_3501245 := by exact prefixLift 3501245
  have htrace : WordTrace (prefixWord ++ tailWord_3501245) baseStart_3501245 baseEnd_3501245 := by
    simpa [prefixWord, tailWord_3501245, baseEnd_3501245] using wordTrace_append hprefix tailTrace_3501245
  have hstable : (prefixWord ++ tailWord_3501245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501245).length < 2 ^ (prefixWord ++ tailWord_3501245).sum := by decide
  have hdescent : baseEnd_3501245 < baseStart_3501245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501249 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3501249 : Nat := 118140960795 + 3501249 * 2 ^ 59
def prefixEnd_3501249 : Nat := 4983230072969 + 3 ^ 40 * 3501249 * 2
def baseEnd_3501249 : Nat := 599274542691292360295185

theorem tailTrace_3501249 : CollatzResearch.WordTrace tailWord_3501249 prefixEnd_3501249 599274542691292360295185 := by
  unfold tailWord_3501249
  simp only [CollatzResearch.WordTrace]
  refine ⟨127701042092580313567826801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85134028061720209045217867 127701042092580313567826801)
  ·
    refine ⟨95775781569435235175870101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127701042092580313567826801 95775781569435235175870101)
    ·
      refine ⟨4489489761067276648868911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95775781569435235175870101 4489489761067276648868911)
      ·
        refine ⟨6734234641600914973303367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489489761067276648868911 6734234641600914973303367)
        ·
          refine ⟨10101351962401372459955051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734234641600914973303367 10101351962401372459955051)
          ·
            refine ⟨15152027943602058689932577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101351962401372459955051 15152027943602058689932577)
            ·
              refine ⟨11364020957701544017449433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15152027943602058689932577 11364020957701544017449433)
              ·
                refine ⟨8523015718276158013087075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11364020957701544017449433 8523015718276158013087075)
                ·
                  refine ⟨12784523577414237019630613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523015718276158013087075 12784523577414237019630613)
                  ·
                    refine ⟨599274542691292360295185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12784523577414237019630613 599274542691292360295185)
                    ·
                      rfl

theorem cell23_3501249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3501249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501249 prefixEnd_3501249 := by exact prefixLift 3501249
  have htrace : WordTrace (prefixWord ++ tailWord_3501249) baseStart_3501249 baseEnd_3501249 := by
    simpa [prefixWord, tailWord_3501249, baseEnd_3501249] using wordTrace_append hprefix tailTrace_3501249
  have hstable : (prefixWord ++ tailWord_3501249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501249).length < 2 ^ (prefixWord ++ tailWord_3501249).sum := by decide
  have hdescent : baseEnd_3501249 < baseStart_3501249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501262 : List Nat := [4, 1, 1, 1, 5, 1, 10]
def baseStart_3501262 : Nat := 118140960795 + 3501262 * 2 ^ 59
def prefixEnd_3501262 : Nat := 4983230072969 + 3 ^ 40 * 3501262 * 2
def baseEnd_3501262 : Nat := 22195435843486241111395

theorem tailTrace_3501262 : CollatzResearch.WordTrace tailWord_3501262 prefixEnd_3501262 22195435843486241111395 := by
  unfold tailWord_3501262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15962689530191652098506255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85134344161022144525366693 15962689530191652098506255)
  ·
    refine ⟨23944034295287478147759383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15962689530191652098506255 23944034295287478147759383)
    ·
      refine ⟨35916051442931217221639075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23944034295287478147759383 35916051442931217221639075)
      ·
        refine ⟨53874077164396825832458613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35916051442931217221639075 53874077164396825832458613)
        ·
          refine ⟨5050694734162202421792995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53874077164396825832458613 5050694734162202421792995)
          ·
            refine ⟨7576042101243303632689493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5050694734162202421792995 7576042101243303632689493)
            ·
              refine ⟨22195435843486241111395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7576042101243303632689493 22195435843486241111395)
              ·
                rfl

theorem cell23_3501262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 10].length) (baseStart_3501262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501262 prefixEnd_3501262 := by exact prefixLift 3501262
  have htrace : WordTrace (prefixWord ++ tailWord_3501262) baseStart_3501262 baseEnd_3501262 := by
    simpa [prefixWord, tailWord_3501262, baseEnd_3501262] using wordTrace_append hprefix tailTrace_3501262
  have hstable : (prefixWord ++ tailWord_3501262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501262).length < 2 ^ (prefixWord ++ tailWord_3501262).sum := by decide
  have hdescent : baseEnd_3501262 < baseStart_3501262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501265 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_3501265 : Nat := 118140960795 + 3501265 * 2 ^ 59
def prefixEnd_3501265 : Nat := 4983230072969 + 3 ^ 40 * 3501265 * 2
def baseEnd_3501265 : Nat := 1797831843764349018285481

theorem tailTrace_3501265 : CollatzResearch.WordTrace tailWord_3501265 prefixEnd_3501265 1797831843764349018285481 := by
  unfold tailWord_3501265
  simp only [CollatzResearch.WordTrace]
  refine ⟨127701625660522348300409249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85134417107014898866939499 127701625660522348300409249)
  ·
    refine ⟨95776219245391761225306937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127701625660522348300409249 95776219245391761225306937)
    ·
      refine ⟨71832164434043820918980203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95776219245391761225306937 71832164434043820918980203)
      ·
        refine ⟨107748246651065731378470305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71832164434043820918980203 107748246651065731378470305)
        ·
          refine ⟨80811184988299298533852729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107748246651065731378470305 80811184988299298533852729)
          ·
            refine ⟨60608388741224473900389547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80811184988299298533852729 60608388741224473900389547)
            ·
              refine ⟨90912583111836710850584321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60608388741224473900389547 90912583111836710850584321)
              ·
                refine ⟨68184437333877533137938241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90912583111836710850584321 68184437333877533137938241)
                ·
                  refine ⟨51138328000408149853453681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68184437333877533137938241 51138328000408149853453681)
                  ·
                    refine ⟨38353746000306112390090261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51138328000408149853453681 38353746000306112390090261)
                    ·
                      refine ⟨1797831843764349018285481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38353746000306112390090261 1797831843764349018285481)
                      ·
                        rfl

theorem cell23_3501265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_3501265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501265 prefixEnd_3501265 := by exact prefixLift 3501265
  have htrace : WordTrace (prefixWord ++ tailWord_3501265) baseStart_3501265 baseEnd_3501265 := by
    simpa [prefixWord, tailWord_3501265, baseEnd_3501265] using wordTrace_append hprefix tailTrace_3501265
  have hstable : (prefixWord ++ tailWord_3501265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501265).length < 2 ^ (prefixWord ++ tailWord_3501265).sum := by decide
  have hdescent : baseEnd_3501265 < baseStart_3501265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501380 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3501380 : Nat := 118140960795 + 3501380 * 2 ^ 59
def prefixEnd_3501380 : Nat := 4983230072969 + 3 ^ 40 * 3501380 * 2
def baseEnd_3501380 : Nat := 1797890894039616068347453

theorem tailTrace_3501380 : CollatzResearch.WordTrace tailWord_3501380 prefixEnd_3501380 1797890894039616068347453 := by
  unfold tailWord_3501380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63852910027552861470422797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85137213370070481960563729 63852910027552861470422797)
  ·
    refine ⟨23944841260332323051408549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63852910027552861470422797 23944841260332323051408549)
    ·
      refine ⟨4489657736312310572139103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23944841260332323051408549 4489657736312310572139103)
      ·
        refine ⟨6734486604468465858208655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489657736312310572139103 6734486604468465858208655)
        ·
          refine ⟨10101729906702698787312983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734486604468465858208655 10101729906702698787312983)
          ·
            refine ⟨15152594860054048180969475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10101729906702698787312983 15152594860054048180969475)
            ·
              refine ⟨22728892290081072271454213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15152594860054048180969475 22728892290081072271454213)
              ·
                refine ⟨4261667304390201050897665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22728892290081072271454213 4261667304390201050897665)
                ·
                  refine ⟨3196250478292650788173249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4261667304390201050897665 3196250478292650788173249)
                  ·
                    refine ⟨2397187858719488091129937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3196250478292650788173249 2397187858719488091129937)
                    ·
                      refine ⟨1797890894039616068347453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397187858719488091129937 1797890894039616068347453)
                      ·
                        rfl

theorem cell23_3501380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3501380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501380 prefixEnd_3501380 := by exact prefixLift 3501380
  have htrace : WordTrace (prefixWord ++ tailWord_3501380) baseStart_3501380 baseEnd_3501380 := by
    simpa [prefixWord, tailWord_3501380, baseEnd_3501380] using wordTrace_append hprefix tailTrace_3501380
  have hstable : (prefixWord ++ tailWord_3501380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501380).length < 2 ^ (prefixWord ++ tailWord_3501380).sum := by decide
  have hdescent : baseEnd_3501380 < baseStart_3501380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501392 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_3501392 : Nat := 118140960795 + 3501392 * 2 ^ 59
def prefixEnd_3501392 : Nat := 4983230072969 + 3 ^ 40 * 3501392 * 2
def baseEnd_3501392 : Nat := 1797897055807470021397397

theorem tailTrace_3501392 : CollatzResearch.WordTrace tailWord_3501392 prefixEnd_3501392 1797897055807470021397397 := by
  unfold tailWord_3501392
  simp only [CollatzResearch.WordTrace]
  refine ⟨63853128865531124495141215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85137505154041499326854953 63853128865531124495141215)
  ·
    refine ⟨95779693298296686742711823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63853128865531124495141215 95779693298296686742711823)
    ·
      refine ⟨143669539947445030114067735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95779693298296686742711823 143669539947445030114067735)
      ·
        refine ⟨215504309921167545171101603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143669539947445030114067735 215504309921167545171101603)
        ·
          refine ⟨323256464881751317756652405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215504309921167545171101603 323256464881751317756652405)
          ·
            refine ⟨30305293582664186039686163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 323256464881751317756652405 30305293582664186039686163)
            ·
              refine ⟨45457940373996279059529245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30305293582664186039686163 45457940373996279059529245)
              ·
                refine ⟨17046727640248604647323467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45457940373996279059529245 17046727640248604647323467)
                ·
                  refine ⟨25570091460372906970985201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17046727640248604647323467 25570091460372906970985201)
                  ·
                    refine ⟨19177568595279680228238901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25570091460372906970985201 19177568595279680228238901)
                    ·
                      refine ⟨1797897055807470021397397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19177568595279680228238901 1797897055807470021397397)
                      ·
                        rfl

theorem cell23_3501392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_3501392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501392 prefixEnd_3501392 := by exact prefixLift 3501392
  have htrace : WordTrace (prefixWord ++ tailWord_3501392) baseStart_3501392 baseEnd_3501392 := by
    simpa [prefixWord, tailWord_3501392, baseEnd_3501392] using wordTrace_append hprefix tailTrace_3501392
  have hstable : (prefixWord ++ tailWord_3501392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501392).length < 2 ^ (prefixWord ++ tailWord_3501392).sum := by decide
  have hdescent : baseEnd_3501392 < baseStart_3501392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501419 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 6, 4, 2]
def baseStart_3501419 : Nat := 118140960795 + 3501419 * 2 ^ 59
def prefixEnd_3501419 : Nat := 4983230072969 + 3 ^ 40 * 3501419 * 2
def baseEnd_3501419 : Nat := 1797910919785141415759773

theorem tailTrace_3501419 : CollatzResearch.WordTrace tailWord_3501419 prefixEnd_3501419 1797910919785141415759773 := by
  unfold tailWord_3501419
  simp only [CollatzResearch.WordTrace]
  refine ⟨127707242501964432601515311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85138161667976288401010207 127707242501964432601515311)
  ·
    refine ⟨191560863752946648902272967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127707242501964432601515311 191560863752946648902272967)
    ·
      refine ⟨287341295629419973353409451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191560863752946648902272967 287341295629419973353409451)
      ·
        refine ⟨431011943444129960030114177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287341295629419973353409451 431011943444129960030114177)
        ·
          refine ⟨323258957583097470022585633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431011943444129960030114177 323258957583097470022585633)
          ·
            refine ⟨242444218187323102516939225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323258957583097470022585633 242444218187323102516939225)
            ·
              refine ⟨181833163640492326887704419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242444218187323102516939225 181833163640492326887704419)
              ·
                refine ⟨272749745460738490331556629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181833163640492326887704419 272749745460738490331556629)
                ·
                  refine ⟨12785144318472116734291717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 272749745460738490331556629 12785144318472116734291717)
                  ·
                    refine ⟨2397214559713521887679697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12785144318472116734291717 2397214559713521887679697)
                    ·
                      refine ⟨1797910919785141415759773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397214559713521887679697 1797910919785141415759773)
                      ·
                        rfl

theorem cell23_3501419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 4, 2].length) (baseStart_3501419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501419 prefixEnd_3501419 := by exact prefixLift 3501419
  have htrace : WordTrace (prefixWord ++ tailWord_3501419) baseStart_3501419 baseEnd_3501419 := by
    simpa [prefixWord, tailWord_3501419, baseEnd_3501419] using wordTrace_append hprefix tailTrace_3501419
  have hstable : (prefixWord ++ tailWord_3501419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501419).length < 2 ^ (prefixWord ++ tailWord_3501419).sum := by decide
  have hdescent : baseEnd_3501419 < baseStart_3501419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501432 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_3501432 : Nat := 118140960795 + 3501432 * 2 ^ 59
def prefixEnd_3501432 : Nat := 4983230072969 + 3 ^ 40 * 3501432 * 2
def baseEnd_3501432 : Nat := 1797917595033649864897213

theorem tailTrace_3501432 : CollatzResearch.WordTrace tailWord_3501432 prefixEnd_3501432 1797917595033649864897213 := by
  unfold tailWord_3501432
  simp only [CollatzResearch.WordTrace]
  refine ⟨63853858325458667910869275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85138477767278223881159033 63853858325458667910869275)
  ·
    refine ⟨95780787488188001866303913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63853858325458667910869275 95780787488188001866303913)
    ·
      refine ⟨71835590616141001399727935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95780787488188001866303913 71835590616141001399727935)
      ·
        refine ⟨107753385924211502099591903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71835590616141001399727935 107753385924211502099591903)
        ·
          refine ⟨161630078886317253149387855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107753385924211502099591903 161630078886317253149387855)
          ·
            refine ⟨242445118329475879724081783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161630078886317253149387855 242445118329475879724081783)
            ·
              refine ⟨363667677494213819586122675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242445118329475879724081783 363667677494213819586122675)
              ·
                refine ⟨545501516241320729379184013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363667677494213819586122675 545501516241320729379184013)
                ·
                  refine ⟨204563068590495273517194005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545501516241320729379184013 204563068590495273517194005)
                  ·
                    refine ⟨9588893840179465946118469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 204563068590495273517194005 9588893840179465946118469)
                    ·
                      refine ⟨1797917595033649864897213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9588893840179465946118469 1797917595033649864897213)
                      ·
                        rfl

theorem cell23_3501432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_3501432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501432 prefixEnd_3501432 := by exact prefixLift 3501432
  have htrace : WordTrace (prefixWord ++ tailWord_3501432) baseStart_3501432 baseEnd_3501432 := by
    simpa [prefixWord, tailWord_3501432, baseEnd_3501432] using wordTrace_append hprefix tailTrace_3501432
  have hstable : (prefixWord ++ tailWord_3501432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501432).length < 2 ^ (prefixWord ++ tailWord_3501432).sum := by decide
  have hdescent : baseEnd_3501432 < baseStart_3501432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501496 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 4, 3, 2]
def baseStart_3501496 : Nat := 118140960795 + 3501496 * 2 ^ 59
def prefixEnd_3501496 : Nat := 4983230072969 + 3 ^ 40 * 3501496 * 2
def baseEnd_3501496 : Nat := 1797950457795537614496919

theorem tailTrace_3501496 : CollatzResearch.WordTrace tailWord_3501496 prefixEnd_3501496 1797950457795537614496919 := by
  unfold tailWord_3501496
  simp only [CollatzResearch.WordTrace]
  refine ⟨63855025461342737376034171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85140033948456983168045561 63855025461342737376034171)
  ·
    refine ⟨95782538192014106064051257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63855025461342737376034171 95782538192014106064051257)
    ·
      refine ⟨71836903644010579548038443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95782538192014106064051257 71836903644010579548038443)
      ·
        refine ⟨107755355466015869322057665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71836903644010579548038443 107755355466015869322057665)
        ·
          refine ⟨80816516599511901991543249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107755355466015869322057665 80816516599511901991543249)
          ·
            refine ⟨60612387449633926493657437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80816516599511901991543249 60612387449633926493657437)
            ·
              refine ⟨22729645293612722435121539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60612387449633926493657437 22729645293612722435121539)
              ·
                refine ⟨34094467940419083652682309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22729645293612722435121539 34094467940419083652682309)
                ·
                  refine ⟨6392712738828578184877933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34094467940419083652682309 6392712738828578184877933)
                  ·
                    refine ⟨2397267277060716819329225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6392712738828578184877933 2397267277060716819329225)
                    ·
                      refine ⟨1797950457795537614496919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397267277060716819329225 1797950457795537614496919)
                      ·
                        rfl

theorem cell23_3501496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_3501496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501496 prefixEnd_3501496 := by exact prefixLift 3501496
  have htrace : WordTrace (prefixWord ++ tailWord_3501496) baseStart_3501496 baseEnd_3501496 := by
    simpa [prefixWord, tailWord_3501496, baseEnd_3501496] using wordTrace_append hprefix tailTrace_3501496
  have hstable : (prefixWord ++ tailWord_3501496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501496).length < 2 ^ (prefixWord ++ tailWord_3501496).sum := by decide
  have hdescent : baseEnd_3501496 < baseStart_3501496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501503 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 1, 1, 3]
def baseStart_3501503 : Nat := 118140960795 + 3501503 * 2 ^ 59
def prefixEnd_3501503 : Nat := 4983230072969 + 3 ^ 40 * 3501503 * 2
def baseEnd_3501503 : Nat := 1797954052160119087109387

theorem tailTrace_3501503 : CollatzResearch.WordTrace tailWord_3501503 prefixEnd_3501503 1797954052160119087109387 := by
  unfold tailWord_3501503
  simp only [CollatzResearch.WordTrace]
  refine ⟨127710306233660114947573163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85140204155773409965048775 127710306233660114947573163)
  ·
    refine ⟨191565459350490172421359745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127710306233660114947573163 191565459350490172421359745)
    ·
      refine ⟨143674094512867629316019809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191565459350490172421359745 143674094512867629316019809)
      ·
        refine ⟨107755570884650721987014857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143674094512867629316019809 107755570884650721987014857)
        ·
          refine ⟨80816678163488041490261143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107755570884650721987014857 80816678163488041490261143)
          ·
            refine ⟨121225017245232062235391715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80816678163488041490261143 121225017245232062235391715)
            ·
              refine ⟨181837525867848093353087573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121225017245232062235391715 181837525867848093353087573)
              ·
                refine ⟨2130908506263844843981495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 181837525867848093353087573 2130908506263844843981495)
                ·
                  refine ⟨3196362759395767265972243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130908506263844843981495 3196362759395767265972243)
                  ·
                    refine ⟨4794544139093650898958365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196362759395767265972243 4794544139093650898958365)
                    ·
                      refine ⟨1797954052160119087109387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4794544139093650898958365 1797954052160119087109387)
                      ·
                        rfl

theorem cell23_3501503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_3501503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501503 prefixEnd_3501503 := by exact prefixLift 3501503
  have htrace : WordTrace (prefixWord ++ tailWord_3501503) baseStart_3501503 baseEnd_3501503 := by
    simpa [prefixWord, tailWord_3501503, baseEnd_3501503] using wordTrace_append hprefix tailTrace_3501503
  have hstable : (prefixWord ++ tailWord_3501503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501503).length < 2 ^ (prefixWord ++ tailWord_3501503).sum := by decide
  have hdescent : baseEnd_3501503 < baseStart_3501503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501549 : List Nat := [1, 5, 1, 3, 13]
def baseStart_3501549 : Nat := 118140960795 + 3501549 * 2 ^ 59
def prefixEnd_3501549 : Nat := 4983230072969 + 3 ^ 40 * 3501549 * 2
def baseEnd_3501549 : Nat := 2466361690356962835575

theorem tailTrace_3501549 : CollatzResearch.WordTrace tailWord_3501549 prefixEnd_3501549 2466361690356962835575 := by
  unfold tailWord_3501549
  simp only [CollatzResearch.WordTrace]
  refine ⟨127711983991493464803747701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85141322660995643202498467 127711983991493464803747701)
  ·
    refine ⟨11972998499202512325351347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127711983991493464803747701 11972998499202512325351347)
    ·
      refine ⟨17959497748803768488027021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11972998499202512325351347 17959497748803768488027021)
      ·
        refine ⟨6734811655801413183010133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17959497748803768488027021 6734811655801413183010133)
        ·
          refine ⟨2466361690356962835575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6734811655801413183010133 2466361690356962835575)
          ·
            rfl

theorem cell23_3501549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 13].length) (baseStart_3501549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501549 prefixEnd_3501549 := by exact prefixLift 3501549
  have htrace : WordTrace (prefixWord ++ tailWord_3501549) baseStart_3501549 baseEnd_3501549 := by
    simpa [prefixWord, tailWord_3501549, baseEnd_3501549] using wordTrace_append hprefix tailTrace_3501549
  have hstable : (prefixWord ++ tailWord_3501549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501549).length < 2 ^ (prefixWord ++ tailWord_3501549).sum := by decide
  have hdescent : baseEnd_3501549 < baseStart_3501549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501553 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 2, 4]
def baseStart_3501553 : Nat := 118140960795 + 3501553 * 2 ^ 59
def prefixEnd_3501553 : Nat := 4983230072969 + 3 ^ 40 * 3501553 * 2
def baseEnd_3501553 : Nat := 599326575397614630494719

theorem tailTrace_3501553 : CollatzResearch.WordTrace tailWord_3501553 prefixEnd_3501553 599326575397614630494719 := by
  unfold tailWord_3501553
  simp only [CollatzResearch.WordTrace]
  refine ⟨127712129883478973486893313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85141419922319315657928875 127712129883478973486893313)
  ·
    refine ⟨95784097412609230115169985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127712129883478973486893313 95784097412609230115169985)
    ·
      refine ⟨71838073059456922586377489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95784097412609230115169985 71838073059456922586377489)
      ·
        refine ⟨53878554794592691939783117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71838073059456922586377489 53878554794592691939783117)
        ·
          refine ⟨20204458047972259477418669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53878554794592691939783117 20204458047972259477418669)
          ·
            refine ⟨7576671767989597304032001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20204458047972259477418669 7576671767989597304032001)
            ·
              refine ⟨5682503825992197978024001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576671767989597304032001 5682503825992197978024001)
              ·
                refine ⟨4261877869494148483518001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682503825992197978024001 4261877869494148483518001)
                ·
                  refine ⟨3196408402120611362638501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4261877869494148483518001 3196408402120611362638501)
                  ·
                    refine ⟨599326575397614630494719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196408402120611362638501 599326575397614630494719)
                    ·
                      rfl

theorem cell23_3501553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_3501553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501553 prefixEnd_3501553 := by exact prefixLift 3501553
  have htrace : WordTrace (prefixWord ++ tailWord_3501553) baseStart_3501553 baseEnd_3501553 := by
    simpa [prefixWord, tailWord_3501553, baseEnd_3501553] using wordTrace_append hprefix tailTrace_3501553
  have hstable : (prefixWord ++ tailWord_3501553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501553).length < 2 ^ (prefixWord ++ tailWord_3501553).sum := by decide
  have hdescent : baseEnd_3501553 < baseStart_3501553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501554 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3501554 : Nat := 118140960795 + 3501554 * 2 ^ 59
def prefixEnd_3501554 : Nat := 4983230072969 + 3 ^ 40 * 3501554 * 2
def baseEnd_3501554 : Nat := 1797980239673498387571653

theorem tailTrace_3501554 : CollatzResearch.WordTrace tailWord_3501554 prefixEnd_3501554 1797980239673498387571653 := by
  unfold tailWord_3501554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928041589118837664419929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85141444237650233771786477 31928041589118837664419929)
  ·
    refine ⟨23946031191839128248314947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31928041589118837664419929 23946031191839128248314947)
    ·
      refine ⟨35919046787758692372472421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23946031191839128248314947 35919046787758692372472421)
      ·
        refine ⟨6734821272704754819838579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35919046787758692372472421 6734821272704754819838579)
        ·
          refine ⟨10102231909057132229757869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734821272704754819838579 10102231909057132229757869)
          ·
            refine ⟨3788336965896424586159201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10102231909057132229757869 3788336965896424586159201)
            ·
              refine ⟨2841252724422318439619401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788336965896424586159201 2841252724422318439619401)
              ·
                refine ⟨2130939543316738829714551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841252724422318439619401 2130939543316738829714551)
                ·
                  refine ⟨3196409314975108244571827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2130939543316738829714551 3196409314975108244571827)
                  ·
                    refine ⟨4794613972462662366857741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196409314975108244571827 4794613972462662366857741)
                    ·
                      refine ⟨1797980239673498387571653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4794613972462662366857741 1797980239673498387571653)
                      ·
                        rfl

theorem cell23_3501554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3501554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501554 prefixEnd_3501554 := by exact prefixLift 3501554
  have htrace : WordTrace (prefixWord ++ tailWord_3501554) baseStart_3501554 baseEnd_3501554 := by
    simpa [prefixWord, tailWord_3501554, baseEnd_3501554] using wordTrace_append hprefix tailTrace_3501554
  have hstable : (prefixWord ++ tailWord_3501554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501554).length < 2 ^ (prefixWord ++ tailWord_3501554).sum := by decide
  have hdescent : baseEnd_3501554 < baseStart_3501554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501570 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3501570 : Nat := 118140960795 + 3501570 * 2 ^ 59
def prefixEnd_3501570 : Nat := 4983230072969 + 3 ^ 40 * 3501570 * 2
def baseEnd_3501570 : Nat := 599329485121323441657193

theorem tailTrace_3501570 : CollatzResearch.WordTrace tailWord_3501570 prefixEnd_3501570 599329485121323441657193 := by
  unfold tailWord_3501570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928187481104346347565541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85141833282944923593508109 31928187481104346347565541)
  ·
    refine ⟨5986535152707064940168539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31928187481104346347565541 5986535152707064940168539)
    ·
      refine ⟨8979802729060597410252809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5986535152707064940168539 8979802729060597410252809)
      ·
        refine ⟨6734852046795448057689607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8979802729060597410252809 6734852046795448057689607)
        ·
          refine ⟨10102278070193172086534411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6734852046795448057689607 10102278070193172086534411)
          ·
            refine ⟨15153417105289758129801617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102278070193172086534411 15153417105289758129801617)
            ·
              refine ⟨11365062828967318597351213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15153417105289758129801617 11365062828967318597351213)
              ·
                refine ⟨4261898560862744474006705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11365062828967318597351213 4261898560862744474006705)
                ·
                  refine ⟨3196423920647058355505029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4261898560862744474006705 3196423920647058355505029)
                  ·
                    refine ⟨599329485121323441657193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196423920647058355505029 599329485121323441657193)
                    ·
                      rfl

theorem cell23_3501570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3501570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501570 prefixEnd_3501570 := by exact prefixLift 3501570
  have htrace : WordTrace (prefixWord ++ tailWord_3501570) baseStart_3501570 baseEnd_3501570 := by
    simpa [prefixWord, tailWord_3501570, baseEnd_3501570] using wordTrace_append hprefix tailTrace_3501570
  have hstable : (prefixWord ++ tailWord_3501570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501570).length < 2 ^ (prefixWord ++ tailWord_3501570).sum := by decide
  have hdescent : baseEnd_3501570 < baseStart_3501570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501576 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3501576 : Nat := 118140960795 + 3501576 * 2 ^ 59
def prefixEnd_3501576 : Nat := 4983230072969 + 3 ^ 40 * 3501576 * 2
def baseEnd_3501576 : Nat := 1797991536247897301496551

theorem tailTrace_3501576 : CollatzResearch.WordTrace tailWord_3501576 prefixEnd_3501576 1797991536247897301496551 := by
  unfold tailWord_3501576
  simp only [CollatzResearch.WordTrace]
  refine ⟨63856484381197824207490291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85141979174930432276653721 63856484381197824207490291)
  ·
    refine ⟨95784726571796736311235437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63856484381197824207490291 95784726571796736311235437)
    ·
      refine ⟨35919272464423776116713289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95784726571796736311235437 35919272464423776116713289)
      ·
        refine ⟨26939454348317832087534967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35919272464423776116713289 26939454348317832087534967)
        ·
          refine ⟨40409181522476748131302451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26939454348317832087534967 40409181522476748131302451)
          ·
            refine ⟨60613772283715122196953677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40409181522476748131302451 60613772283715122196953677)
            ·
              refine ⟨22730164606393170823857629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60613772283715122196953677 22730164606393170823857629)
              ·
                refine ⟨8523811727397439058946611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22730164606393170823857629 8523811727397439058946611)
                ·
                  refine ⟨12785717591096158588419917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8523811727397439058946611 12785717591096158588419917)
                  ·
                    refine ⟨4794644096661059470657469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12785717591096158588419917 4794644096661059470657469)
                    ·
                      refine ⟨1797991536247897301496551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4794644096661059470657469 1797991536247897301496551)
                      ·
                        rfl

theorem cell23_3501576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3501576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501576 prefixEnd_3501576 := by exact prefixLift 3501576
  have htrace : WordTrace (prefixWord ++ tailWord_3501576) baseStart_3501576 baseEnd_3501576 := by
    simpa [prefixWord, tailWord_3501576, baseEnd_3501576] using wordTrace_append hprefix tailTrace_3501576
  have hstable : (prefixWord ++ tailWord_3501576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501576).length < 2 ^ (prefixWord ++ tailWord_3501576).sum := by decide
  have hdescent : baseEnd_3501576 < baseStart_3501576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501581 : List Nat := [1, 7, 1, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_3501581 : Nat := 118140960795 + 3501581 * 2 ^ 59
def prefixEnd_3501581 : Nat := 4983230072969 + 3 ^ 40 * 3501581 * 2
def baseEnd_3501581 : Nat := 1797994103651169781934029

theorem tailTrace_3501581 : CollatzResearch.WordTrace tailWord_3501581 prefixEnd_3501581 1797994103651169781934029 := by
  unfold tailWord_3501581
  simp only [CollatzResearch.WordTrace]
  refine ⟨127713151127377534268912597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85142100751585022845941731 127713151127377534268912597)
  ·
    refine ⟨2993276979547910959427639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 127713151127377534268912597 2993276979547910959427639)
    ·
      refine ⟨4489915469321866439141459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993276979547910959427639 4489915469321866439141459)
      ·
        refine ⟨6734873203982799658712189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489915469321866439141459 6734873203982799658712189)
        ·
          refine ⟨2525577451493549872017071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6734873203982799658712189 2525577451493549872017071)
          ·
            refine ⟨3788366177240324808025607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525577451493549872017071 3788366177240324808025607)
            ·
              refine ⟨5682549265860487212038411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788366177240324808025607 5682549265860487212038411)
              ·
                refine ⟨8523823898790730818057617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682549265860487212038411 8523823898790730818057617)
                ·
                  refine ⟨6392867924093048113543213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8523823898790730818057617 6392867924093048113543213)
                  ·
                    refine ⟨2397325471534893042578705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6392867924093048113543213 2397325471534893042578705)
                    ·
                      refine ⟨1797994103651169781934029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397325471534893042578705 1797994103651169781934029)
                      ·
                        rfl

theorem cell23_3501581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_3501581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501581 prefixEnd_3501581 := by exact prefixLift 3501581
  have htrace : WordTrace (prefixWord ++ tailWord_3501581) baseStart_3501581 baseEnd_3501581 := by
    simpa [prefixWord, tailWord_3501581, baseEnd_3501581] using wordTrace_append hprefix tailTrace_3501581
  have hstable : (prefixWord ++ tailWord_3501581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501581).length < 2 ^ (prefixWord ++ tailWord_3501581).sum := by decide
  have hdescent : baseEnd_3501581 < baseStart_3501581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501650 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_3501650 : Nat := 118140960795 + 3501650 * 2 ^ 59
def prefixEnd_3501650 : Nat := 4983230072969 + 3 ^ 40 * 3501650 * 2
def baseEnd_3501650 : Nat := 1798029533816330011971211

theorem tailTrace_3501650 : CollatzResearch.WordTrace tailWord_3501650 prefixEnd_3501650 1798029533816330011971211 := by
  unfold tailWord_3501650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31928916941031889763293601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85143778509418372702116269 31928916941031889763293601)
  ·
    refine ⟨23946687705773917322470201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31928916941031889763293601 23946687705773917322470201)
    ·
      refine ⟨17960015779330437991852651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23946687705773917322470201 17960015779330437991852651)
      ·
        refine ⟨26940023668995656987778977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17960015779330437991852651 26940023668995656987778977)
        ·
          refine ⟨20205017751746742740834233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26940023668995656987778977 20205017751746742740834233)
          ·
            refine ⟨15153763313810057055625675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20205017751746742740834233 15153763313810057055625675)
            ·
              refine ⟨22730644970715085583438513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15153763313810057055625675 22730644970715085583438513)
              ·
                refine ⟨17047983728036314187578885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22730644970715085583438513 17047983728036314187578885)
                ·
                  refine ⟨3196496949006808910171041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17047983728036314187578885 3196496949006808910171041)
                  ·
                    refine ⟨2397372711755106682628281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3196496949006808910171041 2397372711755106682628281)
                    ·
                      refine ⟨1798029533816330011971211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397372711755106682628281 1798029533816330011971211)
                      ·
                        rfl

theorem cell23_3501650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_3501650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501650 prefixEnd_3501650 := by exact prefixLift 3501650
  have htrace : WordTrace (prefixWord ++ tailWord_3501650) baseStart_3501650 baseEnd_3501650 := by
    simpa [prefixWord, tailWord_3501650, baseEnd_3501650] using wordTrace_append hprefix tailTrace_3501650
  have hstable : (prefixWord ++ tailWord_3501650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501650).length < 2 ^ (prefixWord ++ tailWord_3501650).sum := by decide
  have hdescent : baseEnd_3501650 < baseStart_3501650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501703 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 2, 5]
def baseStart_3501703 : Nat := 118140960795 + 3501703 * 2 ^ 59
def prefixEnd_3501703 : Nat := 4983230072969 + 3 ^ 40 * 3501703 * 2
def baseEnd_3501703 : Nat := 599352249430339434869489

theorem tailTrace_3501703 : CollatzResearch.WordTrace tailWord_3501703 prefixEnd_3501703 599352249430339434869489 := by
  unfold tailWord_3501703
  simp only [CollatzResearch.WordTrace]
  refine ⟨127717600832935549104853763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85145067221957032736569175 127717600832935549104853763)
  ·
    refine ⟨191576401249403323657280645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127717600832935549104853763 191576401249403323657280645)
    ·
      refine ⟨35920575234263123185740121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191576401249403323657280645 35920575234263123185740121)
      ·
        refine ⟨26940431425697342389305091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35920575234263123185740121 26940431425697342389305091)
        ·
          refine ⟨40410647138546013583957637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26940431425697342389305091 40410647138546013583957637)
          ·
            refine ⟨7576996338477377546992057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40410647138546013583957637 7576996338477377546992057)
            ·
              refine ⟨5682747253858033160244043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576996338477377546992057 5682747253858033160244043)
              ·
                refine ⟨8524120880787049740366065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682747253858033160244043 8524120880787049740366065)
                ·
                  refine ⟨6393090660590287305274549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8524120880787049740366065 6393090660590287305274549)
                  ·
                    refine ⟨599352249430339434869489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6393090660590287305274549 599352249430339434869489)
                    ·
                      rfl

theorem cell23_3501703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_3501703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501703 prefixEnd_3501703 := by exact prefixLift 3501703
  have htrace : WordTrace (prefixWord ++ tailWord_3501703) baseStart_3501703 baseEnd_3501703 := by
    simpa [prefixWord, tailWord_3501703, baseEnd_3501703] using wordTrace_append hprefix tailTrace_3501703
  have hstable : (prefixWord ++ tailWord_3501703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501703).length < 2 ^ (prefixWord ++ tailWord_3501703).sum := by decide
  have hdescent : baseEnd_3501703 < baseStart_3501703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501724 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 5]
def baseStart_3501724 : Nat := 118140960795 + 3501724 * 2 ^ 59
def prefixEnd_3501724 : Nat := 4983230072969 + 3 ^ 40 * 3501724 * 2
def baseEnd_3501724 : Nat := 199785281264973635827319

theorem tailTrace_3501724 : CollatzResearch.WordTrace tailWord_3501724 prefixEnd_3501724 199785281264973635827319 := by
  unfold tailWord_3501724
  simp only [CollatzResearch.WordTrace]
  refine ⟨63859183382929734845684113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85145577843906313127578817 63859183382929734845684113)
  ·
    refine ⟨47894387537197301134263085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63859183382929734845684113 47894387537197301134263085)
    ·
      refine ⟨17960395326448987925348657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47894387537197301134263085 17960395326448987925348657)
      ·
        refine ⟨13470296494836740944011493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17960395326448987925348657 13470296494836740944011493)
        ·
          refine ⟨2525680592781888927002155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13470296494836740944011493 2525680592781888927002155)
          ·
            refine ⟨3788520889172833390503233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525680592781888927002155 3788520889172833390503233)
            ·
              refine ⟨2841390666879625042877425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3788520889172833390503233 2841390666879625042877425)
              ·
                refine ⟨2131043000159718782158069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2841390666879625042877425 2131043000159718782158069)
                ·
                  refine ⟨199785281264973635827319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2131043000159718782158069 199785281264973635827319)
                  ·
                    rfl

theorem cell23_3501724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_3501724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501724 prefixEnd_3501724 := by exact prefixLift 3501724
  have htrace : WordTrace (prefixWord ++ tailWord_3501724) baseStart_3501724 baseEnd_3501724 := by
    simpa [prefixWord, tailWord_3501724, baseEnd_3501724] using wordTrace_append hprefix tailTrace_3501724
  have hstable : (prefixWord ++ tailWord_3501724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501724).length < 2 ^ (prefixWord ++ tailWord_3501724).sum := by decide
  have hdescent : baseEnd_3501724 < baseStart_3501724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501776 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_3501776 : Nat := 118140960795 + 3501776 * 2 ^ 59
def prefixEnd_3501776 : Nat := 4983230072969 + 3 ^ 40 * 3501776 * 2
def baseEnd_3501776 : Nat := 599364744126265506331877

theorem tailTrace_3501776 : CollatzResearch.WordTrace tailWord_3501776 prefixEnd_3501776 599364744126265506331877 := by
  unfold tailWord_3501776
  simp only [CollatzResearch.WordTrace]
  refine ⟨63860131680835541286130591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85146842241114055048174121 63860131680835541286130591)
  ·
    refine ⟨95790197521253311929195887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63860131680835541286130591 95790197521253311929195887)
    ·
      refine ⟨143685296281879967893793831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95790197521253311929195887 143685296281879967893793831)
      ·
        refine ⟨215527944422819951840690747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143685296281879967893793831 215527944422819951840690747)
        ·
          refine ⟨323291916634229927761036121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215527944422819951840690747 323291916634229927761036121)
          ·
            refine ⟨242468937475672445820777091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323291916634229927761036121 242468937475672445820777091)
            ·
              refine ⟨363703406213508668731165637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242468937475672445820777091 363703406213508668731165637)
              ·
                refine ⟨68194388665032875387093557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 363703406213508668731165637 68194388665032875387093557)
                ·
                  refine ⟨6393223937346832067540021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68194388665032875387093557 6393223937346832067540021)
                  ·
                    refine ⟨599364744126265506331877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6393223937346832067540021 599364744126265506331877)
                    ·
                      rfl

theorem cell23_3501776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_3501776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501776 prefixEnd_3501776 := by exact prefixLift 3501776
  have htrace : WordTrace (prefixWord ++ tailWord_3501776) baseStart_3501776 baseEnd_3501776 := by
    simpa [prefixWord, tailWord_3501776, baseEnd_3501776] using wordTrace_append hprefix tailTrace_3501776
  have hstable : (prefixWord ++ tailWord_3501776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501776).length < 2 ^ (prefixWord ++ tailWord_3501776).sum := by decide
  have hdescent : baseEnd_3501776 < baseStart_3501776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501780 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 6]
def baseStart_3501780 : Nat := 118140960795 + 3501780 * 2 ^ 59
def prefixEnd_3501780 : Nat := 4983230072969 + 3 ^ 40 * 3501780 * 2
def baseEnd_3501780 : Nat := 199788476255712722593957

theorem tailTrace_3501780 : CollatzResearch.WordTrace tailWord_3501780 prefixEnd_3501780 199788476255712722593957 := by
  unfold tailWord_3501780
  simp only [CollatzResearch.WordTrace]
  refine ⟨63860204626828295627703397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85146939502437727503604529 63860204626828295627703397)
  ·
    refine ⟨11973788367530305430194387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63860204626828295627703397 11973788367530305430194387)
    ·
      refine ⟨17960682551295458145291581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11973788367530305430194387 17960682551295458145291581)
      ·
        refine ⟨6735255956735796804484343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17960682551295458145291581 6735255956735796804484343)
        ·
          refine ⟨10102883935103695206726515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6735255956735796804484343 10102883935103695206726515)
          ·
            refine ⟨15154325902655542810089773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102883935103695206726515 15154325902655542810089773)
            ·
              refine ⟨5682872213495828553783665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15154325902655542810089773 5682872213495828553783665)
              ·
                refine ⟨4262154160121871415337749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682872213495828553783665 4262154160121871415337749)
                ·
                  refine ⟨199788476255712722593957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4262154160121871415337749 199788476255712722593957)
                  ·
                    rfl

theorem cell23_3501780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_3501780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501780 prefixEnd_3501780 := by exact prefixLift 3501780
  have htrace : WordTrace (prefixWord ++ tailWord_3501780) baseStart_3501780 baseEnd_3501780 := by
    simpa [prefixWord, tailWord_3501780, baseEnd_3501780] using wordTrace_append hprefix tailTrace_3501780
  have hstable : (prefixWord ++ tailWord_3501780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501780).length < 2 ^ (prefixWord ++ tailWord_3501780).sum := by decide
  have hdescent : baseEnd_3501780 < baseStart_3501780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501800 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_3501800 : Nat := 118140960795 + 3501800 * 2 ^ 59
def prefixEnd_3501800 : Nat := 4983230072969 + 3 ^ 40 * 3501800 * 2
def baseEnd_3501800 : Nat := 1798106555914504425095521

theorem tailTrace_3501800 : CollatzResearch.WordTrace tailWord_3501800 prefixEnd_3501800 1798106555914504425095521 := by
  unfold tailWord_3501800
  simp only [CollatzResearch.WordTrace]
  refine ⟨63860569356792067335567427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85147425809056089780756569 63860569356792067335567427)
  ·
    refine ⟨95790854035188101003351141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63860569356792067335567427 95790854035188101003351141)
    ·
      refine ⟨17960785131597768938128339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95790854035188101003351141 17960785131597768938128339)
      ·
        refine ⟨26941177697396653407192509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17960785131597768938128339 26941177697396653407192509)
        ·
          refine ⟨10102941636523745027697191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26941177697396653407192509 10102941636523745027697191)
          ·
            refine ⟨15154412454785617541545787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10102941636523745027697191 15154412454785617541545787)
            ·
              refine ⟨22731618682178426312318681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15154412454785617541545787 22731618682178426312318681)
              ·
                refine ⟨17048714011633819734239011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22731618682178426312318681 17048714011633819734239011)
                ·
                  refine ⟨25573071017450729601358517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17048714011633819734239011 25573071017450729601358517)
                  ·
                    refine ⟨2397475407886005900127361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25573071017450729601358517 2397475407886005900127361)
                    ·
                      refine ⟨1798106555914504425095521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397475407886005900127361 1798106555914504425095521)
                      ·
                        rfl

theorem cell23_3501800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_3501800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501800 prefixEnd_3501800 := by exact prefixLift 3501800
  have htrace : WordTrace (prefixWord ++ tailWord_3501800) baseStart_3501800 baseEnd_3501800 := by
    simpa [prefixWord, tailWord_3501800, baseEnd_3501800] using wordTrace_append hprefix tailTrace_3501800
  have hstable : (prefixWord ++ tailWord_3501800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501800).length < 2 ^ (prefixWord ++ tailWord_3501800).sum := by decide
  have hdescent : baseEnd_3501800 < baseStart_3501800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501810 : List Nat := [3, 2, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3501810 : Nat := 118140960795 + 3501810 * 2 ^ 59
def prefixEnd_3501810 : Nat := 4983230072969 + 3 ^ 40 * 3501810 * 2
def baseEnd_3501810 : Nat := 599370563573683128656825

theorem tailTrace_3501810 : CollatzResearch.WordTrace tailWord_3501810 prefixEnd_3501810 599370563573683128656825 := by
  unfold tailWord_3501810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31930375860886976594749721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85147668962365270919332589 31930375860886976594749721)
  ·
    refine ⟨23947781895665232446062291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31930375860886976594749721 23947781895665232446062291)
    ·
      refine ⟨35921672843497848669093437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23947781895665232446062291 35921672843497848669093437)
      ·
        refine ⟨13470627316311693250910039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35921672843497848669093437 13470627316311693250910039)
        ·
          refine ⟨20205940974467539876365059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13470627316311693250910039 20205940974467539876365059)
          ·
            refine ⟨30308911461701309814547589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20205940974467539876365059 30308911461701309814547589)
            ·
              refine ⟨5682920899068995590227673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30308911461701309814547589 5682920899068995590227673)
              ·
                refine ⟨4262190674301746692670755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682920899068995590227673 4262190674301746692670755)
                ·
                  refine ⟨6393286011452620039006133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262190674301746692670755 6393286011452620039006133)
                  ·
                    refine ⟨599370563573683128656825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6393286011452620039006133 599370563573683128656825)
                    ·
                      rfl

theorem cell23_3501810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3501810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501810 prefixEnd_3501810 := by exact prefixLift 3501810
  have htrace : WordTrace (prefixWord ++ tailWord_3501810) baseStart_3501810 baseEnd_3501810 := by
    simpa [prefixWord, tailWord_3501810, baseEnd_3501810] using wordTrace_append hprefix tailTrace_3501810
  have hstable : (prefixWord ++ tailWord_3501810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501810).length < 2 ^ (prefixWord ++ tailWord_3501810).sum := by decide
  have hdescent : baseEnd_3501810 < baseStart_3501810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501823 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 4, 4]
def baseStart_3501823 : Nat := 118140960795 + 3501823 * 2 ^ 59
def prefixEnd_3501823 : Nat := 4983230072969 + 3 ^ 40 * 3501823 * 2
def baseEnd_3501823 : Nat := 599372788656519278369305

theorem tailTrace_3501823 : CollatzResearch.WordTrace tailWord_3501823 prefixEnd_3501823 599372788656519278369305 := by
  unfold tailWord_3501823
  simp only [CollatzResearch.WordTrace]
  refine ⟨127721977592500809599222123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85147985061667206399481415 127721977592500809599222123)
  ·
    refine ⟨191582966388751214398833185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127721977592500809599222123 191582966388751214398833185)
    ·
      refine ⟨143687224791563410799124889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191582966388751214398833185 143687224791563410799124889)
      ·
        refine ⟨107765418593672558099343667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143687224791563410799124889 107765418593672558099343667)
        ·
          refine ⟨161648127890508837149015501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107765418593672558099343667 161648127890508837149015501)
          ·
            refine ⟨60618047958940813930880813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161648127890508837149015501 60618047958940813930880813)
            ·
              refine ⟨22731767984602805224080305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60618047958940813930880813 22731767984602805224080305)
              ·
                refine ⟨17048825988452103918060229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22731767984602805224080305 17048825988452103918060229)
                ·
                  refine ⟨3196654872834769484636293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17048825988452103918060229 3196654872834769484636293)
                  ·
                    refine ⟨599372788656519278369305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196654872834769484636293 599372788656519278369305)
                    ·
                      rfl

theorem cell23_3501823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_3501823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501823 prefixEnd_3501823 := by exact prefixLift 3501823
  have htrace : WordTrace (prefixWord ++ tailWord_3501823) baseStart_3501823 baseEnd_3501823 := by
    simpa [prefixWord, tailWord_3501823, baseEnd_3501823] using wordTrace_append hprefix tailTrace_3501823
  have hstable : (prefixWord ++ tailWord_3501823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501823).length < 2 ^ (prefixWord ++ tailWord_3501823).sum := by decide
  have hdescent : baseEnd_3501823 < baseStart_3501823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501833 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_3501833 : Nat := 118140960795 + 3501833 * 2 ^ 59
def prefixEnd_3501833 : Nat := 4983230072969 + 3 ^ 40 * 3501833 * 2
def baseEnd_3501833 : Nat := 1798123500776102795982869

theorem tailTrace_3501833 : CollatzResearch.WordTrace tailWord_3501833 prefixEnd_3501833 1798123500776102795982869 := by
  unfold tailWord_3501833
  simp only [CollatzResearch.WordTrace]
  refine ⟨127722342322464581307086153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85148228214976387538057435 127722342322464581307086153)
  ·
    refine ⟨95791756741848435980314615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127722342322464581307086153 95791756741848435980314615)
    ·
      refine ⟨143687635112772653970471923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95791756741848435980314615 143687635112772653970471923)
      ·
        refine ⟨215531452669158980955707885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143687635112772653970471923 215531452669158980955707885)
        ·
          refine ⟨80824294750934617858390457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215531452669158980955707885 80824294750934617858390457)
          ·
            refine ⟨60618221063200963393792843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80824294750934617858390457 60618221063200963393792843)
            ·
              refine ⟨90927331594801445090689265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60618221063200963393792843 90927331594801445090689265)
              ·
                refine ⟨68195498696101083818016949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90927331594801445090689265 68195498696101083818016949)
                ·
                  refine ⟨6393328002759476607939089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68195498696101083818016949 6393328002759476607939089)
                  ·
                    refine ⟨4794996002069607455954317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6393328002759476607939089 4794996002069607455954317)
                    ·
                      refine ⟨1798123500776102795982869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4794996002069607455954317 1798123500776102795982869)
                      ·
                        rfl

theorem cell23_3501833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_3501833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501833 prefixEnd_3501833 := by exact prefixLift 3501833
  have htrace : WordTrace (prefixWord ++ tailWord_3501833) baseStart_3501833 baseEnd_3501833 := by
    simpa [prefixWord, tailWord_3501833, baseEnd_3501833] using wordTrace_append hprefix tailTrace_3501833
  have hstable : (prefixWord ++ tailWord_3501833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501833).length < 2 ^ (prefixWord ++ tailWord_3501833).sum := by decide
  have hdescent : baseEnd_3501833 < baseStart_3501833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501836 : List Nat := [2, 2, 1, 2, 2, 1, 13]
def baseStart_3501836 : Nat := 118140960795 + 3501836 * 2 ^ 59
def prefixEnd_3501836 : Nat := 4983230072969 + 3 ^ 40 * 3501836 * 2
def baseEnd_3501836 : Nat := 22199074582939089928955

theorem tailTrace_3501836 : CollatzResearch.WordTrace tailWord_3501836 prefixEnd_3501836 22199074582939089928955 := by
  unfold tailWord_3501836
  simp only [CollatzResearch.WordTrace]
  refine ⟨63861225870726856409722681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85148301160969141879630241 63861225870726856409722681)
  ·
    refine ⟨47895919403045142307292011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63861225870726856409722681 47895919403045142307292011)
    ·
      refine ⟨71843879104567713460938017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47895919403045142307292011 71843879104567713460938017)
      ·
        refine ⟨53882909328425785095703513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71843879104567713460938017 53882909328425785095703513)
        ·
          refine ⟨40412181996319338821777635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53882909328425785095703513 40412181996319338821777635)
          ·
            refine ⟨60618272994479008232666453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40412181996319338821777635 60618272994479008232666453)
            ·
              refine ⟨22199074582939089928955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 60618272994479008232666453 22199074582939089928955)
              ·
                rfl

theorem cell23_3501836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 13].length) (baseStart_3501836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501836 prefixEnd_3501836 := by exact prefixLift 3501836
  have htrace : WordTrace (prefixWord ++ tailWord_3501836) baseStart_3501836 baseEnd_3501836 := by
    simpa [prefixWord, tailWord_3501836, baseEnd_3501836] using wordTrace_append hprefix tailTrace_3501836
  have hstable : (prefixWord ++ tailWord_3501836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501836).length < 2 ^ (prefixWord ++ tailWord_3501836).sum := by decide
  have hdescent : baseEnd_3501836 < baseStart_3501836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501857 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 2, 4]
def baseStart_3501857 : Nat := 118140960795 + 3501857 * 2 ^ 59
def prefixEnd_3501857 : Nat := 4983230072969 + 3 ^ 40 * 3501857 * 2
def baseEnd_3501857 : Nat := 599378608103936900694253

theorem tailTrace_3501857 : CollatzResearch.WordTrace tailWord_3501857 prefixEnd_3501857 599378608103936900694253 := by
  unfold tailWord_3501857
  simp only [CollatzResearch.WordTrace]
  refine ⟨127723217674377633405959825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85148811782918422270639883 127723217674377633405959825)
  ·
    refine ⟨95792413255783225054469869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127723217674377633405959825 95792413255783225054469869)
    ·
      refine ⟨35922154970918709395426201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95792413255783225054469869 35922154970918709395426201)
      ·
        refine ⟨26941616228189032046569651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35922154970918709395426201 26941616228189032046569651)
        ·
          refine ⟨40412424342283548069854477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26941616228189032046569651 40412424342283548069854477)
          ·
            refine ⟨15154659128356330526195429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40412424342283548069854477 15154659128356330526195429)
            ·
              refine ⟨2841498586566811973661643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15154659128356330526195429 2841498586566811973661643)
              ·
                refine ⟨4262247879850217960492465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2841498586566811973661643 4262247879850217960492465)
                ·
                  refine ⟨3196685909887663470369349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262247879850217960492465 3196685909887663470369349)
                  ·
                    refine ⟨599378608103936900694253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196685909887663470369349 599378608103936900694253)
                    ·
                      rfl

theorem cell23_3501857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_3501857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501857 prefixEnd_3501857 := by exact prefixLift 3501857
  have htrace : WordTrace (prefixWord ++ tailWord_3501857) baseStart_3501857 baseEnd_3501857 := by
    simpa [prefixWord, tailWord_3501857, baseEnd_3501857] using wordTrace_append hprefix tailTrace_3501857
  have hstable : (prefixWord ++ tailWord_3501857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501857).length < 2 ^ (prefixWord ++ tailWord_3501857).sum := by decide
  have hdescent : baseEnd_3501857 < baseStart_3501857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501880 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_3501880 : Nat := 118140960795 + 3501880 * 2 ^ 59
def prefixEnd_3501880 : Nat := 4983230072969 + 3 ^ 40 * 3501880 * 2
def baseEnd_3501880 : Nat := 1798147634366864112095153

theorem tailTrace_3501880 : CollatzResearch.WordTrace tailWord_3501880 prefixEnd_3501880 1798147634366864112095153 := by
  unfold tailWord_3501880
  simp only [CollatzResearch.WordTrace]
  refine ⟨63862028276647154167023547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85149371035529538889364729 63862028276647154167023547)
  ·
    refine ⟨95793042414970731250535321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63862028276647154167023547 95793042414970731250535321)
    ·
      refine ⟨71844781811228048437901491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95793042414970731250535321 71844781811228048437901491)
      ·
        refine ⟨107767172716842072656852237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71844781811228048437901491 107767172716842072656852237)
        ·
          refine ⟨40412689768815777246319589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107767172716842072656852237 40412689768815777246319589)
          ·
            refine ⟨7577379331652958233684923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40412689768815777246319589 7577379331652958233684923)
            ·
              refine ⟨11366068997479437350527385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7577379331652958233684923 11366068997479437350527385)
              ·
                refine ⟨8524551748109578012895539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11366068997479437350527385 8524551748109578012895539)
                ·
                  refine ⟨12786827622164367019343309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8524551748109578012895539 12786827622164367019343309)
                  ·
                    refine ⟨4795060358311637632253741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12786827622164367019343309 4795060358311637632253741)
                    ·
                      refine ⟨1798147634366864112095153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795060358311637632253741 1798147634366864112095153)
                      ·
                        rfl

theorem cell23_3501880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_3501880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501880 prefixEnd_3501880 := by exact prefixLift 3501880
  have htrace : WordTrace (prefixWord ++ tailWord_3501880) baseStart_3501880 baseEnd_3501880 := by
    simpa [prefixWord, tailWord_3501880, baseEnd_3501880] using wordTrace_append hprefix tailTrace_3501880
  have hstable : (prefixWord ++ tailWord_3501880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501880).length < 2 ^ (prefixWord ++ tailWord_3501880).sum := by decide
  have hdescent : baseEnd_3501880 < baseStart_3501880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501897 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 3]
def baseStart_3501897 : Nat := 118140960795 + 3501897 * 2 ^ 59
def prefixEnd_3501897 : Nat := 4983230072969 + 3 ^ 40 * 3501897 * 2
def baseEnd_3501897 : Nat := 1798156363537990545582575

theorem tailTrace_3501897 : CollatzResearch.WordTrace tailWord_3501897 prefixEnd_3501897 1798156363537990545582575 := by
  unfold tailWord_3501897
  simp only [CollatzResearch.WordTrace]
  refine ⟨127724676594232720237415945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85149784396155146824943963 127724676594232720237415945)
  ·
    refine ⟨95793507445674540178061959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127724676594232720237415945 95793507445674540178061959)
    ·
      refine ⟨143690261168511810267092939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95793507445674540178061959 143690261168511810267092939)
      ·
        refine ⟨215535391752767715400639409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143690261168511810267092939 215535391752767715400639409)
        ·
          refine ⟨161651543814575786550479557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215535391752767715400639409 161651543814575786550479557)
          ·
            refine ⟨30309664465232959978214917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161651543814575786550479557 30309664465232959978214917)
            ·
              refine ⟨5683062087231179995915297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30309664465232959978214917 5683062087231179995915297)
              ·
                refine ⟨4262296565423384996936473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683062087231179995915297 4262296565423384996936473)
                ·
                  refine ⟨3196722424067538747702355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262296565423384996936473 3196722424067538747702355)
                  ·
                    refine ⟨4795083636101308121553533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196722424067538747702355 4795083636101308121553533)
                    ·
                      refine ⟨1798156363537990545582575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795083636101308121553533 1798156363537990545582575)
                      ·
                        rfl

theorem cell23_3501897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_3501897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501897 prefixEnd_3501897 := by exact prefixLift 3501897
  have htrace : WordTrace (prefixWord ++ tailWord_3501897) baseStart_3501897 baseEnd_3501897 := by
    simpa [prefixWord, tailWord_3501897, baseEnd_3501897] using wordTrace_append hprefix tailTrace_3501897
  have hstable : (prefixWord ++ tailWord_3501897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501897).length < 2 ^ (prefixWord ++ tailWord_3501897).sum := by decide
  have hdescent : baseEnd_3501897 < baseStart_3501897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501913 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_3501913 : Nat := 118140960795 + 3501913 * 2 ^ 59
def prefixEnd_3501913 : Nat := 4983230072969 + 3 ^ 40 * 3501913 * 2
def baseEnd_3501913 : Nat := 599388193076154160994167

theorem tailTrace_3501913 : CollatzResearch.WordTrace tailWord_3501913 prefixEnd_3501913 599388193076154160994167 := by
  unfold tailWord_3501913
  simp only [CollatzResearch.WordTrace]
  refine ⟨127725260162174754969998393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85150173441449836646665595 127725260162174754969998393)
  ·
    refine ⟨95793945121631066227498795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127725260162174754969998393 95793945121631066227498795)
    ·
      refine ⟨143690917682446599341248193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95793945121631066227498795 143690917682446599341248193)
      ·
        refine ⟨107768188261834949505936145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143690917682446599341248193 107768188261834949505936145)
        ·
          refine ⟨80826141196376212129452109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107768188261834949505936145 80826141196376212129452109)
          ·
            refine ⟨30309802948641079548544541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80826141196376212129452109 30309802948641079548544541)
            ·
              refine ⟨11366176105740404830704203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30309802948641079548544541 11366176105740404830704203)
              ·
                refine ⟨17049264158610607246056305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11366176105740404830704203 17049264158610607246056305)
                ·
                  refine ⟨12786948118957955434542229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17049264158610607246056305 12786948118957955434542229)
                  ·
                    refine ⟨599388193076154160994167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12786948118957955434542229 599388193076154160994167)
                    ·
                      rfl

theorem cell23_3501913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_3501913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501913 prefixEnd_3501913 := by exact prefixLift 3501913
  have htrace : WordTrace (prefixWord ++ tailWord_3501913) baseStart_3501913 baseEnd_3501913 := by
    simpa [prefixWord, tailWord_3501913, baseEnd_3501913] using wordTrace_append hprefix tailTrace_3501913
  have hstable : (prefixWord ++ tailWord_3501913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501913).length < 2 ^ (prefixWord ++ tailWord_3501913).sum := by decide
  have hdescent : baseEnd_3501913 < baseStart_3501913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501937 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 4, 2, 2]
def baseStart_3501937 : Nat := 118140960795 + 3501937 * 2 ^ 59
def prefixEnd_3501937 : Nat := 4983230072969 + 3 ^ 40 * 3501937 * 2
def baseEnd_3501937 : Nat := 1798176902764170389082391

theorem tailTrace_3501937 : CollatzResearch.WordTrace tailWord_3501937 prefixEnd_3501937 1798176902764170389082391 := by
  unfold tailWord_3501937
  simp only [CollatzResearch.WordTrace]
  refine ⟨127726135514087807068872065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85150757009391871379248043 127726135514087807068872065)
  ·
    refine ⟨95794601635565855301654049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127726135514087807068872065 95794601635565855301654049)
    ·
      refine ⟨71845951226674391476240537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95794601635565855301654049 71845951226674391476240537)
      ·
        refine ⟨53884463420005793607180403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71845951226674391476240537 53884463420005793607180403)
        ·
          refine ⟨80826695130008690410770605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53884463420005793607180403 80826695130008690410770605)
          ·
            refine ⟨30310010673753258904038977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80826695130008690410770605 30310010673753258904038977)
            ·
              refine ⟨22732508005314944178029233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30310010673753258904038977 22732508005314944178029233)
              ·
                refine ⟨17049381003986208133521925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22732508005314944178029233 17049381003986208133521925)
                ·
                  refine ⟨3196758938247414025035361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17049381003986208133521925 3196758938247414025035361)
                  ·
                    refine ⟨2397569203685560518776521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3196758938247414025035361 2397569203685560518776521)
                    ·
                      refine ⟨1798176902764170389082391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397569203685560518776521 1798176902764170389082391)
                      ·
                        rfl

theorem cell23_3501937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_3501937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501937 prefixEnd_3501937 := by exact prefixLift 3501937
  have htrace : WordTrace (prefixWord ++ tailWord_3501937) baseStart_3501937 baseEnd_3501937 := by
    simpa [prefixWord, tailWord_3501937, baseEnd_3501937] using wordTrace_append hprefix tailTrace_3501937
  have hstable : (prefixWord ++ tailWord_3501937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501937).length < 2 ^ (prefixWord ++ tailWord_3501937).sum := by decide
  have hdescent : baseEnd_3501937 < baseStart_3501937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3501973 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3501973 : Nat := 118140960795 + 3501973 * 2 ^ 59
def prefixEnd_3501973 : Nat := 4983230072969 + 3 ^ 40 * 3501973 * 2
def baseEnd_3501973 : Nat := 599398462689244082744075

theorem tailTrace_3501973 : CollatzResearch.WordTrace tailWord_3501973 prefixEnd_3501973 599398462689244082744075 := by
  unfold tailWord_3501973
  simp only [CollatzResearch.WordTrace]
  refine ⟨127727448541957385217182573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85151632361304923478121715 127727448541957385217182573)
  ·
    refine ⟨47897793203234019456443465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127727448541957385217182573 47897793203234019456443465)
    ·
      refine ⟨35923344902425514592332599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47897793203234019456443465 35923344902425514592332599)
      ·
        refine ⟨53885017353638271888498899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35923344902425514592332599 53885017353638271888498899)
        ·
          refine ⟨80827526030457407832748349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53885017353638271888498899 80827526030457407832748349)
          ·
            refine ⟨30310322261421527937280631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80827526030457407832748349 30310322261421527937280631)
            ·
              refine ⟨45465483392132291905920947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30310322261421527937280631 45465483392132291905920947)
              ·
                refine ⟨68198225088198437858881421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45465483392132291905920947 68198225088198437858881421)
                ·
                  refine ⟨25574334408074414197080533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68198225088198437858881421 25574334408074414197080533)
                  ·
                    refine ⟨599398462689244082744075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25574334408074414197080533 599398462689244082744075)
                    ·
                      rfl

theorem cell23_3501973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3501973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3501973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3501973 prefixEnd_3501973 := by exact prefixLift 3501973
  have htrace : WordTrace (prefixWord ++ tailWord_3501973) baseStart_3501973 baseEnd_3501973 := by
    simpa [prefixWord, tailWord_3501973, baseEnd_3501973] using wordTrace_append hprefix tailTrace_3501973
  have hstable : (prefixWord ++ tailWord_3501973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3501973).length < 2 ^ (prefixWord ++ tailWord_3501973).sum := by decide
  have hdescent : baseEnd_3501973 < baseStart_3501973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3501973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502033 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 10]
def baseStart_3502033 : Nat := 118140960795 + 3502033 * 2 ^ 59
def prefixEnd_3502033 : Nat := 4983230072969 + 3 ^ 40 * 3502033 * 2
def baseEnd_3502033 : Nat := 199802910767444668164661

theorem tailTrace_3502033 : CollatzResearch.WordTrace tailWord_3502033 prefixEnd_3502033 199802910767444668164661 := by
  unfold tailWord_3502033
  simp only [CollatzResearch.WordTrace]
  refine ⟨127729636921740015464366753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85153091281160010309577835 127729636921740015464366753)
  ·
    refine ⟨95797227691305011598275065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127729636921740015464366753 95797227691305011598275065)
    ·
      refine ⟨71847920768478758698706299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95797227691305011598275065 71847920768478758698706299)
      ·
        refine ⟨107771881152718138048059449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71847920768478758698706299 107771881152718138048059449)
        ·
          refine ⟨80828910864538603536044587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107771881152718138048059449 80828910864538603536044587)
          ·
            refine ⟨121243366296807905304066881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80828910864538603536044587 121243366296807905304066881)
            ·
              refine ⟨90932524722605928978050161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121243366296807905304066881 90932524722605928978050161)
              ·
                refine ⟨68199393541954446733537621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90932524722605928978050161 68199393541954446733537621)
                ·
                  refine ⟨199802910767444668164661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 68199393541954446733537621 199802910767444668164661)
                  ·
                    rfl

theorem cell23_3502033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_3502033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502033 prefixEnd_3502033 := by exact prefixLift 3502033
  have htrace : WordTrace (prefixWord ++ tailWord_3502033) baseStart_3502033 baseEnd_3502033 := by
    simpa [prefixWord, tailWord_3502033, baseEnd_3502033] using wordTrace_append hprefix tailTrace_3502033
  have hstable : (prefixWord ++ tailWord_3502033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502033).length < 2 ^ (prefixWord ++ tailWord_3502033).sum := by decide
  have hdescent : baseEnd_3502033 < baseStart_3502033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502047 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_3502047 : Nat := 118140960795 + 3502047 * 2 ^ 59
def prefixEnd_3502047 : Nat := 4983230072969 + 3 ^ 40 * 3502047 * 2
def baseEnd_3502047 : Nat := 1798233385636164958706885

theorem tailTrace_3502047 : CollatzResearch.WordTrace tailWord_3502047 prefixEnd_3502047 1798233385636164958706885 := by
  unfold tailWord_3502047
  simp only [CollatzResearch.WordTrace]
  refine ⟨127730147543689295855376395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85153431695792863903584263 127730147543689295855376395)
  ·
    refine ⟨191595221315533943783064593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127730147543689295855376395 191595221315533943783064593)
    ·
      refine ⟨143696415986650457837298445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191595221315533943783064593 143696415986650457837298445)
      ·
        refine ⟨53886155994993921688986917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143696415986650457837298445 53886155994993921688986917)
        ·
          refine ⟨10103654249061360316685047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53886155994993921688986917 10103654249061360316685047)
          ·
            refine ⟨15155481373592040475027571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10103654249061360316685047 15155481373592040475027571)
            ·
              refine ⟨22733222060388060712541357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15155481373592040475027571 22733222060388060712541357)
              ·
                refine ⟨8524958272645522767203009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22733222060388060712541357 8524958272645522767203009)
                ·
                  refine ⟨6393718704484142075402257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8524958272645522767203009 6393718704484142075402257)
                  ·
                    refine ⟨4795289028363106556551693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6393718704484142075402257 4795289028363106556551693)
                    ·
                      refine ⟨1798233385636164958706885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795289028363106556551693 1798233385636164958706885)
                      ·
                        rfl

theorem cell23_3502047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_3502047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502047 prefixEnd_3502047 := by exact prefixLift 3502047
  have htrace : WordTrace (prefixWord ++ tailWord_3502047) baseStart_3502047 baseEnd_3502047 := by
    simpa [prefixWord, tailWord_3502047, baseEnd_3502047] using wordTrace_append hprefix tailTrace_3502047
  have hstable : (prefixWord ++ tailWord_3502047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502047).length < 2 ^ (prefixWord ++ tailWord_3502047).sum := by decide
  have hdescent : baseEnd_3502047 < baseStart_3502047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502094 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3502094 : Nat := 118140960795 + 3502094 * 2 ^ 59
def prefixEnd_3502094 : Nat := 4983230072969 + 3 ^ 40 * 3502094 * 2
def baseEnd_3502094 : Nat := 1798257519226926274819169

theorem tailTrace_3502094 : CollatzResearch.WordTrace tailWord_3502094 prefixEnd_3502094 1798257519226926274819169 := by
  unfold tailWord_3502094
  simp only [CollatzResearch.WordTrace]
  refine ⟨15966482721814877860292167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85154574516346015254891557 15966482721814877860292167)
  ·
    refine ⟨23949724082722316790438251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15966482721814877860292167 23949724082722316790438251)
    ·
      refine ⟨35924586124083475185657377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23949724082722316790438251 35924586124083475185657377)
      ·
        refine ⟨26943439593062606389243033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35924586124083475185657377 26943439593062606389243033)
        ·
          refine ⟨20207579694796954791932275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26943439593062606389243033 20207579694796954791932275)
          ·
            refine ⟨30311369542195432187898413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20207579694796954791932275 30311369542195432187898413)
            ·
              refine ⟨11366763578323287070461905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30311369542195432187898413 11366763578323287070461905)
              ·
                refine ⟨8525072683742465302846429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11366763578323287070461905 8525072683742465302846429)
                ·
                  refine ⟨3196902256403424488567411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8525072683742465302846429 3196902256403424488567411)
                  ·
                    refine ⟨4795353384605136732851117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196902256403424488567411 4795353384605136732851117)
                    ·
                      refine ⟨1798257519226926274819169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795353384605136732851117 1798257519226926274819169)
                      ·
                        rfl

theorem cell23_3502094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3502094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502094 prefixEnd_3502094 := by exact prefixLift 3502094
  have htrace : WordTrace (prefixWord ++ tailWord_3502094) baseStart_3502094 baseEnd_3502094 := by
    simpa [prefixWord, tailWord_3502094, baseEnd_3502094] using wordTrace_append hprefix tailTrace_3502094
  have hstable : (prefixWord ++ tailWord_3502094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502094).length < 2 ^ (prefixWord ++ tailWord_3502094).sum := by decide
  have hdescent : baseEnd_3502094 < baseStart_3502094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502111 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 1, 1, 3]
def baseStart_3502111 : Nat := 118140960795 + 3502111 * 2 ^ 59
def prefixEnd_3502111 : Nat := 4983230072969 + 3 ^ 40 * 3502111 * 2
def baseEnd_3502111 : Nat := 1798266248398052708306591

theorem tailTrace_3502111 : CollatzResearch.WordTrace tailWord_3502111 prefixEnd_3502111 1798266248398052708306591 := by
  unfold tailWord_3502111
  simp only [CollatzResearch.WordTrace]
  refine ⟨127732481815457434785706187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85154987876971623190470791 127732481815457434785706187)
  ·
    refine ⟨191598722723186152178559281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127732481815457434785706187 191598722723186152178559281)
    ·
      refine ⟨143699042042389614133919461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191598722723186152178559281 143699042042389614133919461)
      ·
        refine ⟨26943570382948052650109899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143699042042389614133919461 26943570382948052650109899)
        ·
          refine ⟨40415355574422078975164849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26943570382948052650109899 40415355574422078975164849)
          ·
            refine ⟨30311516680816559231373637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40415355574422078975164849 30311516680816559231373637)
            ·
              refine ⟨5683409377653104855882557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30311516680816559231373637 5683409377653104855882557)
              ·
                refine ⟨2131278516619914320955959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5683409377653104855882557 2131278516619914320955959)
                ·
                  refine ⟨3196917774929871481433939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131278516619914320955959 3196917774929871481433939)
                  ·
                    refine ⟨4795376662394807222150909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196917774929871481433939 4795376662394807222150909)
                    ·
                      refine ⟨1798266248398052708306591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795376662394807222150909 1798266248398052708306591)
                      ·
                        rfl

theorem cell23_3502111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_3502111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502111 prefixEnd_3502111 := by exact prefixLift 3502111
  have htrace : WordTrace (prefixWord ++ tailWord_3502111) baseStart_3502111 baseEnd_3502111 := by
    simpa [prefixWord, tailWord_3502111, baseEnd_3502111] using wordTrace_append hprefix tailTrace_3502111
  have hstable : (prefixWord ++ tailWord_3502111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502111).length < 2 ^ (prefixWord ++ tailWord_3502111).sum := by decide
  have hdescent : baseEnd_3502111 < baseStart_3502111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502127 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 2, 4]
def baseStart_3502127 : Nat := 118140960795 + 3502127 * 2 ^ 59
def prefixEnd_3502127 : Nat := 4983230072969 + 3 ^ 40 * 3502127 * 2
def baseEnd_3502127 : Nat := 599424821362841548568839

theorem tailTrace_3502127 : CollatzResearch.WordTrace tailWord_3502127 prefixEnd_3502127 599424821362841548568839 := by
  unfold tailWord_3502127
  simp only [CollatzResearch.WordTrace]
  refine ⟨127733065383399469518288635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85155376922266313012192423 127733065383399469518288635)
  ·
    refine ⟨191599598075099204277432953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127733065383399469518288635 191599598075099204277432953)
    ·
      refine ⟨143699698556324403208074715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191599598075099204277432953 143699698556324403208074715)
      ·
        refine ⟨215549547834486604812112073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143699698556324403208074715 215549547834486604812112073)
        ·
          refine ⟨161662160875864953609084055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215549547834486604812112073 161662160875864953609084055)
          ·
            refine ⟨242493241313797430413626083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161662160875864953609084055 242493241313797430413626083)
            ·
              refine ⟨363739861970696145620439125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242493241313797430413626083 363739861970696145620439125)
              ·
                refine ⟨4262576507469095456489521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 363739861970696145620439125 4262576507469095456489521)
                ·
                  refine ⟨3196932380601821592367141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262576507469095456489521 3196932380601821592367141)
                  ·
                    refine ⟨599424821362841548568839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3196932380601821592367141 599424821362841548568839)
                    ·
                      rfl

theorem cell23_3502127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_3502127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502127 prefixEnd_3502127 := by exact prefixLift 3502127
  have htrace : WordTrace (prefixWord ++ tailWord_3502127) baseStart_3502127 baseEnd_3502127 := by
    simpa [prefixWord, tailWord_3502127, baseEnd_3502127] using wordTrace_append hprefix tailTrace_3502127
  have hstable : (prefixWord ++ tailWord_3502127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502127).length < 2 ^ (prefixWord ++ tailWord_3502127).sum := by decide
  have hdescent : baseEnd_3502127 < baseStart_3502127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502140 : List Nat := [2, 2, 2, 2, 2, 1, 2, 10]
def baseStart_3502140 : Nat := 118140960795 + 3502140 * 2 ^ 59
def prefixEnd_3502140 : Nat := 4983230072969 + 3 ^ 40 * 3502140 * 2
def baseEnd_3502140 : Nat := 66603005160630855364591

theorem tailTrace_3502140 : CollatzResearch.WordTrace tailWord_3502140 prefixEnd_3502140 66603005160630855364591 := by
  unfold tailWord_3502140
  simp only [CollatzResearch.WordTrace]
  refine ⟨63866769766176186369255937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85155693021568248492341249 63866769766176186369255937)
  ·
    refine ⟨47900077324632139776941953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63866769766176186369255937 47900077324632139776941953)
    ·
      refine ⟨35925057993474104832706465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47900077324632139776941953 35925057993474104832706465)
      ·
        refine ⟨26943793495105578624529849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35925057993474104832706465 26943793495105578624529849)
        ·
          refine ⟨20207845121329183968397387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26943793495105578624529849 20207845121329183968397387)
          ·
            refine ⟨30311767681993775952596081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20207845121329183968397387 30311767681993775952596081)
            ·
              refine ⟨22733825761495331964447061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30311767681993775952596081 22733825761495331964447061)
              ·
                refine ⟨66603005160630855364591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22733825761495331964447061 66603005160630855364591)
                ·
                  rfl

theorem cell23_3502140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 10].length) (baseStart_3502140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502140 prefixEnd_3502140 := by exact prefixLift 3502140
  have htrace : WordTrace (prefixWord ++ tailWord_3502140) baseStart_3502140 baseEnd_3502140 := by
    simpa [prefixWord, tailWord_3502140, baseEnd_3502140] using wordTrace_append hprefix tailTrace_3502140
  have hstable : (prefixWord ++ tailWord_3502140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502140).length < 2 ^ (prefixWord ++ tailWord_3502140).sum := by decide
  have hdescent : baseEnd_3502140 < baseStart_3502140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502157 : List Nat := [1, 6, 1, 1, 1, 1, 3, 9]
def baseStart_3502157 : Nat := 118140960795 + 3502157 * 2 ^ 59
def prefixEnd_3502157 : Nat := 4983230072969 + 3 ^ 40 * 3502157 * 2
def baseEnd_3502157 : Nat := 66603328463265167715977

theorem tailTrace_3502157 : CollatzResearch.WordTrace tailWord_3502157 prefixEnd_3502157 66603328463265167715977 := by
  unfold tailWord_3502157
  simp only [CollatzResearch.WordTrace]
  refine ⟨127734159573290784641880725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85156106382193856427920483 127734159573290784641880725)
  ·
    refine ⟨5987538729998005530088159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127734159573290784641880725 5987538729998005530088159)
    ·
      refine ⟨8981308094997008295132239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987538729998005530088159 8981308094997008295132239)
      ·
        refine ⟨13471962142495512442698359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8981308094997008295132239 13471962142495512442698359)
        ·
          refine ⟨20207943213743268664047539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13471962142495512442698359 20207943213743268664047539)
          ·
            refine ⟨30311914820614902996071309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20207943213743268664047539 30311914820614902996071309)
            ·
              refine ⟨11366968057730588623526741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30311914820614902996071309 11366968057730588623526741)
              ·
                refine ⟨66603328463265167715977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11366968057730588623526741 66603328463265167715977)
                ·
                  rfl

theorem cell23_3502157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 9].length) (baseStart_3502157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502157 prefixEnd_3502157 := by exact prefixLift 3502157
  have htrace : WordTrace (prefixWord ++ tailWord_3502157) baseStart_3502157 baseEnd_3502157 := by
    simpa [prefixWord, tailWord_3502157, baseEnd_3502157] using wordTrace_append hprefix tailTrace_3502157
  have hstable : (prefixWord ++ tailWord_3502157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502157).length < 2 ^ (prefixWord ++ tailWord_3502157).sum := by decide
  have hdescent : baseEnd_3502157 < baseStart_3502157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502167 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_3502167 : Nat := 118140960795 + 3502167 * 2 ^ 59
def prefixEnd_3502167 : Nat := 4983230072969 + 3 ^ 40 * 3502167 * 2
def baseEnd_3502167 : Nat := 1798295003314704489206333

theorem tailTrace_3502167 : CollatzResearch.WordTrace tailWord_3502167 prefixEnd_3502167 1798295003314704489206333 := by
  unfold tailWord_3502167
  simp only [CollatzResearch.WordTrace]
  refine ⟨127734524303254556349744755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85156349535503037566496503 127734524303254556349744755)
  ·
    refine ⟨191601786454881834524617133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127734524303254556349744755 191601786454881834524617133)
    ·
      refine ⟨71850669920580687946731425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191601786454881834524617133 71850669920580687946731425)
      ·
        refine ⟨53888002440435515960048569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71850669920580687946731425 53888002440435515960048569)
        ·
          refine ⟨40416001830326636970036427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53888002440435515960048569 40416001830326636970036427)
          ·
            refine ⟨60624002745489955455054641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40416001830326636970036427 60624002745489955455054641)
            ·
              refine ⟨45468002059117466591290981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60624002745489955455054641 45468002059117466591290981)
              ·
                refine ⟨8525250386084524985867059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45468002059117466591290981 8525250386084524985867059)
                ·
                  refine ⟨12787875579126787478800589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8525250386084524985867059 12787875579126787478800589)
                  ·
                    refine ⟨4795453342172545304550221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12787875579126787478800589 4795453342172545304550221)
                    ·
                      refine ⟨1798295003314704489206333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795453342172545304550221 1798295003314704489206333)
                      ·
                        rfl

theorem cell23_3502167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_3502167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502167 prefixEnd_3502167 := by exact prefixLift 3502167
  have htrace : WordTrace (prefixWord ++ tailWord_3502167) baseStart_3502167 baseEnd_3502167 := by
    simpa [prefixWord, tailWord_3502167, baseEnd_3502167] using wordTrace_append hprefix tailTrace_3502167
  have hstable : (prefixWord ++ tailWord_3502167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502167).length < 2 ^ (prefixWord ++ tailWord_3502167).sum := by decide
  have hdescent : baseEnd_3502167 < baseStart_3502167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502168 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 1, 2, 2]
def baseStart_3502168 : Nat := 118140960795 + 3502168 * 2 ^ 59
def prefixEnd_3502168 : Nat := 4983230072969 + 3 ^ 40 * 3502168 * 2
def baseEnd_3502168 : Nat := 1798295516795358985293829

theorem tailTrace_3502168 : CollatzResearch.WordTrace tailWord_3502168 prefixEnd_3502168 1798295516795358985293829 := by
  unfold tailWord_3502168
  simp only [CollatzResearch.WordTrace]
  refine ⟨63867280388125466760265579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85156373850833955680354105 63867280388125466760265579)
  ·
    refine ⟨95800920582188200140398369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63867280388125466760265579 95800920582188200140398369)
    ·
      refine ⟨71850690436641150105298777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95800920582188200140398369 71850690436641150105298777)
      ·
        refine ⟨53888017827480862578974083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71850690436641150105298777 53888017827480862578974083)
        ·
          refine ⟨80832026741221293868461125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53888017827480862578974083 80832026741221293868461125)
          ·
            refine ⟨15156005013978992600336461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80832026741221293868461125 15156005013978992600336461)
            ·
              refine ⟨5683501880242122225126173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15156005013978992600336461 5683501880242122225126173)
              ·
                refine ⟨2131313205090795834422315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5683501880242122225126173 2131313205090795834422315)
                ·
                  refine ⟨3196969807636193751633473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131313205090795834422315 3196969807636193751633473)
                  ·
                    refine ⟨2397727355727145313725105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3196969807636193751633473 2397727355727145313725105)
                    ·
                      refine ⟨1798295516795358985293829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397727355727145313725105 1798295516795358985293829)
                      ·
                        rfl

theorem cell23_3502168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_3502168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502168 prefixEnd_3502168 := by exact prefixLift 3502168
  have htrace : WordTrace (prefixWord ++ tailWord_3502168) baseStart_3502168 baseEnd_3502168 := by
    simpa [prefixWord, tailWord_3502168, baseEnd_3502168] using wordTrace_append hprefix tailTrace_3502168
  have hstable : (prefixWord ++ tailWord_3502168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502168).length < 2 ^ (prefixWord ++ tailWord_3502168).sum := by decide
  have hdescent : baseEnd_3502168 < baseStart_3502168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502200 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_3502200 : Nat := 118140960795 + 3502200 * 2 ^ 59
def prefixEnd_3502200 : Nat := 4983230072969 + 3 ^ 40 * 3502200 * 2
def baseEnd_3502200 : Nat := 599437316058767620031227

theorem tailTrace_3502200 : CollatzResearch.WordTrace tailWord_3502200 prefixEnd_3502200 599437316058767620031227 := by
  unfold tailWord_3502200
  simp only [CollatzResearch.WordTrace]
  refine ⟨63867863956067501492848027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85157151941423335323797369 63867863956067501492848027)
  ·
    refine ⟨95801795934101252239272041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63867863956067501492848027 95801795934101252239272041)
    ·
      refine ⟨71851346950575939179454031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95801795934101252239272041 71851346950575939179454031)
      ·
        refine ⟨107777020425863908769181047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71851346950575939179454031 107777020425863908769181047)
        ·
          refine ⟨161665530638795863153771571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107777020425863908769181047 161665530638795863153771571)
          ·
            refine ⟨242498295958193794730657357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161665530638795863153771571 242498295958193794730657357)
            ·
              refine ⟨90936860984322673023996509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242498295958193794730657357 90936860984322673023996509)
              ·
                refine ⟨34101322869121002383998691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90936860984322673023996509 34101322869121002383998691)
                ·
                  refine ⟨51151984303681503575998037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34101322869121002383998691 51151984303681503575998037)
                  ·
                    refine ⟨599437316058767620031227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51151984303681503575998037 599437316058767620031227)
                    ·
                      rfl

theorem cell23_3502200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_3502200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502200 prefixEnd_3502200 := by exact prefixLift 3502200
  have htrace : WordTrace (prefixWord ++ tailWord_3502200) baseStart_3502200 baseEnd_3502200 := by
    simpa [prefixWord, tailWord_3502200, baseEnd_3502200] using wordTrace_append hprefix tailTrace_3502200
  have hstable : (prefixWord ++ tailWord_3502200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502200).length < 2 ^ (prefixWord ++ tailWord_3502200).sum := by decide
  have hdescent : baseEnd_3502200 < baseStart_3502200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502201 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3502201 : Nat := 118140960795 + 3502201 * 2 ^ 59
def prefixEnd_3502201 : Nat := 4983230072969 + 3 ^ 40 * 3502201 * 2
def baseEnd_3502201 : Nat := 1798312461656957356181177

theorem tailTrace_3502201 : CollatzResearch.WordTrace tailWord_3502201 prefixEnd_3502201 1798312461656957356181177 := by
  unfold tailWord_3502201
  simp only [CollatzResearch.WordTrace]
  refine ⟨127735764385131380156482457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85157176256754253437654971 127735764385131380156482457)
  ·
    refine ⟨95801823288848535117361843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127735764385131380156482457 95801823288848535117361843)
    ·
      refine ⟨143702734933272802676042765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95801823288848535117361843 143702734933272802676042765)
      ·
        refine ⟨53888525599977301003516037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143702734933272802676042765 53888525599977301003516037)
        ·
          refine ⟨10104098549995743938159257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53888525599977301003516037 10104098549995743938159257)
          ·
            refine ⟨7578073912496807953619443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10104098549995743938159257 7578073912496807953619443)
            ·
              refine ⟨11367110868745211930429165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7578073912496807953619443 11367110868745211930429165)
              ·
                refine ⟨4262666575779454473910937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11367110868745211930429165 4262666575779454473910937)
                ·
                  refine ⟨3196999931834590855433203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262666575779454473910937 3196999931834590855433203)
                  ·
                    refine ⟨4795499897751886283149805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3196999931834590855433203 4795499897751886283149805)
                    ·
                      refine ⟨1798312461656957356181177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795499897751886283149805 1798312461656957356181177)
                      ·
                        rfl

theorem cell23_3502201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3502201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502201 prefixEnd_3502201 := by exact prefixLift 3502201
  have htrace : WordTrace (prefixWord ++ tailWord_3502201) baseStart_3502201 baseEnd_3502201 := by
    simpa [prefixWord, tailWord_3502201, baseEnd_3502201] using wordTrace_append hprefix tailTrace_3502201
  have hstable : (prefixWord ++ tailWord_3502201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502201).length < 2 ^ (prefixWord ++ tailWord_3502201).sum := by decide
  have hdescent : baseEnd_3502201 < baseStart_3502201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502211 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 1, 3, 2]
def baseStart_3502211 : Nat := 118140960795 + 3502211 * 2 ^ 59
def prefixEnd_3502211 : Nat := 4983230072969 + 3 ^ 40 * 3502211 * 2
def baseEnd_3502211 : Nat := 1798317596463502317056131

theorem tailTrace_3502211 : CollatzResearch.WordTrace tailWord_3502211 prefixEnd_3502211 1798317596463502317056131 := by
  unfold tailWord_3502211
  simp only [CollatzResearch.WordTrace]
  refine ⟨127736129115095151864346487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85157419410063434576230991 127736129115095151864346487)
  ·
    refine ⟨191604193672642727796519731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127736129115095151864346487 191604193672642727796519731)
    ·
      refine ⟨287406290508964091694779597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191604193672642727796519731 287406290508964091694779597)
      ·
        refine ⟨107777358940861534385542349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287406290508964091694779597 107777358940861534385542349)
        ·
          refine ⟨40416509602823075394578381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107777358940861534385542349 40416509602823075394578381)
          ·
            refine ⟨15156191101058653272966893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40416509602823075394578381 15156191101058653272966893)
            ·
              refine ⟨5683571662896994977362585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15156191101058653272966893 5683571662896994977362585)
              ·
                refine ⟨4262678747172746233021939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683571662896994977362585 4262678747172746233021939)
                ·
                  refine ⟨6394018120759119349532909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262678747172746233021939 6394018120759119349532909)
                  ·
                    refine ⟨2397756795284669756074841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6394018120759119349532909 2397756795284669756074841)
                    ·
                      refine ⟨1798317596463502317056131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397756795284669756074841 1798317596463502317056131)
                      ·
                        rfl

theorem cell23_3502211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_3502211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502211 prefixEnd_3502211 := by exact prefixLift 3502211
  have htrace : WordTrace (prefixWord ++ tailWord_3502211) baseStart_3502211 baseEnd_3502211 := by
    simpa [prefixWord, tailWord_3502211, baseEnd_3502211] using wordTrace_append hprefix tailTrace_3502211
  have hstable : (prefixWord ++ tailWord_3502211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502211).length < 2 ^ (prefixWord ++ tailWord_3502211).sum := by decide
  have hdescent : baseEnd_3502211 < baseStart_3502211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502224 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 1, 4, 2]
def baseStart_3502224 : Nat := 118140960795 + 3502224 * 2 ^ 59
def prefixEnd_3502224 : Nat := 4983230072969 + 3 ^ 40 * 3502224 * 2
def baseEnd_3502224 : Nat := 1798324271712010766193571

theorem tailTrace_3502224 : CollatzResearch.WordTrace tailWord_3502224 prefixEnd_3502224 1798324271712010766193571 := by
  unfold tailWord_3502224
  simp only [CollatzResearch.WordTrace]
  refine ⟨63868301632024027542284863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85157735509365370056379817 63868301632024027542284863)
  ·
    refine ⟨95802452448036041313427295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63868301632024027542284863 95802452448036041313427295)
    ·
      refine ⟨143703678672054061970140943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95802452448036041313427295 143703678672054061970140943)
      ·
        refine ⟨215555518008081092955211415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143703678672054061970140943 215555518008081092955211415)
        ·
          refine ⟨323333277012121639432817123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215555518008081092955211415 323333277012121639432817123)
          ·
            refine ⟨484999915518182459149225685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323333277012121639432817123 484999915518182459149225685)
            ·
              refine ⟨11367185519957401386309977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 484999915518182459149225685 11367185519957401386309977)
              ·
                refine ⟨8525389139968051039732483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11367185519957401386309977 8525389139968051039732483)
                ·
                  refine ⟨12788083709952076559598725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8525389139968051039732483 12788083709952076559598725)
                  ·
                    refine ⟨2397765695616014354924761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12788083709952076559598725 2397765695616014354924761)
                    ·
                      refine ⟨1798324271712010766193571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2397765695616014354924761 1798324271712010766193571)
                      ·
                        rfl

theorem cell23_3502224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 1, 4, 2].length) (baseStart_3502224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502224 prefixEnd_3502224 := by exact prefixLift 3502224
  have htrace : WordTrace (prefixWord ++ tailWord_3502224) baseStart_3502224 baseEnd_3502224 := by
    simpa [prefixWord, tailWord_3502224, baseEnd_3502224] using wordTrace_append hprefix tailTrace_3502224
  have hstable : (prefixWord ++ tailWord_3502224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502224).length < 2 ^ (prefixWord ++ tailWord_3502224).sum := by decide
  have hdescent : baseEnd_3502224 < baseStart_3502224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502337 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 10]
def baseStart_3502337 : Nat := 118140960795 + 3502337 * 2 ^ 59
def prefixEnd_3502337 : Nat := 4983230072969 + 3 ^ 40 * 3502337 * 2
def baseEnd_3502337 : Nat := 199820255002885424897839

theorem tailTrace_3502337 : CollatzResearch.WordTrace tailWord_3502337 prefixEnd_3502337 199820255002885424897839 := by
  unfold tailWord_3502337
  simp only [CollatzResearch.WordTrace]
  refine ⟨127740724712638675383433265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85160483141759116922288843 127740724712638675383433265)
  ·
    refine ⟨95805543534479006537574949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127740724712638675383433265 95805543534479006537574949)
    ·
      refine ⟨17963539412714813725795303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95805543534479006537574949 17963539412714813725795303)
      ·
        refine ⟨26945309119072220588692955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17963539412714813725795303 26945309119072220588692955)
        ·
          refine ⟨40417963678608330883039433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26945309119072220588692955 40417963678608330883039433)
          ·
            refine ⟨30313472758956248162279575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40417963678608330883039433 30313472758956248162279575)
            ·
              refine ⟨45470209138434372243419363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30313472758956248162279575 45470209138434372243419363)
              ·
                refine ⟨68205313707651558365129045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45470209138434372243419363 68205313707651558365129045)
                ·
                  refine ⟨199820255002885424897839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 68205313707651558365129045 199820255002885424897839)
                  ·
                    rfl

theorem cell23_3502337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_3502337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502337 prefixEnd_3502337 := by exact prefixLift 3502337
  have htrace : WordTrace (prefixWord ++ tailWord_3502337) baseStart_3502337 baseEnd_3502337 := by
    simpa [prefixWord, tailWord_3502337, baseEnd_3502337] using wordTrace_append hprefix tailTrace_3502337
  have hstable : (prefixWord ++ tailWord_3502337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502337).length < 2 ^ (prefixWord ++ tailWord_3502337).sum := by decide
  have hdescent : baseEnd_3502337 < baseStart_3502337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502341 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_3502341 : Nat := 118140960795 + 3502341 * 2 ^ 59
def prefixEnd_3502341 : Nat := 4983230072969 + 3 ^ 40 * 3502341 * 2
def baseEnd_3502341 : Nat := 599461449649528936143511

theorem tailTrace_3502341 : CollatzResearch.WordTrace tailWord_3502341 prefixEnd_3502341 599461449649528936143511 := by
  unfold tailWord_3502341
  simp only [CollatzResearch.WordTrace]
  refine ⟨127740870604624184066578877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85160580403082789377719251 127740870604624184066578877)
  ·
    refine ⟨47902826476734069024967079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127740870604624184066578877 47902826476734069024967079)
    ·
      refine ⟨71854239715101103537450619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47902826476734069024967079 71854239715101103537450619)
      ·
        refine ⟨107781359572651655306175929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71854239715101103537450619 107781359572651655306175929)
        ·
          refine ⟨80836019679488741479631947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107781359572651655306175929 80836019679488741479631947)
          ·
            refine ⟨121254029519233112219447921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80836019679488741479631947 121254029519233112219447921)
            ·
              refine ⟨90940522139424834164585941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121254029519233112219447921 90940522139424834164585941)
              ·
                refine ⟨2131418487642769550732483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90940522139424834164585941 2131418487642769550732483)
                ·
                  refine ⟨3197127731464154326098725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131418487642769550732483 3197127731464154326098725)
                  ·
                    refine ⟨599461449649528936143511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197127731464154326098725 599461449649528936143511)
                    ·
                      rfl

theorem cell23_3502341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_3502341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502341 prefixEnd_3502341 := by exact prefixLift 3502341
  have htrace : WordTrace (prefixWord ++ tailWord_3502341) baseStart_3502341 baseEnd_3502341 := by
    simpa [prefixWord, tailWord_3502341, baseEnd_3502341] using wordTrace_append hprefix tailTrace_3502341
  have hstable : (prefixWord ++ tailWord_3502341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502341).length < 2 ^ (prefixWord ++ tailWord_3502341).sum := by decide
  have hdescent : baseEnd_3502341 < baseStart_3502341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502357 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_3502357 : Nat := 118140960795 + 3502357 * 2 ^ 59
def prefixEnd_3502357 : Nat := 4983230072969 + 3 ^ 40 * 3502357 * 2
def baseEnd_3502357 : Nat := 1798392564639058745830459

theorem tailTrace_3502357 : CollatzResearch.WordTrace tailWord_3502357 prefixEnd_3502357 1798392564639058745830459 := by
  unfold tailWord_3502357
  simp only [CollatzResearch.WordTrace]
  refine ⟨127741454172566218799161325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85160969448377479199440883 127741454172566218799161325)
  ·
    refine ⟨47903045314712332049685497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127741454172566218799161325 47903045314712332049685497)
    ·
      refine ⟨35927283986034249037264123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47903045314712332049685497 35927283986034249037264123)
      ·
        refine ⟨53890925979051373555896185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35927283986034249037264123 53890925979051373555896185)
        ·
          refine ⟨40418194484288530166922139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53890925979051373555896185 40418194484288530166922139)
          ·
            refine ⟨60627291726432795250383209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40418194484288530166922139 60627291726432795250383209)
            ·
              refine ⟨45470468794824596437787407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60627291726432795250383209 45470468794824596437787407)
              ·
                refine ⟨68205703192236894656681111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45470468794824596437787407 68205703192236894656681111)
                ·
                  refine ⟨102308554788355341985021667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68205703192236894656681111 102308554788355341985021667)
                  ·
                    refine ⟨153462832182533012977532501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102308554788355341985021667 153462832182533012977532501)
                    ·
                      refine ⟨1798392564639058745830459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 153462832182533012977532501 1798392564639058745830459)
                      ·
                        rfl

theorem cell23_3502357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_3502357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502357 prefixEnd_3502357 := by exact prefixLift 3502357
  have htrace : WordTrace (prefixWord ++ tailWord_3502357) baseStart_3502357 baseEnd_3502357 := by
    simpa [prefixWord, tailWord_3502357, baseEnd_3502357] using wordTrace_append hprefix tailTrace_3502357
  have hstable : (prefixWord ++ tailWord_3502357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502357).length < 2 ^ (prefixWord ++ tailWord_3502357).sum := by decide
  have hdescent : baseEnd_3502357 < baseStart_3502357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502384 : List Nat := [2, 1, 1, 1, 2, 2, 2, 6, 1, 5]
def baseStart_3502384 : Nat := 118140960795 + 3502384 * 2 ^ 59
def prefixEnd_3502384 : Nat := 4983230072969 + 3 ^ 40 * 3502384 * 2
def baseEnd_3502384 : Nat := 599468809538910046730945

theorem tailTrace_3502384 : CollatzResearch.WordTrace tailWord_3502384 prefixEnd_3502384 599468809538910046730945 := by
  unfold tailWord_3502384
  simp only [CollatzResearch.WordTrace]
  refine ⟨63871219471734201205197103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85161625962312268273596137 63871219471734201205197103)
  ·
    refine ⟨95806829207601301807795655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63871219471734201205197103 95806829207601301807795655)
    ·
      refine ⟨143710243811401952711693483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95806829207601301807795655 143710243811401952711693483)
      ·
        refine ⟨215565365717102929067540225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143710243811401952711693483 215565365717102929067540225)
        ·
          refine ⟨161674024287827196800655169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215565365717102929067540225 161674024287827196800655169)
          ·
            refine ⟨121255518215870397600491377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161674024287827196800655169 121255518215870397600491377)
            ·
              refine ⟨90941638661902798200368533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121255518215870397600491377 90941638661902798200368533)
              ·
                refine ⟨4262889312276693665642275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90941638661902798200368533 4262889312276693665642275)
                ·
                  refine ⟨6394333968415040498463413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262889312276693665642275 6394333968415040498463413)
                  ·
                    refine ⟨599468809538910046730945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6394333968415040498463413 599468809538910046730945)
                    ·
                      rfl

theorem cell23_3502384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_3502384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502384 prefixEnd_3502384 := by exact prefixLift 3502384
  have htrace : WordTrace (prefixWord ++ tailWord_3502384) baseStart_3502384 baseEnd_3502384 := by
    simpa [prefixWord, tailWord_3502384, baseEnd_3502384] using wordTrace_append hprefix tailTrace_3502384
  have hstable : (prefixWord ++ tailWord_3502384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502384).length < 2 ^ (prefixWord ++ tailWord_3502384).sum := by decide
  have hdescent : baseEnd_3502384 < baseStart_3502384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502431 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 2, 4]
def baseStart_3502431 : Nat := 118140960795 + 3502431 * 2 ^ 59
def prefixEnd_3502431 : Nat := 4983230072969 + 3 ^ 40 * 3502431 * 2
def baseEnd_3502431 : Nat := 599476854069163818768373

theorem tailTrace_3502431 : CollatzResearch.WordTrace tailWord_3502431 prefixEnd_3502431 599476854069163818768373 := by
  unfold tailWord_3502431
  simp only [CollatzResearch.WordTrace]
  refine ⟨127744153174298129437355147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85162768782865419624903431 127744153174298129437355147)
  ·
    refine ⟨191616229761447194156032721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127744153174298129437355147 191616229761447194156032721)
    ·
      refine ⟨143712172321085395617024541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191616229761447194156032721 143712172321085395617024541)
      ·
        refine ⟨53892064620407023356384203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143712172321085395617024541 53892064620407023356384203)
        ·
          refine ⟨80838096930610535034576305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53892064620407023356384203 80838096930610535034576305)
          ·
            refine ⟨60628572697957901275932229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80838096930610535034576305 60628572697957901275932229)
            ·
              refine ⟨11367857380867106489237293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60628572697957901275932229 11367857380867106489237293)
              ·
                refine ⟨4262946517825164933463985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11367857380867106489237293 4262946517825164933463985)
                ·
                  refine ⟨3197209888368873700097989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262946517825164933463985 3197209888368873700097989)
                  ·
                    refine ⟨599476854069163818768373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197209888368873700097989 599476854069163818768373)
                    ·
                      rfl

theorem cell23_3502431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_3502431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502431 prefixEnd_3502431 := by exact prefixLift 3502431
  have htrace : WordTrace (prefixWord ++ tailWord_3502431) baseStart_3502431 baseEnd_3502431 := by
    simpa [prefixWord, tailWord_3502431, baseEnd_3502431] using wordTrace_append hprefix tailTrace_3502431
  have hstable : (prefixWord ++ tailWord_3502431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502431).length < 2 ^ (prefixWord ++ tailWord_3502431).sum := by decide
  have hdescent : baseEnd_3502431 < baseStart_3502431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502441 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 3]
def baseStart_3502441 : Nat := 118140960795 + 3502441 * 2 ^ 59
def prefixEnd_3502441 : Nat := 4983230072969 + 3 ^ 40 * 3502441 * 2
def baseEnd_3502441 : Nat := 1798435697014036417180073

theorem tailTrace_3502441 : CollatzResearch.WordTrace tailWord_3502441 prefixEnd_3502441 1798435697014036417180073 := by
  unfold tailWord_3502441
  simp only [CollatzResearch.WordTrace]
  refine ⟨127744517904261901145219177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85163011936174600763479451 127744517904261901145219177)
  ·
    refine ⟨95808388428196425858914383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127744517904261901145219177 95808388428196425858914383)
    ·
      refine ⟨143712582642294638788371575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95808388428196425858914383 143712582642294638788371575)
      ·
        refine ⟨215568873963441958182557363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143712582642294638788371575 215568873963441958182557363)
        ·
          refine ⟨323353310945162937273836045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215568873963441958182557363 323353310945162937273836045)
          ·
            refine ⟨121257491604436101477688517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323353310945162937273836045 121257491604436101477688517)
            ·
              refine ⟨22735779675831769027066597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121257491604436101477688517 22735779675831769027066597)
              ·
                refine ⟨4262958689218456692574987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22735779675831769027066597 4262958689218456692574987)
                ·
                  refine ⟨6394438033827685038862481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4262958689218456692574987 6394438033827685038862481)
                  ·
                    refine ⟨4795828525370763779146861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6394438033827685038862481 4795828525370763779146861)
                    ·
                      refine ⟨1798435697014036417180073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795828525370763779146861 1798435697014036417180073)
                      ·
                        rfl

theorem cell23_3502441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_3502441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502441 prefixEnd_3502441 := by exact prefixLift 3502441
  have htrace : WordTrace (prefixWord ++ tailWord_3502441) baseStart_3502441 baseEnd_3502441 := by
    simpa [prefixWord, tailWord_3502441, baseEnd_3502441] using wordTrace_append hprefix tailTrace_3502441
  have hstable : (prefixWord ++ tailWord_3502441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502441).length < 2 ^ (prefixWord ++ tailWord_3502441).sum := by decide
  have hdescent : baseEnd_3502441 < baseStart_3502441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502465 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3502465 : Nat := 118140960795 + 3502465 * 2 ^ 59
def prefixEnd_3502465 : Nat := 4983230072969 + 3 ^ 40 * 3502465 * 2
def baseEnd_3502465 : Nat := 599482673516581441093321

theorem tailTrace_3502465 : CollatzResearch.WordTrace tailWord_3502465 prefixEnd_3502465 599482673516581441093321 := by
  unfold tailWord_3502465
  simp only [CollatzResearch.WordTrace]
  refine ⟨127745393256174953244092849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85163595504116635496061899 127745393256174953244092849)
  ·
    refine ⟨95809044942131214933069637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127745393256174953244092849 95809044942131214933069637)
    ·
      refine ⟨17964195926649602799950557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95809044942131214933069637 17964195926649602799950557)
      ·
        refine ⟨6736573472493601049981459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17964195926649602799950557 6736573472493601049981459)
        ·
          refine ⟨10104860208740401574972189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736573472493601049981459 10104860208740401574972189)
          ·
            refine ⟨3789322578277650590614571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10104860208740401574972189 3789322578277650590614571)
            ·
              refine ⟨5683983867416475885921857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789322578277650590614571 5683983867416475885921857)
              ·
                refine ⟨4262987900562356914441393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5683983867416475885921857 4262987900562356914441393)
                ·
                  refine ⟨3197240925421767685831045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4262987900562356914441393 3197240925421767685831045)
                  ·
                    refine ⟨599482673516581441093321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197240925421767685831045 599482673516581441093321)
                    ·
                      rfl

theorem cell23_3502465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3502465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502465 prefixEnd_3502465 := by exact prefixLift 3502465
  have htrace : WordTrace (prefixWord ++ tailWord_3502465) baseStart_3502465 baseEnd_3502465 := by
    simpa [prefixWord, tailWord_3502465, baseEnd_3502465] using wordTrace_append hprefix tailTrace_3502465
  have hstable : (prefixWord ++ tailWord_3502465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502465).length < 2 ^ (prefixWord ++ tailWord_3502465).sum := by decide
  have hdescent : baseEnd_3502465 < baseStart_3502465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502488 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3502488 : Nat := 118140960795 + 3502488 * 2 ^ 59
def prefixEnd_3502488 : Nat := 4983230072969 + 3 ^ 40 * 3502488 * 2
def baseEnd_3502488 : Nat := 1798459830604797733292357

theorem tailTrace_3502488 : CollatzResearch.WordTrace tailWord_3502488 prefixEnd_3502488 1798459830604797733292357 := by
  unfold tailWord_3502488
  simp only [CollatzResearch.WordTrace]
  refine ⟨63873116067545814086090059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85164154756727752114786745 63873116067545814086090059)
  ·
    refine ⟨95809674101318721129135089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63873116067545814086090059 95809674101318721129135089)
    ·
      refine ⟨71857255575989040846851317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95809674101318721129135089 71857255575989040846851317)
      ·
        refine ⟨6736617710248972579392311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71857255575989040846851317 6736617710248972579392311)
        ·
          refine ⟨10104926565373458869088467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6736617710248972579392311 10104926565373458869088467)
          ·
            refine ⟨15157389848060188303632701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10104926565373458869088467 15157389848060188303632701)
            ·
              refine ⟨5684021193022570613862263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15157389848060188303632701 5684021193022570613862263)
              ·
                refine ⟨8526031789533855920793395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684021193022570613862263 8526031789533855920793395)
                ·
                  refine ⟨12789047684300783881190093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8526031789533855920793395 12789047684300783881190093)
                  ·
                    refine ⟨4795892881612793955446285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12789047684300783881190093 4795892881612793955446285)
                    ·
                      refine ⟨1798459830604797733292357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4795892881612793955446285 1798459830604797733292357)
                      ·
                        rfl

theorem cell23_3502488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3502488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502488 prefixEnd_3502488 := by exact prefixLift 3502488
  have htrace : WordTrace (prefixWord ++ tailWord_3502488) baseStart_3502488 baseEnd_3502488 := by
    simpa [prefixWord, tailWord_3502488, baseEnd_3502488] using wordTrace_append hprefix tailTrace_3502488
  have hstable : (prefixWord ++ tailWord_3502488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502488).length < 2 ^ (prefixWord ++ tailWord_3502488).sum := by decide
  have hdescent : baseEnd_3502488 < baseStart_3502488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502618 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_3502618 : Nat := 118140960795 + 3502618 * 2 ^ 59
def prefixEnd_3502618 : Nat := 4983230072969 + 3 ^ 40 * 3502618 * 2
def baseEnd_3502618 : Nat := 1798526583089882224666759

theorem tailTrace_3502618 : CollatzResearch.WordTrace tailWord_3502618 prefixEnd_3502618 1798526583089882224666759 := by
  unfold tailWord_3502618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31937743406155165093603127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85167315749747106916275005 31937743406155165093603127)
  ·
    refine ⟨47906615109232747640404691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31937743406155165093603127 47906615109232747640404691)
    ·
      refine ⟨71859922663849121460607037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47906615109232747640404691 71859922663849121460607037)
      ·
        refine ⟨26947470998943420547727639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71859922663849121460607037 26947470998943420547727639)
        ·
          refine ⟨40421206498415130821591459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26947470998943420547727639 40421206498415130821591459)
          ·
            refine ⟨60631809747622696232387189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40421206498415130821591459 60631809747622696232387189)
            ·
              refine ⟨5684232163839627771786299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60631809747622696232387189 5684232163839627771786299)
              ·
                refine ⟨8526348245759441657679449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684232163839627771786299 8526348245759441657679449)
                ·
                  refine ⟨6394761184319581243259587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8526348245759441657679449 6394761184319581243259587)
                  ·
                    refine ⟨9592141776479371864889381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394761184319581243259587 9592141776479371864889381)
                    ·
                      refine ⟨1798526583089882224666759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9592141776479371864889381 1798526583089882224666759)
                      ·
                        rfl

theorem cell23_3502618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_3502618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502618 prefixEnd_3502618 := by exact prefixLift 3502618
  have htrace : WordTrace (prefixWord ++ tailWord_3502618) baseStart_3502618 baseEnd_3502618 := by
    simpa [prefixWord, tailWord_3502618, baseEnd_3502618] using wordTrace_append hprefix tailTrace_3502618
  have hstable : (prefixWord ++ tailWord_3502618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502618).length < 2 ^ (prefixWord ++ tailWord_3502618).sum := by decide
  have hdescent : baseEnd_3502618 < baseStart_3502618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502645 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3502645 : Nat := 118140960795 + 3502645 * 2 ^ 59
def prefixEnd_3502645 : Nat := 4983230072969 + 3 ^ 40 * 3502645 * 2
def baseEnd_3502645 : Nat := 599513482355851206343045

theorem tailTrace_3502645 : CollatzResearch.WordTrace tailWord_3502645 prefixEnd_3502645 599513482355851206343045 := by
  unfold tailWord_3502645
  simp only [CollatzResearch.WordTrace]
  refine ⟨127751958395522843985645389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85167972263681895990430259 127751958395522843985645389)
  ·
    refine ⟨47906984398321066494617021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127751958395522843985645389 47906984398321066494617021)
    ·
      refine ⟨17965119149370399935481383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47906984398321066494617021 17965119149370399935481383)
      ·
        refine ⟨26947678724055599903222075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17965119149370399935481383 26947678724055599903222075)
        ·
          refine ⟨40421518086083399854833113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26947678724055599903222075 40421518086083399854833113)
          ·
            refine ⟨30316138564562549891124835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40421518086083399854833113 30316138564562549891124835)
            ·
              refine ⟨45474207846843824836687253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30316138564562549891124835 45474207846843824836687253)
              ·
                refine ⟨2131603492820804289219715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45474207846843824836687253 2131603492820804289219715)
                ·
                  refine ⟨3197405239231206433829573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131603492820804289219715 3197405239231206433829573)
                  ·
                    refine ⟨599513482355851206343045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197405239231206433829573 599513482355851206343045)
                    ·
                      rfl

theorem cell23_3502645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3502645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502645 prefixEnd_3502645 := by exact prefixLift 3502645
  have htrace : WordTrace (prefixWord ++ tailWord_3502645) baseStart_3502645 baseEnd_3502645 := by
    simpa [prefixWord, tailWord_3502645, baseEnd_3502645] using wordTrace_append hprefix tailTrace_3502645
  have hstable : (prefixWord ++ tailWord_3502645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502645).length < 2 ^ (prefixWord ++ tailWord_3502645).sum := by decide
  have hdescent : baseEnd_3502645 < baseStart_3502645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502662 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3502662 : Nat := 118140960795 + 3502662 * 2 ^ 59
def prefixEnd_3502662 : Nat := 4983230072969 + 3 ^ 40 * 3502662 * 2
def baseEnd_3502662 : Nat := 599516392079560017505519

theorem tailTrace_3502662 : CollatzResearch.WordTrace tailWord_3502662 prefixEnd_3502662 599516392079560017505519 := by
  unfold tailWord_3502662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992268076139414246531695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85168385624307503926009493 3992268076139414246531695)
  ·
    refine ⟨5988402114209121369797543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3992268076139414246531695 5988402114209121369797543)
    ·
      refine ⟨8982603171313682054696315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988402114209121369797543 8982603171313682054696315)
      ·
        refine ⟨13473904756970523082044473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982603171313682054696315 13473904756970523082044473)
        ·
          refine ⟨10105428567727892311533355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13473904756970523082044473 10105428567727892311533355)
          ·
            refine ⟨15158142851591838467300033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105428567727892311533355 15158142851591838467300033)
            ·
              refine ⟨11368607138693878850475025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15158142851591838467300033 11368607138693878850475025)
              ·
                refine ⟨8526455354020409137856269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11368607138693878850475025 8526455354020409137856269)
                ·
                  refine ⟨3197420757757653426696101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8526455354020409137856269 3197420757757653426696101)
                  ·
                    refine ⟨599516392079560017505519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197420757757653426696101 599516392079560017505519)
                    ·
                      rfl

theorem cell23_3502662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3502662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502662 prefixEnd_3502662 := by exact prefixLift 3502662
  have htrace : WordTrace (prefixWord ++ tailWord_3502662) baseStart_3502662 baseEnd_3502662 := by
    simpa [prefixWord, tailWord_3502662, baseEnd_3502662] using wordTrace_append hprefix tailTrace_3502662
  have hstable : (prefixWord ++ tailWord_3502662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502662).length < 2 ^ (prefixWord ++ tailWord_3502662).sum := by decide
  have hdescent : baseEnd_3502662 < baseStart_3502662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502671 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 3, 5]
def baseStart_3502671 : Nat := 118140960795 + 3502671 * 2 ^ 59
def prefixEnd_3502671 : Nat := 4983230072969 + 3 ^ 40 * 3502671 * 2
def baseEnd_3502671 : Nat := 599517932521523505768005

theorem tailTrace_3502671 : CollatzResearch.WordTrace tailWord_3502671 prefixEnd_3502671 599517932521523505768005 := by
  unfold tailWord_3502671
  simp only [CollatzResearch.WordTrace]
  refine ⟨127752906693428650426091867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85168604462285766950727911 127752906693428650426091867)
  ·
    refine ⟨191629360040142975639137801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127752906693428650426091867 191629360040142975639137801)
    ·
      refine ⟨143722020030107231729353351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191629360040142975639137801 143722020030107231729353351)
      ·
        refine ⟨215583030045160847594030027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143722020030107231729353351 215583030045160847594030027)
        ·
          refine ⟨323374545067741271391045041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215583030045160847594030027 323374545067741271391045041)
          ·
            refine ⟨242530908800805953543283781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323374545067741271391045041 242530908800805953543283781)
            ·
              refine ⟨45474545400151116289365709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242530908800805953543283781 45474545400151116289365709)
              ·
                refine ⟨17052954525056668608512141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45474545400151116289365709 17052954525056668608512141)
                ·
                  refine ⟨6394857946896250728192053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17052954525056668608512141 6394857946896250728192053)
                  ·
                    refine ⟨599517932521523505768005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6394857946896250728192053 599517932521523505768005)
                    ·
                      rfl

theorem cell23_3502671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_3502671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502671 prefixEnd_3502671 := by exact prefixLift 3502671
  have htrace : WordTrace (prefixWord ++ tailWord_3502671) baseStart_3502671 baseEnd_3502671 := by
    simpa [prefixWord, tailWord_3502671, baseEnd_3502671] using wordTrace_append hprefix tailTrace_3502671
  have hstable : (prefixWord ++ tailWord_3502671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502671).length < 2 ^ (prefixWord ++ tailWord_3502671).sum := by decide
  have hdescent : baseEnd_3502671 < baseStart_3502671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502688 : List Nat := [2, 1, 1, 3, 2, 1, 4, 3, 1, 5]
def baseStart_3502688 : Nat := 118140960795 + 3502688 * 2 ^ 59
def prefixEnd_3502688 : Nat := 4983230072969 + 3 ^ 40 * 3502688 * 2
def baseEnd_3502688 : Nat := 599520842245232316930479

theorem tailTrace_3502688 : CollatzResearch.WordTrace tailWord_3502688 prefixEnd_3502688 599520842245232316930479 := by
  unfold tailWord_3502688
  simp only [CollatzResearch.WordTrace]
  refine ⟨63876763367183531164730359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85169017822911374886307145 63876763367183531164730359)
  ·
    refine ⟨95815145050775296747095539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63876763367183531164730359 95815145050775296747095539)
    ·
      refine ⟨143722717576162945120643309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95815145050775296747095539 143722717576162945120643309)
      ·
        refine ⟨53896019091061104420241241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143722717576162945120643309 53896019091061104420241241)
        ·
          refine ⟨40422014318295828315180931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53896019091061104420241241 40422014318295828315180931)
          ·
            refine ⟨60633021477443742472771397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40422014318295828315180931 60633021477443742472771397)
            ·
              refine ⟨11368691527020701713644637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60633021477443742472771397 11368691527020701713644637)
              ·
                refine ⟨4263259322632763142616739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11368691527020701713644637 4263259322632763142616739)
                ·
                  refine ⟨6394888983949144713925109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263259322632763142616739 6394888983949144713925109)
                  ·
                    refine ⟨599520842245232316930479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6394888983949144713925109 599520842245232316930479)
                    ·
                      rfl

theorem cell23_3502688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_3502688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502688 prefixEnd_3502688 := by exact prefixLift 3502688
  have htrace : WordTrace (prefixWord ++ tailWord_3502688) baseStart_3502688 baseEnd_3502688 := by
    simpa [prefixWord, tailWord_3502688, baseEnd_3502688] using wordTrace_append hprefix tailTrace_3502688
  have hstable : (prefixWord ++ tailWord_3502688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502688).length < 2 ^ (prefixWord ++ tailWord_3502688).sum := by decide
  have hdescent : baseEnd_3502688 < baseStart_3502688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502702 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_3502702 : Nat := 118140960795 + 3502702 * 2 ^ 59
def prefixEnd_3502702 : Nat := 4983230072969 + 3 ^ 40 * 3502702 * 2
def baseEnd_3502702 : Nat := 1798569715464859896016373

theorem tailTrace_3502702 : CollatzResearch.WordTrace tailWord_3502702 prefixEnd_3502702 1798569715464859896016373 := by
  unfold tailWord_3502702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15969254669539542840058795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85169358237544228480313573 15969254669539542840058795)
  ·
    refine ⟨23953882004309314260088193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15969254669539542840058795 23953882004309314260088193)
    ·
      refine ⟨17965411503231985695066145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23953882004309314260088193 17965411503231985695066145)
      ·
        refine ⟨13474058627423989271299609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17965411503231985695066145 13474058627423989271299609)
        ·
          refine ⟨10105543970567991953474707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13474058627423989271299609 10105543970567991953474707)
          ·
            refine ⟨15158315955851987930212061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10105543970567991953474707 15158315955851987930212061)
            ·
              refine ⟨5684368483444495473829523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15158315955851987930212061 5684368483444495473829523)
              ·
                refine ⟨8526552725166743210744285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684368483444495473829523 8526552725166743210744285)
                ·
                  refine ⟨3197457271937528704029107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8526552725166743210744285 3197457271937528704029107)
                  ·
                    refine ⟨4796185907906293056043661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3197457271937528704029107 4796185907906293056043661)
                    ·
                      refine ⟨1798569715464859896016373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4796185907906293056043661 1798569715464859896016373)
                      ·
                        rfl

theorem cell23_3502702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_3502702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502702 prefixEnd_3502702 := by exact prefixLift 3502702
  have htrace : WordTrace (prefixWord ++ tailWord_3502702) baseStart_3502702 baseEnd_3502702 := by
    simpa [prefixWord, tailWord_3502702, baseEnd_3502702] using wordTrace_append hprefix tailTrace_3502702
  have hstable : (prefixWord ++ tailWord_3502702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502702).length < 2 ^ (prefixWord ++ tailWord_3502702).sum := by decide
  have hdescent : baseEnd_3502702 < baseStart_3502702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502709 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 6]
def baseStart_3502709 : Nat := 118140960795 + 3502709 * 2 ^ 59
def prefixEnd_3502709 : Nat := 4983230072969 + 3 ^ 40 * 3502709 * 2
def baseEnd_3502709 : Nat := 199841478869937929847649

theorem tailTrace_3502709 : CollatzResearch.WordTrace tailWord_3502709 prefixEnd_3502709 199841478869937929847649 := by
  unfold tailWord_3502709
  simp only [CollatzResearch.WordTrace]
  refine ⟨127754292667290982915975181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85169528444860655277316787 127754292667290982915975181)
  ·
    refine ⟨47907859750234118593490693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127754292667290982915975181 47907859750234118593490693)
    ·
      refine ⟨8982723703168897236279505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47907859750234118593490693 8982723703168897236279505)
      ·
        refine ⟨6737042777376672927209629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8982723703168897236279505 6737042777376672927209629)
        ·
          refine ⟨2526391041516252347703611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6737042777376672927209629 2526391041516252347703611)
          ·
            refine ⟨3789586562274378521555417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526391041516252347703611 3789586562274378521555417)
            ·
              refine ⟨2842189921705783891166563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789586562274378521555417 2842189921705783891166563)
              ·
                refine ⟨4263284882558675836749845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842189921705783891166563 4263284882558675836749845)
                ·
                  refine ⟨199841478869937929847649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4263284882558675836749845 199841478869937929847649)
                  ·
                    rfl

theorem cell23_3502709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_3502709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502709 prefixEnd_3502709 := by exact prefixLift 3502709
  have htrace : WordTrace (prefixWord ++ tailWord_3502709) baseStart_3502709 baseEnd_3502709 := by
    simpa [prefixWord, tailWord_3502709, baseEnd_3502709] using wordTrace_append hprefix tailTrace_3502709
  have hstable : (prefixWord ++ tailWord_3502709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502709).length < 2 ^ (prefixWord ++ tailWord_3502709).sum := by decide
  have hdescent : baseEnd_3502709 < baseStart_3502709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502725 : List Nat := [1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_3502725 : Nat := 118140960795 + 3502725 * 2 ^ 59
def prefixEnd_3502725 : Nat := 4983230072969 + 3 ^ 40 * 3502725 * 2
def baseEnd_3502725 : Nat := 1798581525519913306028767

theorem tailTrace_3502725 : CollatzResearch.WordTrace tailWord_3502725 prefixEnd_3502725 1798581525519913306028767 := by
  unfold tailWord_3502725
  simp only [CollatzResearch.WordTrace]
  refine ⟨127754876235233017648557629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85169917490155345099038419 127754876235233017648557629)
  ·
    refine ⟨47908078588212381618209111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127754876235233017648557629 47908078588212381618209111)
    ·
      refine ⟨71862117882318572427313667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47908078588212381618209111 71862117882318572427313667)
      ·
        refine ⟨107793176823477858640970501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71862117882318572427313667 107793176823477858640970501)
        ·
          refine ⟨20211220654402098495181969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107793176823477858640970501 20211220654402098495181969)
          ·
            refine ⟨15158415490801573871386477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20211220654402098495181969 15158415490801573871386477)
            ·
              refine ⟨5684405809050590201769929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15158415490801573871386477 5684405809050590201769929)
              ·
                refine ⟨4263304356787942651327447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684405809050590201769929 4263304356787942651327447)
                ·
                  refine ⟨6394956535181913976991171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263304356787942651327447 6394956535181913976991171)
                  ·
                    refine ⟨9592434802772870965486757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6394956535181913976991171 9592434802772870965486757)
                    ·
                      refine ⟨1798581525519913306028767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9592434802772870965486757 1798581525519913306028767)
                      ·
                        rfl

theorem cell23_3502725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_3502725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502725 prefixEnd_3502725 := by exact prefixLift 3502725
  have htrace : WordTrace (prefixWord ++ tailWord_3502725) baseStart_3502725 baseEnd_3502725 := by
    simpa [prefixWord, tailWord_3502725, baseEnd_3502725] using wordTrace_append hprefix tailTrace_3502725
  have hstable : (prefixWord ++ tailWord_3502725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502725).length < 2 ^ (prefixWord ++ tailWord_3502725).sum := by decide
  have hdescent : baseEnd_3502725 < baseStart_3502725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502752 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 2, 4]
def baseStart_3502752 : Nat := 118140960795 + 3502752 * 2 ^ 59
def prefixEnd_3502752 : Nat := 4983230072969 + 3 ^ 40 * 3502752 * 2
def baseEnd_3502752 : Nat := 599531796499194900130381

theorem tailTrace_3502752 : CollatzResearch.WordTrace tailWord_3502752 prefixEnd_3502752 599531796499194900130381 := by
  unfold tailWord_3502752
  simp only [CollatzResearch.WordTrace]
  refine ⟨63877930503067600629895255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85170574004090134173193673 63877930503067600629895255)
  ·
    refine ⟨95816895754601400944842883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63877930503067600629895255 95816895754601400944842883)
    ·
      refine ⟨143725343631902101417264325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95816895754601400944842883 143725343631902101417264325)
      ·
        refine ⟨26948501930981644015737061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143725343631902101417264325 26948501930981644015737061)
        ·
          refine ⟨5052844112059058252950699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26948501930981644015737061 5052844112059058252950699)
          ·
            refine ⟨7579266168088587379426049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5052844112059058252950699 7579266168088587379426049)
            ·
              refine ⟨5684449626066440534569537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7579266168088587379426049 5684449626066440534569537)
              ·
                refine ⟨4263337219549830400927153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684449626066440534569537 4263337219549830400927153)
                ·
                  refine ⟨3197502914662372800695365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4263337219549830400927153 3197502914662372800695365)
                  ·
                    refine ⟨599531796499194900130381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197502914662372800695365 599531796499194900130381)
                    ·
                      rfl

theorem cell23_3502752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_3502752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502752 prefixEnd_3502752 := by exact prefixLift 3502752
  have htrace : WordTrace (prefixWord ++ tailWord_3502752) baseStart_3502752 baseEnd_3502752 := by
    simpa [prefixWord, tailWord_3502752, baseEnd_3502752] using wordTrace_append hprefix tailTrace_3502752
  have hstable : (prefixWord ++ tailWord_3502752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502752).length < 2 ^ (prefixWord ++ tailWord_3502752).sum := by decide
  have hdescent : baseEnd_3502752 < baseStart_3502752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502753 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3502753 : Nat := 118140960795 + 3502753 * 2 ^ 59
def prefixEnd_3502753 : Nat := 4983230072969 + 3 ^ 40 * 3502753 * 2
def baseEnd_3502753 : Nat := 1798595902978239196478639

theorem tailTrace_3502753 : CollatzResearch.WordTrace tailWord_3502753 prefixEnd_3502753 1798595902978239196478639 := by
  unfold tailWord_3502753
  simp only [CollatzResearch.WordTrace]
  refine ⟨127755897479131578430576913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85170598319421052287051275 127755897479131578430576913)
  ·
    refine ⟨95816923109348683822932685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127755897479131578430576913 95816923109348683822932685)
    ·
      refine ⟨35931346166005756433599757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95816923109348683822932685 35931346166005756433599757)
      ·
        refine ⟨13474254812252158662599909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35931346166005756433599757 13474254812252158662599909)
        ·
          refine ⟨2526422777297279749237483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13474254812252158662599909 2526422777297279749237483)
          ·
            refine ⟨3789634165945919623856225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526422777297279749237483 3789634165945919623856225)
            ·
              refine ⟨2842225624459439717892169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789634165945919623856225 2842225624459439717892169)
              ·
                refine ⟨2131669218344579788419127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842225624459439717892169 2131669218344579788419127)
                ·
                  refine ⟨3197503827516869682628691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131669218344579788419127 3197503827516869682628691)
                  ·
                    refine ⟨4796255741275304523943037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3197503827516869682628691 4796255741275304523943037)
                    ·
                      refine ⟨1798595902978239196478639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4796255741275304523943037 1798595902978239196478639)
                      ·
                        rfl

theorem cell23_3502753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3502753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502753 prefixEnd_3502753 := by exact prefixLift 3502753
  have htrace : WordTrace (prefixWord ++ tailWord_3502753) baseStart_3502753 baseEnd_3502753 := by
    simpa [prefixWord, tailWord_3502753, baseEnd_3502753] using wordTrace_append hprefix tailTrace_3502753
  have hstable : (prefixWord ++ tailWord_3502753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502753).length < 2 ^ (prefixWord ++ tailWord_3502753).sum := by decide
  have hdescent : baseEnd_3502753 < baseStart_3502753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502761 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_3502761 : Nat := 118140960795 + 3502761 * 2 ^ 59
def prefixEnd_3502761 : Nat := 4983230072969 + 3 ^ 40 * 3502761 * 2
def baseEnd_3502761 : Nat := 599533336941158388392867

theorem tailTrace_3502761 : CollatzResearch.WordTrace tailWord_3502761 prefixEnd_3502761 599533336941158388392867 := by
  unfold tailWord_3502761
  simp only [CollatzResearch.WordTrace]
  refine ⟨127756189263102595796868137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85170792842068397197912091 127756189263102595796868137)
  ·
    refine ⟨95817141947326946847651103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127756189263102595796868137 95817141947326946847651103)
    ·
      refine ⟨143725712920990420271476655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95817141947326946847651103 143725712920990420271476655)
      ·
        refine ⟨215588569381485630407214983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143725712920990420271476655 215588569381485630407214983)
        ·
          refine ⟨323382854072228445610822475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215588569381485630407214983 323382854072228445610822475)
          ·
            refine ⟨485074281108342668416233713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323382854072228445610822475 485074281108342668416233713)
            ·
              refine ⟨363805710831257001312175285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485074281108342668416233713 363805710831257001312175285)
              ·
                refine ⟨34106785390430343873016433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363805710831257001312175285 34106785390430343873016433)
                ·
                  refine ⟨25580089042822757904762325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34106785390430343873016433 25580089042822757904762325)
                  ·
                    refine ⟨599533336941158388392867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25580089042822757904762325 599533336941158388392867)
                    ·
                      rfl

theorem cell23_3502761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_3502761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502761 prefixEnd_3502761 := by exact prefixLift 3502761
  have htrace : WordTrace (prefixWord ++ tailWord_3502761) baseStart_3502761 baseEnd_3502761 := by
    simpa [prefixWord, tailWord_3502761, baseEnd_3502761] using wordTrace_append hprefix tailTrace_3502761
  have hstable : (prefixWord ++ tailWord_3502761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502761).length < 2 ^ (prefixWord ++ tailWord_3502761).sum := by decide
  have hdescent : baseEnd_3502761 < baseStart_3502761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502765 : List Nat := [1, 5, 2, 1, 1, 4, 1, 8]
def baseStart_3502765 : Nat := 118140960795 + 3502765 * 2 ^ 59
def prefixEnd_3502765 : Nat := 4983230072969 + 3 ^ 40 * 3502765 * 2
def baseEnd_3502765 : Nat := 66614891286892338871429

theorem tailTrace_3502765 : CollatzResearch.WordTrace tailWord_3502765 prefixEnd_3502765 66614891286892338871429 := by
  unfold tailWord_3502765
  simp only [CollatzResearch.WordTrace]
  refine ⟨127756335155088104480013749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85170890103392069653342499 127756335155088104480013749)
  ·
    refine ⟨11977156420789509795001289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127756335155088104480013749 11977156420789509795001289)
    ·
      refine ⟨8982867315592132346250967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11977156420789509795001289 8982867315592132346250967)
      ·
        refine ⟨13474300973388198519376451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982867315592132346250967 13474300973388198519376451)
        ·
          refine ⟨20211451460082297779064677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13474300973388198519376451 20211451460082297779064677)
          ·
            refine ⟨3789647148765430833574627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20211451460082297779064677 3789647148765430833574627)
            ·
              refine ⟨5684470723148146250361941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789647148765430833574627 5684470723148146250361941)
              ·
                refine ⟨66614891286892338871429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5684470723148146250361941 66614891286892338871429)
                ·
                  rfl

theorem cell23_3502765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 8].length) (baseStart_3502765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502765 prefixEnd_3502765 := by exact prefixLift 3502765
  have htrace : WordTrace (prefixWord ++ tailWord_3502765) baseStart_3502765 baseEnd_3502765 := by
    simpa [prefixWord, tailWord_3502765, baseEnd_3502765] using wordTrace_append hprefix tailTrace_3502765
  have hstable : (prefixWord ++ tailWord_3502765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502765).length < 2 ^ (prefixWord ++ tailWord_3502765).sum := by decide
  have hdescent : baseEnd_3502765 < baseStart_3502765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502808 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_3502808 : Nat := 118140960795 + 3502808 * 2 ^ 59
def prefixEnd_3502808 : Nat := 4983230072969 + 3 ^ 40 * 3502808 * 2
def baseEnd_3502808 : Nat := 599541381471412160430295

theorem tailTrace_3502808 : CollatzResearch.WordTrace tailWord_3502808 prefixEnd_3502808 599541381471412160430295 := by
  unfold tailWord_3502808
  simp only [CollatzResearch.WordTrace]
  refine ⟨63878951746966161411914539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85171935662621548549219385 63878951746966161411914539)
  ·
    refine ⟨95818427620449242117871809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63878951746966161411914539 95818427620449242117871809)
    ·
      refine ⟨71863820715336931588403857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95818427620449242117871809 71863820715336931588403857)
      ·
        refine ⟨53897865536502698691302893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71863820715336931588403857 53897865536502698691302893)
        ·
          refine ⟨20211699576188512009238585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53897865536502698691302893 20211699576188512009238585)
          ·
            refine ⟨15158774682141384006928939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20211699576188512009238585 15158774682141384006928939)
            ·
              refine ⟨22738162023212076010393409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15158774682141384006928939 22738162023212076010393409)
              ·
                refine ⟨17053621517409057007795057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22738162023212076010393409 17053621517409057007795057)
                ·
                  refine ⟨12790216138056792755846293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17053621517409057007795057 12790216138056792755846293)
                  ·
                    refine ⟨599541381471412160430295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12790216138056792755846293 599541381471412160430295)
                    ·
                      rfl

theorem cell23_3502808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_3502808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502808 prefixEnd_3502808 := by exact prefixLift 3502808
  have htrace : WordTrace (prefixWord ++ tailWord_3502808) baseStart_3502808 baseEnd_3502808 := by
    simpa [prefixWord, tailWord_3502808, baseEnd_3502808] using wordTrace_append hprefix tailTrace_3502808
  have hstable : (prefixWord ++ tailWord_3502808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502808).length < 2 ^ (prefixWord ++ tailWord_3502808).sum := by decide
  have hdescent : baseEnd_3502808 < baseStart_3502808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502928 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 8]
def baseStart_3502928 : Nat := 118140960795 + 3502928 * 2 ^ 59
def prefixEnd_3502928 : Nat := 4983230072969 + 3 ^ 40 * 3502928 * 2
def baseEnd_3502928 : Nat := 199853973565864001310037

theorem tailTrace_3502928 : CollatzResearch.WordTrace tailWord_3502928 prefixEnd_3502928 199853973565864001310037 := by
  unfold tailWord_3502928
  simp only [CollatzResearch.WordTrace]
  refine ⟨63881140126748791659098719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85174853502331722212131625 63881140126748791659098719)
  ·
    refine ⟨95821710190123187488648079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63881140126748791659098719 95821710190123187488648079)
    ·
      refine ⟨143732565285184781232972119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95821710190123187488648079 143732565285184781232972119)
      ·
        refine ⟨215598847927777171849458179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143732565285184781232972119 215598847927777171849458179)
        ·
          refine ⟨323398271891665757774187269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215598847927777171849458179 323398271891665757774187269)
          ·
            refine ⟨60637175979687329582660113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323398271891665757774187269 60637175979687329582660113)
            ·
              refine ⟨45477881984765497186995085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60637175979687329582660113 45477881984765497186995085)
              ·
                refine ⟨17054205744287061445123157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45477881984765497186995085 17054205744287061445123157)
                ·
                  refine ⟨199853973565864001310037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17054205744287061445123157 199853973565864001310037)
                  ·
                    rfl

theorem cell23_3502928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_3502928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502928 prefixEnd_3502928 := by exact prefixLift 3502928
  have htrace : WordTrace (prefixWord ++ tailWord_3502928) baseStart_3502928 baseEnd_3502928 := by
    simpa [prefixWord, tailWord_3502928, baseEnd_3502928] using wordTrace_append hprefix tailTrace_3502928
  have hstable : (prefixWord ++ tailWord_3502928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502928).length < 2 ^ (prefixWord ++ tailWord_3502928).sum := by decide
  have hdescent : baseEnd_3502928 < baseStart_3502928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502966 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_3502966 : Nat := 118140960795 + 3502966 * 2 ^ 59
def prefixEnd_3502966 : Nat := 4983230072969 + 3 ^ 40 * 3502966 * 2
def baseEnd_3502966 : Nat := 599568424785882287705053

theorem tailTrace_3502966 : CollatzResearch.WordTrace tailWord_3502966 prefixEnd_3502966 599568424785882287705053 := by
  unfold tailWord_3502966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7985229139209994738005047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85175777484906610538720501 7985229139209994738005047)
  ·
    refine ⟨11977843708814992107007571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7985229139209994738005047 11977843708814992107007571)
    ·
      refine ⟨17966765563222488160511357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11977843708814992107007571 17966765563222488160511357)
      ·
        refine ⟨6737537086208433060191759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17966765563222488160511357 6737537086208433060191759)
        ·
          refine ⟨10106305629312649590287639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737537086208433060191759 10106305629312649590287639)
          ·
            refine ⟨15159458443968974385431459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10106305629312649590287639 15159458443968974385431459)
            ·
              refine ⟨22739187665953461578147189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15159458443968974385431459 22739187665953461578147189)
              ·
                refine ⟨2131798843683137022951299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22739187665953461578147189 2131798843683137022951299)
                ·
                  refine ⟨3197698265524705534426949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2131798843683137022951299 3197698265524705534426949)
                  ·
                    refine ⟨599568424785882287705053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3197698265524705534426949 599568424785882287705053)
                    ·
                      rfl

theorem cell23_3502966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_3502966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502966 prefixEnd_3502966 := by exact prefixLift 3502966
  have htrace : WordTrace (prefixWord ++ tailWord_3502966) baseStart_3502966 baseEnd_3502966 := by
    simpa [prefixWord, tailWord_3502966, baseEnd_3502966] using wordTrace_append hprefix tailTrace_3502966
  have hstable : (prefixWord ++ tailWord_3502966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502966).length < 2 ^ (prefixWord ++ tailWord_3502966).sum := by decide
  have hdescent : baseEnd_3502966 < baseStart_3502966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3502995 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 4]
def baseStart_3502995 : Nat := 118140960795 + 3502995 * 2 ^ 59
def prefixEnd_3502995 : Nat := 4983230072969 + 3 ^ 40 * 3502995 * 2
def baseEnd_3502995 : Nat := 1798720165296627249652525

theorem tailTrace_3502995 : CollatzResearch.WordTrace tailWord_3502995 prefixEnd_3502995 1798720165296627249652525 := by
  unfold tailWord_3502995
  simp only [CollatzResearch.WordTrace]
  refine ⟨127764723944254853760886439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85176482629503235840590959 127764723944254853760886439)
  ·
    refine ⟨191647085916382280641329659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127764723944254853760886439 191647085916382280641329659)
    ·
      refine ⟨287470628874573420961994489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191647085916382280641329659 287470628874573420961994489)
      ·
        refine ⟨215602971655930065721495867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287470628874573420961994489 215602971655930065721495867)
        ·
          refine ⟨323404457483895098582243801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215602971655930065721495867 323404457483895098582243801)
          ·
            refine ⟨242553343112921323936682851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323404457483895098582243801 242553343112921323936682851)
            ·
              refine ⟨363830014669381985905024277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242553343112921323936682851 363830014669381985905024277)
              ·
                refine ⟨17054531937627280589298013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 363830014669381985905024277 17054531937627280589298013)
                ·
                  refine ⟨6395449476610230220986755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17054531937627280589298013 6395449476610230220986755)
                  ·
                    refine ⟨9593174214915345331480133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395449476610230220986755 9593174214915345331480133)
                    ·
                      refine ⟨1798720165296627249652525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9593174214915345331480133 1798720165296627249652525)
                      ·
                        rfl

theorem cell23_3502995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_3502995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3502995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3502995 prefixEnd_3502995 := by exact prefixLift 3502995
  have htrace : WordTrace (prefixWord ++ tailWord_3502995) baseStart_3502995 baseEnd_3502995 := by
    simpa [prefixWord, tailWord_3502995, baseEnd_3502995] using wordTrace_append hprefix tailTrace_3502995
  have hstable : (prefixWord ++ tailWord_3502995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3502995).length < 2 ^ (prefixWord ++ tailWord_3502995).sum := by decide
  have hdescent : baseEnd_3502995 < baseStart_3502995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3502995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503009 : List Nat := [1, 2, 3, 4, 1, 2, 2, 2, 1, 5]
def baseStart_3503009 : Nat := 118140960795 + 3503009 * 2 ^ 59
def prefixEnd_3503009 : Nat := 4983230072969 + 3 ^ 40 * 3503009 * 2
def baseEnd_3503009 : Nat := 599575784675263398292487

theorem tailTrace_3503009 : CollatzResearch.WordTrace tailWord_3503009 prefixEnd_3503009 599575784675263398292487 := by
  unfold tailWord_3503009
  simp only [CollatzResearch.WordTrace]
  refine ⟨127765234566204134151896081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85176823044136089434597387 127765234566204134151896081)
  ·
    refine ⟨95823925924653100613922061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127765234566204134151896081 95823925924653100613922061)
    ·
      refine ⟨35933972221744912730220773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95823925924653100613922061 35933972221744912730220773)
      ·
        refine ⟨6737619791577171136916395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35933972221744912730220773 6737619791577171136916395)
        ·
          refine ⟨10106429687365756705374593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737619791577171136916395 10106429687365756705374593)
          ·
            refine ⟨7579822265524317529030945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106429687365756705374593 7579822265524317529030945)
            ·
              refine ⟨5684866699143238146773209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7579822265524317529030945 5684866699143238146773209)
              ·
                refine ⟨4263650024357428610079907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684866699143238146773209 4263650024357428610079907)
                ·
                  refine ⟨6395475036536142915119861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263650024357428610079907 6395475036536142915119861)
                  ·
                    refine ⟨599575784675263398292487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6395475036536142915119861 599575784675263398292487)
                    ·
                      rfl

theorem cell23_3503009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_3503009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503009 prefixEnd_3503009 := by exact prefixLift 3503009
  have htrace : WordTrace (prefixWord ++ tailWord_3503009) baseStart_3503009 baseEnd_3503009 := by
    simpa [prefixWord, tailWord_3503009, baseEnd_3503009] using wordTrace_append hprefix tailTrace_3503009
  have hstable : (prefixWord ++ tailWord_3503009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503009).length < 2 ^ (prefixWord ++ tailWord_3503009).sum := by decide
  have hdescent : baseEnd_3503009 < baseStart_3503009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503012 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 2, 6, 2]
def baseStart_3503012 : Nat := 118140960795 + 3503012 * 2 ^ 59
def prefixEnd_3503012 : Nat := 4983230072969 + 3 ^ 40 * 3503012 * 2
def baseEnd_3503012 : Nat := 1798728894467753683139947

theorem tailTrace_3503012 : CollatzResearch.WordTrace tailWord_3503012 prefixEnd_3503012 1798728894467753683139947 := by
  unfold tailWord_3503012
  simp only [CollatzResearch.WordTrace]
  refine ⟨63882671992596632832127645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85176895990128843776170193 63882671992596632832127645)
  ·
    refine ⟨23956001997223737312047867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63882671992596632832127645 23956001997223737312047867)
    ·
      refine ⟨35934002995835605968071801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23956001997223737312047867 35934002995835605968071801)
      ·
        refine ⟨26950502246876704476053851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35934002995835605968071801 26950502246876704476053851)
        ·
          refine ⟨40425753370315056714080777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26950502246876704476053851 40425753370315056714080777)
          ·
            refine ⟨30319315027736292535560583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40425753370315056714080777 30319315027736292535560583)
            ·
              refine ⟨45478972541604438803340875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30319315027736292535560583 45478972541604438803340875)
              ·
                refine ⟨68218458812406658205011313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45478972541604438803340875 68218458812406658205011313)
                ·
                  refine ⟨51163844109304993653758485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68218458812406658205011313 51163844109304993653758485)
                  ·
                    refine ⟨2398305192623671577519929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51163844109304993653758485 2398305192623671577519929)
                    ·
                      refine ⟨1798728894467753683139947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398305192623671577519929 1798728894467753683139947)
                      ·
                        rfl

theorem cell23_3503012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_3503012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503012 prefixEnd_3503012 := by exact prefixLift 3503012
  have htrace : WordTrace (prefixWord ++ tailWord_3503012) baseStart_3503012 baseEnd_3503012 := by
    simpa [prefixWord, tailWord_3503012, baseEnd_3503012] using wordTrace_append hprefix tailTrace_3503012
  have hstable : (prefixWord ++ tailWord_3503012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503012).length < 2 ^ (prefixWord ++ tailWord_3503012).sum := by decide
  have hdescent : baseEnd_3503012 < baseStart_3503012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503032 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_3503032 : Nat := 118140960795 + 3503032 * 2 ^ 59
def prefixEnd_3503032 : Nat := 4983230072969 + 3 ^ 40 * 3503032 * 2
def baseEnd_3503032 : Nat := 1798739164080843604889855

theorem tailTrace_3503032 : CollatzResearch.WordTrace tailWord_3503032 prefixEnd_3503032 1798739164080843604889855 := by
  unfold tailWord_3503032
  simp only [CollatzResearch.WordTrace]
  refine ⟨63883036722560404539991675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85177382296747206053322233 63883036722560404539991675)
  ·
    refine ⟨95824555083840606809987513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63883036722560404539991675 95824555083840606809987513)
    ·
      refine ⟨71868416312880455107490635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95824555083840606809987513 71868416312880455107490635)
      ·
        refine ⟨107802624469320682661235953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71868416312880455107490635 107802624469320682661235953)
        ·
          refine ⟨80851968351990511995926965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107802624469320682661235953 80851968351990511995926965)
          ·
            refine ⟨7579872032999110499618153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80851968351990511995926965 7579872032999110499618153)
            ·
              refine ⟨5684904024749332874713615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7579872032999110499618153 5684904024749332874713615)
              ·
                refine ⟨8527356037123999312070423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5684904024749332874713615 8527356037123999312070423)
                ·
                  refine ⟨12791034055685998968105635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8527356037123999312070423 12791034055685998968105635)
                  ·
                    refine ⟨19186551083528998452158453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12791034055685998968105635 19186551083528998452158453)
                    ·
                      refine ⟨1798739164080843604889855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19186551083528998452158453 1798739164080843604889855)
                      ·
                        rfl

theorem cell23_3503032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_3503032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503032 prefixEnd_3503032 := by exact prefixLift 3503032
  have htrace : WordTrace (prefixWord ++ tailWord_3503032) baseStart_3503032 baseEnd_3503032 := by
    simpa [prefixWord, tailWord_3503032, baseEnd_3503032] using wordTrace_append hprefix tailTrace_3503032
  have hstable : (prefixWord ++ tailWord_3503032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503032).length < 2 ^ (prefixWord ++ tailWord_3503032).sum := by decide
  have hdescent : baseEnd_3503032 < baseStart_3503032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503066 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_3503066 : Nat := 118140960795 + 3503066 * 2 ^ 59
def prefixEnd_3503066 : Nat := 4983230072969 + 3 ^ 40 * 3503066 * 2
def baseEnd_3503066 : Nat := 1798756622423096471864699

theorem tailTrace_3503066 : CollatzResearch.WordTrace tailWord_3503066 prefixEnd_3503066 1798756622423096471864699 := by
  unfold tailWord_3503066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31941828381749408221680263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85178209017998421924480701 31941828381749408221680263)
  ·
    refine ⟨47912742572624112332520395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31941828381749408221680263 47912742572624112332520395)
    ·
      refine ⟨71869113858936168498780593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47912742572624112332520395 71869113858936168498780593)
      ·
        refine ⟨53901835394202126374085445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71869113858936168498780593 53901835394202126374085445)
        ·
          refine ⟨10106594136412898695141021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53901835394202126374085445 10106594136412898695141021)
          ·
            refine ⟨3789972801154837010677883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10106594136412898695141021 3789972801154837010677883)
            ·
              refine ⟨5684959201732255516016825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3789972801154837010677883 5684959201732255516016825)
              ·
                refine ⟨4263719401299191637012619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5684959201732255516016825 4263719401299191637012619)
                ·
                  refine ⟨6395579101948787455518929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263719401299191637012619 6395579101948787455518929)
                  ·
                    refine ⟨4796684326461590591639197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395579101948787455518929 4796684326461590591639197)
                    ·
                      refine ⟨1798756622423096471864699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4796684326461590591639197 1798756622423096471864699)
                      ·
                        rfl

theorem cell23_3503066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_3503066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503066 prefixEnd_3503066 := by exact prefixLift 3503066
  have htrace : WordTrace (prefixWord ++ tailWord_3503066) baseStart_3503066 baseEnd_3503066 := by
    simpa [prefixWord, tailWord_3503066, baseEnd_3503066] using wordTrace_append hprefix tailTrace_3503066
  have hstable : (prefixWord ++ tailWord_3503066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503066).length < 2 ^ (prefixWord ++ tailWord_3503066).sum := by decide
  have hdescent : baseEnd_3503066 < baseStart_3503066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503079 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3503079 : Nat := 118140960795 + 3503079 * 2 ^ 59
def prefixEnd_3503079 : Nat := 4983230072969 + 3 ^ 40 * 3503079 * 2
def baseEnd_3503079 : Nat := 1798763297671604921002139

theorem tailTrace_3503079 : CollatzResearch.WordTrace tailWord_3503079 prefixEnd_3503079 1798763297671604921002139 := by
  unfold tailWord_3503079
  simp only [CollatzResearch.WordTrace]
  refine ⟨127767787675950536106944291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85178525117300357404629527 127767787675950536106944291)
  ·
    refine ⟨191651681513925804160416437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127767787675950536106944291 191651681513925804160416437)
    ·
      refine ⟨17967345141930544140039041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191651681513925804160416437 17967345141930544140039041)
      ·
        refine ⟨13475508856447908105029281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17967345141930544140039041 13475508856447908105029281)
        ·
          refine ⟨10106631642335931078771961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13475508856447908105029281 10106631642335931078771961)
          ·
            refine ⟨7579973731751948309078971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10106631642335931078771961 7579973731751948309078971)
            ·
              refine ⟨11369960597627922463618457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7579973731751948309078971 11369960597627922463618457)
              ·
                refine ⟨8527470448220941847713843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11369960597627922463618457 8527470448220941847713843)
                ·
                  refine ⟨12791205672331412771570765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8527470448220941847713843 12791205672331412771570765)
                  ·
                    refine ⟨4796702127124279789339037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12791205672331412771570765 4796702127124279789339037)
                    ·
                      refine ⟨1798763297671604921002139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4796702127124279789339037 1798763297671604921002139)
                      ·
                        rfl

theorem cell23_3503079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3503079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503079 prefixEnd_3503079 := by exact prefixLift 3503079
  have htrace : WordTrace (prefixWord ++ tailWord_3503079) baseStart_3503079 baseEnd_3503079 := by
    simpa [prefixWord, tailWord_3503079, baseEnd_3503079] using wordTrace_append hprefix tailTrace_3503079
  have hstable : (prefixWord ++ tailWord_3503079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503079).length < 2 ^ (prefixWord ++ tailWord_3503079).sum := by decide
  have hdescent : baseEnd_3503079 < baseStart_3503079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503112 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_3503112 : Nat := 118140960795 + 3503112 * 2 ^ 59
def prefixEnd_3503112 : Nat := 4983230072969 + 3 ^ 40 * 3503112 * 2
def baseEnd_3503112 : Nat := 599593414177734430629829

theorem tailTrace_3503112 : CollatzResearch.WordTrace tailWord_3503112 prefixEnd_3503112 599593414177734430629829 := by
  unfold tailWord_3503112
  simp only [CollatzResearch.WordTrace]
  refine ⟨63884495642415491371447795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85179327523220655161930393 63884495642415491371447795)
  ·
    refine ⟨95826743463623237057171693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63884495642415491371447795 95826743463623237057171693)
    ·
      refine ⟨35935028798858713896439385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95826743463623237057171693 35935028798858713896439385)
      ·
        refine ⟨26951271599144035422329539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35935028798858713896439385 26951271599144035422329539)
        ·
          refine ⟨40426907398716053133494309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26951271599144035422329539 40426907398716053133494309)
          ·
            refine ⟨7580045137259259962530183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40426907398716053133494309 7580045137259259962530183)
            ·
              refine ⟨11370067705888889943795275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580045137259259962530183 11370067705888889943795275)
              ·
                refine ⟨17055101558833334915692913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11370067705888889943795275 17055101558833334915692913)
                ·
                  refine ⟨12791326169125001186769685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17055101558833334915692913 12791326169125001186769685)
                  ·
                    refine ⟨599593414177734430629829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12791326169125001186769685 599593414177734430629829)
                    ·
                      rfl

theorem cell23_3503112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_3503112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503112 prefixEnd_3503112 := by exact prefixLift 3503112
  have htrace : WordTrace (prefixWord ++ tailWord_3503112) baseStart_3503112 baseEnd_3503112 := by
    simpa [prefixWord, tailWord_3503112, baseEnd_3503112] using wordTrace_append hprefix tailTrace_3503112
  have hstable : (prefixWord ++ tailWord_3503112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503112).length < 2 ^ (prefixWord ++ tailWord_3503112).sum := by decide
  have hdescent : baseEnd_3503112 < baseStart_3503112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503140 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3503140 : Nat := 118140960795 + 3503140 * 2 ^ 59
def prefixEnd_3503140 : Nat := 4983230072969 + 3 ^ 40 * 3503140 * 2
def baseEnd_3503140 : Nat := 1798794619991529182339359

theorem tailTrace_3503140 : CollatzResearch.WordTrace tailWord_3503140 prefixEnd_3503140 1798794619991529182339359 := by
  unfold tailWord_3503140
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885006264364771762457437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85180008352486362349943249 63885006264364771762457437)
  ·
    refine ⟨23956877349136789410921539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63885006264364771762457437 23956877349136789410921539)
    ·
      refine ⟨35935316023705184116382309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23956877349136789410921539 35935316023705184116382309)
      ·
        refine ⟨6737871754444722021821683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35935316023705184116382309 6737871754444722021821683)
        ·
          refine ⟨10106807631667083032732525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6737871754444722021821683 10106807631667083032732525)
          ·
            refine ⟨3790052861875156137274697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10106807631667083032732525 3790052861875156137274697)
            ·
              refine ⟨2842539646406367102956023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790052861875156137274697 2842539646406367102956023)
              ·
                refine ⟨4263809469609550654434035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842539646406367102956023 4263809469609550654434035)
                ·
                  refine ⟨6395714204414325981651053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4263809469609550654434035 6395714204414325981651053)
                  ·
                    refine ⟨2398392826655372243119145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6395714204414325981651053 2398392826655372243119145)
                    ·
                      refine ⟨1798794619991529182339359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398392826655372243119145 1798794619991529182339359)
                      ·
                        rfl

theorem cell23_3503140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3503140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503140 prefixEnd_3503140 := by exact prefixLift 3503140
  have htrace : WordTrace (prefixWord ++ tailWord_3503140) baseStart_3503140 baseEnd_3503140 := by
    simpa [prefixWord, tailWord_3503140, baseEnd_3503140] using wordTrace_append hprefix tailTrace_3503140
  have hstable : (prefixWord ++ tailWord_3503140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503140).length < 2 ^ (prefixWord ++ tailWord_3503140).sum := by decide
  have hdescent : baseEnd_3503140 < baseStart_3503140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503152 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_3503152 : Nat := 118140960795 + 3503152 * 2 ^ 59
def prefixEnd_3503152 : Nat := 4983230072969 + 3 ^ 40 * 3503152 * 2
def baseEnd_3503152 : Nat := 1798800781759383135389303

theorem tailTrace_3503152 : CollatzResearch.WordTrace tailWord_3503152 prefixEnd_3503152 1798800781759383135389303 := by
  unfold tailWord_3503152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885225102343034787175855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85180300136457379716234473 63885225102343034787175855)
  ·
    refine ⟨95827837653514552180763783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63885225102343034787175855 95827837653514552180763783)
    ·
      refine ⟨143741756480271828271145675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95827837653514552180763783 143741756480271828271145675)
      ·
        refine ⟨215612634720407742406718513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143741756480271828271145675 215612634720407742406718513)
        ·
          refine ⟨161709476040305806805038885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215612634720407742406718513 161709476040305806805038885)
          ·
            refine ⟨30320526757557338775944791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161709476040305806805038885 30320526757557338775944791)
            ·
              refine ⟨45480790136336008163917187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30320526757557338775944791 45480790136336008163917187)
              ·
                refine ⟨68221185204504012245875781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45480790136336008163917187 68221185204504012245875781)
                ·
                  refine ⟨12791472225844502296101709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68221185204504012245875781 12791472225844502296101709)
                  ·
                    refine ⟨4796802084691688361038141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12791472225844502296101709 4796802084691688361038141)
                    ·
                      refine ⟨1798800781759383135389303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4796802084691688361038141 1798800781759383135389303)
                      ·
                        rfl

theorem cell23_3503152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_3503152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503152 prefixEnd_3503152 := by exact prefixLift 3503152
  have htrace : WordTrace (prefixWord ++ tailWord_3503152) baseStart_3503152 baseEnd_3503152 := by
    simpa [prefixWord, tailWord_3503152, baseEnd_3503152] using wordTrace_append hprefix tailTrace_3503152
  have hstable : (prefixWord ++ tailWord_3503152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503152).length < 2 ^ (prefixWord ++ tailWord_3503152).sum := by decide
  have hdescent : baseEnd_3503152 < baseStart_3503152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503192 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_3503192 : Nat := 118140960795 + 3503192 * 2 ^ 59
def prefixEnd_3503192 : Nat := 4983230072969 + 3 ^ 40 * 3503192 * 2
def baseEnd_3503192 : Nat := 1798821320985562978889119

theorem tailTrace_3503192 : CollatzResearch.WordTrace tailWord_3503192 prefixEnd_3503192 1798821320985562978889119 := by
  unfold tailWord_3503192
  simp only [CollatzResearch.WordTrace]
  refine ⟨63885954562270578202903915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85181272749694104270538553 63885954562270578202903915)
  ·
    refine ⟨95828931843405867304355873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63885954562270578202903915 95828931843405867304355873)
    ·
      refine ⟨71871698882554400478266905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95828931843405867304355873 71871698882554400478266905)
      ·
        refine ⟨53903774161915800358700179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71871698882554400478266905 53903774161915800358700179)
        ·
          refine ⟨80855661242873700538050269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53903774161915800358700179 80855661242873700538050269)
          ·
            refine ⟨30320872966077637701768851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80855661242873700538050269 30320872966077637701768851)
            ·
              refine ⟨45481309449116456552653277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30320872966077637701768851 45481309449116456552653277)
              ·
                refine ⟨17055491043418671207244979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45481309449116456552653277 17055491043418671207244979)
                ·
                  refine ⟨25583236565128006810867469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17055491043418671207244979 25583236565128006810867469)
                  ·
                    refine ⟨9593713711923002554075301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25583236565128006810867469 9593713711923002554075301)
                    ·
                      refine ⟨1798821320985562978889119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9593713711923002554075301 1798821320985562978889119)
                      ·
                        rfl

theorem cell23_3503192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_3503192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503192 prefixEnd_3503192 := by exact prefixLift 3503192
  have htrace : WordTrace (prefixWord ++ tailWord_3503192) baseStart_3503192 baseEnd_3503192 := by
    simpa [prefixWord, tailWord_3503192, baseEnd_3503192] using wordTrace_append hprefix tailTrace_3503192
  have hstable : (prefixWord ++ tailWord_3503192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503192).length < 2 ^ (prefixWord ++ tailWord_3503192).sum := by decide
  have hdescent : baseEnd_3503192 < baseStart_3503192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503209 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_3503209 : Nat := 118140960795 + 3503209 * 2 ^ 59
def prefixEnd_3503209 : Nat := 4983230072969 + 3 ^ 40 * 3503209 * 2
def baseEnd_3503209 : Nat := 1798830050156689412376541

theorem tailTrace_3503209 : CollatzResearch.WordTrace tailWord_3503209 prefixEnd_3503209 1798830050156689412376541 := by
  unfold tailWord_3503209
  simp only [CollatzResearch.WordTrace]
  refine ⟨127772529165479568309176681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85181686110319712206117787 127772529165479568309176681)
  ·
    refine ⟨95829396874109676231882511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127772529165479568309176681 95829396874109676231882511)
    ·
      refine ⟨143744095311164514347823767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95829396874109676231882511 143744095311164514347823767)
      ·
        refine ⟨215616142966746771521735651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143744095311164514347823767 215616142966746771521735651)
        ·
          refine ⟨323424214450120157282603477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215616142966746771521735651 323424214450120157282603477)
          ·
            refine ⟨7580255026174691186311019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 323424214450120157282603477 7580255026174691186311019)
            ·
              refine ⟨11370382539262036779466529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580255026174691186311019 11370382539262036779466529)
              ·
                refine ⟨8527786904446527584599897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11370382539262036779466529 8527786904446527584599897)
                ·
                  refine ⟨6395840178334895688449923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527786904446527584599897 6395840178334895688449923)
                  ·
                    refine ⟨9593760267502343532674885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6395840178334895688449923 9593760267502343532674885)
                    ·
                      refine ⟨1798830050156689412376541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9593760267502343532674885 1798830050156689412376541)
                      ·
                        rfl

theorem cell23_3503209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_3503209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503209 prefixEnd_3503209 := by exact prefixLift 3503209
  have htrace : WordTrace (prefixWord ++ tailWord_3503209) baseStart_3503209 baseEnd_3503209 := by
    simpa [prefixWord, tailWord_3503209, baseEnd_3503209] using wordTrace_append hprefix tailTrace_3503209
  have hstable : (prefixWord ++ tailWord_3503209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503209).length < 2 ^ (prefixWord ++ tailWord_3503209).sum := by decide
  have hdescent : baseEnd_3503209 < baseStart_3503209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503229 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_3503229 : Nat := 118140960795 + 3503229 * 2 ^ 59
def prefixEnd_3503229 : Nat := 4983230072969 + 3 ^ 40 * 3503229 * 2
def baseEnd_3503229 : Nat := 1798840319769779334126449

theorem tailTrace_3503229 : CollatzResearch.WordTrace tailWord_3503229 prefixEnd_3503229 1798840319769779334126449 := by
  unfold tailWord_3503229
  simp only [CollatzResearch.WordTrace]
  refine ⟨127773258625407111724904741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85182172416938074483269827 127773258625407111724904741)
  ·
    refine ⟨23957485992263833448419639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127773258625407111724904741 23957485992263833448419639)
    ·
      refine ⟨35936228988395750172629459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23957485992263833448419639 35936228988395750172629459)
      ·
        refine ⟨53904343482593625258944189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35936228988395750172629459 53904343482593625258944189)
        ·
          refine ⟨20214128805972609472104071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53904343482593625258944189 20214128805972609472104071)
          ·
            refine ⟨30321193208958914208156107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20214128805972609472104071 30321193208958914208156107)
            ·
              refine ⟨45481789813438371312234161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30321193208958914208156107 45481789813438371312234161)
              ·
                refine ⟨34111342360078778484175621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45481789813438371312234161 34111342360078778484175621)
                ·
                  refine ⟨6395876692514770965782929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34111342360078778484175621 6395876692514770965782929)
                  ·
                    refine ⟨4796907519386078224337197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395876692514770965782929 4796907519386078224337197)
                    ·
                      refine ⟨1798840319769779334126449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4796907519386078224337197 1798840319769779334126449)
                      ·
                        rfl

theorem cell23_3503229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_3503229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503229 prefixEnd_3503229 := by exact prefixLift 3503229
  have htrace : WordTrace (prefixWord ++ tailWord_3503229) baseStart_3503229 baseEnd_3503229 := by
    simpa [prefixWord, tailWord_3503229, baseEnd_3503229] using wordTrace_append hprefix tailTrace_3503229
  have hstable : (prefixWord ++ tailWord_3503229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503229).length < 2 ^ (prefixWord ++ tailWord_3503229).sum := by decide
  have hdescent : baseEnd_3503229 < baseStart_3503229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503246 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3503246 : Nat := 118140960795 + 3503246 * 2 ^ 59
def prefixEnd_3503246 : Nat := 4983230072969 + 3 ^ 40 * 3503246 * 2
def baseEnd_3503246 : Nat := 1798849048940905767613871

theorem tailTrace_3503246 : CollatzResearch.WordTrace tailWord_3503246 prefixEnd_3503246 1798849048940905767613871 := by
  unfold tailWord_3503246
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971734833293190453534199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85182585777563682418849061 15971734833293190453534199)
  ·
    refine ⟨23957602249939785680301299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15971734833293190453534199 23957602249939785680301299)
    ·
      refine ⟨35936403374909678520451949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23957602249939785680301299 35936403374909678520451949)
      ·
        refine ⟨13476151265591129445169481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35936403374909678520451949 13476151265591129445169481)
        ·
          refine ⟨10107113449193347083877111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13476151265591129445169481 10107113449193347083877111)
          ·
            refine ⟨15160670173790020625815667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107113449193347083877111 15160670173790020625815667)
            ·
              refine ⟨22741005260685030938723501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15160670173790020625815667 22741005260685030938723501)
              ·
                refine ⟨8527876972756886602021313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22741005260685030938723501 8527876972756886602021313)
                ·
                  refine ⟨6395907729567664951515985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8527876972756886602021313 6395907729567664951515985)
                  ·
                    refine ⟨4796930797175748713636989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6395907729567664951515985 4796930797175748713636989)
                    ·
                      refine ⟨1798849048940905767613871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4796930797175748713636989 1798849048940905767613871)
                      ·
                        rfl

theorem cell23_3503246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3503246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503246 prefixEnd_3503246 := by exact prefixLift 3503246
  have htrace : WordTrace (prefixWord ++ tailWord_3503246) baseStart_3503246 baseEnd_3503246 := by
    simpa [prefixWord, tailWord_3503246, baseEnd_3503246] using wordTrace_append hprefix tailTrace_3503246
  have hstable : (prefixWord ++ tailWord_3503246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503246).length < 2 ^ (prefixWord ++ tailWord_3503246).sum := by decide
  have hdescent : baseEnd_3503246 < baseStart_3503246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503299 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 8, 2]
def baseStart_3503299 : Nat := 118140960795 + 3503299 * 2 ^ 59
def prefixEnd_3503299 : Nat := 4983230072969 + 3 ^ 40 * 3503299 * 2
def baseEnd_3503299 : Nat := 1798876263415594060251127

theorem tailTrace_3503299 : CollatzResearch.WordTrace tailWord_3503299 prefixEnd_3503299 1798876263415594060251127 := by
  unfold tailWord_3503299
  simp only [CollatzResearch.WordTrace]
  refine ⟨127775811735153513679952951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85183874490102342453301967 127775811735153513679952951)
  ·
    refine ⟨191663717602730270519929427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127775811735153513679952951 191663717602730270519929427)
    ·
      refine ⟨287495576404095405779894141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191663717602730270519929427 287495576404095405779894141)
      ·
        refine ⟨107810841151535777167460303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287495576404095405779894141 107810841151535777167460303)
        ·
          refine ⟨161716261727303665751190455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107810841151535777167460303 161716261727303665751190455)
          ·
            refine ⟨242574392590955498626785683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161716261727303665751190455 242574392590955498626785683)
            ·
              refine ⟨363861588886433247940178525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242574392590955498626785683 363861588886433247940178525)
              ·
                refine ⟨136448095832412467977566947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363861588886433247940178525 136448095832412467977566947)
                ·
                  refine ⟨204672143748618701966350421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136448095832412467977566947 204672143748618701966350421)
                  ·
                    refine ⟨2398501684554125413668169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 204672143748618701966350421 2398501684554125413668169)
                    ·
                      refine ⟨1798876263415594060251127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398501684554125413668169 1798876263415594060251127)
                      ·
                        rfl

theorem cell23_3503299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_3503299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503299 prefixEnd_3503299 := by exact prefixLift 3503299
  have htrace : WordTrace (prefixWord ++ tailWord_3503299) baseStart_3503299 baseEnd_3503299 := by
    simpa [prefixWord, tailWord_3503299, baseEnd_3503299] using wordTrace_append hprefix tailTrace_3503299
  have hstable : (prefixWord ++ tailWord_3503299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503299).length < 2 ^ (prefixWord ++ tailWord_3503299).sum := by decide
  have hdescent : baseEnd_3503299 < baseStart_3503299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503343 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 1, 6]
def baseStart_3503343 : Nat := 118140960795 + 3503343 * 2 ^ 59
def prefixEnd_3503343 : Nat := 4983230072969 + 3 ^ 40 * 3503343 * 2
def baseEnd_3503343 : Nat := 599632952188130629366975

theorem tailTrace_3503343 : CollatzResearch.WordTrace tailWord_3503343 prefixEnd_3503343 599632952188130629366975 := by
  unfold tailWord_3503343
  simp only [CollatzResearch.WordTrace]
  refine ⟨127777416546994109194554683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85184944364662739463036455 127777416546994109194554683)
  ·
    refine ⟨191666124820491163791832025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127777416546994109194554683 191666124820491163791832025)
    ·
      refine ⟨143749593615368372843874019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191666124820491163791832025 143749593615368372843874019)
      ·
        refine ⟨215624390423052559265811029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143749593615368372843874019 215624390423052559265811029)
        ·
          refine ⟨2526848325270147178896223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 215624390423052559265811029 2526848325270147178896223)
          ·
            refine ⟨3790272487905220768344335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2526848325270147178896223 3790272487905220768344335)
            ·
              refine ⟨5685408731857831152516503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790272487905220768344335 5685408731857831152516503)
              ·
                refine ⟨8528113097786746728774755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685408731857831152516503 8528113097786746728774755)
                ·
                  refine ⟨12792169646680120093162133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528113097786746728774755 12792169646680120093162133)
                  ·
                    refine ⟨599632952188130629366975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12792169646680120093162133 599632952188130629366975)
                    ·
                      rfl

theorem cell23_3503343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 1, 6].length) (baseStart_3503343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503343 prefixEnd_3503343 := by exact prefixLift 3503343
  have htrace : WordTrace (prefixWord ++ tailWord_3503343) baseStart_3503343 baseEnd_3503343 := by
    simpa [prefixWord, tailWord_3503343, baseEnd_3503343] using wordTrace_append hprefix tailTrace_3503343
  have hstable : (prefixWord ++ tailWord_3503343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503343).length < 2 ^ (prefixWord ++ tailWord_3503343).sum := by decide
  have hdescent : baseEnd_3503343 < baseStart_3503343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503346 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3503346 : Nat := 118140960795 + 3503346 * 2 ^ 59
def prefixEnd_3503346 : Nat := 4983230072969 + 3 ^ 40 * 3503346 * 2
def baseEnd_3503346 : Nat := 1798900397006355376363411

theorem tailTrace_3503346 : CollatzResearch.WordTrace tailWord_3503346 prefixEnd_3503346 1798900397006355376363411 := by
  unfold tailWord_3503346
  simp only [CollatzResearch.WordTrace]
  refine ⟨31944381491495810176728473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85185017310655493804609261 31944381491495810176728473)
  ·
    refine ⟨23958286118621857632546355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31944381491495810176728473 23958286118621857632546355)
    ·
      refine ⟨35937429177932786448819533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23958286118621857632546355 35937429177932786448819533)
      ·
        refine ⟨13476535941724794918307325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35937429177932786448819533 13476535941724794918307325)
        ·
          refine ⟨5053700978146798094365247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13476535941724794918307325 5053700978146798094365247)
          ·
            refine ⟨7580551467220197141547871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5053700978146798094365247 7580551467220197141547871)
            ·
              refine ⟨11370827200830295712321807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580551467220197141547871 11370827200830295712321807)
              ·
                refine ⟨17056240801245443568482711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11370827200830295712321807 17056240801245443568482711)
                ·
                  refine ⟨25584361201868165352724067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17056240801245443568482711 25584361201868165352724067)
                  ·
                    refine ⟨38376541802802248029086101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25584361201868165352724067 38376541802802248029086101)
                    ·
                      refine ⟨1798900397006355376363411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38376541802802248029086101 1798900397006355376363411)
                      ·
                        rfl

theorem cell23_3503346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3503346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503346 prefixEnd_3503346 := by exact prefixLift 3503346
  have htrace : WordTrace (prefixWord ++ tailWord_3503346) baseStart_3503346 baseEnd_3503346 := by
    simpa [prefixWord, tailWord_3503346, baseEnd_3503346] using wordTrace_append hprefix tailTrace_3503346
  have hstable : (prefixWord ++ tailWord_3503346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503346).length < 2 ^ (prefixWord ++ tailWord_3503346).sum := by decide
  have hdescent : baseEnd_3503346 < baseStart_3503346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503383 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3503383 : Nat := 118140960795 + 3503383 * 2 ^ 59
def prefixEnd_3503383 : Nat := 4983230072969 + 3 ^ 40 * 3503383 * 2
def baseEnd_3503383 : Nat := 1798919395790571731600741

theorem tailTrace_3503383 : CollatzResearch.WordTrace tailWord_3503383 prefixEnd_3503383 1798919395790571731600741 := by
  unfold tailWord_3503383
  simp only [CollatzResearch.WordTrace]
  refine ⟨127778875466849196026010803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85185916977899464017340535 127778875466849196026010803)
  ·
    refine ⟨191668313200273794039016205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127778875466849196026010803 191668313200273794039016205)
    ·
      refine ⟨71875617450102672764631077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191668313200273794039016205 71875617450102672764631077)
      ·
        refine ⟨13476678271894251143368327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71875617450102672764631077 13476678271894251143368327)
        ·
          refine ⟨20215017407841376715052491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13476678271894251143368327 20215017407841376715052491)
          ·
            refine ⟨30322526111762065072578737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20215017407841376715052491 30322526111762065072578737)
            ·
              refine ⟨22741894583821548804434053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30322526111762065072578737 22741894583821548804434053)
              ·
                refine ⟨4264105234466540400831385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22741894583821548804434053 4264105234466540400831385)
                ·
                  refine ⟨3198078925849905300623539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264105234466540400831385 3198078925849905300623539)
                  ·
                    refine ⟨4797118388774857950935309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3198078925849905300623539 4797118388774857950935309)
                    ·
                      refine ⟨1798919395790571731600741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797118388774857950935309 1798919395790571731600741)
                      ·
                        rfl

theorem cell23_3503383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3503383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503383 prefixEnd_3503383 := by exact prefixLift 3503383
  have htrace : WordTrace (prefixWord ++ tailWord_3503383) baseStart_3503383 baseEnd_3503383 := by
    simpa [prefixWord, tailWord_3503383, baseEnd_3503383] using wordTrace_append hprefix tailTrace_3503383
  have hstable : (prefixWord ++ tailWord_3503383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503383).length < 2 ^ (prefixWord ++ tailWord_3503383).sum := by decide
  have hdescent : baseEnd_3503383 < baseStart_3503383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503400 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3503400 : Nat := 118140960795 + 3503400 * 2 ^ 59
def prefixEnd_3503400 : Nat := 4983230072969 + 3 ^ 40 * 3503400 * 2
def baseEnd_3503400 : Nat := 1798928124961698165088163

theorem tailTrace_3503400 : CollatzResearch.WordTrace tailWord_3503400 prefixEnd_3503400 1798928124961698165088163 := by
  unfold tailWord_3503400
  simp only [CollatzResearch.WordTrace]
  refine ⟨63889747753893803964689827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85186330338525071952919769 63889747753893803964689827)
  ·
    refine ⟨95834621630840705947034741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63889747753893803964689827 95834621630840705947034741)
    ·
      refine ⟨8984495777891316182534507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95834621630840705947034741 8984495777891316182534507)
      ·
        refine ⟨13476743666836974273801761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984495777891316182534507 13476743666836974273801761)
        ·
          refine ⟨10107557750127730705351321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13476743666836974273801761 10107557750127730705351321)
          ·
            refine ⟨7580668312595798029013491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10107557750127730705351321 7580668312595798029013491)
            ·
              refine ⟨11371002468893697043520237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580668312595798029013491 11371002468893697043520237)
              ·
                refine ⟨4264125925835136391320089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11371002468893697043520237 4264125925835136391320089)
                ·
                  refine ⟨3198094444376352293490067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264125925835136391320089 3198094444376352293490067)
                  ·
                    refine ⟨4797141666564528440235101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3198094444376352293490067 4797141666564528440235101)
                    ·
                      refine ⟨1798928124961698165088163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797141666564528440235101 1798928124961698165088163)
                      ·
                        rfl

theorem cell23_3503400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3503400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503400 prefixEnd_3503400 := by exact prefixLift 3503400
  have htrace : WordTrace (prefixWord ++ tailWord_3503400) baseStart_3503400 baseEnd_3503400 := by
    simpa [prefixWord, tailWord_3503400, baseEnd_3503400] using wordTrace_append hprefix tailTrace_3503400
  have hstable : (prefixWord ++ tailWord_3503400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503400).length < 2 ^ (prefixWord ++ tailWord_3503400).sum := by decide
  have hdescent : baseEnd_3503400 < baseStart_3503400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503410 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2]
def baseStart_3503410 : Nat := 118140960795 + 3503410 * 2 ^ 59
def prefixEnd_3503410 : Nat := 4983230072969 + 3 ^ 40 * 3503410 * 2
def baseEnd_3503410 : Nat := 1798933259768243125963117

theorem tailTrace_3503410 : CollatzResearch.WordTrace tailWord_3503410 prefixEnd_3503410 1798933259768243125963117 := by
  unfold tailWord_3503410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31944965059437844909310921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85186573491834253091495789 31944965059437844909310921)
  ·
    refine ⟨23958723794578383681983191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31944965059437844909310921 23958723794578383681983191)
    ·
      refine ⟨35938085691867575522974787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23958723794578383681983191 35938085691867575522974787)
      ·
        refine ⟨53907128537801363284462181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35938085691867575522974787 53907128537801363284462181)
        ·
          refine ⟨10107586600837755615836659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53907128537801363284462181 10107586600837755615836659)
          ·
            refine ⟨15161379901256633423754989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107586600837755615836659 15161379901256633423754989)
            ·
              refine ⟨5685517462971237533908121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15161379901256633423754989 5685517462971237533908121)
              ·
                refine ⟨4264138097228428150431091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685517462971237533908121 4264138097228428150431091)
                ·
                  refine ⟨6396207145842642225646637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264138097228428150431091 6396207145842642225646637)
                  ·
                    refine ⟨2398577679690990834617489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6396207145842642225646637 2398577679690990834617489)
                    ·
                      refine ⟨1798933259768243125963117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398577679690990834617489 1798933259768243125963117)
                      ·
                        rfl

theorem cell23_3503410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_3503410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503410 prefixEnd_3503410 := by exact prefixLift 3503410
  have htrace : WordTrace (prefixWord ++ tailWord_3503410) baseStart_3503410 baseEnd_3503410 := by
    simpa [prefixWord, tailWord_3503410, baseEnd_3503410] using wordTrace_append hprefix tailTrace_3503410
  have hstable : (prefixWord ++ tailWord_3503410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503410).length < 2 ^ (prefixWord ++ tailWord_3503410).sum := by decide
  have hdescent : baseEnd_3503410 < baseStart_3503410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503423 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 1, 4, 2]
def baseStart_3503423 : Nat := 118140960795 + 3503423 * 2 ^ 59
def prefixEnd_3503423 : Nat := 4983230072969 + 3 ^ 40 * 3503423 * 2
def baseEnd_3503423 : Nat := 1798939935016751575100557

theorem tailTrace_3503423 : CollatzResearch.WordTrace tailWord_3503423 prefixEnd_3503423 1798939935016751575100557 := by
  unfold tailWord_3503423
  simp only [CollatzResearch.WordTrace]
  refine ⟨127780334386704282857466923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85186889591136188571644615 127780334386704282857466923)
  ·
    refine ⟨191670501580056424286200385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127780334386704282857466923 191670501580056424286200385)
    ·
      refine ⟨143752876185042318214650289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191670501580056424286200385 143752876185042318214650289)
      ·
        refine ⟨107814657138781738660987717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143752876185042318214650289 107814657138781738660987717)
        ·
          refine ⟨20215248213521575998935197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107814657138781738660987717 20215248213521575998935197)
          ·
            refine ⟨7580718080070590999600699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20215248213521575998935197 7580718080070590999600699)
            ·
              refine ⟨11371077120105886499401049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7580718080070590999600699 11371077120105886499401049)
              ·
                refine ⟨8528307840079414874550787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11371077120105886499401049 8528307840079414874550787)
                ·
                  refine ⟨12792461760119122311826181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528307840079414874550787 12792461760119122311826181)
                  ·
                    refine ⟨2398586580022335433467409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12792461760119122311826181 2398586580022335433467409)
                    ·
                      refine ⟨1798939935016751575100557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398586580022335433467409 1798939935016751575100557)
                      ·
                        rfl

theorem cell23_3503423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_3503423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503423 prefixEnd_3503423 := by exact prefixLift 3503423
  have htrace : WordTrace (prefixWord ++ tailWord_3503423) baseStart_3503423 baseEnd_3503423 := by
    simpa [prefixWord, tailWord_3503423, baseEnd_3503423] using wordTrace_append hprefix tailTrace_3503423
  have hstable : (prefixWord ++ tailWord_3503423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503423).length < 2 ^ (prefixWord ++ tailWord_3503423).sum := by decide
  have hdescent : baseEnd_3503423 < baseStart_3503423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503440 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 2, 2, 2]
def baseStart_3503440 : Nat := 118140960795 + 3503440 * 2 ^ 59
def prefixEnd_3503440 : Nat := 4983230072969 + 3 ^ 40 * 3503440 * 2
def baseEnd_3503440 : Nat := 1798948664187878008587979

theorem tailTrace_3503440 : CollatzResearch.WordTrace tailWord_3503440 prefixEnd_3503440 1798948664187878008587979 := by
  unfold tailWord_3503440
  simp only [CollatzResearch.WordTrace]
  refine ⟨63890477213821347380417887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85187302951761796507223849 63890477213821347380417887)
  ·
    refine ⟨95835715820732021070626831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63890477213821347380417887 95835715820732021070626831)
    ·
      refine ⟨143753573731098031605940247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95835715820732021070626831 143753573731098031605940247)
      ·
        refine ⟨215630360596647047408910371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143753573731098031605940247 215630360596647047408910371)
        ·
          refine ⟨323445540894970571113365557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215630360596647047408910371 323445540894970571113365557)
          ·
            refine ⟨30323019458903491041878021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 323445540894970571113365557 30323019458903491041878021)
            ·
              refine ⟨5685566148544404570352129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30323019458903491041878021 5685566148544404570352129)
              ·
                refine ⟨4264174611408303427764097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685566148544404570352129 4264174611408303427764097)
                ·
                  refine ⟨3198130958556227570823073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264174611408303427764097 3198130958556227570823073)
                  ·
                    refine ⟨2398598218917170678117305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3198130958556227570823073 2398598218917170678117305)
                    ·
                      refine ⟨1798948664187878008587979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398598218917170678117305 1798948664187878008587979)
                      ·
                        rfl

theorem cell23_3503440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2, 2, 2].length) (baseStart_3503440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503440 prefixEnd_3503440 := by exact prefixLift 3503440
  have htrace : WordTrace (prefixWord ++ tailWord_3503440) baseStart_3503440 baseEnd_3503440 := by
    simpa [prefixWord, tailWord_3503440, baseEnd_3503440] using wordTrace_append hprefix tailTrace_3503440
  have hstable : (prefixWord ++ tailWord_3503440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503440).length < 2 ^ (prefixWord ++ tailWord_3503440).sum := by decide
  have hdescent : baseEnd_3503440 < baseStart_3503440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503456 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_3503456 : Nat := 118140960795 + 3503456 * 2 ^ 59
def prefixEnd_3503456 : Nat := 4983230072969 + 3 ^ 40 * 3503456 * 2
def baseEnd_3503456 : Nat := 1798956879878349945987905

theorem tailTrace_3503456 : CollatzResearch.WordTrace tailWord_3503456 prefixEnd_3503456 1798956879878349945987905 := by
  unfold tailWord_3503456
  simp only [CollatzResearch.WordTrace]
  refine ⟨63890768997792364746709111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85187691997056486328945481 63890768997792364746709111)
  ·
    refine ⟨95836153496688547120063667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63890768997792364746709111 95836153496688547120063667)
    ·
      refine ⟨143754230245032820680095501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95836153496688547120063667 143754230245032820680095501)
      ·
        refine ⟨53907836341887307755035813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143754230245032820680095501 53907836341887307755035813)
        ·
          refine ⟨10107719314103870204069215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53907836341887307755035813 10107719314103870204069215)
          ·
            refine ⟨15161578971155805306103823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107719314103870204069215 15161578971155805306103823)
            ·
              refine ⟨22742368456733707959155735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15161578971155805306103823 22742368456733707959155735)
              ·
                refine ⟨34113552685100561938733603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22742368456733707959155735 34113552685100561938733603)
                ·
                  refine ⟨51170329027650842908100405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34113552685100561938733603 51170329027650842908100405)
                  ·
                    refine ⟨4797218346342266522634413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51170329027650842908100405 4797218346342266522634413)
                    ·
                      refine ⟨1798956879878349945987905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797218346342266522634413 1798956879878349945987905)
                      ·
                        rfl

theorem cell23_3503456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_3503456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503456 prefixEnd_3503456 := by exact prefixLift 3503456
  have htrace : WordTrace (prefixWord ++ tailWord_3503456) baseStart_3503456 baseEnd_3503456 := by
    simpa [prefixWord, tailWord_3503456, baseEnd_3503456] using wordTrace_append hprefix tailTrace_3503456
  have hstable : (prefixWord ++ tailWord_3503456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503456).length < 2 ^ (prefixWord ++ tailWord_3503456).sum := by decide
  have hdescent : baseEnd_3503456 < baseStart_3503456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503490 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3503490 : Nat := 118140960795 + 3503490 * 2 ^ 59
def prefixEnd_3503490 : Nat := 4983230072969 + 3 ^ 40 * 3503490 * 2
def baseEnd_3503490 : Nat := 1798974338220602812962749

theorem tailTrace_3503490 : CollatzResearch.WordTrace tailWord_3503490 prefixEnd_3503490 1798974338220602812962749 := by
  unfold tailWord_3503490
  simp only [CollatzResearch.WordTrace]
  refine ⟨31945694519365388325038981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85188518718307702200103949 31945694519365388325038981)
  ·
    refine ⟨5989817722381010310944809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31945694519365388325038981 5989817722381010310944809)
    ·
      refine ⟨4492363291785757733208607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5989817722381010310944809 4492363291785757733208607)
      ·
        refine ⟨6738544937678636599812911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492363291785757733208607 6738544937678636599812911)
        ·
          refine ⟨10107817406517954899719367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6738544937678636599812911 10107817406517954899719367)
          ·
            refine ⟨15161726109776932349579051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107817406517954899719367 15161726109776932349579051)
            ·
              refine ⟨22742589164665398524368577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15161726109776932349579051 22742589164665398524368577)
              ·
                refine ⟨17056941873499048893276433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22742589164665398524368577 17056941873499048893276433)
                ·
                  refine ⟨12792706405124286669957325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17056941873499048893276433 12792706405124286669957325)
                  ·
                    refine ⟨4797264901921607501233997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12792706405124286669957325 4797264901921607501233997)
                    ·
                      refine ⟨1798974338220602812962749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797264901921607501233997 1798974338220602812962749)
                      ·
                        rfl

theorem cell23_3503490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3503490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503490 prefixEnd_3503490 := by exact prefixLift 3503490
  have htrace : WordTrace (prefixWord ++ tailWord_3503490) baseStart_3503490 baseEnd_3503490 := by
    simpa [prefixWord, tailWord_3503490, baseEnd_3503490] using wordTrace_append hprefix tailTrace_3503490
  have hstable : (prefixWord ++ tailWord_3503490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503490).length < 2 ^ (prefixWord ++ tailWord_3503490).sum := by decide
  have hdescent : baseEnd_3503490 < baseStart_3503490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503513 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 2, 4, 2]
def baseStart_3503513 : Nat := 118140960795 + 3503513 * 2 ^ 59
def prefixEnd_3503513 : Nat := 4983230072969 + 3 ^ 40 * 3503513 * 2
def baseEnd_3503513 : Nat := 1798986148275656222975143

theorem tailTrace_3503513 : CollatzResearch.WordTrace tailWord_3503513 prefixEnd_3503513 1798986148275656222975143 := by
  unfold tailWord_3503513
  simp only [CollatzResearch.WordTrace]
  refine ⟨127783616956378228228243193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85189077970918818818828795 127783616956378228228243193)
  ·
    refine ⟨95837712717283671171182395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127783616956378228228243193 95837712717283671171182395)
    ·
      refine ⟨143756569075925506756773593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95837712717283671171182395 143756569075925506756773593)
      ·
        refine ⟨107817426806944130067580195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143756569075925506756773593 107817426806944130067580195)
        ·
          refine ⟨161726140210416195101370293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107817426806944130067580195 161726140210416195101370293)
          ·
            refine ⟨15161825644726518290753465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161726140210416195101370293 15161825644726518290753465)
            ·
              refine ⟨11371369233544888718065099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15161825644726518290753465 11371369233544888718065099)
              ·
                refine ⟨17057053850317333077097649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371369233544888718065099 17057053850317333077097649)
                ·
                  refine ⟨12792790387737999807823237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17057053850317333077097649 12792790387737999807823237)
                  ·
                    refine ⟨2398648197700874963966857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12792790387737999807823237 2398648197700874963966857)
                    ·
                      refine ⟨1798986148275656222975143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398648197700874963966857 1798986148275656222975143)
                      ·
                        rfl

theorem cell23_3503513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_3503513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503513 prefixEnd_3503513 := by exact prefixLift 3503513
  have htrace : WordTrace (prefixWord ++ tailWord_3503513) baseStart_3503513 baseEnd_3503513 := by
    simpa [prefixWord, tailWord_3503513, baseEnd_3503513] using wordTrace_append hprefix tailTrace_3503513
  have hstable : (prefixWord ++ tailWord_3503513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503513).length < 2 ^ (prefixWord ++ tailWord_3503513).sum := by decide
  have hdescent : baseEnd_3503513 < baseStart_3503513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503529 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_3503529 : Nat := 118140960795 + 3503529 * 2 ^ 59
def prefixEnd_3503529 : Nat := 4983230072969 + 3 ^ 40 * 3503529 * 2
def baseEnd_3503529 : Nat := 1798994363966128160375069

theorem tailTrace_3503529 : CollatzResearch.WordTrace tailWord_3503529 prefixEnd_3503529 1798994363966128160375069 := by
  unfold tailWord_3503529
  simp only [CollatzResearch.WordTrace]
  refine ⟨127784200524320262960825641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85189467016213508640550427 127784200524320262960825641)
  ·
    refine ⟨95838150393240197220619231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127784200524320262960825641 95838150393240197220619231)
    ·
      refine ⟨143757225589860295830928847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95838150393240197220619231 143757225589860295830928847)
      ·
        refine ⟨215635838384790443746393271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143757225589860295830928847 215635838384790443746393271)
        ·
          refine ⟨323453757577185665619589907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215635838384790443746393271 323453757577185665619589907)
          ·
            refine ⟨485180636365778498429384861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323453757577185665619589907 485180636365778498429384861)
            ·
              refine ⟨181942738637166936911019323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485180636365778498429384861 181942738637166936911019323)
              ·
                refine ⟨272914107955750405366528985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181942738637166936911019323 272914107955750405366528985)
                ·
                  refine ⟨204685580966812804024896739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272914107955750405366528985 204685580966812804024896739)
                  ·
                    refine ⟨307028371450219206037345109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204685580966812804024896739 307028371450219206037345109)
                    ·
                      refine ⟨1798994363966128160375069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 307028371450219206037345109 1798994363966128160375069)
                      ·
                        rfl

theorem cell23_3503529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_3503529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503529 prefixEnd_3503529 := by exact prefixLift 3503529
  have htrace : WordTrace (prefixWord ++ tailWord_3503529) baseStart_3503529 baseEnd_3503529 := by
    simpa [prefixWord, tailWord_3503529, baseEnd_3503529] using wordTrace_append hprefix tailTrace_3503529
  have hstable : (prefixWord ++ tailWord_3503529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503529).length < 2 ^ (prefixWord ++ tailWord_3503529).sum := by decide
  have hdescent : baseEnd_3503529 < baseStart_3503529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503554 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3503554 : Nat := 118140960795 + 3503554 * 2 ^ 59
def prefixEnd_3503554 : Nat := 4983230072969 + 3 ^ 40 * 3503554 * 2
def baseEnd_3503554 : Nat := 1799007200982490562562455

theorem tailTrace_3503554 : CollatzResearch.WordTrace tailWord_3503554 prefixEnd_3503554 1799007200982490562562455 := by
  unfold tailWord_3503554
  simp only [CollatzResearch.WordTrace]
  refine ⟨31946278087307423057621429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85190074899486461486990477 31946278087307423057621429)
  ·
    refine ⟨2994963570685070911652009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31946278087307423057621429 2994963570685070911652009)
    ·
      refine ⟨2246222678013803183739007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2994963570685070911652009 2246222678013803183739007)
      ·
        refine ⟨3369334017020704775608511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2246222678013803183739007 3369334017020704775608511)
        ·
          refine ⟨5054001025531057163412767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369334017020704775608511 5054001025531057163412767)
          ·
            refine ⟨7581001538296585745119151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054001025531057163412767 7581001538296585745119151)
            ·
              refine ⟨11371502307444878617678727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581001538296585745119151 11371502307444878617678727)
              ·
                refine ⟨17057253461167317926518091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11371502307444878617678727 17057253461167317926518091)
                ·
                  refine ⟨25585880191750976889777137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17057253461167317926518091 25585880191750976889777137)
                  ·
                    refine ⟨19189410143813232667332853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25585880191750976889777137 19189410143813232667332853)
                    ·
                      refine ⟨1799007200982490562562455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19189410143813232667332853 1799007200982490562562455)
                      ·
                        rfl

theorem cell23_3503554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3503554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503554 prefixEnd_3503554 := by exact prefixLift 3503554
  have htrace : WordTrace (prefixWord ++ tailWord_3503554) baseStart_3503554 baseEnd_3503554 := by
    simpa [prefixWord, tailWord_3503554, baseEnd_3503554] using wordTrace_append hprefix tailTrace_3503554
  have hstable : (prefixWord ++ tailWord_3503554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503554).length < 2 ^ (prefixWord ++ tailWord_3503554).sum := by decide
  have hdescent : baseEnd_3503554 < baseStart_3503554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503600 : List Nat := [2, 1, 1, 1, 3, 5, 3, 1, 1, 5]
def baseStart_3503600 : Nat := 118140960795 + 3503600 * 2 ^ 59
def prefixEnd_3503600 : Nat := 4983230072969 + 3 ^ 40 * 3503600 * 2
def baseEnd_3503600 : Nat := 599676940364199127529081

theorem tailTrace_3503600 : CollatzResearch.WordTrace tailWord_3503600 prefixEnd_3503600 599676940364199127529081 := by
  unfold tailWord_3503600
  simp only [CollatzResearch.WordTrace]
  refine ⟨63893395053531521043330127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85191193404708694724440169 63893395053531521043330127)
  ·
    refine ⟨95840092580297281564995191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63893395053531521043330127 95840092580297281564995191)
    ·
      refine ⟨143760138870445922347492787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95840092580297281564995191 143760138870445922347492787)
      ·
        refine ⟨215640208305668883521239181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143760138870445922347492787 215640208305668883521239181)
        ·
          refine ⟨80865078114625831320464693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215640208305668883521239181 80865078114625831320464693)
          ·
            refine ⟨7581101073246171686293565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80865078114625831320464693 7581101073246171686293565)
            ·
              refine ⟨2842912902467314382360087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7581101073246171686293565 2842912902467314382360087)
              ·
                refine ⟨4264369353700971573540131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2842912902467314382360087 4264369353700971573540131)
                ·
                  refine ⟨6396554030551457360310197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264369353700971573540131 6396554030551457360310197)
                  ·
                    refine ⟨599676940364199127529081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6396554030551457360310197 599676940364199127529081)
                    ·
                      rfl

theorem cell23_3503600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 1, 1, 5].length) (baseStart_3503600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503600 prefixEnd_3503600 := by exact prefixLift 3503600
  have htrace : WordTrace (prefixWord ++ tailWord_3503600) baseStart_3503600 baseEnd_3503600 := by
    simpa [prefixWord, tailWord_3503600, baseEnd_3503600] using wordTrace_append hprefix tailTrace_3503600
  have hstable : (prefixWord ++ tailWord_3503600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503600).length < 2 ^ (prefixWord ++ tailWord_3503600).sum := by decide
  have hdescent : baseEnd_3503600 < baseStart_3503600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503630 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_3503630 : Nat := 118140960795 + 3503630 * 2 ^ 59
def prefixEnd_3503630 : Nat := 4983230072969 + 3 ^ 40 * 3503630 * 2
def baseEnd_3503630 : Nat := 599682075170744088404035

theorem tailTrace_3503630 : CollatzResearch.WordTrace tailWord_3503630 prefixEnd_3503630 599682075170744088404035 := by
  unfold tailWord_3503630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973485537119294651281543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85191922864636238140168229 15973485537119294651281543)
  ·
    refine ⟨23960228305678941976922315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15973485537119294651281543 23960228305678941976922315)
    ·
      refine ⟨35940342458518412965383473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23960228305678941976922315 35940342458518412965383473)
      ·
        refine ⟨26955256843888809724037605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35940342458518412965383473 26955256843888809724037605)
        ·
          refine ⟨5054110658229151823257051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26955256843888809724037605 5054110658229151823257051)
          ·
            refine ⟨7581165987343727734885577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054110658229151823257051 7581165987343727734885577)
            ·
              refine ⟨5685874490507795801164183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7581165987343727734885577 5685874490507795801164183)
              ·
                refine ⟨8528811735761693701746275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685874490507795801164183 8528811735761693701746275)
                ·
                  refine ⟨12793217603642540552619413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528811735761693701746275 12793217603642540552619413)
                  ·
                    refine ⟨599682075170744088404035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12793217603642540552619413 599682075170744088404035)
                    ·
                      rfl

theorem cell23_3503630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_3503630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503630 prefixEnd_3503630 := by exact prefixLift 3503630
  have htrace : WordTrace (prefixWord ++ tailWord_3503630) baseStart_3503630 baseEnd_3503630 := by
    simpa [prefixWord, tailWord_3503630, baseEnd_3503630] using wordTrace_append hprefix tailTrace_3503630
  have hstable : (prefixWord ++ tailWord_3503630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503630).length < 2 ^ (prefixWord ++ tailWord_3503630).sum := by decide
  have hdescent : baseEnd_3503630 < baseStart_3503630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503633 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_3503633 : Nat := 118140960795 + 3503633 * 2 ^ 59
def prefixEnd_3503633 : Nat := 4983230072969 + 3 ^ 40 * 3503633 * 2
def baseEnd_3503633 : Nat := 1799047765954195753474591

theorem tailTrace_3503633 : CollatzResearch.WordTrace tailWord_3503633 prefixEnd_3503633 1799047765954195753474591 := by
  unfold tailWord_3503633
  simp only [CollatzResearch.WordTrace]
  refine ⟨127787993715943488722611553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85191995810628992481741035 127787993715943488722611553)
  ·
    refine ⟨95840995286957616541958665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127787993715943488722611553 95840995286957616541958665)
    ·
      refine ⟨71880746465218212406468999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95840995286957616541958665 71880746465218212406468999)
      ·
        refine ⟨107821119697827318609703499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71880746465218212406468999 107821119697827318609703499)
        ·
          refine ⟨161731679546740977914555249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107821119697827318609703499 161731679546740977914555249)
          ·
            refine ⟨121298759660055733435916437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161731679546740977914555249 121298759660055733435916437)
            ·
              refine ⟨5685879359065112504808583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121298759660055733435916437 5685879359065112504808583)
              ·
                refine ⟨8528819038597668757212875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685879359065112504808583 8528819038597668757212875)
                ·
                  refine ⟨12793228557896503135819313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528819038597668757212875 12793228557896503135819313)
                  ·
                    refine ⟨9594921418422377351864485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12793228557896503135819313 9594921418422377351864485)
                    ·
                      refine ⟨1799047765954195753474591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9594921418422377351864485 1799047765954195753474591)
                      ·
                        rfl

theorem cell23_3503633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_3503633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503633 prefixEnd_3503633 := by exact prefixLift 3503633
  have htrace : WordTrace (prefixWord ++ tailWord_3503633) baseStart_3503633 baseEnd_3503633 := by
    simpa [prefixWord, tailWord_3503633, baseEnd_3503633] using wordTrace_append hprefix tailTrace_3503633
  have hstable : (prefixWord ++ tailWord_3503633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503633).length < 2 ^ (prefixWord ++ tailWord_3503633).sum := by decide
  have hdescent : baseEnd_3503633 < baseStart_3503633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503637 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_3503637 : Nat := 118140960795 + 3503637 * 2 ^ 59
def prefixEnd_3503637 : Nat := 4983230072969 + 3 ^ 40 * 3503637 * 2
def baseEnd_3503637 : Nat := 1799049819876813737824573

theorem tailTrace_3503637 : CollatzResearch.WordTrace tailWord_3503637 prefixEnd_3503637 1799049819876813737824573 := by
  unfold tailWord_3503637
  simp only [CollatzResearch.WordTrace]
  refine ⟨127788139607928997405757165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85192093071952664937171443 127788139607928997405757165)
  ·
    refine ⟨47920552352973374027158937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127788139607928997405757165 47920552352973374027158937)
    ·
      refine ⟨35940414264730030520369203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47920552352973374027158937 35940414264730030520369203)
      ·
        refine ⟨53910621397095045780553805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35940414264730030520369203 53910621397095045780553805)
        ·
          refine ⟨20216483023910642167707677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53910621397095045780553805 20216483023910642167707677)
          ·
            refine ⟨7581181133966490812890379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20216483023910642167707677 7581181133966490812890379)
            ·
              refine ⟨11371771700949736219335569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581181133966490812890379 11371771700949736219335569)
              ·
                refine ⟨8528828775712302164501677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11371771700949736219335569 8528828775712302164501677)
                ·
                  refine ⟨3198310790892113311688129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8528828775712302164501677 3198310790892113311688129)
                  ·
                    refine ⟨2398733093169084983766097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3198310790892113311688129 2398733093169084983766097)
                    ·
                      refine ⟨1799049819876813737824573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398733093169084983766097 1799049819876813737824573)
                      ·
                        rfl

theorem cell23_3503637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_3503637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503637 prefixEnd_3503637 := by exact prefixLift 3503637
  have htrace : WordTrace (prefixWord ++ tailWord_3503637) baseStart_3503637 baseEnd_3503637 := by
    simpa [prefixWord, tailWord_3503637, baseEnd_3503637] using wordTrace_append hprefix tailTrace_3503637
  have hstable : (prefixWord ++ tailWord_3503637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503637).length < 2 ^ (prefixWord ++ tailWord_3503637).sum := by decide
  have hdescent : baseEnd_3503637 < baseStart_3503637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503687 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_3503687 : Nat := 118140960795 + 3503687 * 2 ^ 59
def prefixEnd_3503687 : Nat := 4983230072969 + 3 ^ 40 * 3503687 * 2
def baseEnd_3503687 : Nat := 1799075493909538542199343

theorem tailTrace_3503687 : CollatzResearch.WordTrace tailWord_3503687 prefixEnd_3503687 1799075493909538542199343 := by
  unfold tailWord_3503687
  simp only [CollatzResearch.WordTrace]
  refine ⟨127789963257747855945077315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85193308838498570630051543 127789963257747855945077315)
  ·
    refine ⟨191684944886621783917615973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127789963257747855945077315 191684944886621783917615973)
    ·
      refine ⟨35940927166241584484552995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191684944886621783917615973 35940927166241584484552995)
      ·
        refine ⟨53911390749362376726829493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35940927166241584484552995 53911390749362376726829493)
        ·
          refine ⟨5054192882752722818140265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53911390749362376726829493 5054192882752722818140265)
          ·
            refine ⟨3790644662064542113605199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054192882752722818140265 3790644662064542113605199)
            ·
              refine ⟨5685966993096813170407799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790644662064542113605199 5685966993096813170407799)
              ·
                refine ⟨8528950489645219755611699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5685966993096813170407799 8528950489645219755611699)
                ·
                  refine ⟨12793425734467829633417549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8528950489645219755611699 12793425734467829633417549)
                  ·
                    refine ⟨4797534650425436112531581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12793425734467829633417549 4797534650425436112531581)
                    ·
                      refine ⟨1799075493909538542199343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797534650425436112531581 1799075493909538542199343)
                      ·
                        rfl

theorem cell23_3503687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_3503687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503687 prefixEnd_3503687 := by exact prefixLift 3503687
  have htrace : WordTrace (prefixWord ++ tailWord_3503687) baseStart_3503687 baseEnd_3503687 := by
    simpa [prefixWord, tailWord_3503687, baseEnd_3503687] using wordTrace_append hprefix tailTrace_3503687
  have hstable : (prefixWord ++ tailWord_3503687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503687).length < 2 ^ (prefixWord ++ tailWord_3503687).sum := by decide
  have hdescent : baseEnd_3503687 < baseStart_3503687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503697 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 1, 3, 2]
def baseStart_3503697 : Nat := 118140960795 + 3503697 * 2 ^ 59
def prefixEnd_3503697 : Nat := 4983230072969 + 3 ^ 40 * 3503697 * 2
def baseEnd_3503697 : Nat := 1799080628716083503074297

theorem tailTrace_3503697 : CollatzResearch.WordTrace tailWord_3503697 prefixEnd_3503697 1799080628716083503074297 := by
  unfold tailWord_3503697
  simp only [CollatzResearch.WordTrace]
  refine ⟨127790327987711627652941345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85193551991807751768627563 127790327987711627652941345)
  ·
    refine ⟨95842745990783720739706009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127790327987711627652941345 95842745990783720739706009)
    ·
      refine ⟨71882059493087790554779507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95842745990783720739706009 71882059493087790554779507)
      ·
        refine ⟨107823089239631685832169261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71882059493087790554779507 107823089239631685832169261)
        ·
          refine ⟨40433658464861882187063473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107823089239631685832169261 40433658464861882187063473)
          ·
            refine ⟨30325243848646411640297605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40433658464861882187063473 30325243848646411640297605)
            ·
              refine ⟨5685983221621202182555801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30325243848646411640297605 5685983221621202182555801)
              ·
                refine ⟨4264487416215901636916851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5685983221621202182555801 4264487416215901636916851)
                ·
                  refine ⟨6396731124323852455375277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264487416215901636916851 6396731124323852455375277)
                  ·
                    refine ⟨2398774171621444670765729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6396731124323852455375277 2398774171621444670765729)
                    ·
                      refine ⟨1799080628716083503074297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398774171621444670765729 1799080628716083503074297)
                      ·
                        rfl

theorem cell23_3503697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_3503697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503697 prefixEnd_3503697 := by exact prefixLift 3503697
  have htrace : WordTrace (prefixWord ++ tailWord_3503697) baseStart_3503697 baseEnd_3503697 := by
    simpa [prefixWord, tailWord_3503697, baseEnd_3503697] using wordTrace_append hprefix tailTrace_3503697
  have hstable : (prefixWord ++ tailWord_3503697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503697).length < 2 ^ (prefixWord ++ tailWord_3503697).sum := by decide
  have hdescent : baseEnd_3503697 < baseStart_3503697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503713 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3503713 : Nat := 118140960795 + 3503713 * 2 ^ 59
def prefixEnd_3503713 : Nat := 4983230072969 + 3 ^ 40 * 3503713 * 2
def baseEnd_3503713 : Nat := 1799088844406555440474223

theorem tailTrace_3503713 : CollatzResearch.WordTrace tailWord_3503713 prefixEnd_3503713 1799088844406555440474223 := by
  unfold tailWord_3503713
  simp only [CollatzResearch.WordTrace]
  refine ⟨127790911555653662385523793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85193941037102441590349195 127790911555653662385523793)
  ·
    refine ⟨95843183666740246789142845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127790911555653662385523793 95843183666740246789142845)
    ·
      refine ⟨35941193875027592545928567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95843183666740246789142845 35941193875027592545928567)
      ·
        refine ⟨53911790812541388818892851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35941193875027592545928567 53911790812541388818892851)
        ·
          refine ⟨80867686218812083228339277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53911790812541388818892851 80867686218812083228339277)
          ·
            refine ⟨30325382332054531210627229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80867686218812083228339277 30325382332054531210627229)
            ·
              refine ⟨11372018374520449203985211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30325382332054531210627229 11372018374520449203985211)
              ·
                refine ⟨17058027561780673805977817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372018374520449203985211 17058027561780673805977817)
                ·
                  refine ⟨12793520671335505354483363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17058027561780673805977817 12793520671335505354483363)
                  ·
                    refine ⟨19190281007003258031725045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12793520671335505354483363 19190281007003258031725045)
                    ·
                      refine ⟨1799088844406555440474223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19190281007003258031725045 1799088844406555440474223)
                      ·
                        rfl

theorem cell23_3503713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3503713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503713 prefixEnd_3503713 := by exact prefixLift 3503713
  have htrace : WordTrace (prefixWord ++ tailWord_3503713) baseStart_3503713 baseEnd_3503713 := by
    simpa [prefixWord, tailWord_3503713, baseEnd_3503713] using wordTrace_append hprefix tailTrace_3503713
  have hstable : (prefixWord ++ tailWord_3503713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503713).length < 2 ^ (prefixWord ++ tailWord_3503713).sum := by decide
  have hdescent : baseEnd_3503713 < baseStart_3503713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503727 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 2, 2, 2]
def baseStart_3503727 : Nat := 118140960795 + 3503727 * 2 ^ 59
def prefixEnd_3503727 : Nat := 4983230072969 + 3 ^ 40 * 3503727 * 2
def baseEnd_3503727 : Nat := 1799096033135718385699159

theorem tailTrace_3503727 : CollatzResearch.WordTrace tailWord_3503727 prefixEnd_3503727 1799096033135718385699159 := by
  unfold tailWord_3503727
  simp only [CollatzResearch.WordTrace]
  refine ⟨127791422177602942776533435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85194281451735295184355623 127791422177602942776533435)
  ·
    refine ⟨191687133266404414164800153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127791422177602942776533435 191687133266404414164800153)
    ·
      refine ⟨143765349949803310623600115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191687133266404414164800153 143765349949803310623600115)
      ·
        refine ⟨215648024924704965935400173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143765349949803310623600115 215648024924704965935400173)
        ·
          refine ⟨80868009346764362225775065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215648024924704965935400173 80868009346764362225775065)
          ·
            refine ⟨60651007010073271669331299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80868009346764362225775065 60651007010073271669331299)
            ·
              refine ⟨90976510515109907503996949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60651007010073271669331299 90976510515109907503996949)
              ·
                refine ⟨4264523930395776914249857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90976510515109907503996949 4264523930395776914249857)
                ·
                  refine ⟨3198392947796832685687393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264523930395776914249857 3198392947796832685687393)
                  ·
                    refine ⟨2398794710847624514265545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3198392947796832685687393 2398794710847624514265545)
                    ·
                      refine ⟨1799096033135718385699159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398794710847624514265545 1799096033135718385699159)
                      ·
                        rfl

theorem cell23_3503727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 2, 2, 2].length) (baseStart_3503727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503727 prefixEnd_3503727 := by exact prefixLift 3503727
  have htrace : WordTrace (prefixWord ++ tailWord_3503727) baseStart_3503727 baseEnd_3503727 := by
    simpa [prefixWord, tailWord_3503727, baseEnd_3503727] using wordTrace_append hprefix tailTrace_3503727
  have hstable : (prefixWord ++ tailWord_3503727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503727).length < 2 ^ (prefixWord ++ tailWord_3503727).sum := by decide
  have hdescent : baseEnd_3503727 < baseStart_3503727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503743 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 3]
def baseStart_3503743 : Nat := 118140960795 + 3503743 * 2 ^ 59
def prefixEnd_3503743 : Nat := 4983230072969 + 3 ^ 40 * 3503743 * 2
def baseEnd_3503743 : Nat := 1799104248826190323099085

theorem tailTrace_3503743 : CollatzResearch.WordTrace tailWord_3503743 prefixEnd_3503743 1799104248826190323099085 := by
  unfold tailWord_3503743
  simp only [CollatzResearch.WordTrace]
  refine ⟨127792005745544977509115883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85194670497029985006077255 127792005745544977509115883)
  ·
    refine ⟨191688008618317466263673825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127792005745544977509115883 191688008618317466263673825)
    ·
      refine ⟨143766006463738099697755369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191688008618317466263673825 143766006463738099697755369)
      ·
        refine ⟨107824504847803574773316527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143766006463738099697755369 107824504847803574773316527)
        ·
          refine ⟨161736757271705362159974791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107824504847803574773316527 161736757271705362159974791)
          ·
            refine ⟨242605135907558043239962187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161736757271705362159974791 242605135907558043239962187)
            ·
              refine ⟨363907703861337064859943281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242605135907558043239962187 363907703861337064859943281)
              ·
                refine ⟨272930777896002798644957461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363907703861337064859943281 272930777896002798644957461)
                ·
                  refine ⟨12793630213875131186482381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 272930777896002798644957461 12793630213875131186482381)
                  ·
                    refine ⟨4797611330203174194930893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12793630213875131186482381 4797611330203174194930893)
                    ·
                      refine ⟨1799104248826190323099085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797611330203174194930893 1799104248826190323099085)
                      ·
                        rfl

theorem cell23_3503743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_3503743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503743 prefixEnd_3503743 := by exact prefixLift 3503743
  have htrace : WordTrace (prefixWord ++ tailWord_3503743) baseStart_3503743 baseEnd_3503743 := by
    simpa [prefixWord, tailWord_3503743, baseEnd_3503743] using wordTrace_append hprefix tailTrace_3503743
  have hstable : (prefixWord ++ tailWord_3503743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503743).length < 2 ^ (prefixWord ++ tailWord_3503743).sum := by decide
  have hdescent : baseEnd_3503743 < baseStart_3503743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503778 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3503778 : Nat := 118140960795 + 3503778 * 2 ^ 59
def prefixEnd_3503778 : Nat := 4983230072969 + 3 ^ 40 * 3503778 * 2
def baseEnd_3503778 : Nat := 1799122220649097686161425

theorem tailTrace_3503778 : CollatzResearch.WordTrace tailWord_3503778 prefixEnd_3503778 1799122220649097686161425 := by
  unfold tailWord_3503778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31948320575104544621659997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85195521533612118991093325 31948320575104544621659997)
  ·
    refine ⟨11980620215664204233122499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31948320575104544621659997 11980620215664204233122499)
    ·
      refine ⟨17970930323496306349683749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980620215664204233122499 17970930323496306349683749)
      ·
        refine ⟨3369549435655557440565703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17970930323496306349683749 3369549435655557440565703)
        ·
          refine ⟨5054324153483336160848555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369549435655557440565703 5054324153483336160848555)
          ·
            refine ⟨7581486230225004241272833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5054324153483336160848555 7581486230225004241272833)
            ·
              refine ⟨5686114672668753180954625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7581486230225004241272833 5686114672668753180954625)
              ·
                refine ⟨4264586004501564885715969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5686114672668753180954625 4264586004501564885715969)
                ·
                  refine ⟨3198439503376173664286977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264586004501564885715969 3198439503376173664286977)
                  ·
                    refine ⟨2398829627532130248215233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3198439503376173664286977 2398829627532130248215233)
                    ·
                      refine ⟨1799122220649097686161425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398829627532130248215233 1799122220649097686161425)
                      ·
                        rfl

theorem cell23_3503778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3503778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503778 prefixEnd_3503778 := by exact prefixLift 3503778
  have htrace : WordTrace (prefixWord ++ tailWord_3503778) baseStart_3503778 baseEnd_3503778 := by
    simpa [prefixWord, tailWord_3503778, baseEnd_3503778] using wordTrace_append hprefix tailTrace_3503778
  have hstable : (prefixWord ++ tailWord_3503778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503778).length < 2 ^ (prefixWord ++ tailWord_3503778).sum := by decide
  have hdescent : baseEnd_3503778 < baseStart_3503778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503780 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_3503780 : Nat := 118140960795 + 3503780 * 2 ^ 59
def prefixEnd_3503780 : Nat := 4983230072969 + 3 ^ 40 * 3503780 * 2
def baseEnd_3503780 : Nat := 599707749203468892778805

theorem tailTrace_3503780 : CollatzResearch.WordTrace tailWord_3503780 prefixEnd_3503780 599707749203468892778805 := by
  unfold tailWord_3503780
  simp only [CollatzResearch.WordTrace]
  refine ⟨63896677623205466414106397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85195570164273955218808529 63896677623205466414106397)
  ·
    refine ⟨23961254108702049905289899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63896677623205466414106397 23961254108702049905289899)
    ·
      refine ⟨35941881163053074857934849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23961254108702049905289899 35941881163053074857934849)
      ·
        refine ⟨26956410872289806143451137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35941881163053074857934849 26956410872289806143451137)
        ·
          refine ⟨20217308154217354607588353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26956410872289806143451137 20217308154217354607588353)
          ·
            refine ⟨15162981115663015955691265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20217308154217354607588353 15162981115663015955691265)
            ·
              refine ⟨11372235836747261966768449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15162981115663015955691265 11372235836747261966768449)
              ·
                refine ⟨8529176877560446475076337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11372235836747261966768449 8529176877560446475076337)
                ·
                  refine ⟨6396882658170334856307253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8529176877560446475076337 6396882658170334856307253)
                  ·
                    refine ⟨599707749203468892778805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6396882658170334856307253 599707749203468892778805)
                    ·
                      rfl

theorem cell23_3503780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_3503780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503780 prefixEnd_3503780 := by exact prefixLift 3503780
  have htrace : WordTrace (prefixWord ++ tailWord_3503780) baseStart_3503780 baseEnd_3503780 := by
    simpa [prefixWord, tailWord_3503780, baseEnd_3503780] using wordTrace_append hprefix tailTrace_3503780
  have hstable : (prefixWord ++ tailWord_3503780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503780).length < 2 ^ (prefixWord ++ tailWord_3503780).sum := by decide
  have hdescent : baseEnd_3503780 < baseStart_3503780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503813 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_3503813 : Nat := 118140960795 + 3503813 * 2 ^ 59
def prefixEnd_3503813 : Nat := 4983230072969 + 3 ^ 40 * 3503813 * 2
def baseEnd_3503813 : Nat := 1799140192472005049223763

theorem tailTrace_3503813 : CollatzResearch.WordTrace tailWord_3503813 prefixEnd_3503813 1799140192472005049223763 := by
  unfold tailWord_3503813
  simp only [CollatzResearch.WordTrace]
  refine ⟨127794558855291379464164093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85196372570194252976109395 127794558855291379464164093)
  ·
    refine ⟨47922959570734267299061535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127794558855291379464164093 47922959570734267299061535)
    ·
      refine ⟨71884439356101400948592303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47922959570734267299061535 71884439356101400948592303)
      ·
        refine ⟨107826659034152101422888455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71884439356101400948592303 107826659034152101422888455)
        ·
          refine ⟨161739988551228152134332683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107826659034152101422888455 161739988551228152134332683)
          ·
            refine ⟨242609982826842228201499025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161739988551228152134332683 242609982826842228201499025)
            ·
              refine ⟨181957487120131671151124269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242609982826842228201499025 181957487120131671151124269)
              ·
                refine ⟨68234057670049376681671601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181957487120131671151124269 68234057670049376681671601)
                ·
                  refine ⟨51175543252537032511253701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68234057670049376681671601 51175543252537032511253701)
                  ·
                    refine ⟨9595414359850693595860069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51175543252537032511253701 9595414359850693595860069)
                    ·
                      refine ⟨1799140192472005049223763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9595414359850693595860069 1799140192472005049223763)
                      ·
                        rfl

theorem cell23_3503813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_3503813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503813 prefixEnd_3503813 := by exact prefixLift 3503813
  have htrace : WordTrace (prefixWord ++ tailWord_3503813) baseStart_3503813 baseEnd_3503813 := by
    simpa [prefixWord, tailWord_3503813, baseEnd_3503813] using wordTrace_append hprefix tailTrace_3503813
  have hstable : (prefixWord ++ tailWord_3503813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503813).length < 2 ^ (prefixWord ++ tailWord_3503813).sum := by decide
  have hdescent : baseEnd_3503813 < baseStart_3503813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503814 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3503814 : Nat := 118140960795 + 3503814 * 2 ^ 59
def prefixEnd_3503814 : Nat := 4983230072969 + 3 ^ 40 * 3503814 * 2
def baseEnd_3503814 : Nat := 599713568650886515103753

theorem tailTrace_3503814 : CollatzResearch.WordTrace tailWord_3503814 prefixEnd_3503814 599713568650886515103753 := by
  unfold tailWord_3503814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993581104008992394842203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85196396885525171089966997 3993581104008992394842203)
  ·
    refine ⟨5990371656013488592263305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3993581104008992394842203 5990371656013488592263305)
    ·
      refine ⟨4492778742010116444197479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5990371656013488592263305 4492778742010116444197479)
      ·
        refine ⟨6739168113015174666296219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4492778742010116444197479 6739168113015174666296219)
        ·
          refine ⟨10108752169522761999444329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6739168113015174666296219 10108752169522761999444329)
          ·
            refine ⟨7581564127142071499583247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10108752169522761999444329 7581564127142071499583247)
            ·
              refine ⟨11372346190713107249374871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581564127142071499583247 11372346190713107249374871)
              ·
                refine ⟨17058519286069660874062307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372346190713107249374871 17058519286069660874062307)
                ·
                  refine ⟨25587778929104491311093461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17058519286069660874062307 25587778929104491311093461)
                  ·
                    refine ⟨599713568650886515103753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25587778929104491311093461 599713568650886515103753)
                    ·
                      rfl

theorem cell23_3503814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3503814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503814 prefixEnd_3503814 := by exact prefixLift 3503814
  have htrace : WordTrace (prefixWord ++ tailWord_3503814) baseStart_3503814 baseEnd_3503814 := by
    simpa [prefixWord, tailWord_3503814, baseEnd_3503814] using wordTrace_append hprefix tailTrace_3503814
  have hstable : (prefixWord ++ tailWord_3503814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503814).length < 2 ^ (prefixWord ++ tailWord_3503814).sum := by decide
  have hdescent : baseEnd_3503814 < baseStart_3503814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503840 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 6]
def baseStart_3503840 : Nat := 118140960795 + 3503840 * 2 ^ 59
def prefixEnd_3503840 : Nat := 4983230072969 + 3 ^ 40 * 3503840 * 2
def baseEnd_3503840 : Nat := 199906006272186271509571

theorem tailTrace_3503840 : CollatzResearch.WordTrace tailWord_3503840 prefixEnd_3503840 199906006272186271509571 := by
  unfold tailWord_3503840
  simp only [CollatzResearch.WordTrace]
  refine ⟨63897771813096781537698487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85197029084129042050264649 63897771813096781537698487)
  ·
    refine ⟨95846657719645172306547731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63897771813096781537698487 95846657719645172306547731)
    ·
      refine ⟨143769986579467758459821597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95846657719645172306547731 143769986579467758459821597)
      ·
        refine ⟨53913744967300409422433099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143769986579467758459821597 53913744967300409422433099)
        ·
          refine ⟨80870617450950614133649649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53913744967300409422433099 80870617450950614133649649)
          ·
            refine ⟨60652963088212960600237237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80870617450950614133649649 60652963088212960600237237)
            ·
              refine ⟨5686215289519965056272241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60652963088212960600237237 5686215289519965056272241)
              ·
                refine ⟨4264661467139973792204181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5686215289519965056272241 4264661467139973792204181)
                ·
                  refine ⟨199906006272186271509571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4264661467139973792204181 199906006272186271509571)
                  ·
                    rfl

theorem cell23_3503840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 6].length) (baseStart_3503840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503840 prefixEnd_3503840 := by exact prefixLift 3503840
  have htrace : WordTrace (prefixWord ++ tailWord_3503840) baseStart_3503840 baseEnd_3503840 := by
    simpa [prefixWord, tailWord_3503840, baseEnd_3503840] using wordTrace_append hprefix tailTrace_3503840
  have hstable : (prefixWord ++ tailWord_3503840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503840).length < 2 ^ (prefixWord ++ tailWord_3503840).sum := by decide
  have hdescent : baseEnd_3503840 < baseStart_3503840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503857 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 6]
def baseStart_3503857 : Nat := 118140960795 + 3503857 * 2 ^ 59
def prefixEnd_3503857 : Nat := 4983230072969 + 3 ^ 40 * 3503857 * 2
def baseEnd_3503857 : Nat := 199906976180089208563729

theorem tailTrace_3503857 : CollatzResearch.WordTrace tailWord_3503857 prefixEnd_3503857 199906976180089208563729 := by
  unfold tailWord_3503857
  simp only [CollatzResearch.WordTrace]
  refine ⟨127796163667131974978765825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85197442444754649985843883 127796163667131974978765825)
  ·
    refine ⟨95847122750348981234074369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127796163667131974978765825 95847122750348981234074369)
    ·
      refine ⟨71885342062761735925555777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95847122750348981234074369 71885342062761735925555777)
      ·
        refine ⟨53914006547071301944166833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71885342062761735925555777 53914006547071301944166833)
        ·
          refine ⟨40435504910303476458125125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53914006547071301944166833 40435504910303476458125125)
          ·
            refine ⟨7581657170681901835898461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40435504910303476458125125 7581657170681901835898461)
            ·
              refine ⟨2843121439005713188461923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7581657170681901835898461 2843121439005713188461923)
              ·
                refine ⟨4264682158508569782692885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843121439005713188461923 4264682158508569782692885)
                ·
                  refine ⟨199906976180089208563729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4264682158508569782692885 199906976180089208563729)
                  ·
                    rfl

theorem cell23_3503857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 6].length) (baseStart_3503857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503857 prefixEnd_3503857 := by exact prefixLift 3503857
  have htrace : WordTrace (prefixWord ++ tailWord_3503857) baseStart_3503857 baseEnd_3503857 := by
    simpa [prefixWord, tailWord_3503857, baseEnd_3503857] using wordTrace_append hprefix tailTrace_3503857
  have hstable : (prefixWord ++ tailWord_3503857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503857).length < 2 ^ (prefixWord ++ tailWord_3503857).sum := by decide
  have hdescent : baseEnd_3503857 < baseStart_3503857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503863 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_3503863 : Nat := 118140960795 + 3503863 * 2 ^ 59
def prefixEnd_3503863 : Nat := 4983230072969 + 3 ^ 40 * 3503863 * 2
def baseEnd_3503863 : Nat := 1799165866504729853598533

theorem tailTrace_3503863 : CollatzResearch.WordTrace tailWord_3503863 prefixEnd_3503863 1799165866504729853598533 := by
  unfold tailWord_3503863
  simp only [CollatzResearch.WordTrace]
  refine ⟨127796382505110238003484243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85197588336740158668989495 127796382505110238003484243)
  ·
    refine ⟨191694573757665357005226365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127796382505110238003484243 191694573757665357005226365)
    ·
      refine ⟨71885465159124508876959887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191694573757665357005226365 71885465159124508876959887)
      ·
        refine ⟨107828197738686763315439831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71885465159124508876959887 107828197738686763315439831)
        ·
          refine ⟨161742296608030144973159747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107828197738686763315439831 161742296608030144973159747)
          ·
            refine ⟨242613444912045217459739621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161742296608030144973159747 242613444912045217459739621)
            ·
              refine ⟨45490020921008478273701179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242613444912045217459739621 45490020921008478273701179)
              ·
                refine ⟨68235031381512717410551769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45490020921008478273701179 68235031381512717410551769)
                ·
                  refine ⟨51176273536134538057913827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68235031381512717410551769 51176273536134538057913827)
                  ·
                    refine ⟨76764410304201807086870741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51176273536134538057913827 76764410304201807086870741)
                    ·
                      refine ⟨1799165866504729853598533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76764410304201807086870741 1799165866504729853598533)
                      ·
                        rfl

theorem cell23_3503863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_3503863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503863 prefixEnd_3503863 := by exact prefixLift 3503863
  have htrace : WordTrace (prefixWord ++ tailWord_3503863) baseStart_3503863 baseEnd_3503863 := by
    simpa [prefixWord, tailWord_3503863, baseEnd_3503863] using wordTrace_append hprefix tailTrace_3503863
  have hstable : (prefixWord ++ tailWord_3503863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503863).length < 2 ^ (prefixWord ++ tailWord_3503863).sum := by decide
  have hdescent : baseEnd_3503863 < baseStart_3503863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503924 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3503924 : Nat := 118140960795 + 3503924 * 2 ^ 59
def prefixEnd_3503924 : Nat := 4983230072969 + 3 ^ 40 * 3503924 * 2
def baseEnd_3503924 : Nat := 1799197188824654114935753

theorem tailTrace_3503924 : CollatzResearch.WordTrace tailWord_3503924 prefixEnd_3503924 1799197188824654114935753 := by
  unfold tailWord_3503924
  simp only [CollatzResearch.WordTrace]
  refine ⟨63899303678944622710727413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85199071571926163614303217 63899303678944622710727413)
  ·
    refine ⟨5990559719901058379130695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63899303678944622710727413 5990559719901058379130695)
    ·
      refine ⟨8985839579851587568696043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5990559719901058379130695 8985839579851587568696043)
      ·
        refine ⟨13478759369777381353044065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8985839579851587568696043 13478759369777381353044065)
        ·
          refine ⟨10109069527333036014783049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13478759369777381353044065 10109069527333036014783049)
          ·
            refine ⟨7581802145499777011087287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10109069527333036014783049 7581802145499777011087287)
            ·
              refine ⟨11372703218249665516630931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7581802145499777011087287 11372703218249665516630931)
              ·
                refine ⟨17059054827374498274946397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11372703218249665516630931 17059054827374498274946397)
                ·
                  refine ⟨6397145560265436853104899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17059054827374498274946397 6397145560265436853104899)
                  ·
                    refine ⟨9595718340398155279657349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6397145560265436853104899 9595718340398155279657349)
                    ·
                      refine ⟨1799197188824654114935753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9595718340398155279657349 1799197188824654114935753)
                      ·
                        rfl

theorem cell23_3503924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3503924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503924 prefixEnd_3503924 := by exact prefixLift 3503924
  have htrace : WordTrace (prefixWord ++ tailWord_3503924) baseStart_3503924 baseEnd_3503924 := by
    simpa [prefixWord, tailWord_3503924, baseEnd_3503924] using wordTrace_append hprefix tailTrace_3503924
  have hstable : (prefixWord ++ tailWord_3503924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503924).length < 2 ^ (prefixWord ++ tailWord_3503924).sum := by decide
  have hdescent : baseEnd_3503924 < baseStart_3503924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503927 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_3503927 : Nat := 118140960795 + 3503927 * 2 ^ 59
def prefixEnd_3503927 : Nat := 4983230072969 + 3 ^ 40 * 3503927 * 2
def baseEnd_3503927 : Nat := 1799198729266617603198239

theorem tailTrace_3503927 : CollatzResearch.WordTrace tailWord_3503927 prefixEnd_3503927 1799198729266617603198239 := by
  unfold tailWord_3503927
  simp only [CollatzResearch.WordTrace]
  refine ⟨127798716776878376933814035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85199144517918917955876023 127798716776878376933814035)
  ·
    refine ⟨191698075165317565400721053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127798716776878376933814035 191698075165317565400721053)
    ·
      refine ⟨71886778186994087025270395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191698075165317565400721053 71886778186994087025270395)
      ·
        refine ⟨107830167280491130537905593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71886778186994087025270395 107830167280491130537905593)
        ·
          refine ⟨80872625460368347903429195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107830167280491130537905593 80872625460368347903429195)
          ·
            refine ⟨121308938190552521855143793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80872625460368347903429195 121308938190552521855143793)
            ·
              refine ⟨90981703642914391391357845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121308938190552521855143793 90981703642914391391357845)
              ·
                refine ⟨4264767358261612096469899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90981703642914391391357845 4264767358261612096469899)
                ·
                  refine ⟨6397151037392418144704849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264767358261612096469899 6397151037392418144704849)
                  ·
                    refine ⟨4797863278044313608528637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6397151037392418144704849 4797863278044313608528637)
                    ·
                      refine ⟨1799198729266617603198239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797863278044313608528637 1799198729266617603198239)
                      ·
                        rfl

theorem cell23_3503927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_3503927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503927 prefixEnd_3503927 := by exact prefixLift 3503927
  have htrace : WordTrace (prefixWord ++ tailWord_3503927) baseStart_3503927 baseEnd_3503927 := by
    simpa [prefixWord, tailWord_3503927, baseEnd_3503927] using wordTrace_append hprefix tailTrace_3503927
  have hstable : (prefixWord ++ tailWord_3503927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503927).length < 2 ^ (prefixWord ++ tailWord_3503927).sum := by decide
  have hdescent : baseEnd_3503927 < baseStart_3503927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503930 : List Nat := [3, 1, 1, 1, 5, 1, 2, 9]
def baseStart_3503930 : Nat := 118140960795 + 3503930 * 2 ^ 59
def prefixEnd_3503930 : Nat := 4983230072969 + 3 ^ 40 * 3503930 * 2
def baseEnd_3503930 : Nat := 66637047026243744128175

theorem tailTrace_3503930 : CollatzResearch.WordTrace tailWord_3503930 prefixEnd_3503930 66637047026243744128175 := by
  unfold tailWord_3503930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31949706548966877111543311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85199217463911672297448829 31949706548966877111543311)
  ·
    refine ⟨47924559823450315667314967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31949706548966877111543311 47924559823450315667314967)
    ·
      refine ⟨71886839735175473500972451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47924559823450315667314967 71886839735175473500972451)
      ·
        refine ⟨107830259602763210251458677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71886839735175473500972451 107830259602763210251458677)
        ·
          refine ⟨10109086837759050961074251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107830259602763210251458677 10109086837759050961074251)
          ·
            refine ⟨15163630256638576441611377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10109086837759050961074251 15163630256638576441611377)
            ·
              refine ⟨11372722692478932331208533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15163630256638576441611377 11372722692478932331208533)
              ·
                refine ⟨66637047026243744128175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11372722692478932331208533 66637047026243744128175)
                ·
                  rfl

theorem cell23_3503930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_3503930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503930 prefixEnd_3503930 := by exact prefixLift 3503930
  have htrace : WordTrace (prefixWord ++ tailWord_3503930) baseStart_3503930 baseEnd_3503930 := by
    simpa [prefixWord, tailWord_3503930, baseEnd_3503930] using wordTrace_append hprefix tailTrace_3503930
  have hstable : (prefixWord ++ tailWord_3503930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503930).length < 2 ^ (prefixWord ++ tailWord_3503930).sum := by decide
  have hdescent : baseEnd_3503930 < baseStart_3503930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503941 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 1, 2, 2]
def baseStart_3503941 : Nat := 118140960795 + 3503941 * 2 ^ 59
def prefixEnd_3503941 : Nat := 4983230072969 + 3 ^ 40 * 3503941 * 2
def baseEnd_3503941 : Nat := 1799205917995780548423175

theorem tailTrace_3503941 : CollatzResearch.WordTrace tailWord_3503941 prefixEnd_3503941 1799205917995780548423175 := by
  unfold tailWord_3503941
  simp only [CollatzResearch.WordTrace]
  refine ⟨127799227398827657324823677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85199484932551771549882451 127799227398827657324823677)
  ·
    refine ⟨47924710274560371496808879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127799227398827657324823677 47924710274560371496808879)
    ·
      refine ⟨71887065411840557245213319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47924710274560371496808879 71887065411840557245213319)
      ·
        refine ⟨107830598117760835867819979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71887065411840557245213319 107830598117760835867819979)
        ·
          refine ⟨161745897176641253801729969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107830598117760835867819979 161745897176641253801729969)
          ·
            refine ⟨121309422882480940351297477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161745897176641253801729969 121309422882480940351297477)
            ·
              refine ⟨22745516790465176315868277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121309422882480940351297477 22745516790465176315868277)
              ·
                refine ⟨2132392199106110279612651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22745516790465176315868277 2132392199106110279612651)
                ·
                  refine ⟨3198588298659165419418977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132392199106110279612651 3198588298659165419418977)
                  ·
                    refine ⟨2398941223994374064564233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3198588298659165419418977 2398941223994374064564233)
                    ·
                      refine ⟨1799205917995780548423175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398941223994374064564233 1799205917995780548423175)
                      ·
                        rfl

theorem cell23_3503941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_3503941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503941 prefixEnd_3503941 := by exact prefixLift 3503941
  have htrace : WordTrace (prefixWord ++ tailWord_3503941) baseStart_3503941 baseEnd_3503941 := by
    simpa [prefixWord, tailWord_3503941, baseEnd_3503941] using wordTrace_append hprefix tailTrace_3503941
  have hstable : (prefixWord ++ tailWord_3503941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503941).length < 2 ^ (prefixWord ++ tailWord_3503941).sum := by decide
  have hdescent : baseEnd_3503941 < baseStart_3503941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503964 : List Nat := [2, 2, 4, 2, 2, 2, 1, 8]
def baseStart_3503964 : Nat := 118140960795 + 3503964 * 2 ^ 59
def prefixEnd_3503964 : Nat := 4983230072969 + 3 ^ 40 * 3503964 * 2
def baseEnd_3503964 : Nat := 66637693631512368830947

theorem tailTrace_3503964 : CollatzResearch.WordTrace tailWord_3503964 prefixEnd_3503964 66637693631512368830947 := by
  unfold tailWord_3503964
  simp only [CollatzResearch.WordTrace]
  refine ⟨63900033138872166126455473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85200044185162888168607297 63900033138872166126455473)
  ·
    refine ⟨47925024854154124594841605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63900033138872166126455473 47925024854154124594841605)
    ·
      refine ⟨8985942160153898361532801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47925024854154124594841605 8985942160153898361532801)
      ·
        refine ⟨6739456620115423771149601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8985942160153898361532801 6739456620115423771149601)
        ·
          refine ⟨5054592465086567828362201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6739456620115423771149601 5054592465086567828362201)
          ·
            refine ⟨3790944348814925871271651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054592465086567828362201 3790944348814925871271651)
            ·
              refine ⟨5686416523222388806907477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790944348814925871271651 5686416523222388806907477)
              ·
                refine ⟨66637693631512368830947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5686416523222388806907477 66637693631512368830947)
                ·
                  rfl

theorem cell23_3503964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 8].length) (baseStart_3503964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503964 prefixEnd_3503964 := by exact prefixLift 3503964
  have htrace : WordTrace (prefixWord ++ tailWord_3503964) baseStart_3503964 baseEnd_3503964 := by
    simpa [prefixWord, tailWord_3503964, baseEnd_3503964] using wordTrace_append hprefix tailTrace_3503964
  have hstable : (prefixWord ++ tailWord_3503964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503964).length < 2 ^ (prefixWord ++ tailWord_3503964).sum := by decide
  have hdescent : baseEnd_3503964 < baseStart_3503964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3503984 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 1, 3, 2]
def baseStart_3503984 : Nat := 118140960795 + 3503984 * 2 ^ 59
def prefixEnd_3503984 : Nat := 4983230072969 + 3 ^ 40 * 3503984 * 2
def baseEnd_3503984 : Nat := 1799227997663923880185477

theorem tailTrace_3503984 : CollatzResearch.WordTrace tailWord_3503984 prefixEnd_3503984 1799227997663923880185477 := by
  unfold tailWord_3503984
  simp only [CollatzResearch.WordTrace]
  refine ⟨63900397868835937834319503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85200530491781250445759337 63900397868835937834319503)
  ·
    refine ⟨95850596803253906751479255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63900397868835937834319503 95850596803253906751479255)
    ·
      refine ⟨143775895204880860127218883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95850596803253906751479255 143775895204880860127218883)
      ·
        refine ⟨215663842807321290190828325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143775895204880860127218883 215663842807321290190828325)
        ·
          refine ⟨40436970526372741910780311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215663842807321290190828325 40436970526372741910780311)
          ·
            refine ⟨60655455789559112866170467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40436970526372741910780311 60655455789559112866170467)
            ·
              refine ⟨90983183684338669299255701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60655455789559112866170467 90983183684338669299255701)
              ·
                refine ⟨4264836735203375123402611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90983183684338669299255701 4264836735203375123402611)
                ·
                  refine ⟨6397255102805062685103917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4264836735203375123402611 6397255102805062685103917)
                  ·
                    refine ⟨2398970663551898506913969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6397255102805062685103917 2398970663551898506913969)
                    ·
                      refine ⟨1799227997663923880185477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2398970663551898506913969 1799227997663923880185477)
                      ·
                        rfl

theorem cell23_3503984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 3, 2].length) (baseStart_3503984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3503984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3503984 prefixEnd_3503984 := by exact prefixLift 3503984
  have htrace : WordTrace (prefixWord ++ tailWord_3503984) baseStart_3503984 baseEnd_3503984 := by
    simpa [prefixWord, tailWord_3503984, baseEnd_3503984] using wordTrace_append hprefix tailTrace_3503984
  have hstable : (prefixWord ++ tailWord_3503984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3503984).length < 2 ^ (prefixWord ++ tailWord_3503984).sum := by decide
  have hdescent : baseEnd_3503984 < baseStart_3503984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3503984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504000 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_3504000 : Nat := 118140960795 + 3504000 * 2 ^ 59
def prefixEnd_3504000 : Nat := 4983230072969 + 3 ^ 40 * 3504000 * 2
def baseEnd_3504000 : Nat := 1799236213354395817585403

theorem tailTrace_3504000 : CollatzResearch.WordTrace tailWord_3504000 prefixEnd_3504000 1799236213354395817585403 := by
  unfold tailWord_3504000
  simp only [CollatzResearch.WordTrace]
  refine ⟨63900689652806955200610727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85200919537075940267480969 63900689652806955200610727)
  ·
    refine ⟨95851034479210432800916091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63900689652806955200610727 95851034479210432800916091)
    ·
      refine ⟨143776551718815649201374137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95851034479210432800916091 143776551718815649201374137)
      ·
        refine ⟨107832413789111736901030603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143776551718815649201374137 107832413789111736901030603)
        ·
          refine ⟨161748620683667605351545905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107832413789111736901030603 161748620683667605351545905)
          ·
            refine ⟨121311465512750704013659429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161748620683667605351545905 121311465512750704013659429)
            ·
              refine ⟨22745899783640757002561143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121311465512750704013659429 22745899783640757002561143)
              ·
                refine ⟨34118849675461135503841715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22745899783640757002561143 34118849675461135503841715)
                ·
                  refine ⟨51178274513191703255762573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34118849675461135503841715 51178274513191703255762573)
                  ·
                    refine ⟨19191852942446888720910965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51178274513191703255762573 19191852942446888720910965)
                    ·
                      refine ⟨1799236213354395817585403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19191852942446888720910965 1799236213354395817585403)
                      ·
                        rfl

theorem cell23_3504000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_3504000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504000 prefixEnd_3504000 := by exact prefixLift 3504000
  have htrace : WordTrace (prefixWord ++ tailWord_3504000) baseStart_3504000 baseEnd_3504000 := by
    simpa [prefixWord, tailWord_3504000, baseEnd_3504000] using wordTrace_append hprefix tailTrace_3504000
  have hstable : (prefixWord ++ tailWord_3504000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504000).length < 2 ^ (prefixWord ++ tailWord_3504000).sum := by decide
  have hdescent : baseEnd_3504000 < baseStart_3504000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504008 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3504008 : Nat := 118140960795 + 3504008 * 2 ^ 59
def prefixEnd_3504008 : Nat := 4983230072969 + 3 ^ 40 * 3504008 * 2
def baseEnd_3504008 : Nat := 1799240321199631786285367

theorem tailTrace_3504008 : CollatzResearch.WordTrace tailWord_3504008 prefixEnd_3504008 1799240321199631786285367 := by
  unfold tailWord_3504008
  simp only [CollatzResearch.WordTrace]
  refine ⟨63900835544792463883756339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85201114059723285178341785 63900835544792463883756339)
  ·
    refine ⟨95851253317188695825634509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63900835544792463883756339 95851253317188695825634509)
    ·
      refine ⟨35944219993945760934612941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95851253317188695825634509 35944219993945760934612941)
      ·
        refine ⟨13479082497729660350479853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35944219993945760934612941 13479082497729660350479853)
        ·
          refine ⟨5054655936648622631429945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13479082497729660350479853 5054655936648622631429945)
          ·
            refine ⟨3790991952486466973572459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054655936648622631429945 3790991952486466973572459)
            ·
              refine ⟨5686487928729700460358689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3790991952486466973572459 5686487928729700460358689)
              ·
                refine ⟨4264865946547275345269017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5686487928729700460358689 4264865946547275345269017)
                ·
                  refine ⟨3198649459910456508951763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264865946547275345269017 3198649459910456508951763)
                  ·
                    refine ⟨4797974189865684763427645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3198649459910456508951763 4797974189865684763427645)
                    ·
                      refine ⟨1799240321199631786285367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4797974189865684763427645 1799240321199631786285367)
                      ·
                        rfl

theorem cell23_3504008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3504008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504008 prefixEnd_3504008 := by exact prefixLift 3504008
  have htrace : WordTrace (prefixWord ++ tailWord_3504008) baseStart_3504008 baseEnd_3504008 := by
    simpa [prefixWord, tailWord_3504008, baseEnd_3504008] using wordTrace_append hprefix tailTrace_3504008
  have hstable : (prefixWord ++ tailWord_3504008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504008).length < 2 ^ (prefixWord ++ tailWord_3504008).sum := by decide
  have hdescent : baseEnd_3504008 < baseStart_3504008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504082 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3504082 : Nat := 118140960795 + 3504082 * 2 ^ 59
def prefixEnd_3504082 : Nat := 4983230072969 + 3 ^ 40 * 3504082 * 2
def baseEnd_3504082 : Nat := 1799278318768064496760027

theorem tailTrace_3504082 : CollatzResearch.WordTrace tailWord_3504082 prefixEnd_3504082 1799278318768064496760027 := by
  unfold tailWord_3504082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31951092522829209601426625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85202913394211225603804333 31951092522829209601426625)
  ·
    refine ⟨23963319392121907201069969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31951092522829209601426625 23963319392121907201069969)
    ·
      refine ⟨17972489544091430400802477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23963319392121907201069969 17972489544091430400802477)
      ·
        refine ⟨6739683579034286400300929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17972489544091430400802477 6739683579034286400300929)
        ·
          refine ⟨5054762684275714800225697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6739683579034286400300929 5054762684275714800225697)
          ·
            refine ⟨3791072013206786100169273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054762684275714800225697 3791072013206786100169273)
            ·
              refine ⟨2843304009905089575126955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791072013206786100169273 2843304009905089575126955)
              ·
                refine ⟨4264956014857634362690433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843304009905089575126955 4264956014857634362690433)
                ·
                  refine ⟨3198717011143225772017825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4264956014857634362690433 3198717011143225772017825)
                  ·
                    refine ⟨2399037758357419329013369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3198717011143225772017825 2399037758357419329013369)
                    ·
                      refine ⟨1799278318768064496760027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399037758357419329013369 1799278318768064496760027)
                      ·
                        rfl

theorem cell23_3504082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3504082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504082 prefixEnd_3504082 := by exact prefixLift 3504082
  have htrace : WordTrace (prefixWord ++ tailWord_3504082) baseStart_3504082 baseEnd_3504082 := by
    simpa [prefixWord, tailWord_3504082, baseEnd_3504082] using wordTrace_append hprefix tailTrace_3504082
  have hstable : (prefixWord ++ tailWord_3504082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504082).length < 2 ^ (prefixWord ++ tailWord_3504082).sum := by decide
  have hdescent : baseEnd_3504082 < baseStart_3504082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504087 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_3504087 : Nat := 118140960795 + 3504087 * 2 ^ 59
def prefixEnd_3504087 : Nat := 4983230072969 + 3 ^ 40 * 3504087 * 2
def baseEnd_3504087 : Nat := 1799280886171336977197503

theorem tailTrace_3504087 : CollatzResearch.WordTrace tailWord_3504087 prefixEnd_3504087 1799280886171336977197503 := by
  unfold tailWord_3504087
  simp only [CollatzResearch.WordTrace]
  refine ⟨127804552456298724259638515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85203034970865816173092343 127804552456298724259638515)
  ·
    refine ⟨191706828684448086389457773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127804552456298724259638515 191706828684448086389457773)
    ·
      refine ⟨71890060756668032396046665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191706828684448086389457773 71890060756668032396046665)
      ·
        refine ⟨53917545567501024297034999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71890060756668032396046665 53917545567501024297034999)
        ·
          refine ⟨80876318351251536445552499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53917545567501024297034999 80876318351251536445552499)
          ·
            refine ⟨121314477526877304668328749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80876318351251536445552499 121314477526877304668328749)
            ·
              refine ⟨45492929072578989250623281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121314477526877304668328749 45492929072578989250623281)
              ·
                refine ⟨34119696804434241937967461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45492929072578989250623281 34119696804434241937967461)
                ·
                  refine ⟨6397443150831420363368899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34119696804434241937967461 6397443150831420363368899)
                  ·
                    refine ⟨9596164726247130545053349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6397443150831420363368899 9596164726247130545053349)
                    ·
                      refine ⟨1799280886171336977197503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9596164726247130545053349 1799280886171336977197503)
                      ·
                        rfl

theorem cell23_3504087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_3504087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504087 prefixEnd_3504087 := by exact prefixLift 3504087
  have htrace : WordTrace (prefixWord ++ tailWord_3504087) baseStart_3504087 baseEnd_3504087 := by
    simpa [prefixWord, tailWord_3504087, baseEnd_3504087] using wordTrace_append hprefix tailTrace_3504087
  have hstable : (prefixWord ++ tailWord_3504087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504087).length < 2 ^ (prefixWord ++ tailWord_3504087).sum := by decide
  have hdescent : baseEnd_3504087 < baseStart_3504087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504104 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_3504104 : Nat := 118140960795 + 3504104 * 2 ^ 59
def prefixEnd_3504104 : Nat := 4983230072969 + 3 ^ 40 * 3504104 * 2
def baseEnd_3504104 : Nat := 1799289615342463410684925

theorem tailTrace_3504104 : CollatzResearch.WordTrace tailWord_3504104 prefixEnd_3504104 1799289615342463410684925 := by
  unfold tailWord_3504104
  simp only [CollatzResearch.WordTrace]
  refine ⟨63902586248618568081503683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85203448331491424108671577 63902586248618568081503683)
  ·
    refine ⟨95853879372927852122255525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63902586248618568081503683 95853879372927852122255525)
    ·
      refine ⟨17972602382423972272922911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95853879372927852122255525 17972602382423972272922911)
      ·
        refine ⟨26958903573635958409384367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17972602382423972272922911 26958903573635958409384367)
        ·
          refine ⟨40438355360453937614076551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26958903573635958409384367 40438355360453937614076551)
          ·
            refine ⟨60657533040680906421114827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40438355360453937614076551 60657533040680906421114827)
            ·
              refine ⟨90986299561021359631672241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60657533040680906421114827 90986299561021359631672241)
              ·
                refine ⟨68239724670766019723754181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90986299561021359631672241 68239724670766019723754181)
                ·
                  refine ⟨12794948375768628698203909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68239724670766019723754181 12794948375768628698203909)
                  ·
                    refine ⟨2399052820456617880913233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12794948375768628698203909 2399052820456617880913233)
                    ·
                      refine ⟨1799289615342463410684925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399052820456617880913233 1799289615342463410684925)
                      ·
                        rfl

theorem cell23_3504104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_3504104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504104 prefixEnd_3504104 := by exact prefixLift 3504104
  have htrace : WordTrace (prefixWord ++ tailWord_3504104) baseStart_3504104 baseEnd_3504104 := by
    simpa [prefixWord, tailWord_3504104, baseEnd_3504104] using wordTrace_append hprefix tailTrace_3504104
  have hstable : (prefixWord ++ tailWord_3504104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504104).length < 2 ^ (prefixWord ++ tailWord_3504104).sum := by decide
  have hdescent : baseEnd_3504104 < baseStart_3504104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504107 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 3]
def baseStart_3504107 : Nat := 118140960795 + 3504107 * 2 ^ 59
def prefixEnd_3504107 : Nat := 4983230072969 + 3 ^ 40 * 3504107 * 2
def baseEnd_3504107 : Nat := 1799291155784426898947411

theorem tailTrace_3504107 : CollatzResearch.WordTrace tailWord_3504107 prefixEnd_3504107 1799291155784426898947411 := by
  unfold tailWord_3504107
  simp only [CollatzResearch.WordTrace]
  refine ⟨127805281916226267675366575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85203521277484178450244383 127805281916226267675366575)
  ·
    refine ⟨191707922874339401513049863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127805281916226267675366575 191707922874339401513049863)
    ·
      refine ⟨287561884311509102269574795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191707922874339401513049863 287561884311509102269574795)
      ·
        refine ⟨431342826467263653404362193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287561884311509102269574795 431342826467263653404362193)
        ·
          refine ⟨323507119850447740053271645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431342826467263653404362193 323507119850447740053271645)
          ·
            refine ⟨121315169943917902519976867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323507119850447740053271645 121315169943917902519976867)
            ·
              refine ⟨181972754915876853779965301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121315169943917902519976867 181972754915876853779965301)
              ·
                refine ⟨17059945773363455041871747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181972754915876853779965301 17059945773363455041871747)
                ·
                  refine ⟨25589918660045182562807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17059945773363455041871747 25589918660045182562807621)
                  ·
                    refine ⟨4798109748758471730526429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25589918660045182562807621 4798109748758471730526429)
                    ·
                      refine ⟨1799291155784426898947411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798109748758471730526429 1799291155784426898947411)
                      ·
                        rfl

theorem cell23_3504107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 3].length) (baseStart_3504107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504107 prefixEnd_3504107 := by exact prefixLift 3504107
  have htrace : WordTrace (prefixWord ++ tailWord_3504107) baseStart_3504107 baseEnd_3504107 := by
    simpa [prefixWord, tailWord_3504107, baseEnd_3504107] using wordTrace_append hprefix tailTrace_3504107
  have hstable : (prefixWord ++ tailWord_3504107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504107).length < 2 ^ (prefixWord ++ tailWord_3504107).sum := by decide
  have hdescent : baseEnd_3504107 < baseStart_3504107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504124 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 2, 2, 3]
def baseStart_3504124 : Nat := 118140960795 + 3504124 * 2 ^ 59
def prefixEnd_3504124 : Nat := 4983230072969 + 3 ^ 40 * 3504124 * 2
def baseEnd_3504124 : Nat := 1799299884955553332434833

theorem tailTrace_3504124 : CollatzResearch.WordTrace tailWord_3504124 prefixEnd_3504124 1799299884955553332434833 := by
  unfold tailWord_3504124
  simp only [CollatzResearch.WordTrace]
  refine ⟨63902950978582339789367713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85203934638109786385823617 63902950978582339789367713)
  ·
    refine ⟨47927213233936754842025785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63902950978582339789367713 47927213233936754842025785)
    ·
      refine ⟨35945409925452566131519339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47927213233936754842025785 35945409925452566131519339)
      ·
        refine ⟨53918114888178849197279009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35945409925452566131519339 53918114888178849197279009)
        ·
          refine ⟨40438586166134136897959257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53918114888178849197279009 40438586166134136897959257)
          ·
            refine ⟨30328939624600602673469443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40438586166134136897959257 30328939624600602673469443)
            ·
              refine ⟨45493409436900904010204165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30328939624600602673469443 45493409436900904010204165)
              ·
                refine ⟨8530014269418919501913281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45493409436900904010204165 8530014269418919501913281)
                ·
                  refine ⟨6397510702064189626434961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8530014269418919501913281 6397510702064189626434961)
                  ·
                    refine ⟨4798133026548142219826221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6397510702064189626434961 4798133026548142219826221)
                    ·
                      refine ⟨1799299884955553332434833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798133026548142219826221 1799299884955553332434833)
                      ·
                        rfl

theorem cell23_3504124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_3504124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504124 prefixEnd_3504124 := by exact prefixLift 3504124
  have htrace : WordTrace (prefixWord ++ tailWord_3504124) baseStart_3504124 baseEnd_3504124 := by
    simpa [prefixWord, tailWord_3504124, baseEnd_3504124] using wordTrace_append hprefix tailTrace_3504124
  have hstable : (prefixWord ++ tailWord_3504124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504124).length < 2 ^ (prefixWord ++ tailWord_3504124).sum := by decide
  have hdescent : baseEnd_3504124 < baseStart_3504124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504137 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_3504137 : Nat := 118140960795 + 3504137 * 2 ^ 59
def prefixEnd_3504137 : Nat := 4983230072969 + 3 ^ 40 * 3504137 * 2
def baseEnd_3504137 : Nat := 1799306560204061781572273

theorem tailTrace_3504137 : CollatzResearch.WordTrace tailWord_3504137 prefixEnd_3504137 1799306560204061781572273 := by
  unfold tailWord_3504137
  simp only [CollatzResearch.WordTrace]
  refine ⟨127806376106117582798958665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85204250737411721865972443 127806376106117582798958665)
  ·
    refine ⟨95854782079588187099218999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127806376106117582798958665 95854782079588187099218999)
    ·
      refine ⟨143782173119382280648828499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95854782079588187099218999 143782173119382280648828499)
      ·
        refine ⟨215673259679073420973242749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143782173119382280648828499 215673259679073420973242749)
        ·
          refine ⟨80877472379652532864966031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215673259679073420973242749 80877472379652532864966031)
          ·
            refine ⟨121316208569478799297449047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80877472379652532864966031 121316208569478799297449047)
            ·
              refine ⟨181974312854218198946173571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121316208569478799297449047 181974312854218198946173571)
              ·
                refine ⟨272961469281327298419260357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181974312854218198946173571 272961469281327298419260357)
                ·
                  refine ⟨51180275490248868453611317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 272961469281327298419260357 51180275490248868453611317)
                  ·
                    refine ⟨4798150827210831417526061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51180275490248868453611317 4798150827210831417526061)
                    ·
                      refine ⟨1799306560204061781572273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798150827210831417526061 1799306560204061781572273)
                      ·
                        rfl

theorem cell23_3504137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_3504137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504137 prefixEnd_3504137 := by exact prefixLift 3504137
  have htrace : WordTrace (prefixWord ++ tailWord_3504137) baseStart_3504137 baseEnd_3504137 := by
    simpa [prefixWord, tailWord_3504137, baseEnd_3504137] using wordTrace_append hprefix tailTrace_3504137
  have hstable : (prefixWord ++ tailWord_3504137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504137).length < 2 ^ (prefixWord ++ tailWord_3504137).sum := by decide
  have hdescent : baseEnd_3504137 < baseStart_3504137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504181 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_3504181 : Nat := 118140960795 + 3504181 * 2 ^ 59
def prefixEnd_3504181 : Nat := 4983230072969 + 3 ^ 40 * 3504181 * 2
def baseEnd_3504181 : Nat := 1799329153352859609422071

theorem tailTrace_3504181 : CollatzResearch.WordTrace tailWord_3504181 prefixEnd_3504181 1799329153352859609422071 := by
  unfold tailWord_3504181
  simp only [CollatzResearch.WordTrace]
  refine ⟨127807980917958178313560397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85205320611972118875706931 127807980917958178313560397)
  ·
    refine ⟨47927992844234316867585149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127807980917958178313560397 47927992844234316867585149)
    ·
      refine ⟨17972997316587868825344431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47927992844234316867585149 17972997316587868825344431)
      ·
        refine ⟨26959495974881803238016647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17972997316587868825344431 26959495974881803238016647)
        ·
          refine ⟨40439243962322704857024971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26959495974881803238016647 40439243962322704857024971)
          ·
            refine ⟨60658865943484057285537457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40439243962322704857024971 60658865943484057285537457)
            ·
              refine ⟨45494149457613042964153093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60658865943484057285537457 45494149457613042964153093)
              ·
                refine ⟨8530153023302445555778705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45494149457613042964153093 8530153023302445555778705)
                ·
                  refine ⟨6397614767476834166834029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8530153023302445555778705 6397614767476834166834029)
                  ·
                    refine ⟨2399105537803812812562761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6397614767476834166834029 2399105537803812812562761)
                    ·
                      refine ⟨1799329153352859609422071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399105537803812812562761 1799329153352859609422071)
                      ·
                        rfl

theorem cell23_3504181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_3504181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504181 prefixEnd_3504181 := by exact prefixLift 3504181
  have htrace : WordTrace (prefixWord ++ tailWord_3504181) baseStart_3504181 baseEnd_3504181 := by
    simpa [prefixWord, tailWord_3504181, baseEnd_3504181] using wordTrace_append hprefix tailTrace_3504181
  have hstable : (prefixWord ++ tailWord_3504181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504181).length < 2 ^ (prefixWord ++ tailWord_3504181).sum := by decide
  have hdescent : baseEnd_3504181 < baseStart_3504181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504188 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 1, 1, 3]
def baseStart_3504188 : Nat := 118140960795 + 3504188 * 2 ^ 59
def prefixEnd_3504188 : Nat := 4983230072969 + 3 ^ 40 * 3504188 * 2
def baseEnd_3504188 : Nat := 1799332747717441082034539

theorem tailTrace_3504188 : CollatzResearch.WordTrace tailWord_3504188 prefixEnd_3504188 1799332747717441082034539 := by
  unfold tailWord_3504188
  simp only [CollatzResearch.WordTrace]
  refine ⟨63904118114466409254532609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85205490819288545672710145 63904118114466409254532609)
  ·
    refine ⟨47928088585849806940899457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63904118114466409254532609 47928088585849806940899457)
    ·
      refine ⟨35946066439387355205674593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47928088585849806940899457 35946066439387355205674593)
      ·
        refine ⟨26959549829540516404255945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35946066439387355205674593 26959549829540516404255945)
        ·
          refine ⟨20219662372155387303191959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26959549829540516404255945 20219662372155387303191959)
          ·
            refine ⟨30329493558233080954787939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20219662372155387303191959 30329493558233080954787939)
            ·
              refine ⟨45494240337349621432181909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30329493558233080954787939 45494240337349621432181909)
              ·
                refine ⟨2132542515813263504633527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45494240337349621432181909 2132542515813263504633527)
                ·
                  refine ⟨3198813773719895256950291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132542515813263504633527 3198813773719895256950291)
                  ·
                    refine ⟨4798220660579842885425437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3198813773719895256950291 4798220660579842885425437)
                    ·
                      refine ⟨1799332747717441082034539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798220660579842885425437 1799332747717441082034539)
                      ·
                        rfl

theorem cell23_3504188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_3504188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504188 prefixEnd_3504188 := by exact prefixLift 3504188
  have htrace : WordTrace (prefixWord ++ tailWord_3504188) baseStart_3504188 baseEnd_3504188 := by
    simpa [prefixWord, tailWord_3504188, baseEnd_3504188] using wordTrace_append hprefix tailTrace_3504188
  have hstable : (prefixWord ++ tailWord_3504188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504188).length < 2 ^ (prefixWord ++ tailWord_3504188).sum := by decide
  have hdescent : baseEnd_3504188 < baseStart_3504188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504198 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3504198 : Nat := 118140960795 + 3504198 * 2 ^ 59
def prefixEnd_3504198 : Nat := 4983230072969 + 3 ^ 40 * 3504198 * 2
def baseEnd_3504198 : Nat := 1799337882523986042909493

theorem tailTrace_3504198 : CollatzResearch.WordTrace tailWord_3504198 prefixEnd_3504198 1799337882523986042909493 := by
  unfold tailWord_3504198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994018779965518444279039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85205733972597726811286165 3994018779965518444279039)
  ·
    refine ⟨5991028169948277666418559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3994018779965518444279039 5991028169948277666418559)
    ·
      refine ⟨8986542254922416499627839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5991028169948277666418559 8986542254922416499627839)
      ·
        refine ⟨13479813382383624749441759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986542254922416499627839 13479813382383624749441759)
        ·
          refine ⟨20219720073575437124162639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13479813382383624749441759 20219720073575437124162639)
          ·
            refine ⟨30329580110363155686243959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20219720073575437124162639 30329580110363155686243959)
            ·
              refine ⟨45494370165544733529365939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30329580110363155686243959 45494370165544733529365939)
              ·
                refine ⟨68241555248317100294048909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45494370165544733529365939 68241555248317100294048909)
                ·
                  refine ⟨25590583218118912610268341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68241555248317100294048909 25590583218118912610268341)
                  ·
                    refine ⟨2399117176698648057212657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25590583218118912610268341 2399117176698648057212657)
                    ·
                      refine ⟨1799337882523986042909493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399117176698648057212657 1799337882523986042909493)
                      ·
                        rfl

theorem cell23_3504198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3504198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504198 prefixEnd_3504198 := by exact prefixLift 3504198
  have htrace : WordTrace (prefixWord ++ tailWord_3504198) baseStart_3504198 baseEnd_3504198 := by
    simpa [prefixWord, tailWord_3504198, baseEnd_3504198] using wordTrace_append hprefix tailTrace_3504198
  have hstable : (prefixWord ++ tailWord_3504198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504198).length < 2 ^ (prefixWord ++ tailWord_3504198).sum := by decide
  have hdescent : baseEnd_3504198 < baseStart_3504198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504204 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 1, 6]
def baseStart_3504204 : Nat := 118140960795 + 3504204 * 2 ^ 59
def prefixEnd_3504204 : Nat := 4983230072969 + 3 ^ 40 * 3504204 * 2
def baseEnd_3504204 : Nat := 599780321135971006478155

theorem tailTrace_3504204 : CollatzResearch.WordTrace tailWord_3504204 prefixEnd_3504204 599780321135971006478155 := by
  unfold tailWord_3504204
  simp only [CollatzResearch.WordTrace]
  refine ⟨63904409898437426620823833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85205879864583235494431777 63904409898437426620823833)
  ·
    refine ⟨47928307423828069965617875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63904409898437426620823833 47928307423828069965617875)
    ·
      refine ⟨71892461135742104948426813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47928307423828069965617875 71892461135742104948426813)
      ·
        refine ⟨26959672925903289355660055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71892461135742104948426813 26959672925903289355660055)
        ·
          refine ⟨40439509388854934033490083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26959672925903289355660055 40439509388854934033490083)
          ·
            refine ⟨60659264083282401050235125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40439509388854934033490083 60659264083282401050235125)
            ·
              refine ⟨5686806007807725098459543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60659264083282401050235125 5686806007807725098459543)
              ·
                refine ⟨8530209011711587647689315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5686806007807725098459543 8530209011711587647689315)
                ·
                  refine ⟨12795313517567381471533973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8530209011711587647689315 12795313517567381471533973)
                  ·
                    refine ⟨599780321135971006478155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12795313517567381471533973 599780321135971006478155)
                    ·
                      rfl

theorem cell23_3504204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 1, 6].length) (baseStart_3504204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504204 prefixEnd_3504204 := by exact prefixLift 3504204
  have htrace : WordTrace (prefixWord ++ tailWord_3504204) baseStart_3504204 baseEnd_3504204 := by
    simpa [prefixWord, tailWord_3504204, baseEnd_3504204] using wordTrace_append hprefix tailTrace_3504204
  have hstable : (prefixWord ++ tailWord_3504204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504204).length < 2 ^ (prefixWord ++ tailWord_3504204).sum := by decide
  have hdescent : baseEnd_3504204 < baseStart_3504204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504207 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_3504207 : Nat := 118140960795 + 3504207 * 2 ^ 59
def prefixEnd_3504207 : Nat := 4983230072969 + 3 ^ 40 * 3504207 * 2
def baseEnd_3504207 : Nat := 1799342503849876507696951

theorem tailTrace_3504207 : CollatzResearch.WordTrace tailWord_3504207 prefixEnd_3504207 1799342503849876507696951 := by
  unfold tailWord_3504207
  simp only [CollatzResearch.WordTrace]
  refine ⟨127808929215863984754006875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85205952810575989836004583 127808929215863984754006875)
  ·
    refine ⟨191713393823795977131010313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127808929215863984754006875 191713393823795977131010313)
    ·
      refine ⟨143785045367846982848257735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191713393823795977131010313 143785045367846982848257735)
      ·
        refine ⟨215677568051770474272386603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143785045367846982848257735 215677568051770474272386603)
        ·
          refine ⟨323516352077655711408579905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215677568051770474272386603 323516352077655711408579905)
          ·
            refine ⟨242637264058241783556434929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323516352077655711408579905 242637264058241783556434929)
            ·
              refine ⟨181977948043681337667326197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242637264058241783556434929 181977948043681337667326197)
              ·
                refine ⟨17060432629095125406311831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181977948043681337667326197 17060432629095125406311831)
                ·
                  refine ⟨25590648943642688109467747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17060432629095125406311831 25590648943642688109467747)
                  ·
                    refine ⟨38385973415464032164201621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25590648943642688109467747 38385973415464032164201621)
                    ·
                      refine ⟨1799342503849876507696951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38385973415464032164201621 1799342503849876507696951)
                      ·
                        rfl

theorem cell23_3504207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_3504207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504207 prefixEnd_3504207 := by exact prefixLift 3504207
  have htrace : WordTrace (prefixWord ++ tailWord_3504207) baseStart_3504207 baseEnd_3504207 := by
    simpa [prefixWord, tailWord_3504207, baseEnd_3504207] using wordTrace_append hprefix tailTrace_3504207
  have hstable : (prefixWord ++ tailWord_3504207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504207).length < 2 ^ (prefixWord ++ tailWord_3504207).sum := by decide
  have hdescent : baseEnd_3504207 < baseStart_3504207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504217 : List Nat := [1, 2, 1, 2, 2, 1, 5, 9]
def baseStart_3504217 : Nat := 118140960795 + 3504217 * 2 ^ 59
def prefixEnd_3504217 : Nat := 4983230072969 + 3 ^ 40 * 3504217 * 2
def baseEnd_3504217 : Nat := 66642505135423017354515

theorem tailTrace_3504217 : CollatzResearch.WordTrace tailWord_3504217 prefixEnd_3504217 66642505135423017354515 := by
  unfold tailWord_3504217
  simp only [CollatzResearch.WordTrace]
  refine ⟨127809293945827756461870905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85206195963885170974580603 127809293945827756461870905)
  ·
    refine ⟨95856970459370817346403179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127809293945827756461870905 95856970459370817346403179)
    ·
      refine ⟨143785455689056226019604769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95856970459370817346403179 143785455689056226019604769)
      ·
        refine ⟨107839091766792169514703577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143785455689056226019604769 107839091766792169514703577)
        ·
          refine ⟨80879318825094127136027683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107839091766792169514703577 80879318825094127136027683)
          ·
            refine ⟨121318978237641190704041525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80879318825094127136027683 121318978237641190704041525)
            ·
              refine ⟨11373654209778861628503893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121318978237641190704041525 11373654209778861628503893)
              ·
                refine ⟨66642505135423017354515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11373654209778861628503893 66642505135423017354515)
                ·
                  rfl

theorem cell23_3504217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 9].length) (baseStart_3504217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504217 prefixEnd_3504217 := by exact prefixLift 3504217
  have htrace : WordTrace (prefixWord ++ tailWord_3504217) baseStart_3504217 baseEnd_3504217 := by
    simpa [prefixWord, tailWord_3504217, baseEnd_3504217] using wordTrace_append hprefix tailTrace_3504217
  have hstable : (prefixWord ++ tailWord_3504217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504217).length < 2 ^ (prefixWord ++ tailWord_3504217).sum := by decide
  have hdescent : baseEnd_3504217 < baseStart_3504217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504231 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_3504231 : Nat := 118140960795 + 3504231 * 2 ^ 59
def prefixEnd_3504231 : Nat := 4983230072969 + 3 ^ 40 * 3504231 * 2
def baseEnd_3504231 : Nat := 1799354827385584413796841

theorem tailTrace_3504231 : CollatzResearch.WordTrace tailWord_3504231 prefixEnd_3504231 1799354827385584413796841 := by
  unfold tailWord_3504231
  simp only [CollatzResearch.WordTrace]
  refine ⟨127809804567777036852880547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85206536378518024568587031 127809804567777036852880547)
  ·
    refine ⟨191714706851665555279320821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127809804567777036852880547 191714706851665555279320821)
    ·
      refine ⟨17973253767343645807436327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191714706851665555279320821 17973253767343645807436327)
      ·
        refine ⟨26959880651015468711154491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17973253767343645807436327 26959880651015468711154491)
        ·
          refine ⟨40439820976523203066731737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26959880651015468711154491 40439820976523203066731737)
          ·
            refine ⟨30329865732392402300048803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40439820976523203066731737 30329865732392402300048803)
            ·
              refine ⟨45494798598588603450073205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30329865732392402300048803 45494798598588603450073205)
              ·
                refine ⟨4265137368617681573444363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45494798598588603450073205 4265137368617681573444363)
                ·
                  refine ⟨6397706052926522360166545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265137368617681573444363 6397706052926522360166545)
                  ·
                    refine ⟨4798279539694891770124909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6397706052926522360166545 4798279539694891770124909)
                    ·
                      refine ⟨1799354827385584413796841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798279539694891770124909 1799354827385584413796841)
                      ·
                        rfl

theorem cell23_3504231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_3504231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504231 prefixEnd_3504231 := by exact prefixLift 3504231
  have htrace : WordTrace (prefixWord ++ tailWord_3504231) baseStart_3504231 baseEnd_3504231 := by
    simpa [prefixWord, tailWord_3504231, baseEnd_3504231] using wordTrace_append hprefix tailTrace_3504231
  have hstable : (prefixWord ++ tailWord_3504231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504231).length < 2 ^ (prefixWord ++ tailWord_3504231).sum := by decide
  have hdescent : baseEnd_3504231 < baseStart_3504231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504267 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10]
def baseStart_3504267 : Nat := 118140960795 + 3504267 * 2 ^ 59
def prefixEnd_3504267 : Nat := 4983230072969 + 3 ^ 40 * 3504267 * 2
def baseEnd_3504267 : Nat := 1799373312689146272946675

theorem tailTrace_3504267 : CollatzResearch.WordTrace tailWord_3504267 prefixEnd_3504267 1799373312689146272946675 := by
  unfold tailWord_3504267
  simp only [CollatzResearch.WordTrace]
  refine ⟨127811117595646615001191055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85207411730431076667460703 127811117595646615001191055)
  ·
    refine ⟨191716676393469922501786583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127811117595646615001191055 191716676393469922501786583)
    ·
      refine ⟨287575014590204883752679875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191716676393469922501786583 287575014590204883752679875)
      ·
        refine ⟨431362521885307325629019813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287575014590204883752679875 431362521885307325629019813)
        ·
          refine ⟨80880472853495123555441215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431362521885307325629019813 80880472853495123555441215)
          ·
            refine ⟨121320709280242685333161823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80880472853495123555441215 121320709280242685333161823)
            ·
              refine ⟨181981063920364027999742735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121320709280242685333161823 181981063920364027999742735)
              ·
                refine ⟨272971595880546041999614103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181981063920364027999742735 272971595880546041999614103)
                ·
                  refine ⟨409457393820819062999421155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272971595880546041999614103 409457393820819062999421155)
                  ·
                    refine ⟨614186090731228594499131733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 409457393820819062999421155 614186090731228594499131733)
                    ·
                      refine ⟨1799373312689146272946675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 614186090731228594499131733 1799373312689146272946675)
                      ·
                        rfl

theorem cell23_3504267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_3504267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504267 prefixEnd_3504267 := by exact prefixLift 3504267
  have htrace : WordTrace (prefixWord ++ tailWord_3504267) baseStart_3504267 baseEnd_3504267 := by
    simpa [prefixWord, tailWord_3504267, baseEnd_3504267] using wordTrace_append hprefix tailTrace_3504267
  have hstable : (prefixWord ++ tailWord_3504267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504267).length < 2 ^ (prefixWord ++ tailWord_3504267).sum := by decide
  have hdescent : baseEnd_3504267 < baseStart_3504267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504301 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3504301 : Nat := 118140960795 + 3504301 * 2 ^ 59
def prefixEnd_3504301 : Nat := 4983230072969 + 3 ^ 40 * 3504301 * 2
def baseEnd_3504301 : Nat := 1799390771031399139921519

theorem tailTrace_3504301 : CollatzResearch.WordTrace tailWord_3504301 prefixEnd_3504301 1799390771031399139921519 := by
  unfold tailWord_3504301
  simp only [CollatzResearch.WordTrace]
  refine ⟨127812357677523438807928757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85208238451682292538619171 127812357677523438807928757)
  ·
    refine ⟨11982408532267822388243321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127812357677523438807928757 11982408532267822388243321)
    ·
      refine ⟨8986806399200866791182491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11982408532267822388243321 8986806399200866791182491)
      ·
        refine ⟨13480209598801300186773737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8986806399200866791182491 13480209598801300186773737)
        ·
          refine ⟨10110157199100975140080303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13480209598801300186773737 10110157199100975140080303)
          ·
            refine ⟨15165235798651462710120455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10110157199100975140080303 15165235798651462710120455)
            ·
              refine ⟨22747853697977194065180683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15165235798651462710120455 22747853697977194065180683)
              ·
                refine ⟨34121780546965791097771025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22747853697977194065180683 34121780546965791097771025)
                ·
                  refine ⟨25591335410224343323328269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34121780546965791097771025 25591335410224343323328269)
                  ·
                    refine ⟨9596750778834128746248101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25591335410224343323328269 9596750778834128746248101)
                    ·
                      refine ⟨1799390771031399139921519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9596750778834128746248101 1799390771031399139921519)
                      ·
                        rfl

theorem cell23_3504301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3504301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504301 prefixEnd_3504301 := by exact prefixLift 3504301
  have htrace : WordTrace (prefixWord ++ tailWord_3504301) baseStart_3504301 baseEnd_3504301 := by
    simpa [prefixWord, tailWord_3504301, baseEnd_3504301] using wordTrace_append hprefix tailTrace_3504301
  have hstable : (prefixWord ++ tailWord_3504301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504301).length < 2 ^ (prefixWord ++ tailWord_3504301).sum := by decide
  have hdescent : baseEnd_3504301 < baseStart_3504301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504314 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_3504314 : Nat := 118140960795 + 3504314 * 2 ^ 59
def prefixEnd_3504314 : Nat := 4983230072969 + 3 ^ 40 * 3504314 * 2
def baseEnd_3504314 : Nat := 1799397446279907589058959

theorem tailTrace_3504314 : CollatzResearch.WordTrace tailWord_3504314 prefixEnd_3504314 1799397446279907589058959 := by
  unfold tailWord_3504314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31953207956619085507037999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85208554550984228018767997 31953207956619085507037999)
  ·
    refine ⟨47929811934928628260556999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31953207956619085507037999 47929811934928628260556999)
    ·
      refine ⟨71894717902392942390835499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47929811934928628260556999 71894717902392942390835499)
      ·
        refine ⟨107842076853589413586253249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71894717902392942390835499 107842076853589413586253249)
        ·
          refine ⟨80881557640192060189689937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107842076853589413586253249 80881557640192060189689937)
          ·
            refine ⟨60661168230144045142267453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80881557640192060189689937 60661168230144045142267453)
            ·
              refine ⟨22747938086304016928350295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60661168230144045142267453 22747938086304016928350295)
              ·
                refine ⟨34121907129456025392525443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22747938086304016928350295 34121907129456025392525443)
                ·
                  refine ⟨51182860694184038088788165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34121907129456025392525443 51182860694184038088788165)
                  ·
                    refine ⟨9596786380159507141647781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51182860694184038088788165 9596786380159507141647781)
                    ·
                      refine ⟨1799397446279907589058959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9596786380159507141647781 1799397446279907589058959)
                      ·
                        rfl

theorem cell23_3504314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_3504314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504314 prefixEnd_3504314 := by exact prefixLift 3504314
  have htrace : WordTrace (prefixWord ++ tailWord_3504314) baseStart_3504314 baseEnd_3504314 := by
    simpa [prefixWord, tailWord_3504314, baseEnd_3504314] using wordTrace_append hprefix tailTrace_3504314
  have hstable : (prefixWord ++ tailWord_3504314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504314).length < 2 ^ (prefixWord ++ tailWord_3504314).sum := by decide
  have hdescent : baseEnd_3504314 < baseStart_3504314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504322 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_3504322 : Nat := 118140960795 + 3504322 * 2 ^ 59
def prefixEnd_3504322 : Nat := 4983230072969 + 3 ^ 40 * 3504322 * 2
def baseEnd_3504322 : Nat := 1799401554125143557758923

theorem tailTrace_3504322 : CollatzResearch.WordTrace tailWord_3504322 prefixEnd_3504322 1799401554125143557758923 := by
  unfold tailWord_3504322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31953280902611839848610805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85208749073631572929628813 31953280902611839848610805)
  ·
    refine ⟨2995620084619859985807263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31953280902611839848610805 2995620084619859985807263)
    ·
      refine ⟨4493430126929789978710895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995620084619859985807263 4493430126929789978710895)
      ·
        refine ⟨6740145190394684968066343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493430126929789978710895 6740145190394684968066343)
        ·
          refine ⟨10110217785592027452099515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740145190394684968066343 10110217785592027452099515)
          ·
            refine ⟨15165326678388041178149273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10110217785592027452099515 15165326678388041178149273)
            ·
              refine ⟨11373995008791030883611955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15165326678388041178149273 11373995008791030883611955)
              ·
                refine ⟨17060992513186546325417933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11373995008791030883611955 17060992513186546325417933)
                ·
                  refine ⟨6397872192444954872031725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17060992513186546325417933 6397872192444954872031725)
                  ·
                    refine ⟨2399202072166858077011897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6397872192444954872031725 2399202072166858077011897)
                    ·
                      refine ⟨1799401554125143557758923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399202072166858077011897 1799401554125143557758923)
                      ·
                        rfl

theorem cell23_3504322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_3504322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504322 prefixEnd_3504322 := by exact prefixLift 3504322
  have htrace : WordTrace (prefixWord ++ tailWord_3504322) baseStart_3504322 baseEnd_3504322 := by
    simpa [prefixWord, tailWord_3504322, baseEnd_3504322] using wordTrace_append hprefix tailTrace_3504322
  have hstable : (prefixWord ++ tailWord_3504322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504322).length < 2 ^ (prefixWord ++ tailWord_3504322).sum := by decide
  have hdescent : baseEnd_3504322 < baseStart_3504322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504364 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3504364 : Nat := 118140960795 + 3504364 * 2 ^ 59
def prefixEnd_3504364 : Nat := 4983230072969 + 3 ^ 40 * 3504364 * 2
def baseEnd_3504364 : Nat := 1799423120312632393433729

theorem tailTrace_3504364 : CollatzResearch.WordTrace tailWord_3504364 prefixEnd_3504364 1799423120312632393433729 := by
  unfold tailWord_3504364
  simp only [CollatzResearch.WordTrace]
  refine ⟨63907327738147600283736073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85209770317530133711648097 63907327738147600283736073)
  ·
    refine ⟨47930495803610700212802055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63907327738147600283736073 47930495803610700212802055)
    ·
      refine ⟨71895743705416050319203083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47930495803610700212802055 71895743705416050319203083)
      ·
        refine ⟨107843615558124075478804625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71895743705416050319203083 107843615558124075478804625)
        ·
          refine ⟨80882711668593056609103469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107843615558124075478804625 80882711668593056609103469)
          ·
            refine ⟨30331016875722396228413801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80882711668593056609103469 30331016875722396228413801)
            ·
              refine ⟨22748262656791797171310351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30331016875722396228413801 22748262656791797171310351)
              ·
                refine ⟨34122393985187695756965527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22748262656791797171310351 34122393985187695756965527)
                ·
                  refine ⟨51183590977781543635448291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34122393985187695756965527 51183590977781543635448291)
                  ·
                    refine ⟨76775386466672315453172437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51183590977781543635448291 76775386466672315453172437)
                    ·
                      refine ⟨1799423120312632393433729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76775386466672315453172437 1799423120312632393433729)
                      ·
                        rfl

theorem cell23_3504364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3504364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504364 prefixEnd_3504364 := by exact prefixLift 3504364
  have htrace : WordTrace (prefixWord ++ tailWord_3504364) baseStart_3504364 baseEnd_3504364 := by
    simpa [prefixWord, tailWord_3504364, baseEnd_3504364] using wordTrace_append hprefix tailTrace_3504364
  have hstable : (prefixWord ++ tailWord_3504364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504364).length < 2 ^ (prefixWord ++ tailWord_3504364).sum := by decide
  have hdescent : baseEnd_3504364 < baseStart_3504364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504411 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 3]
def baseStart_3504411 : Nat := 118140960795 + 3504411 * 2 ^ 59
def prefixEnd_3504411 : Nat := 4983230072969 + 3 ^ 40 * 3504411 * 2
def baseEnd_3504411 : Nat := 1799447253903393709546013

theorem tailTrace_3504411 : CollatzResearch.WordTrace tailWord_3504411 prefixEnd_3504411 1799447253903393709546013 := by
  unfold tailWord_3504411
  simp only [CollatzResearch.WordTrace]
  refine ⟨127816369707124927594433087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85210913138083285062955391 127816369707124927594433087)
  ·
    refine ⟨191724554560687391391649631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127816369707124927594433087 191724554560687391391649631)
    ·
      refine ⟨287586831841031087087474447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191724554560687391391649631 287586831841031087087474447)
      ·
        refine ⟨431380247761546630631211671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287586831841031087087474447 431380247761546630631211671)
        ·
          refine ⟨647070371642319945946817507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431380247761546630631211671 647070371642319945946817507)
          ·
            refine ⟨970605557463479918920226261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647070371642319945946817507 970605557463479918920226261)
            ·
              refine ⟨22748567753050310599692803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 970605557463479918920226261 22748567753050310599692803)
              ·
                refine ⟨34122851629575465899539205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22748567753050310599692803 34122851629575465899539205)
                ·
                  refine ⟨6398034680545399856163601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34122851629575465899539205 6398034680545399856163601)
                  ·
                    refine ⟨4798526010409049892122701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6398034680545399856163601 4798526010409049892122701)
                    ·
                      refine ⟨1799447253903393709546013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798526010409049892122701 1799447253903393709546013)
                      ·
                        rfl

theorem cell23_3504411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 3].length) (baseStart_3504411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504411 prefixEnd_3504411 := by exact prefixLift 3504411
  have htrace : WordTrace (prefixWord ++ tailWord_3504411) baseStart_3504411 baseEnd_3504411 := by
    simpa [prefixWord, tailWord_3504411, baseEnd_3504411] using wordTrace_append hprefix tailTrace_3504411
  have hstable : (prefixWord ++ tailWord_3504411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504411).length < 2 ^ (prefixWord ++ tailWord_3504411).sum := by decide
  have hdescent : baseEnd_3504411 < baseStart_3504411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504469 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_3504469 : Nat := 118140960795 + 3504469 * 2 ^ 59
def prefixEnd_3504469 : Nat := 4983230072969 + 3 ^ 40 * 3504469 * 2
def baseEnd_3504469 : Nat := 599825678593784827540249

theorem tailTrace_3504469 : CollatzResearch.WordTrace tailWord_3504469 prefixEnd_3504469 599825678593784827540249 := by
  unfold tailWord_3504469
  simp only [CollatzResearch.WordTrace]
  refine ⟨127818485140914803500044461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85212323427276535666696307 127818485140914803500044461)
  ·
    refine ⟨47931931927843051312516673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127818485140914803500044461 47931931927843051312516673)
    ·
      refine ⟨35948948945882288484387505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47931931927843051312516673 35948948945882288484387505)
      ·
        refine ⟨26961711709411716363290629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35948948945882288484387505 26961711709411716363290629)
        ·
          refine ⟨5055320945514696818116993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26961711709411716363290629 5055320945514696818116993)
          ·
            refine ⟨3791490709136022613587745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055320945514696818116993 3791490709136022613587745)
            ·
              refine ⟨2843618031852016960190809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791490709136022613587745 2843618031852016960190809)
              ·
                refine ⟨2132713523889012720143107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843618031852016960190809 2132713523889012720143107)
                ·
                  refine ⟨3199070285833519080214661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132713523889012720143107 3199070285833519080214661)
                  ·
                    refine ⟨599825678593784827540249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199070285833519080214661 599825678593784827540249)
                    ·
                      rfl

theorem cell23_3504469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_3504469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504469 prefixEnd_3504469 := by exact prefixLift 3504469
  have htrace : WordTrace (prefixWord ++ tailWord_3504469) baseStart_3504469 baseEnd_3504469 := by
    simpa [prefixWord, tailWord_3504469, baseEnd_3504469] using wordTrace_append hprefix tailTrace_3504469
  have hstable : (prefixWord ++ tailWord_3504469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504469).length < 2 ^ (prefixWord ++ tailWord_3504469).sum := by decide
  have hdescent : baseEnd_3504469 < baseStart_3504469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504498 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3504498 : Nat := 118140960795 + 3504498 * 2 ^ 59
def prefixEnd_3504498 : Nat := 4983230072969 + 3 ^ 40 * 3504498 * 2
def baseEnd_3504498 : Nat := 1799491926720334869158113

theorem tailTrace_3504498 : CollatzResearch.WordTrace tailWord_3504498 prefixEnd_3504498 1799491926720334869158113 := by
  unfold tailWord_3504498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31954885714452435363212537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85213028571873160968566765 31954885714452435363212537)
  ·
    refine ⟨23966164285839326522409403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31954885714452435363212537 23966164285839326522409403)
    ·
      refine ⟨35949246428758989783614105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23966164285839326522409403 35949246428758989783614105)
      ·
        refine ⟨26961934821569242337710579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35949246428758989783614105 26961934821569242337710579)
        ·
          refine ⟨40442902232353863506565869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26961934821569242337710579 40442902232353863506565869)
          ·
            refine ⟨15166088337132698814962201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40442902232353863506565869 15166088337132698814962201)
            ·
              refine ⟨11374566252849524111221651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15166088337132698814962201 11374566252849524111221651)
              ·
                refine ⟨17061849379274286166832477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11374566252849524111221651 17061849379274286166832477)
                ·
                  refine ⟨6398193517227857312562179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17061849379274286166832477 6398193517227857312562179)
                  ·
                    refine ⟨9597290275841785968843269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398193517227857312562179 9597290275841785968843269)
                    ·
                      refine ⟨1799491926720334869158113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9597290275841785968843269 1799491926720334869158113)
                      ·
                        rfl

theorem cell23_3504498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3504498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504498 prefixEnd_3504498 := by exact prefixLift 3504498
  have htrace : WordTrace (prefixWord ++ tailWord_3504498) baseStart_3504498 baseEnd_3504498 := by
    simpa [prefixWord, tailWord_3504498, baseEnd_3504498] using wordTrace_append hprefix tailTrace_3504498
  have hstable : (prefixWord ++ tailWord_3504498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504498).length < 2 ^ (prefixWord ++ tailWord_3504498).sum := by decide
  have hdescent : baseEnd_3504498 < baseStart_3504498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504515 : List Nat := [1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 4]
def baseStart_3504515 : Nat := 118140960795 + 3504515 * 2 ^ 59
def prefixEnd_3504515 : Nat := 4983230072969 + 3 ^ 40 * 3504515 * 2
def baseEnd_3504515 : Nat := 1799500655891461302645535

theorem tailTrace_3504515 : CollatzResearch.WordTrace tailWord_3504515 prefixEnd_3504515 1799500655891461302645535 := by
  unfold tailWord_3504515
  simp only [CollatzResearch.WordTrace]
  refine ⟨127820162898748153356218999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85213441932498768904145999 127820162898748153356218999)
  ·
    refine ⟨191730244348122230034328499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127820162898748153356218999 191730244348122230034328499)
    ·
      refine ⟨287595366522183345051492749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191730244348122230034328499 287595366522183345051492749)
      ·
        refine ⟨107848262445818754394309781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287595366522183345051492749 107848262445818754394309781)
        ·
          refine ⟨5055387302147754112233271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107848262445818754394309781 5055387302147754112233271)
          ·
            refine ⟨7583080953221631168349907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055387302147754112233271 7583080953221631168349907)
            ·
              refine ⟨11374621429832446752524861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583080953221631168349907 11374621429832446752524861)
              ·
                refine ⟨4265483036187167532196823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11374621429832446752524861 4265483036187167532196823)
                ·
                  refine ⟨6398224554280751298295235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265483036187167532196823 6398224554280751298295235)
                  ·
                    refine ⟨9597336831421126947442853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398224554280751298295235 9597336831421126947442853)
                    ·
                      refine ⟨1799500655891461302645535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9597336831421126947442853 1799500655891461302645535)
                      ·
                        rfl

theorem cell23_3504515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_3504515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504515 prefixEnd_3504515 := by exact prefixLift 3504515
  have htrace : WordTrace (prefixWord ++ tailWord_3504515) baseStart_3504515 baseEnd_3504515 := by
    simpa [prefixWord, tailWord_3504515, baseEnd_3504515] using wordTrace_append hprefix tailTrace_3504515
  have hstable : (prefixWord ++ tailWord_3504515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504515).length < 2 ^ (prefixWord ++ tailWord_3504515).sum := by decide
  have hdescent : baseEnd_3504515 < baseStart_3504515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504521 : List Nat := [1, 2, 1, 1, 6, 2, 10]
def baseStart_3504521 : Nat := 118140960795 + 3504521 * 2 ^ 59
def prefixEnd_3504521 : Nat := 4983230072969 + 3 ^ 40 * 3504521 * 2
def baseEnd_3504521 : Nat := 22216095515745534310747

theorem tailTrace_3504521 : CollatzResearch.WordTrace tailWord_3504521 prefixEnd_3504521 22216095515745534310747 := by
  unfold tailWord_3504521
  simp only [CollatzResearch.WordTrace]
  refine ⟨127820381736726416380937417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85213587824484277587291611 127820381736726416380937417)
  ·
    refine ⟨95865286302544812285703063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127820381736726416380937417 95865286302544812285703063)
    ·
      refine ⟨143797929453817218428554595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95865286302544812285703063 143797929453817218428554595)
      ·
        refine ⟨215696894180725827642831893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143797929453817218428554595 215696894180725827642831893)
        ·
          refine ⟨10110791914721523170757745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215696894180725827642831893 10110791914721523170757745)
          ·
            refine ⟨7583093936041142378068309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10110791914721523170757745 7583093936041142378068309)
            ·
              refine ⟨22216095515745534310747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7583093936041142378068309 22216095515745534310747)
              ·
                rfl

theorem cell23_3504521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 10].length) (baseStart_3504521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504521 prefixEnd_3504521 := by exact prefixLift 3504521
  have htrace : WordTrace (prefixWord ++ tailWord_3504521) baseStart_3504521 baseEnd_3504521 := by
    simpa [prefixWord, tailWord_3504521, baseEnd_3504521] using wordTrace_append hprefix tailTrace_3504521
  have hstable : (prefixWord ++ tailWord_3504521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504521).length < 2 ^ (prefixWord ++ tailWord_3504521).sum := by decide
  have hdescent : baseEnd_3504521 < baseStart_3504521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504531 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 3]
def baseStart_3504531 : Nat := 118140960795 + 3504531 * 2 ^ 59
def prefixEnd_3504531 : Nat := 4983230072969 + 3 ^ 40 * 3504531 * 2
def baseEnd_3504531 : Nat := 1799508871581933240045461

theorem tailTrace_3504531 : CollatzResearch.WordTrace tailWord_3504531 prefixEnd_3504531 1799508871581933240045461 := by
  unfold tailWord_3504531
  simp only [CollatzResearch.WordTrace]
  refine ⟨127820746466690188088801447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85213830977793458725867631 127820746466690188088801447)
  ·
    refine ⟨191731119700035282133202171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127820746466690188088801447 191731119700035282133202171)
    ·
      refine ⟨287596679550052923199803257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191731119700035282133202171 287596679550052923199803257)
      ·
        refine ⟨215697509662539692399852443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287596679550052923199803257 215697509662539692399852443)
        ·
          refine ⟨323546264493809538599778665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215697509662539692399852443 323546264493809538599778665)
          ·
            refine ⟨242659698370357153949833999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323546264493809538599778665 242659698370357153949833999)
            ·
              refine ⟨363989547555535730924750999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242659698370357153949833999 363989547555535730924750999)
              ·
                refine ⟨545984321333303596387126499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363989547555535730924750999 545984321333303596387126499)
                ·
                  refine ⟨818976481999955394580689749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545984321333303596387126499 818976481999955394580689749)
                  ·
                    refine ⟨4798690324218488640121229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 818976481999955394580689749 4798690324218488640121229)
                    ·
                      refine ⟨1799508871581933240045461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798690324218488640121229 1799508871581933240045461)
                      ·
                        rfl

theorem cell23_3504531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_3504531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504531 prefixEnd_3504531 := by exact prefixLift 3504531
  have htrace : WordTrace (prefixWord ++ tailWord_3504531) baseStart_3504531 baseEnd_3504531 := by
    simpa [prefixWord, tailWord_3504531, baseEnd_3504531] using wordTrace_append hprefix tailTrace_3504531
  have hstable : (prefixWord ++ tailWord_3504531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504531).length < 2 ^ (prefixWord ++ tailWord_3504531).sum := by decide
  have hdescent : baseEnd_3504531 < baseStart_3504531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504542 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3504542 : Nat := 118140960795 + 3504542 * 2 ^ 59
def prefixEnd_3504542 : Nat := 4983230072969 + 3 ^ 40 * 3504542 * 2
def baseEnd_3504542 : Nat := 599838173289710899002637

theorem tailTrace_3504542 : CollatzResearch.WordTrace tailWord_3504542 prefixEnd_3504542 599838173289710899002637 := by
  unfold tailWord_3504542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15977643458706292120931485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85214098446433557978301253 15977643458706292120931485)
  ·
    refine ⟨5991616297014859545349307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15977643458706292120931485 5991616297014859545349307)
    ·
      refine ⟨8987424445522289318023961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5991616297014859545349307 8987424445522289318023961)
      ·
        refine ⟨6740568334141716988517971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8987424445522289318023961 6740568334141716988517971)
        ·
          refine ⟨10110852501212575482776957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740568334141716988517971 10110852501212575482776957)
          ·
            refine ⟨3791569687954715806041359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10110852501212575482776957 3791569687954715806041359)
            ·
              refine ⟨5687354531932073709062039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3791569687954715806041359 5687354531932073709062039)
              ·
                refine ⟨8531031797898110563593059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687354531932073709062039 8531031797898110563593059)
                ·
                  refine ⟨12796547696847165845389589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531031797898110563593059 12796547696847165845389589)
                  ·
                    refine ⟨599838173289710899002637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12796547696847165845389589 599838173289710899002637)
                    ·
                      rfl

theorem cell23_3504542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3504542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504542 prefixEnd_3504542 := by exact prefixLift 3504542
  have htrace : WordTrace (prefixWord ++ tailWord_3504542) baseStart_3504542 baseEnd_3504542 := by
    simpa [prefixWord, tailWord_3504542, baseEnd_3504542] using wordTrace_append hprefix tailTrace_3504542
  have hstable : (prefixWord ++ tailWord_3504542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504542).length < 2 ^ (prefixWord ++ tailWord_3504542).sum := by decide
  have hdescent : baseEnd_3504542 < baseStart_3504542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504545 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3504545 : Nat := 118140960795 + 3504545 * 2 ^ 59
def prefixEnd_3504545 : Nat := 4983230072969 + 3 ^ 40 * 3504545 * 2
def baseEnd_3504545 : Nat := 1799516060311096185270397

theorem tailTrace_3504545 : CollatzResearch.WordTrace tailWord_3504545 prefixEnd_3504545 1799516060311096185270397 := by
  unfold tailWord_3504545
  simp only [CollatzResearch.WordTrace]
  refine ⟨127821257088639468479811089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85214171392426312319874059 127821257088639468479811089)
  ·
    refine ⟨95865942816479601359858317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127821257088639468479811089 95865942816479601359858317)
    ·
      refine ⟨35949728556179850509946869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95865942816479601359858317 35949728556179850509946869)
      ·
        refine ⟨3370287052141860985307519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35949728556179850509946869 3370287052141860985307519)
        ·
          refine ⟨5055430578212791477961279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370287052141860985307519 5055430578212791477961279)
          ·
            refine ⟨7583145867319187216941919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055430578212791477961279 7583145867319187216941919)
            ·
              refine ⟨11374718800978780825412879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583145867319187216941919 11374718800978780825412879)
              ·
                refine ⟨17062078201468171238119319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11374718800978780825412879 17062078201468171238119319)
                ·
                  refine ⟨25593117302202256857178979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17062078201468171238119319 25593117302202256857178979)
                  ·
                    refine ⟨38389675953303385285768469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25593117302202256857178979 38389675953303385285768469)
                    ·
                      refine ⟨1799516060311096185270397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38389675953303385285768469 1799516060311096185270397)
                      ·
                        rfl

theorem cell23_3504545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3504545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504545 prefixEnd_3504545 := by exact prefixLift 3504545
  have htrace : WordTrace (prefixWord ++ tailWord_3504545) baseStart_3504545 baseEnd_3504545 := by
    simpa [prefixWord, tailWord_3504545, baseEnd_3504545] using wordTrace_append hprefix tailTrace_3504545
  have hstable : (prefixWord ++ tailWord_3504545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504545).length < 2 ^ (prefixWord ++ tailWord_3504545).sum := by decide
  have hdescent : baseEnd_3504545 < baseStart_3504545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504552 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3504552 : Nat := 118140960795 + 3504552 * 2 ^ 59
def prefixEnd_3504552 : Nat := 4983230072969 + 3 ^ 40 * 3504552 * 2
def baseEnd_3504552 : Nat := 1799519654675677657882865

theorem tailTrace_3504552 : CollatzResearch.WordTrace tailWord_3504552 prefixEnd_3504552 1799519654675677657882865 := by
  unfold tailWord_3504552
  simp only [CollatzResearch.WordTrace]
  refine ⟨63910756199807054337657955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85214341599742739116877273 63910756199807054337657955)
  ·
    refine ⟨95866134299710581506486933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63910756199807054337657955 95866134299710581506486933)
    ·
      refine ⟨4493725045298933508116575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95866134299710581506486933 4493725045298933508116575)
      ·
        refine ⟨6740587567948400262174863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493725045298933508116575 6740587567948400262174863)
        ·
          refine ⟨10110881351922600393262295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740587567948400262174863 10110881351922600393262295)
          ·
            refine ⟨15166322027883900589893443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10110881351922600393262295 15166322027883900589893443)
            ·
              refine ⟨22749483041825850884840165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15166322027883900589893443 22749483041825850884840165)
              ·
                refine ⟨4265528070342347040907531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22749483041825850884840165 4265528070342347040907531)
                ·
                  refine ⟨6398292105513520561361297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265528070342347040907531 6398292105513520561361297)
                  ·
                    refine ⟨4798719079135140421020973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6398292105513520561361297 4798719079135140421020973)
                    ·
                      refine ⟨1799519654675677657882865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4798719079135140421020973 1799519654675677657882865)
                      ·
                        rfl

theorem cell23_3504552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3504552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504552 prefixEnd_3504552 := by exact prefixLift 3504552
  have htrace : WordTrace (prefixWord ++ tailWord_3504552) baseStart_3504552 baseEnd_3504552 := by
    simpa [prefixWord, tailWord_3504552, baseEnd_3504552] using wordTrace_append hprefix tailTrace_3504552
  have hstable : (prefixWord ++ tailWord_3504552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504552).length < 2 ^ (prefixWord ++ tailWord_3504552).sum := by decide
  have hdescent : baseEnd_3504552 < baseStart_3504552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504571 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4]
def baseStart_3504571 : Nat := 118140960795 + 3504571 * 2 ^ 59
def prefixEnd_3504571 : Nat := 4983230072969 + 3 ^ 40 * 3504571 * 2
def baseEnd_3504571 : Nat := 1799529410808113083545277

theorem tailTrace_3504571 : CollatzResearch.WordTrace tailWord_3504571 prefixEnd_3504571 1799529410808113083545277 := by
  unfold tailWord_3504571
  simp only [CollatzResearch.WordTrace]
  refine ⟨127822205386545274920257567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85214803591030183280171711 127822205386545274920257567)
  ·
    refine ⟨191733308079817912380386351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127822205386545274920257567 191733308079817912380386351)
    ·
      refine ⟨287599962119726868570579527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191733308079817912380386351 287599962119726868570579527)
      ·
        refine ⟨431399943179590302855869291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287599962119726868570579527 431399943179590302855869291)
        ·
          refine ⟨647099914769385454283803937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431399943179590302855869291 647099914769385454283803937)
          ·
            refine ⟨485324936077039090712852953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647099914769385454283803937 485324936077039090712852953)
            ·
              refine ⟨363993702057779318034639715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485324936077039090712852953 363993702057779318034639715)
              ·
                refine ⟨545990553086668977051959573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363993702057779318034639715 545990553086668977051959573)
                ·
                  refine ⟨25593307175937608299310605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 545990553086668977051959573 25593307175937608299310605)
                  ·
                    refine ⟨9597490190976603112241477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25593307175937608299310605 9597490190976603112241477)
                    ·
                      refine ⟨1799529410808113083545277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9597490190976603112241477 1799529410808113083545277)
                      ·
                        rfl

theorem cell23_3504571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 4].length) (baseStart_3504571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504571 prefixEnd_3504571 := by exact prefixLift 3504571
  have htrace : WordTrace (prefixWord ++ tailWord_3504571) baseStart_3504571 baseEnd_3504571 := by
    simpa [prefixWord, tailWord_3504571, baseEnd_3504571] using wordTrace_append hprefix tailTrace_3504571
  have hstable : (prefixWord ++ tailWord_3504571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504571).length < 2 ^ (prefixWord ++ tailWord_3504571).sum := by decide
  have hdescent : baseEnd_3504571 < baseStart_3504571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504591 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_3504591 : Nat := 118140960795 + 3504591 * 2 ^ 59
def prefixEnd_3504591 : Nat := 4983230072969 + 3 ^ 40 * 3504591 * 2
def baseEnd_3504591 : Nat := 1799539680421203005295185

theorem tailTrace_3504591 : CollatzResearch.WordTrace tailWord_3504591 prefixEnd_3504591 1799539680421203005295185 := by
  unfold tailWord_3504591
  simp only [CollatzResearch.WordTrace]
  refine ⟨127822934846472818335985627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85215289897648545557323751 127822934846472818335985627)
  ·
    refine ⟨191734402269709227503978441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127822934846472818335985627 191734402269709227503978441)
    ·
      refine ⟨143800801702281920627983831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191734402269709227503978441 143800801702281920627983831)
      ·
        refine ⟨215701202553422880941975747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143800801702281920627983831 215701202553422880941975747)
        ·
          refine ⟨323551803830134321412963621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215701202553422880941975747 323551803830134321412963621)
          ·
            refine ⟨60665963218150185264930679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323551803830134321412963621 60665963218150185264930679)
            ·
              refine ⟨90998944827225277897396019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60665963218150185264930679 90998944827225277897396019)
              ·
                refine ⟨136498417240837916846094029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90998944827225277897396019 136498417240837916846094029)
                ·
                  refine ⟨51186906465314218817285261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136498417240837916846094029 51186906465314218817285261)
                  ·
                    refine ⟨19195089924492832056481973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51186906465314218817285261 19195089924492832056481973)
                    ·
                      refine ⟨1799539680421203005295185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19195089924492832056481973 1799539680421203005295185)
                      ·
                        rfl

theorem cell23_3504591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_3504591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504591 prefixEnd_3504591 := by exact prefixLift 3504591
  have htrace : WordTrace (prefixWord ++ tailWord_3504591) baseStart_3504591 baseEnd_3504591 := by
    simpa [prefixWord, tailWord_3504591, baseEnd_3504591] using wordTrace_append hprefix tailTrace_3504591
  have hstable : (prefixWord ++ tailWord_3504591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504591).length < 2 ^ (prefixWord ++ tailWord_3504591).sum := by decide
  have hdescent : baseEnd_3504591 < baseStart_3504591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504622 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_3504622 : Nat := 118140960795 + 3504622 * 2 ^ 59
def prefixEnd_3504622 : Nat := 4983230072969 + 3 ^ 40 * 3504622 * 2
def baseEnd_3504622 : Nat := 1799555598321492384007543

theorem tailTrace_3504622 : CollatzResearch.WordTrace tailWord_3504622 prefixEnd_3504622 1799555598321492384007543 := by
  unfold tailWord_3504622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978008188670063828795515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85216043672907007086909413 15978008188670063828795515)
  ·
    refine ⟨23967012283005095743193273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15978008188670063828795515 23967012283005095743193273)
    ·
      refine ⟨17975259212253821807394955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23967012283005095743193273 17975259212253821807394955)
      ·
        refine ⟨26962888818380732711092433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17975259212253821807394955 26962888818380732711092433)
        ·
          refine ⟨20222166613785549533319325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26962888818380732711092433 20222166613785549533319325)
          ·
            refine ⟨7583312480169581074994747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20222166613785549533319325 7583312480169581074994747)
            ·
              refine ⟨11374968720254371612492121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583312480169581074994747 11374968720254371612492121)
              ·
                refine ⟨8531226540190778709369091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11374968720254371612492121 8531226540190778709369091)
                ·
                  refine ⟨12796839810286168064053637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531226540190778709369091 12796839810286168064053637)
                  ·
                    refine ⟨2399407464428656512010057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12796839810286168064053637 2399407464428656512010057)
                    ·
                      refine ⟨1799555598321492384007543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399407464428656512010057 1799555598321492384007543)
                      ·
                        rfl

theorem cell23_3504622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_3504622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504622 prefixEnd_3504622 := by exact prefixLift 3504622
  have htrace : WordTrace (prefixWord ++ tailWord_3504622) baseStart_3504622 baseEnd_3504622 := by
    simpa [prefixWord, tailWord_3504622, baseEnd_3504622] using wordTrace_append hprefix tailTrace_3504622
  have hstable : (prefixWord ++ tailWord_3504622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504622).length < 2 ^ (prefixWord ++ tailWord_3504622).sum := by decide
  have hdescent : baseEnd_3504622 < baseStart_3504622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504626 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3504626 : Nat := 118140960795 + 3504626 * 2 ^ 59
def prefixEnd_3504626 : Nat := 4983230072969 + 3 ^ 40 * 3504626 * 2
def baseEnd_3504626 : Nat := 1799557652244110368357525

theorem tailTrace_3504626 : CollatzResearch.WordTrace tailWord_3504626 prefixEnd_3504626 1799557652244110368357525 := by
  unfold tailWord_3504626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31956052850336504828377433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85216140934230679542339821 31956052850336504828377433)
  ·
    refine ⟨23967039637752378621283075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31956052850336504828377433 23967039637752378621283075)
    ·
      refine ⟨35950559456628567931924613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23967039637752378621283075 35950559456628567931924613)
      ·
        refine ⟨6740729898117856487235865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35950559456628567931924613 6740729898117856487235865)
        ·
          refine ⟨5055547423588392365426899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740729898117856487235865 5055547423588392365426899)
          ·
            refine ⟨7583321135382588548140349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055547423588392365426899 7583321135382588548140349)
            ·
              refine ⟨2843745425768470705552631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7583321135382588548140349 2843745425768470705552631)
              ·
                refine ⟨4265618138652706058328947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843745425768470705552631 4265618138652706058328947)
                ·
                  refine ⟨6398427207979059087493421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265618138652706058328947 6398427207979059087493421)
                  ·
                    refine ⟨2399410202992147157810033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6398427207979059087493421 2399410202992147157810033)
                    ·
                      refine ⟨1799557652244110368357525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399410202992147157810033 1799557652244110368357525)
                      ·
                        rfl

theorem cell23_3504626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3504626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504626 prefixEnd_3504626 := by exact prefixLift 3504626
  have htrace : WordTrace (prefixWord ++ tailWord_3504626) baseStart_3504626 baseEnd_3504626 := by
    simpa [prefixWord, tailWord_3504626, baseEnd_3504626] using wordTrace_append hprefix tailTrace_3504626
  have hstable : (prefixWord ++ tailWord_3504626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504626).length < 2 ^ (prefixWord ++ tailWord_3504626).sum := by decide
  have hdescent : baseEnd_3504626 < baseStart_3504626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504631 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_3504631 : Nat := 118140960795 + 3504631 * 2 ^ 59
def prefixEnd_3504631 : Nat := 4983230072969 + 3 ^ 40 * 3504631 * 2
def baseEnd_3504631 : Nat := 1799560219647382848795001

theorem tailTrace_3504631 : CollatzResearch.WordTrace tailWord_3504631 prefixEnd_3504631 1799560219647382848795001 := by
  unfold tailWord_3504631
  simp only [CollatzResearch.WordTrace]
  refine ⟨127824393766327905167441747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85216262510885270111627831 127824393766327905167441747)
  ·
    refine ⟨191736590649491857751162621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127824393766327905167441747 191736590649491857751162621)
    ·
      refine ⟨71901221493559446656685983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191736590649491857751162621 71901221493559446656685983)
      ·
        refine ⟨107851832240339169985028975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71901221493559446656685983 107851832240339169985028975)
        ·
          refine ⟨161777748360508754977543463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107851832240339169985028975 161777748360508754977543463)
          ·
            refine ⟨242666622540763132466315195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161777748360508754977543463 242666622540763132466315195)
            ·
              refine ⟨363999933811144698699472793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242666622540763132466315195 363999933811144698699472793)
              ·
                refine ⟨272999950358358524024604595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363999933811144698699472793 272999950358358524024604595)
                ·
                  refine ⟨409499925537537786036906893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272999950358358524024604595 409499925537537786036906893)
                  ·
                    refine ⟨153562472076576669763840085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 409499925537537786036906893 153562472076576669763840085)
                    ·
                      refine ⟨1799560219647382848795001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 153562472076576669763840085 1799560219647382848795001)
                      ·
                        rfl

theorem cell23_3504631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_3504631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504631 prefixEnd_3504631 := by exact prefixLift 3504631
  have htrace : WordTrace (prefixWord ++ tailWord_3504631) baseStart_3504631 baseEnd_3504631 := by
    simpa [prefixWord, tailWord_3504631, baseEnd_3504631] using wordTrace_append hprefix tailTrace_3504631
  have hstable : (prefixWord ++ tailWord_3504631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504631).length < 2 ^ (prefixWord ++ tailWord_3504631).sum := by decide
  have hdescent : baseEnd_3504631 < baseStart_3504631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504675 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 2, 5]
def baseStart_3504675 : Nat := 118140960795 + 3504675 * 2 ^ 59
def prefixEnd_3504675 : Nat := 4983230072969 + 3 ^ 40 * 3504675 * 2
def baseEnd_3504675 : Nat := 599860937598726892214933

theorem tailTrace_3504675 : CollatzResearch.WordTrace tailWord_3504675 prefixEnd_3504675 599860937598726892214933 := by
  unfold tailWord_3504675
  simp only [CollatzResearch.WordTrace]
  refine ⟨127825998578168500682043479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85217332385445667121362319 127825998578168500682043479)
  ·
    refine ⟨191738997867252751023065219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127825998578168500682043479 191738997867252751023065219)
    ·
      refine ⟨287608496800879126534597829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191738997867252751023065219 287608496800879126534597829)
      ·
        refine ⟨53926593150164836225237093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287608496800879126534597829 53926593150164836225237093)
        ·
          refine ⟨10111236215655906792231955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53926593150164836225237093 10111236215655906792231955)
          ·
            refine ⟨15166854323483860188347933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10111236215655906792231955 15166854323483860188347933)
            ·
              refine ⟨5687570371306447570630475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15166854323483860188347933 5687570371306447570630475)
              ·
                refine ⟨8531355556959671355945713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687570371306447570630475 8531355556959671355945713)
                ·
                  refine ⟨6398516667719753516959285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8531355556959671355945713 6398516667719753516959285)
                  ·
                    refine ⟨599860937598726892214933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6398516667719753516959285 599860937598726892214933)
                    ·
                      rfl

theorem cell23_3504675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 5].length) (baseStart_3504675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504675 prefixEnd_3504675 := by exact prefixLift 3504675
  have htrace : WordTrace (prefixWord ++ tailWord_3504675) baseStart_3504675 baseEnd_3504675 := by
    simpa [prefixWord, tailWord_3504675, baseEnd_3504675] using wordTrace_append hprefix tailTrace_3504675
  have hstable : (prefixWord ++ tailWord_3504675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504675).length < 2 ^ (prefixWord ++ tailWord_3504675).sum := by decide
  have hdescent : baseEnd_3504675 < baseStart_3504675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504695 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 4, 4, 2]
def baseStart_3504695 : Nat := 118140960795 + 3504695 * 2 ^ 59
def prefixEnd_3504695 : Nat := 4983230072969 + 3 ^ 40 * 3504695 * 2
def baseEnd_3504695 : Nat := 1799593082409270598394707

theorem tailTrace_3504695 : CollatzResearch.WordTrace tailWord_3504695 prefixEnd_3504695 1799593082409270598394707 := by
  unfold tailWord_3504695
  simp only [CollatzResearch.WordTrace]
  refine ⟨127826728038096044097771539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85217818692064029398514359 127826728038096044097771539)
  ·
    refine ⟨191740092057144066146657309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127826728038096044097771539 191740092057144066146657309)
    ·
      refine ⟨71902534521429024804996491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191740092057144066146657309 71902534521429024804996491)
      ·
        refine ⟨107853801782143537207494737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71902534521429024804996491 107853801782143537207494737)
        ·
          refine ⟨80890351336607652905621053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107853801782143537207494737 80890351336607652905621053)
          ·
            refine ⟨30333881751227869839607895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80890351336607652905621053 30333881751227869839607895)
            ·
              refine ⟨45500822626841804759411843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30333881751227869839607895 45500822626841804759411843)
              ·
                refine ⟨68251233940262707139117765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45500822626841804759411843 68251233940262707139117765)
                ·
                  refine ⟨12797106363799257588584581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68251233940262707139117765 12797106363799257588584581)
                  ·
                    refine ⟨2399457443212360797859609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12797106363799257588584581 2399457443212360797859609)
                    ·
                      refine ⟨1799593082409270598394707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399457443212360797859609 1799593082409270598394707)
                      ·
                        rfl

theorem cell23_3504695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_3504695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504695 prefixEnd_3504695 := by exact prefixLift 3504695
  have htrace : WordTrace (prefixWord ++ tailWord_3504695) baseStart_3504695 baseEnd_3504695 := by
    simpa [prefixWord, tailWord_3504695, baseEnd_3504695] using wordTrace_append hprefix tailTrace_3504695
  have hstable : (prefixWord ++ tailWord_3504695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504695).length < 2 ^ (prefixWord ++ tailWord_3504695).sum := by decide
  have hdescent : baseEnd_3504695 < baseStart_3504695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504755 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 3, 5, 2]
def baseStart_3504755 : Nat := 118140960795 + 3504755 * 2 ^ 59
def prefixEnd_3504755 : Nat := 4983230072969 + 3 ^ 40 * 3504755 * 2
def baseEnd_3504755 : Nat := 1799623891248540363644431

theorem tailTrace_3504755 : CollatzResearch.WordTrace tailWord_3504755 prefixEnd_3504755 1799623891248540363644431 := by
  unfold tailWord_3504755
  simp only [CollatzResearch.WordTrace]
  refine ⟨127828916417878674344955719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85219277611919116229970479 127828916417878674344955719)
  ·
    refine ⟨191743374626818011517433579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127828916417878674344955719 191743374626818011517433579)
    ·
      refine ⟨287615061940227017276150369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191743374626818011517433579 287615061940227017276150369)
      ·
        refine ⟨215711296455170262957112777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287615061940227017276150369 215711296455170262957112777)
        ·
          refine ⟨161783472341377697217834583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215711296455170262957112777 161783472341377697217834583)
          ·
            refine ⟨242675208512066545826751875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161783472341377697217834583 242675208512066545826751875)
            ·
              refine ⟨364012812768099818740127813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242675208512066545826751875 364012812768099818740127813)
              ·
                refine ⟨68252402394018716013773965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364012812768099818740127813 68252402394018716013773965)
                ·
                  refine ⟨25594650897757018505165237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68252402394018716013773965 25594650897757018505165237)
                  ·
                    refine ⟨2399498521664720484859241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25594650897757018505165237 2399498521664720484859241)
                    ·
                      refine ⟨1799623891248540363644431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399498521664720484859241 1799623891248540363644431)
                      ·
                        rfl

theorem cell23_3504755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 5, 2].length) (baseStart_3504755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504755 prefixEnd_3504755 := by exact prefixLift 3504755
  have htrace : WordTrace (prefixWord ++ tailWord_3504755) baseStart_3504755 baseEnd_3504755 := by
    simpa [prefixWord, tailWord_3504755, baseEnd_3504755] using wordTrace_append hprefix tailTrace_3504755
  have hstable : (prefixWord ++ tailWord_3504755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504755).length < 2 ^ (prefixWord ++ tailWord_3504755).sum := by decide
  have hdescent : baseEnd_3504755 < baseStart_3504755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504813 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_3504813 : Nat := 118140960795 + 3504813 * 2 ^ 59
def prefixEnd_3504813 : Nat := 4983230072969 + 3 ^ 40 * 3504813 * 2
def baseEnd_3504813 : Nat := 1799653673126501136719165

theorem tailTrace_3504813 : CollatzResearch.WordTrace tailWord_3504813 prefixEnd_3504813 1799653673126501136719165 := by
  unfold tailWord_3504813
  simp only [CollatzResearch.WordTrace]
  refine ⟨127831031851668550250567093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85220687901112366833711395 127831031851668550250567093)
  ·
    refine ⟨11984159236093926585990665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127831031851668550250567093 11984159236093926585990665)
    ·
      refine ⟨8988119427070444939492999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11984159236093926585990665 8988119427070444939492999)
      ·
        refine ⟨13482179140605667409239499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8988119427070444939492999 13482179140605667409239499)
        ·
          refine ⟨20223268710908501113859249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13482179140605667409239499 20223268710908501113859249)
          ·
            refine ⟨15167451533181375835394437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20223268710908501113859249 15167451533181375835394437)
            ·
              refine ⟨2843897162471507969136457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15167451533181375835394437 2843897162471507969136457)
              ·
                refine ⟨2132922871853630976852343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2843897162471507969136457 2132922871853630976852343)
                ·
                  refine ⟨3199384307780446465278515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2132922871853630976852343 3199384307780446465278515)
                  ·
                    refine ⟨4799076461670669697917773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3199384307780446465278515 4799076461670669697917773)
                    ·
                      refine ⟨1799653673126501136719165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799076461670669697917773 1799653673126501136719165)
                      ·
                        rfl

theorem cell23_3504813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_3504813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504813 prefixEnd_3504813 := by exact prefixLift 3504813
  have htrace : WordTrace (prefixWord ++ tailWord_3504813) baseStart_3504813 baseEnd_3504813 := by
    simpa [prefixWord, tailWord_3504813, baseEnd_3504813] using wordTrace_append hprefix tailTrace_3504813
  have hstable : (prefixWord ++ tailWord_3504813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504813).length < 2 ^ (prefixWord ++ tailWord_3504813).sum := by decide
  have hdescent : baseEnd_3504813 < baseStart_3504813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504832 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4]
def baseStart_3504832 : Nat := 118140960795 + 3504832 * 2 ^ 59
def prefixEnd_3504832 : Nat := 4983230072969 + 3 ^ 40 * 3504832 * 2
def baseEnd_3504832 : Nat := 1799663429258936562381577

theorem tailTrace_3504832 : CollatzResearch.WordTrace tailWord_3504832 prefixEnd_3504832 1799663429258936562381577 := by
  unfold tailWord_3504832
  simp only [CollatzResearch.WordTrace]
  refine ⟨63915862419299858247754375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85221149892399810997005833 63915862419299858247754375)
  ·
    refine ⟨95873793628949787371631563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63915862419299858247754375 95873793628949787371631563)
    ·
      refine ⟨143810690443424681057447345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95873793628949787371631563 143810690443424681057447345)
      ·
        refine ⟨107858017832568510793085509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143810690443424681057447345 107858017832568510793085509)
        ·
          refine ⟨20223378343606595773703533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107858017832568510793085509 20223378343606595773703533)
          ·
            refine ⟨7583766878852473415138825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20223378343606595773703533 7583766878852473415138825)
            ·
              refine ⟨5687825159139355061354119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7583766878852473415138825 5687825159139355061354119)
              ·
                refine ⟨8531737738709032592031179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687825159139355061354119 8531737738709032592031179)
                ·
                  refine ⟨12797606608063548888046769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531737738709032592031179 12797606608063548888046769)
                  ·
                    refine ⟨9598204956047661666035077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12797606608063548888046769 9598204956047661666035077)
                    ·
                      refine ⟨1799663429258936562381577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9598204956047661666035077 1799663429258936562381577)
                      ·
                        rfl

theorem cell23_3504832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_3504832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504832 prefixEnd_3504832 := by exact prefixLift 3504832
  have htrace : WordTrace (prefixWord ++ tailWord_3504832) baseStart_3504832 baseEnd_3504832 := by
    simpa [prefixWord, tailWord_3504832, baseEnd_3504832] using wordTrace_append hprefix tailTrace_3504832
  have hstable : (prefixWord ++ tailWord_3504832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504832).length < 2 ^ (prefixWord ++ tailWord_3504832).sum := by decide
  have hdescent : baseEnd_3504832 < baseStart_3504832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504836 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_3504836 : Nat := 118140960795 + 3504836 * 2 ^ 59
def prefixEnd_3504836 : Nat := 4983230072969 + 3 ^ 40 * 3504836 * 2
def baseEnd_3504836 : Nat := 1799665483181554546731559

theorem tailTrace_3504836 : CollatzResearch.WordTrace tailWord_3504836 prefixEnd_3504836 1799665483181554546731559 := by
  unfold tailWord_3504836
  simp only [CollatzResearch.WordTrace]
  refine ⟨63915935365292612589327181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85221247153723483452436241 63915935365292612589327181)
  ·
    refine ⟨23968475761984729720997693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63915935365292612589327181 23968475761984729720997693)
    ·
      refine ⟨8988178410744273645374135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23968475761984729720997693 8988178410744273645374135)
      ·
        refine ⟨13482267616116410468061203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8988178410744273645374135 13482267616116410468061203)
        ·
          refine ⟨20223401424174615702091805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13482267616116410468061203 20223401424174615702091805)
          ·
            refine ⟨7583775534065480888284427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20223401424174615702091805 7583775534065480888284427)
            ·
              refine ⟨11375663301098221332426641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583775534065480888284427 11375663301098221332426641)
              ·
                refine ⟨8531747475823665999319981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375663301098221332426641 8531747475823665999319981)
                ·
                  refine ⟨3199405303433874749744993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8531747475823665999319981 3199405303433874749744993)
                  ·
                    refine ⟨2399553977575406062308745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3199405303433874749744993 2399553977575406062308745)
                    ·
                      refine ⟨1799665483181554546731559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399553977575406062308745 1799665483181554546731559)
                      ·
                        rfl

theorem cell23_3504836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_3504836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504836 prefixEnd_3504836 := by exact prefixLift 3504836
  have htrace : WordTrace (prefixWord ++ tailWord_3504836) baseStart_3504836 baseEnd_3504836 := by
    simpa [prefixWord, tailWord_3504836, baseEnd_3504836] using wordTrace_append hprefix tailTrace_3504836
  have hstable : (prefixWord ++ tailWord_3504836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504836).length < 2 ^ (prefixWord ++ tailWord_3504836).sum := by decide
  have hdescent : baseEnd_3504836 < baseStart_3504836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504842 : List Nat := [3, 1, 2, 1, 4, 2, 3, 7]
def baseStart_3504842 : Nat := 118140960795 + 3504842 * 2 ^ 59
def prefixEnd_3504842 : Nat := 4983230072969 + 3 ^ 40 * 3504842 * 2
def baseEnd_3504842 : Nat := 66654391261684500861353

theorem tailTrace_3504842 : CollatzResearch.WordTrace tailWord_3504842 prefixEnd_3504842 66654391261684500861353 := by
  unfold tailWord_3504842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31958022392140872050843195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85221393045708992135581853 31958022392140872050843195)
  ·
    refine ⟨47937033588211308076264793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31958022392140872050843195 47937033588211308076264793)
    ·
      refine ⟨35952775191158481057198595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47937033588211308076264793 35952775191158481057198595)
      ·
        refine ⟨53929162786737721585797893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35952775191158481057198595 53929162786737721585797893)
        ·
          refine ⟨10111718022513322797337105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53929162786737721585797893 10111718022513322797337105)
          ·
            refine ⟨7583788516884992098002829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10111718022513322797337105 7583788516884992098002829)
            ·
              refine ⟨2843920693831872036751061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7583788516884992098002829 2843920693831872036751061)
              ·
                refine ⟨66654391261684500861353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2843920693831872036751061 66654391261684500861353)
                ·
                  rfl

theorem cell23_3504842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_3504842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504842 prefixEnd_3504842 := by exact prefixLift 3504842
  have htrace : WordTrace (prefixWord ++ tailWord_3504842) baseStart_3504842 baseEnd_3504842 := by
    simpa [prefixWord, tailWord_3504842, baseEnd_3504842] using wordTrace_append hprefix tailTrace_3504842
  have hstable : (prefixWord ++ tailWord_3504842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504842).length < 2 ^ (prefixWord ++ tailWord_3504842).sum := by decide
  have hdescent : baseEnd_3504842 < baseStart_3504842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504853 : List Nat := [1, 3, 2, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3504853 : Nat := 118140960795 + 3504853 * 2 ^ 59
def prefixEnd_3504853 : Nat := 4983230072969 + 3 ^ 40 * 3504853 * 2
def baseEnd_3504853 : Nat := 1799674212352680980218981

theorem tailTrace_3504853 : CollatzResearch.WordTrace tailWord_3504853 prefixEnd_3504853 1799674212352680980218981 := by
  unfold tailWord_3504853
  simp only [CollatzResearch.WordTrace]
  refine ⟨127832490771523637082023213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85221660514349091388015475 127832490771523637082023213)
  ·
    refine ⟨47937184039321363905758705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127832490771523637082023213 47937184039321363905758705)
    ·
      refine ⟨35952888029491022929319029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47937184039321363905758705 35952888029491022929319029)
      ·
        refine ⟨3370583252764783399623659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35952888029491022929319029 3370583252764783399623659)
        ·
          refine ⟨5055874879147175099435489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370583252764783399623659 5055874879147175099435489)
          ·
            refine ⟨3791906159360381324576617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5055874879147175099435489 3791906159360381324576617)
            ·
              refine ⟨2843929619520285993432463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791906159360381324576617 2843929619520285993432463)
              ·
                refine ⟨4265894429280428990148695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843929619520285993432463 4265894429280428990148695)
                ·
                  refine ⟨6398841643920643485223043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265894429280428990148695 6398841643920643485223043)
                  ·
                    refine ⟨9598262465880965227834565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398841643920643485223043 9598262465880965227834565)
                    ·
                      refine ⟨1799674212352680980218981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9598262465880965227834565 1799674212352680980218981)
                      ·
                        rfl

theorem cell23_3504853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3504853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504853 prefixEnd_3504853 := by exact prefixLift 3504853
  have htrace : WordTrace (prefixWord ++ tailWord_3504853) baseStart_3504853 baseEnd_3504853 := by
    simpa [prefixWord, tailWord_3504853, baseEnd_3504853] using wordTrace_append hprefix tailTrace_3504853
  have hstable : (prefixWord ++ tailWord_3504853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504853).length < 2 ^ (prefixWord ++ tailWord_3504853).sum := by decide
  have hdescent : baseEnd_3504853 < baseStart_3504853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504856 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 1, 2, 3]
def baseStart_3504856 : Nat := 118140960795 + 3504856 * 2 ^ 59
def prefixEnd_3504856 : Nat := 4983230072969 + 3 ^ 40 * 3504856 * 2
def baseEnd_3504856 : Nat := 1799675752794644468481467

theorem tailTrace_3504856 : CollatzResearch.WordTrace tailWord_3504856 prefixEnd_3504856 1799675752794644468481467 := by
  unfold tailWord_3504856
  simp only [CollatzResearch.WordTrace]
  refine ⟨63916300095256384297191211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85221733460341845729588281 63916300095256384297191211)
  ·
    refine ⟨95874450142884576445786817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63916300095256384297191211 95874450142884576445786817)
    ·
      refine ⟨71905837607163432334340113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95874450142884576445786817 71905837607163432334340113)
      ·
        refine ⟨53929378205372574250755085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71905837607163432334340113 53929378205372574250755085)
        ·
          refine ⟨20223516827014715344033157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53929378205372574250755085 20223516827014715344033157)
          ·
            refine ⟨3791909405065259127006217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20223516827014715344033157 3791909405065259127006217)
            ·
              refine ⟨2843932053798944345254663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3791909405065259127006217 2843932053798944345254663)
              ·
                refine ⟨4265898080698416517881995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843932053798944345254663 4265898080698416517881995)
                ·
                  refine ⟨6398847121047624776822993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265898080698416517881995 6398847121047624776822993)
                  ·
                    refine ⟨4799135340785718582617245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6398847121047624776822993 4799135340785718582617245)
                    ·
                      refine ⟨1799675752794644468481467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799135340785718582617245 1799675752794644468481467)
                      ·
                        rfl

theorem cell23_3504856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_3504856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504856 prefixEnd_3504856 := by exact prefixLift 3504856
  have htrace : WordTrace (prefixWord ++ tailWord_3504856) baseStart_3504856 baseEnd_3504856 := by
    simpa [prefixWord, tailWord_3504856, baseEnd_3504856] using wordTrace_append hprefix tailTrace_3504856
  have hstable : (prefixWord ++ tailWord_3504856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504856).length < 2 ^ (prefixWord ++ tailWord_3504856).sum := by decide
  have hdescent : baseEnd_3504856 < baseStart_3504856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504869 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3504869 : Nat := 118140960795 + 3504869 * 2 ^ 59
def prefixEnd_3504869 : Nat := 4983230072969 + 3 ^ 40 * 3504869 * 2
def baseEnd_3504869 : Nat := 1799682428043152917618907

theorem tailTrace_3504869 : CollatzResearch.WordTrace tailWord_3504869 prefixEnd_3504869 1799682428043152917618907 := by
  unfold tailWord_3504869
  simp only [CollatzResearch.WordTrace]
  refine ⟨127833074339465671814605661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85222049559643781209737107 127833074339465671814605661)
  ·
    refine ⟨47937402877299626930477123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127833074339465671814605661 47937402877299626930477123)
    ·
      refine ⟨71906104315949440395715685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47937402877299626930477123 71906104315949440395715685)
      ·
        refine ⟨13482394559240520074196691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71906104315949440395715685 13482394559240520074196691)
        ·
          refine ⟨20223591838860780111295037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13482394559240520074196691 20223591838860780111295037)
          ·
            refine ⟨7583846939572792541735639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20223591838860780111295037 7583846939572792541735639)
            ·
              refine ⟨11375770409359188812603459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583846939572792541735639 11375770409359188812603459)
              ·
                refine ⟨17063655614038783218905189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11375770409359188812603459 17063655614038783218905189)
                ·
                  refine ⟨3199435427632271853544723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17063655614038783218905189 3199435427632271853544723)
                  ·
                    refine ⟨4799153141448407780317085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3199435427632271853544723 4799153141448407780317085)
                    ·
                      refine ⟨1799682428043152917618907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799153141448407780317085 1799682428043152917618907)
                      ·
                        rfl

theorem cell23_3504869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3504869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504869 prefixEnd_3504869 := by exact prefixLift 3504869
  have htrace : WordTrace (prefixWord ++ tailWord_3504869) baseStart_3504869 baseEnd_3504869 := by
    simpa [prefixWord, tailWord_3504869, baseEnd_3504869] using wordTrace_append hprefix tailTrace_3504869
  have hstable : (prefixWord ++ tailWord_3504869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504869).length < 2 ^ (prefixWord ++ tailWord_3504869).sum := by decide
  have hdescent : baseEnd_3504869 < baseStart_3504869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504895 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_3504895 : Nat := 118140960795 + 3504895 * 2 ^ 59
def prefixEnd_3504895 : Nat := 4983230072969 + 3 ^ 40 * 3504895 * 2
def baseEnd_3504895 : Nat := 1799695778540169815893787

theorem tailTrace_3504895 : CollatzResearch.WordTrace tailWord_3504895 prefixEnd_3504895 1799695778540169815893787 := by
  unfold tailWord_3504895
  simp only [CollatzResearch.WordTrace]
  refine ⟨127834022637371478255052139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85222681758247652170034759 127834022637371478255052139)
  ·
    refine ⟨191751033956057217382578209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127834022637371478255052139 191751033956057217382578209)
    ·
      refine ⟨143813275467042913036933657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191751033956057217382578209 143813275467042913036933657)
      ·
        refine ⟨107859956600282184777700243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143813275467042913036933657 107859956600282184777700243)
        ·
          refine ⟨161789934900423277166550365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107859956600282184777700243 161789934900423277166550365)
          ·
            refine ⟨60671225587658728937456387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161789934900423277166550365 60671225587658728937456387)
            ·
              refine ⟨91006838381488093406184581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60671225587658728937456387 91006838381488093406184581)
              ·
                refine ⟨17063782196529017513659609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91006838381488093406184581 17063782196529017513659609)
                ·
                  refine ⟨12797836647396763135244707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17063782196529017513659609 12797836647396763135244707)
                  ·
                    refine ⟨19196754971095144702867061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12797836647396763135244707 19196754971095144702867061)
                    ·
                      refine ⟨1799695778540169815893787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19196754971095144702867061 1799695778540169815893787)
                      ·
                        rfl

theorem cell23_3504895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_3504895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504895 prefixEnd_3504895 := by exact prefixLift 3504895
  have htrace : WordTrace (prefixWord ++ tailWord_3504895) baseStart_3504895 baseEnd_3504895 := by
    simpa [prefixWord, tailWord_3504895, baseEnd_3504895] using wordTrace_append hprefix tailTrace_3504895
  have hstable : (prefixWord ++ tailWord_3504895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504895).length < 2 ^ (prefixWord ++ tailWord_3504895).sum := by decide
  have hdescent : baseEnd_3504895 < baseStart_3504895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504905 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_3504905 : Nat := 118140960795 + 3504905 * 2 ^ 59
def prefixEnd_3504905 : Nat := 4983230072969 + 3 ^ 40 * 3504905 * 2
def baseEnd_3504905 : Nat := 1799700913346714776768741

theorem tailTrace_3504905 : CollatzResearch.WordTrace tailWord_3504905 prefixEnd_3504905 1799700913346714776768741 := by
  unfold tailWord_3504905
  simp only [CollatzResearch.WordTrace]
  refine ⟨127834387367335249962916169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85222924911556833308610779 127834387367335249962916169)
  ·
    refine ⟨95875790525501437472187127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127834387367335249962916169 95875790525501437472187127)
    ·
      refine ⟨143813685788252156208280691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95875790525501437472187127 143813685788252156208280691)
      ·
        refine ⟨215720528682378234312421037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143813685788252156208280691 215720528682378234312421037)
        ·
          refine ⟨80895198255891837867157889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215720528682378234312421037 80895198255891837867157889)
          ·
            refine ⟨60671398691918878400368417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80895198255891837867157889 60671398691918878400368417)
            ·
              refine ⟨45503549018939158800276313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60671398691918878400368417 45503549018939158800276313)
              ·
                refine ⟨34127661764204369100207235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45503549018939158800276313 34127661764204369100207235)
                ·
                  refine ⟨51191492646306553650310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34127661764204369100207235 51191492646306553650310853)
                  ·
                    refine ⟨9598404871182478809433285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51191492646306553650310853 9598404871182478809433285)
                    ·
                      refine ⟨1799700913346714776768741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9598404871182478809433285 1799700913346714776768741)
                      ·
                        rfl

theorem cell23_3504905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_3504905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504905 prefixEnd_3504905 := by exact prefixLift 3504905
  have htrace : WordTrace (prefixWord ++ tailWord_3504905) baseStart_3504905 baseEnd_3504905 := by
    simpa [prefixWord, tailWord_3504905, baseEnd_3504905] using wordTrace_append hprefix tailTrace_3504905
  have hstable : (prefixWord ++ tailWord_3504905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504905).length < 2 ^ (prefixWord ++ tailWord_3504905).sum := by decide
  have hdescent : baseEnd_3504905 < baseStart_3504905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504972 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3504972 : Nat := 118140960795 + 3504972 * 2 ^ 59
def prefixEnd_3504972 : Nat := 4983230072969 + 3 ^ 40 * 3504972 * 2
def baseEnd_3504972 : Nat := 1799735316550566014630933

theorem tailTrace_3504972 : CollatzResearch.WordTrace tailWord_3504972 prefixEnd_3504972 1799735316550566014630933 := by
  unfold tailWord_3504972
  simp only [CollatzResearch.WordTrace]
  refine ⟨63918415529046260202802585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85224554038728346937070113 63918415529046260202802585)
  ·
    refine ⟨47938811646784695152101939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63918415529046260202802585 47938811646784695152101939)
    ·
      refine ⟨71908217470177042728152909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47938811646784695152101939 71908217470177042728152909)
      ·
        refine ⟨26965581551316391023057341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71908217470177042728152909 26965581551316391023057341)
        ·
          refine ⟨10112093081743646633646503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26965581551316391023057341 10112093081743646633646503)
          ·
            refine ⟨15168139622615469950469755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112093081743646633646503 15168139622615469950469755)
            ·
              refine ⟨22752209433923204925704633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15168139622615469950469755 22752209433923204925704633)
              ·
                refine ⟨17064157075442403694278475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22752209433923204925704633 17064157075442403694278475)
                ·
                  refine ⟨25596235613163605541417713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17064157075442403694278475 25596235613163605541417713)
                  ·
                    refine ⟨19197176709872704156063285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25596235613163605541417713 19197176709872704156063285)
                    ·
                      refine ⟨1799735316550566014630933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19197176709872704156063285 1799735316550566014630933)
                      ·
                        rfl

theorem cell23_3504972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3504972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504972 prefixEnd_3504972 := by exact prefixLift 3504972
  have htrace : WordTrace (prefixWord ++ tailWord_3504972) baseStart_3504972 baseEnd_3504972 := by
    simpa [prefixWord, tailWord_3504972, baseEnd_3504972] using wordTrace_append hprefix tailTrace_3504972
  have hstable : (prefixWord ++ tailWord_3504972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504972).length < 2 ^ (prefixWord ++ tailWord_3504972).sum := by decide
  have hdescent : baseEnd_3504972 < baseStart_3504972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3504999 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_3504999 : Nat := 118140960795 + 3504999 * 2 ^ 59
def prefixEnd_3504999 : Nat := 4983230072969 + 3 ^ 40 * 3504999 * 2
def baseEnd_3504999 : Nat := 1799749180528237408993309

theorem tailTrace_3504999 : CollatzResearch.WordTrace tailWord_3504999 prefixEnd_3504999 1799749180528237408993309 := by
  unfold tailWord_3504999
  simp only [CollatzResearch.WordTrace]
  refine ⟨127837815828994704016838051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85225210552663136011225367 127837815828994704016838051)
  ·
    refine ⟨191756723743492056025257077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127837815828994704016838051 191756723743492056025257077)
    ·
      refine ⟨17977192850952380252367851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191756723743492056025257077 17977192850952380252367851)
      ·
        refine ⟨26965789276428570378551777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17977192850952380252367851 26965789276428570378551777)
        ·
          refine ⟨20224341957321427783913833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26965789276428570378551777 20224341957321427783913833)
          ·
            refine ⟨15168256467991070837935375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20224341957321427783913833 15168256467991070837935375)
            ·
              refine ⟨22752384701986606256903063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15168256467991070837935375 22752384701986606256903063)
              ·
                refine ⟨34128577052979909385354595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22752384701986606256903063 34128577052979909385354595)
                ·
                  refine ⟨51192865579469864078031893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34128577052979909385354595 51192865579469864078031893)
                  ·
                    refine ⟨2399665574037649878657745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51192865579469864078031893 2399665574037649878657745)
                    ·
                      refine ⟨1799749180528237408993309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399665574037649878657745 1799749180528237408993309)
                      ·
                        rfl

theorem cell23_3504999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_3504999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3504999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3504999 prefixEnd_3504999 := by exact prefixLift 3504999
  have htrace : WordTrace (prefixWord ++ tailWord_3504999) baseStart_3504999 baseEnd_3504999 := by
    simpa [prefixWord, tailWord_3504999, baseEnd_3504999] using wordTrace_append hprefix tailTrace_3504999
  have hstable : (prefixWord ++ tailWord_3504999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3504999).length < 2 ^ (prefixWord ++ tailWord_3504999).sum := by decide
  have hdescent : baseEnd_3504999 < baseStart_3504999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3504999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505009 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 3, 4]
def baseStart_3505009 : Nat := 118140960795 + 3505009 * 2 ^ 59
def prefixEnd_3505009 : Nat := 4983230072969 + 3 ^ 40 * 3505009 * 2
def baseEnd_3505009 : Nat := 599918105111594123289421

theorem tailTrace_3505009 : CollatzResearch.WordTrace tailWord_3505009 prefixEnd_3505009 599918105111594123289421 := by
  unfold tailWord_3505009
  simp only [CollatzResearch.WordTrace]
  refine ⟨127838180558958475724702081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85225453705972317149801387 127838180558958475724702081)
  ·
    refine ⟨95878635419218856793526561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127838180558958475724702081 95878635419218856793526561)
    ·
      refine ⟨71908976564414142595144921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95878635419218856793526561 71908976564414142595144921)
      ·
        refine ⟨53931732423310606946358691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71908976564414142595144921 53931732423310606946358691)
        ·
          refine ⟨80897598634965910419538037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53931732423310606946358691 80897598634965910419538037)
          ·
            refine ⟨7584149872028054101831691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80897598634965910419538037 7584149872028054101831691)
            ·
              refine ⟨11376224808042081152747537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584149872028054101831691 11376224808042081152747537)
              ·
                refine ⟨8532168606031560864560653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11376224808042081152747537 8532168606031560864560653)
                ·
                  refine ⟨3199563227261835324210245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8532168606031560864560653 3199563227261835324210245)
                  ·
                    refine ⟨599918105111594123289421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199563227261835324210245 599918105111594123289421)
                    ·
                      rfl

theorem cell23_3505009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_3505009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505009 prefixEnd_3505009 := by exact prefixLift 3505009
  have htrace : WordTrace (prefixWord ++ tailWord_3505009) baseStart_3505009 baseEnd_3505009 := by
    simpa [prefixWord, tailWord_3505009, baseEnd_3505009] using wordTrace_append hprefix tailTrace_3505009
  have hstable : (prefixWord ++ tailWord_3505009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505009).length < 2 ^ (prefixWord ++ tailWord_3505009).sum := by decide
  have hdescent : baseEnd_3505009 < baseStart_3505009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505019 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 3]
def baseStart_3505019 : Nat := 118140960795 + 3505019 * 2 ^ 59
def prefixEnd_3505019 : Nat := 4983230072969 + 3 ^ 40 * 3505019 * 2
def baseEnd_3505019 : Nat := 1799759450141327330743217

theorem tailTrace_3505019 : CollatzResearch.WordTrace tailWord_3505019 prefixEnd_3505019 1799759450141327330743217 := by
  unfold tailWord_3505019
  simp only [CollatzResearch.WordTrace]
  refine ⟨127838545288922247432566111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85225696859281498288377407 127838545288922247432566111)
  ·
    refine ⟨191757817933383371148849167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127838545288922247432566111 191757817933383371148849167)
    ·
      refine ⟨287636726900075056723273751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191757817933383371148849167 287636726900075056723273751)
      ·
        refine ⟨431455090350112585084910627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287636726900075056723273751 431455090350112585084910627)
        ·
          refine ⟨647182635525168877627365941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431455090350112585084910627 647182635525168877627365941)
          ·
            refine ⟨60673372080484582277565557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 647182635525168877627365941 60673372080484582277565557)
            ·
              refine ⟨5688128632545429588521771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60673372080484582277565557 5688128632545429588521771)
              ·
                refine ⟨8532192948818144382782657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688128632545429588521771 8532192948818144382782657)
                ·
                  refine ⟨6399144711613608287086993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8532192948818144382782657 6399144711613608287086993)
                  ·
                    refine ⟨4799358533710206215315245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6399144711613608287086993 4799358533710206215315245)
                    ·
                      refine ⟨1799759450141327330743217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799358533710206215315245 1799759450141327330743217)
                      ·
                        rfl

theorem cell23_3505019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 2, 2, 3].length) (baseStart_3505019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505019 prefixEnd_3505019 := by exact prefixLift 3505019
  have htrace : WordTrace (prefixWord ++ tailWord_3505019) baseStart_3505019 baseEnd_3505019 := by
    simpa [prefixWord, tailWord_3505019, baseEnd_3505019] using wordTrace_append hprefix tailTrace_3505019
  have hstable : (prefixWord ++ tailWord_3505019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505019).length < 2 ^ (prefixWord ++ tailWord_3505019).sum := by decide
  have hdescent : baseEnd_3505019 < baseStart_3505019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505059 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 1, 5, 2]
def baseStart_3505059 : Nat := 118140960795 + 3505059 * 2 ^ 59
def prefixEnd_3505059 : Nat := 4983230072969 + 3 ^ 40 * 3505059 * 2
def baseEnd_3505059 : Nat := 1799779989367507174243033

theorem tailTrace_3505059 : CollatzResearch.WordTrace tailWord_3505059 prefixEnd_3505059 1799779989367507174243033 := by
  unfold tailWord_3505059
  simp only [CollatzResearch.WordTrace]
  refine ⟨127840004208777334264022231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85226669472518222842681487 127840004208777334264022231)
  ·
    refine ⟨191760006313166001396033347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127840004208777334264022231 191760006313166001396033347)
    ·
      refine ⟨287640009469749002094050021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191760006313166001396033347 287640009469749002094050021)
      ·
        refine ⟨53932501775577937892634379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287640009469749002094050021 53932501775577937892634379)
        ·
          refine ⟨80898752663366906838951569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53932501775577937892634379 80898752663366906838951569)
          ·
            refine ⟨60674064497525180129213677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80898752663366906838951569 60674064497525180129213677)
            ·
              refine ⟨22752774186571942548455129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60674064497525180129213677 22752774186571942548455129)
              ·
                refine ⟨17064580639928956911341347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22752774186571942548455129 17064580639928956911341347)
                ·
                  refine ⟨25596870959893435367012021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17064580639928956911341347 25596870959893435367012021)
                  ·
                    refine ⟨2399706652490009565657377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25596870959893435367012021 2399706652490009565657377)
                    ·
                      refine ⟨1799779989367507174243033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399706652490009565657377 1799779989367507174243033)
                      ·
                        rfl

theorem cell23_3505059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_3505059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505059 prefixEnd_3505059 := by exact prefixLift 3505059
  have htrace : WordTrace (prefixWord ++ tailWord_3505059) baseStart_3505059 baseEnd_3505059 := by
    simpa [prefixWord, tailWord_3505059, baseEnd_3505059] using wordTrace_append hprefix tailTrace_3505059
  have hstable : (prefixWord ++ tailWord_3505059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505059).length < 2 ^ (prefixWord ++ tailWord_3505059).sum := by decide
  have hdescent : baseEnd_3505059 < baseStart_3505059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505082 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_3505082 : Nat := 118140960795 + 3505082 * 2 ^ 59
def prefixEnd_3505082 : Nat := 4983230072969 + 3 ^ 40 * 3505082 * 2
def baseEnd_3505082 : Nat := 599930599807520194751809

theorem tailTrace_3505082 : CollatzResearch.WordTrace tailWord_3505082 prefixEnd_3505082 599930599807520194751809 := by
  unfold tailWord_3505082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31960210771923502298027375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85227228725129339461406333 31960210771923502298027375)
  ·
    refine ⟨47940316157885253447041063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31960210771923502298027375 47940316157885253447041063)
    ·
      refine ⟨71910474236827880170561595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47940316157885253447041063 71910474236827880170561595)
      ·
        refine ⟨107865711355241820255842393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71910474236827880170561595 107865711355241820255842393)
        ·
          refine ⟨80899283516431365191881795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107865711355241820255842393 80899283516431365191881795)
          ·
            refine ⟨121348925274647047787822693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80899283516431365191881795 121348925274647047787822693)
            ·
              refine ⟨22752923488996321460216755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121348925274647047787822693 22752923488996321460216755)
              ·
                refine ⟨34129385233494482190325133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22752923488996321460216755 34129385233494482190325133)
                ·
                  refine ⟨12798519462560430821371925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34129385233494482190325133 12798519462560430821371925)
                  ·
                    refine ⟨599930599807520194751809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12798519462560430821371925 599930599807520194751809)
                    ·
                      rfl

theorem cell23_3505082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_3505082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505082 prefixEnd_3505082 := by exact prefixLift 3505082
  have htrace : WordTrace (prefixWord ++ tailWord_3505082) baseStart_3505082 baseEnd_3505082 := by
    simpa [prefixWord, tailWord_3505082, baseEnd_3505082] using wordTrace_append hprefix tailTrace_3505082
  have hstable : (prefixWord ++ tailWord_3505082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505082).length < 2 ^ (prefixWord ++ tailWord_3505082).sum := by decide
  have hdescent : baseEnd_3505082 < baseStart_3505082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505094 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3505094 : Nat := 118140960795 + 3505094 * 2 ^ 59
def prefixEnd_3505094 : Nat := 4983230072969 + 3 ^ 40 * 3505094 * 2
def baseEnd_3505094 : Nat := 599932653730138179101791

theorem tailTrace_3505094 : CollatzResearch.WordTrace tailWord_3505094 prefixEnd_3505094 599932653730138179101791 := by
  unfold tailWord_3505094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995040023864079226298323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85227520509100356827697557 3995040023864079226298323)
  ·
    refine ⟨5992560035796118839447485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3995040023864079226298323 5992560035796118839447485)
    ·
      refine ⟨2247210013423544564792807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5992560035796118839447485 2247210013423544564792807)
      ·
        refine ⟨3370815020135316847189211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247210013423544564792807 3370815020135316847189211)
        ·
          refine ⟨5056222530202975270783817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3370815020135316847189211 5056222530202975270783817)
          ·
            refine ⟨3792166897652231453087863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5056222530202975270783817 3792166897652231453087863)
            ·
              refine ⟨5688250346478347179631795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792166897652231453087863 5688250346478347179631795)
              ·
                refine ⟨8532375519717520769447693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688250346478347179631795 8532375519717520769447693)
                ·
                  refine ⟨3199640819894070288542885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8532375519717520769447693 3199640819894070288542885)
                  ·
                    refine ⟨599932653730138179101791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199640819894070288542885 599932653730138179101791)
                    ·
                      rfl

theorem cell23_3505094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3505094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505094 prefixEnd_3505094 := by exact prefixLift 3505094
  have htrace : WordTrace (prefixWord ++ tailWord_3505094) baseStart_3505094 baseEnd_3505094 := by
    simpa [prefixWord, tailWord_3505094, baseEnd_3505094] using wordTrace_append hprefix tailTrace_3505094
  have hstable : (prefixWord ++ tailWord_3505094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505094).length < 2 ^ (prefixWord ++ tailWord_3505094).sum := by decide
  have hdescent : baseEnd_3505094 < baseStart_3505094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505099 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 4, 4]
def baseStart_3505099 : Nat := 118140960795 + 3505099 * 2 ^ 59
def prefixEnd_3505099 : Nat := 4983230072969 + 3 ^ 40 * 3505099 * 2
def baseEnd_3505099 : Nat := 599933509531229005914283

theorem tailTrace_3505099 : CollatzResearch.WordTrace tailWord_3505099 prefixEnd_3505099 599933509531229005914283 := by
  unfold tailWord_3505099
  simp only [CollatzResearch.WordTrace]
  refine ⟨127841463128632421095478351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85227642085754947396985567 127841463128632421095478351)
  ·
    refine ⟨191762194692948631643217527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127841463128632421095478351 191762194692948631643217527)
    ·
      refine ⟨287643292039422947464826291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191762194692948631643217527 287643292039422947464826291)
      ·
        refine ⟨431464938059134421197239437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287643292039422947464826291 431464938059134421197239437)
        ·
          refine ⟨161799351772175407948964789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431464938059134421197239437 161799351772175407948964789)
          ·
            refine ⟨15168689228641444495215449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161799351772175407948964789 15168689228641444495215449)
            ·
              refine ⟨11376516921481083371411587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15168689228641444495215449 11376516921481083371411587)
              ·
                refine ⟨17064775382221625057117381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11376516921481083371411587 17064775382221625057117381)
                ·
                  refine ⟨3199645384166554698209509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17064775382221625057117381 3199645384166554698209509)
                  ·
                    refine ⟨599933509531229005914283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199645384166554698209509 599933509531229005914283)
                    ·
                      rfl

theorem cell23_3505099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 4].length) (baseStart_3505099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505099 prefixEnd_3505099 := by exact prefixLift 3505099
  have htrace : WordTrace (prefixWord ++ tailWord_3505099) baseStart_3505099 baseEnd_3505099 := by
    simpa [prefixWord, tailWord_3505099, baseEnd_3505099] using wordTrace_append hprefix tailTrace_3505099
  have hstable : (prefixWord ++ tailWord_3505099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505099).length < 2 ^ (prefixWord ++ tailWord_3505099).sum := by decide
  have hdescent : baseEnd_3505099 < baseStart_3505099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505100 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3505100 : Nat := 118140960795 + 3505100 * 2 ^ 59
def prefixEnd_3505100 : Nat := 4983230072969 + 3 ^ 40 * 3505100 * 2
def baseEnd_3505100 : Nat := 1799801042074341513830345

theorem tailTrace_3505100 : CollatzResearch.WordTrace tailWord_3505100 prefixEnd_3505100 1799801042074341513830345 := by
  unfold tailWord_3505100
  simp only [CollatzResearch.WordTrace]
  refine ⟨63920749800814399133132377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85227666401085865510843169 63920749800814399133132377)
  ·
    refine ⟨47940562350610799349849283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63920749800814399133132377 47940562350610799349849283)
    ·
      refine ⟨71910843525916199024773925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47940562350610799349849283 71910843525916199024773925)
      ·
        refine ⟨13483283161109287317145111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71910843525916199024773925 13483283161109287317145111)
        ·
          refine ⟨20224924741663930975717667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13483283161109287317145111 20224924741663930975717667)
          ·
            refine ⟨30337387112495896463576501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20224924741663930975717667 30337387112495896463576501)
            ·
              refine ⟨2844130041796490293460297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30337387112495896463576501 2844130041796490293460297)
              ·
                refine ⟨2133097531347367720095223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844130041796490293460297 2133097531347367720095223)
                ·
                  refine ⟨3199646297021051580142835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133097531347367720095223 3199646297021051580142835)
                  ·
                    refine ⟨4799469445531577370214253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3199646297021051580142835 4799469445531577370214253)
                    ·
                      refine ⟨1799801042074341513830345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799469445531577370214253 1799801042074341513830345)
                      ·
                        rfl

theorem cell23_3505100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3505100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505100 prefixEnd_3505100 := by exact prefixLift 3505100
  have htrace : WordTrace (prefixWord ++ tailWord_3505100) baseStart_3505100 baseEnd_3505100 := by
    simpa [prefixWord, tailWord_3505100, baseEnd_3505100] using wordTrace_append hprefix tailTrace_3505100
  have hstable : (prefixWord ++ tailWord_3505100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505100).length < 2 ^ (prefixWord ++ tailWord_3505100).sum := by decide
  have hdescent : baseEnd_3505100 < baseStart_3505100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505112 : List Nat := [2, 1, 2, 2, 2, 3, 1, 10]
def baseStart_3505112 : Nat := 118140960795 + 3505112 * 2 ^ 59
def prefixEnd_3505112 : Nat := 4983230072969 + 3 ^ 40 * 3505112 * 2
def baseEnd_3505112 : Nat := 66659526068229461736307

theorem tailTrace_3505112 : CollatzResearch.WordTrace tailWord_3505112 prefixEnd_3505112 66659526068229461736307 := by
  unfold tailWord_3505112
  simp only [CollatzResearch.WordTrace]
  refine ⟨63920968638792662157850795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85227958185056882877134393 63920968638792662157850795)
  ·
    refine ⟨95881452958188993236776193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63920968638792662157850795 95881452958188993236776193)
    ·
      refine ⟨71911089718641744927582145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95881452958188993236776193 71911089718641744927582145)
      ·
        refine ⟨53933317288981308695686609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71911089718641744927582145 53933317288981308695686609)
        ·
          refine ⟨40449987966735981521764957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53933317288981308695686609 40449987966735981521764957)
          ·
            refine ⟨15168745487525993070661859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40449987966735981521764957 15168745487525993070661859)
            ·
              refine ⟨22753118231288989605992789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15168745487525993070661859 22753118231288989605992789)
              ·
                refine ⟨66659526068229461736307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22753118231288989605992789 66659526068229461736307)
                ·
                  rfl

theorem cell23_3505112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 10].length) (baseStart_3505112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505112 prefixEnd_3505112 := by exact prefixLift 3505112
  have htrace : WordTrace (prefixWord ++ tailWord_3505112) baseStart_3505112 baseEnd_3505112 := by
    simpa [prefixWord, tailWord_3505112, baseEnd_3505112] using wordTrace_append hprefix tailTrace_3505112
  have hstable : (prefixWord ++ tailWord_3505112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505112).length < 2 ^ (prefixWord ++ tailWord_3505112).sum := by decide
  have hdescent : baseEnd_3505112 < baseStart_3505112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505150 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3505150 : Nat := 118140960795 + 3505150 * 2 ^ 59
def prefixEnd_3505150 : Nat := 4983230072969 + 3 ^ 40 * 3505150 * 2
def baseEnd_3505150 : Nat := 599942238702355439401705

theorem tailTrace_3505150 : CollatzResearch.WordTrace tailWord_3505150 prefixEnd_3505150 599942238702355439401705 := by
  unfold tailWord_3505150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980415406430957100698113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85228882167631771203723269 15980415406430957100698113)
  ·
    refine ⟨11985311554823217825523585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15980415406430957100698113 11985311554823217825523585)
    ·
      refine ⟨8988983666117413369142689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11985311554823217825523585 8988983666117413369142689)
      ·
        refine ⟨6741737749588060026857017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8988983666117413369142689 6741737749588060026857017)
        ·
          refine ⟨5056303312191045020142763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6741737749588060026857017 5056303312191045020142763)
          ·
            refine ⟨7584454968286567530214145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056303312191045020142763 7584454968286567530214145)
            ·
              refine ⟨5688341226214925647660609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7584454968286567530214145 5688341226214925647660609)
              ·
                refine ⟨4266255919661194235745457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688341226214925647660609 4266255919661194235745457)
                ·
                  refine ⟨3199691939745895676809093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266255919661194235745457 3199691939745895676809093)
                  ·
                    refine ⟨599942238702355439401705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199691939745895676809093 599942238702355439401705)
                    ·
                      rfl

theorem cell23_3505150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3505150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505150 prefixEnd_3505150 := by exact prefixLift 3505150
  have htrace : WordTrace (prefixWord ++ tailWord_3505150) baseStart_3505150 baseEnd_3505150 := by
    simpa [prefixWord, tailWord_3505150, baseEnd_3505150] using wordTrace_append hprefix tailTrace_3505150
  have hstable : (prefixWord ++ tailWord_3505150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505150).length < 2 ^ (prefixWord ++ tailWord_3505150).sum := by decide
  have hdescent : baseEnd_3505150 < baseStart_3505150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505152 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5]
def baseStart_3505152 : Nat := 118140960795 + 3505152 * 2 ^ 59
def prefixEnd_3505152 : Nat := 4983230072969 + 3 ^ 40 * 3505152 * 2
def baseEnd_3505152 : Nat := 1799827743068375310380105

theorem tailTrace_3505152 : CollatzResearch.WordTrace tailWord_3505152 prefixEnd_3505152 1799827743068375310380105 := by
  unfold tailWord_3505152
  simp only [CollatzResearch.WordTrace]
  refine ⟨63921698098720205573578855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85228930798293607431438473 63921698098720205573578855)
  ·
    refine ⟨95882547148080308360368283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63921698098720205573578855 95882547148080308360368283)
    ·
      refine ⟨143823820722120462540552425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95882547148080308360368283 143823820722120462540552425)
      ·
        refine ⟨107867865541590346905414319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143823820722120462540552425 107867865541590346905414319)
        ·
          refine ⟨161801798312385520358121479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107867865541590346905414319 161801798312385520358121479)
          ·
            refine ⟨242702697468578280537182219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161801798312385520358121479 242702697468578280537182219)
            ·
              refine ⟨364054046202867420805773329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242702697468578280537182219 364054046202867420805773329)
              ·
                refine ⟨273040534652150565604329997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364054046202867420805773329 273040534652150565604329997)
                ·
                  refine ⟨102390200494556462101623749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273040534652150565604329997 102390200494556462101623749)
                  ·
                    refine ⟨19198162592729336644054453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102390200494556462101623749 19198162592729336644054453)
                    ·
                      refine ⟨1799827743068375310380105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19198162592729336644054453 1799827743068375310380105)
                      ·
                        rfl

theorem cell23_3505152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_3505152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505152 prefixEnd_3505152 := by exact prefixLift 3505152
  have htrace : WordTrace (prefixWord ++ tailWord_3505152) baseStart_3505152 baseEnd_3505152 := by
    simpa [prefixWord, tailWord_3505152, baseEnd_3505152] using wordTrace_append hprefix tailTrace_3505152
  have hstable : (prefixWord ++ tailWord_3505152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505152).length < 2 ^ (prefixWord ++ tailWord_3505152).sum := by decide
  have hdescent : baseEnd_3505152 < baseStart_3505152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505173 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_3505173 : Nat := 118140960795 + 3505173 * 2 ^ 59
def prefixEnd_3505173 : Nat := 4983230072969 + 3 ^ 40 * 3505173 * 2
def baseEnd_3505173 : Nat := 1799838526162119728217509

theorem tailTrace_3505173 : CollatzResearch.WordTrace tailWord_3505173 prefixEnd_3505173 1799838526162119728217509 := by
  unfold tailWord_3505173
  simp only [CollatzResearch.WordTrace]
  refine ⟨127844162130364331733672173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85229441420242887822448115 127844162130364331733672173)
  ·
    refine ⟨47941560798886624400127065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127844162130364331733672173 47941560798886624400127065)
    ·
      refine ⟨35956170599164968300095299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47941560798886624400127065 35956170599164968300095299)
      ·
        refine ⟨53934255898747452450142949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35956170599164968300095299 53934255898747452450142949)
        ·
          refine ⟨10112672981015147334401803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53934255898747452450142949 10112672981015147334401803)
          ·
            refine ⟨15169009471522721001602705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112672981015147334401803 15169009471522721001602705)
            ·
              refine ⟨11376757103642040751202029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15169009471522721001602705 11376757103642040751202029)
              ·
                refine ⟨4266283913865765281700761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11376757103642040751202029 4266283913865765281700761)
                ·
                  refine ⟨3199712935399323961275571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4266283913865765281700761 3199712935399323961275571)
                  ·
                    refine ⟨4799569403098985941913357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3199712935399323961275571 4799569403098985941913357)
                    ·
                      refine ⟨1799838526162119728217509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799569403098985941913357 1799838526162119728217509)
                      ·
                        rfl

theorem cell23_3505173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_3505173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505173 prefixEnd_3505173 := by exact prefixLift 3505173
  have htrace : WordTrace (prefixWord ++ tailWord_3505173) baseStart_3505173 baseEnd_3505173 := by
    simpa [prefixWord, tailWord_3505173, baseEnd_3505173] using wordTrace_append hprefix tailTrace_3505173
  have hstable : (prefixWord ++ tailWord_3505173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505173).length < 2 ^ (prefixWord ++ tailWord_3505173).sum := by decide
  have hdescent : baseEnd_3505173 < baseStart_3505173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505196 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 1, 4, 2]
def baseStart_3505196 : Nat := 118140960795 + 3505196 * 2 ^ 59
def prefixEnd_3505196 : Nat := 4983230072969 + 3 ^ 40 * 3505196 * 2
def baseEnd_3505196 : Nat := 1799850336217173138229903

theorem tailTrace_3505196 : CollatzResearch.WordTrace tailWord_3505196 prefixEnd_3505196 1799850336217173138229903 := by
  unfold tailWord_3505196
  simp only [CollatzResearch.WordTrace]
  refine ⟨63922500504640503330879721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85230000672854004441172961 63922500504640503330879721)
  ·
    refine ⟨47941875378480377498159791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63922500504640503330879721 47941875378480377498159791)
    ·
      refine ⟨71912813067720566247239687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47941875378480377498159791 71912813067720566247239687)
      ·
        refine ⟨107869219601580849370859531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71912813067720566247239687 107869219601580849370859531)
        ·
          refine ⟨161803829402371274056289297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107869219601580849370859531 161803829402371274056289297)
          ·
            refine ⟨121352872051778455542216973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161803829402371274056289297 121352872051778455542216973)
            ·
              refine ⟨45507327019416920828331365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121352872051778455542216973 45507327019416920828331365)
              ·
                refine ⟨8532623816140672655312131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45507327019416920828331365 8532623816140672655312131)
                ·
                  refine ⟨12798935724211008982968197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8532623816140672655312131 12798935724211008982968197)
                  ·
                    refine ⟨2399800448289564184306537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12798935724211008982968197 2399800448289564184306537)
                    ·
                      refine ⟨1799850336217173138229903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2399800448289564184306537 1799850336217173138229903)
                      ·
                        rfl

theorem cell23_3505196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_3505196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505196 prefixEnd_3505196 := by exact prefixLift 3505196
  have htrace : WordTrace (prefixWord ++ tailWord_3505196) baseStart_3505196 baseEnd_3505196 := by
    simpa [prefixWord, tailWord_3505196, baseEnd_3505196] using wordTrace_append hprefix tailTrace_3505196
  have hstable : (prefixWord ++ tailWord_3505196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505196).length < 2 ^ (prefixWord ++ tailWord_3505196).sum := by decide
  have hdescent : baseEnd_3505196 < baseStart_3505196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505206 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3505206 : Nat := 118140960795 + 3505206 * 2 ^ 59
def prefixEnd_3505206 : Nat := 4983230072969 + 3 ^ 40 * 3505206 * 2
def baseEnd_3505206 : Nat := 599951823674572699701619

theorem tailTrace_3505206 : CollatzResearch.WordTrace tailWord_3505206 prefixEnd_3505206 599951823674572699701619 := by
  unfold tailWord_3505206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990335358702798648101467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85230243826163185579748981 7990335358702798648101467)
  ·
    refine ⟨11985503038054197972152201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7990335358702798648101467 11985503038054197972152201)
    ·
      refine ⟨8989127278540648479114151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11985503038054197972152201 8989127278540648479114151)
      ·
        refine ⟨13483690917810972718671227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989127278540648479114151 13483690917810972718671227)
        ·
          refine ⟨20225536376716459078006841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13483690917810972718671227 20225536376716459078006841)
          ·
            refine ⟨15169152282537344308505131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20225536376716459078006841 15169152282537344308505131)
            ·
              refine ⟨22753728423806016462757697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15169152282537344308505131 22753728423806016462757697)
              ·
                refine ⟨17065296317854512347068273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22753728423806016462757697 17065296317854512347068273)
                ·
                  refine ⟨12798972238390884260301205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17065296317854512347068273 12798972238390884260301205)
                  ·
                    refine ⟨599951823674572699701619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12798972238390884260301205 599951823674572699701619)
                    ·
                      rfl

theorem cell23_3505206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3505206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505206 prefixEnd_3505206 := by exact prefixLift 3505206
  have htrace : WordTrace (prefixWord ++ tailWord_3505206) baseStart_3505206 baseEnd_3505206 := by
    simpa [prefixWord, tailWord_3505206, baseEnd_3505206] using wordTrace_append hprefix tailTrace_3505206
  have hstable : (prefixWord ++ tailWord_3505206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505206).length < 2 ^ (prefixWord ++ tailWord_3505206).sum := by decide
  have hdescent : baseEnd_3505206 < baseStart_3505206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505219 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 7]
def baseStart_3505219 : Nat := 118140960795 + 3505219 * 2 ^ 59
def prefixEnd_3505219 : Nat := 4983230072969 + 3 ^ 40 * 3505219 * 2
def baseEnd_3505219 : Nat := 199984682919136283138033

theorem tailTrace_3505219 : CollatzResearch.WordTrace tailWord_3505219 prefixEnd_3505219 199984682919136283138033 := by
  unfold tailWord_3505219
  simp only [CollatzResearch.WordTrace]
  refine ⟨127845839888197681589846711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85230559925465121059897807 127845839888197681589846711)
  ·
    refine ⟨191768759832296522384770067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127845839888197681589846711 191768759832296522384770067)
    ·
      refine ⟨287653139748444783577155101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191768759832296522384770067 287653139748444783577155101)
      ·
        refine ⟨107869927405666793841433163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287653139748444783577155101 107869927405666793841433163)
        ·
          refine ⟨161804891108500190762149745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107869927405666793841433163 161804891108500190762149745)
          ·
            refine ⟨121353668331375143071612309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161804891108500190762149745 121353668331375143071612309)
            ·
              refine ⟨5688453203033209831481827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121353668331375143071612309 5688453203033209831481827)
              ·
                refine ⟨8532679804549814747222741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688453203033209831481827 8532679804549814747222741)
                ·
                  refine ⟨199984682919136283138033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8532679804549814747222741 199984682919136283138033)
                  ·
                    rfl

theorem cell23_3505219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 7].length) (baseStart_3505219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505219 prefixEnd_3505219 := by exact prefixLift 3505219
  have htrace : WordTrace (prefixWord ++ tailWord_3505219) baseStart_3505219 baseEnd_3505219 := by
    simpa [prefixWord, tailWord_3505219, baseEnd_3505219] using wordTrace_append hprefix tailTrace_3505219
  have hstable : (prefixWord ++ tailWord_3505219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505219).length < 2 ^ (prefixWord ++ tailWord_3505219).sum := by decide
  have hdescent : baseEnd_3505219 < baseStart_3505219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505249 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_3505249 : Nat := 118140960795 + 3505249 * 2 ^ 59
def prefixEnd_3505249 : Nat := 4983230072969 + 3 ^ 40 * 3505249 * 2
def baseEnd_3505249 : Nat := 599959183563953810289053

theorem tailTrace_3505249 : CollatzResearch.WordTrace tailWord_3505249 prefixEnd_3505249 599959183563953810289053 := by
  unfold tailWord_3505249
  simp only [CollatzResearch.WordTrace]
  refine ⟨127846934078088996713438801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85231289385392664475625867 127846934078088996713438801)
  ·
    refine ⟨95885200558566747535079101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127846934078088996713438801 95885200558566747535079101)
    ·
      refine ⟨35956950209462530325654663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95885200558566747535079101 35956950209462530325654663)
      ·
        refine ⟨53935425314193795488481995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35956950209462530325654663 53935425314193795488481995)
        ·
          refine ⟨80903137971290693232722993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53935425314193795488481995 80903137971290693232722993)
          ·
            refine ⟨60677353478468019924542245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80903137971290693232722993 60677353478468019924542245)
            ·
              refine ⟨11377003777212753735851671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60677353478468019924542245 11377003777212753735851671)
              ·
                refine ⟨17065505665819130603777507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11377003777212753735851671 17065505665819130603777507)
                ·
                  refine ⟨25598258498728695905666261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17065505665819130603777507 25598258498728695905666261)
                  ·
                    refine ⟨599959183563953810289053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25598258498728695905666261 599959183563953810289053)
                    ·
                      rfl

theorem cell23_3505249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_3505249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505249 prefixEnd_3505249 := by exact prefixLift 3505249
  have htrace : WordTrace (prefixWord ++ tailWord_3505249) baseStart_3505249 baseEnd_3505249 := by
    simpa [prefixWord, tailWord_3505249, baseEnd_3505249] using wordTrace_append hprefix tailTrace_3505249
  have hstable : (prefixWord ++ tailWord_3505249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505249).length < 2 ^ (prefixWord ++ tailWord_3505249).sum := by decide
  have hdescent : baseEnd_3505249 < baseStart_3505249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505266 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3505266 : Nat := 118140960795 + 3505266 * 2 ^ 59
def prefixEnd_3505266 : Nat := 4983230072969 + 3 ^ 40 * 3505266 * 2
def baseEnd_3505266 : Nat := 599962093287662621451527

theorem tailTrace_3505266 : CollatzResearch.WordTrace tailWord_3505266 prefixEnd_3505266 599962093287662621451527 := by
  unfold tailWord_3505266
  simp only [CollatzResearch.WordTrace]
  refine ⟨31961888529756852154201913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85231702746018272411205101 31961888529756852154201913)
  ·
    refine ⟨23971416397317639115651435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31961888529756852154201913 23971416397317639115651435)
    ·
      refine ⟨35957124595976458673477153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23971416397317639115651435 35957124595976458673477153)
      ·
        refine ⟨26967843446982344005107865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35957124595976458673477153 26967843446982344005107865)
        ·
          refine ⟨20225882585236758003830899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26967843446982344005107865 20225882585236758003830899)
          ·
            refine ⟨30338823877855137005746349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20225882585236758003830899 30338823877855137005746349)
            ·
              refine ⟨11377058954195676377154881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30338823877855137005746349 11377058954195676377154881)
              ·
                refine ⟨8532794215646757282866161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11377058954195676377154881 8532794215646757282866161)
                ·
                  refine ⟨6399595661735067962149621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8532794215646757282866161 6399595661735067962149621)
                  ·
                    refine ⟨599962093287662621451527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6399595661735067962149621 599962093287662621451527)
                    ·
                      rfl

theorem cell23_3505266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3505266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505266 prefixEnd_3505266 := by exact prefixLift 3505266
  have htrace : WordTrace (prefixWord ++ tailWord_3505266) baseStart_3505266 baseEnd_3505266 := by
    simpa [prefixWord, tailWord_3505266, baseEnd_3505266] using wordTrace_append hprefix tailTrace_3505266
  have hstable : (prefixWord ++ tailWord_3505266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505266).length < 2 ^ (prefixWord ++ tailWord_3505266).sum := by decide
  have hdescent : baseEnd_3505266 < baseStart_3505266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505270 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_3505270 : Nat := 118140960795 + 3505270 * 2 ^ 59
def prefixEnd_3505270 : Nat := 4983230072969 + 3 ^ 40 * 3505270 * 2
def baseEnd_3505270 : Nat := 199987592642845094300507

theorem tailTrace_3505270 : CollatzResearch.WordTrace tailWord_3505270 prefixEnd_3505270 199987592642845094300507 := by
  unfold tailWord_3505270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7990481250688307331247079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85231800007341944866635509 7990481250688307331247079)
  ·
    refine ⟨11985721876032460996870619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7990481250688307331247079 11985721876032460996870619)
    ·
      refine ⟨17978582814048691495305929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11985721876032460996870619 17978582814048691495305929)
      ·
        refine ⟨13483937110536518621479447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17978582814048691495305929 13483937110536518621479447)
        ·
          refine ⟨20225905665804777932219171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13483937110536518621479447 20225905665804777932219171)
          ·
            refine ⟨30338858498707166898328757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20225905665804777932219171 30338858498707166898328757)
            ·
              refine ⟨2844267984253796896718321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30338858498707166898328757 2844267984253796896718321)
              ·
                refine ⟨2133200988190347672538741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844267984253796896718321 2133200988190347672538741)
                ·
                  refine ⟨199987592642845094300507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2133200988190347672538741 199987592642845094300507)
                  ·
                    rfl

theorem cell23_3505270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_3505270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505270 prefixEnd_3505270 := by exact prefixLift 3505270
  have htrace : WordTrace (prefixWord ++ tailWord_3505270) baseStart_3505270 baseEnd_3505270 := by
    simpa [prefixWord, tailWord_3505270, baseEnd_3505270] using wordTrace_append hprefix tailTrace_3505270
  have hstable : (prefixWord ++ tailWord_3505270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505270).length < 2 ^ (prefixWord ++ tailWord_3505270).sum := by decide
  have hdescent : baseEnd_3505270 < baseStart_3505270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505299 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4]
def baseStart_3505299 : Nat := 118140960795 + 3505299 * 2 ^ 59
def prefixEnd_3505299 : Nat := 4983230072969 + 3 ^ 40 * 3505299 * 2
def baseEnd_3505299 : Nat := 1799903224724586235241929

theorem tailTrace_3505299 : CollatzResearch.WordTrace tailWord_3505299 prefixEnd_3505299 1799903224724586235241929 := by
  unfold tailWord_3505299
  simp only [CollatzResearch.WordTrace]
  refine ⟨127848757727907855252758951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85232505151938570168505967 127848757727907855252758951)
  ·
    refine ⟨191773136591861782879138427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127848757727907855252758951 191773136591861782879138427)
    ·
      refine ⟨287659704887792674318707641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191773136591861782879138427 287659704887792674318707641)
      ·
        refine ⟨215744778665844505739030731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287659704887792674318707641 215744778665844505739030731)
        ·
          refine ⟨323617167998766758608546097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215744778665844505739030731 323617167998766758608546097)
          ·
            refine ⟨242712875999075068956409573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323617167998766758608546097 242712875999075068956409573)
            ·
              refine ⟨45508664249826575429326795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242712875999075068956409573 45508664249826575429326795)
              ·
                refine ⟨68262996374739863143990193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45508664249826575429326795 68262996374739863143990193)
                ·
                  refine ⟨51197247281054897357992645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68262996374739863143990193 51197247281054897357992645)
                  ·
                    refine ⟨9599483865197793254623621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51197247281054897357992645 9599483865197793254623621)
                    ·
                      refine ⟨1799903224724586235241929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9599483865197793254623621 1799903224724586235241929)
                      ·
                        rfl

theorem cell23_3505299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_3505299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505299 prefixEnd_3505299 := by exact prefixLift 3505299
  have htrace : WordTrace (prefixWord ++ tailWord_3505299) baseStart_3505299 baseEnd_3505299 := by
    simpa [prefixWord, tailWord_3505299, baseEnd_3505299] using wordTrace_append hprefix tailTrace_3505299
  have hstable : (prefixWord ++ tailWord_3505299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505299).length < 2 ^ (prefixWord ++ tailWord_3505299).sum := by decide
  have hdescent : baseEnd_3505299 < baseStart_3505299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505303 : List Nat := [1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_3505303 : Nat := 118140960795 + 3505303 * 2 ^ 59
def prefixEnd_3505303 : Nat := 4983230072969 + 3 ^ 40 * 3505303 * 2
def baseEnd_3505303 : Nat := 1799905278647204219591911

theorem tailTrace_3505303 : CollatzResearch.WordTrace tailWord_3505303 prefixEnd_3505303 1799905278647204219591911 := by
  unfold tailWord_3505303
  simp only [CollatzResearch.WordTrace]
  refine ⟨127848903619893363935904563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85232602413262242623936375 127848903619893363935904563)
  ·
    refine ⟨191773355429840045903856845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127848903619893363935904563 191773355429840045903856845)
    ·
      refine ⟨71915008286190017213946317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191773355429840045903856845 71915008286190017213946317)
      ·
        refine ⟨26968128107321256455229869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71915008286190017213946317 26968128107321256455229869)
        ·
          refine ⟨10113048040245471170711201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26968128107321256455229869 10113048040245471170711201)
          ·
            refine ⟨7584786030184103378033401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10113048040245471170711201 7584786030184103378033401)
            ·
              refine ⟨5688589522638077533525051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7584786030184103378033401 5688589522638077533525051)
              ·
                refine ⟨8532884283957116300287577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688589522638077533525051 8532884283957116300287577)
                ·
                  refine ⟨6399663212967837225215683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8532884283957116300287577 6399663212967837225215683)
                  ·
                    refine ⟨9599494819451755837823525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6399663212967837225215683 9599494819451755837823525)
                    ·
                      refine ⟨1799905278647204219591911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9599494819451755837823525 1799905278647204219591911)
                      ·
                        rfl

theorem cell23_3505303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_3505303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505303 prefixEnd_3505303 := by exact prefixLift 3505303
  have htrace : WordTrace (prefixWord ++ tailWord_3505303) baseStart_3505303 baseEnd_3505303 := by
    simpa [prefixWord, tailWord_3505303, baseEnd_3505303] using wordTrace_append hprefix tailTrace_3505303
  have hstable : (prefixWord ++ tailWord_3505303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505303).length < 2 ^ (prefixWord ++ tailWord_3505303).sum := by decide
  have hdescent : baseEnd_3505303 < baseStart_3505303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505330 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_3505330 : Nat := 118140960795 + 3505330 * 2 ^ 59
def prefixEnd_3505330 : Nat := 4983230072969 + 3 ^ 40 * 3505330 * 2
def baseEnd_3505330 : Nat := 599973047541625204651429

theorem tailTrace_3505330 : CollatzResearch.WordTrace tailWord_3505330 prefixEnd_3505330 599973047541625204651429 := by
  unfold tailWord_3505330
  simp only [CollatzResearch.WordTrace]
  refine ⟨31962472097698886886784361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85233258927197031698091629 31962472097698886886784361)
  ·
    refine ⟨23971854073274165165088271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31962472097698886886784361 23971854073274165165088271)
    ·
      refine ⟨35957781109911247747632407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23971854073274165165088271 35957781109911247747632407)
      ·
        refine ⟨53936671664866871621448611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35957781109911247747632407 53936671664866871621448611)
        ·
          refine ⟨80905007497300307432172917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53936671664866871621448611 80905007497300307432172917)
          ·
            refine ⟨7584844452871903821766211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80905007497300307432172917 7584844452871903821766211)
            ·
              refine ⟨11377266679307855732649317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584844452871903821766211 11377266679307855732649317)
              ·
                refine ⟨2133237502370222949871747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11377266679307855732649317 2133237502370222949871747)
                ·
                  refine ⟨3199856253555334424807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133237502370222949871747 3199856253555334424807621)
                  ·
                    refine ⟨599973047541625204651429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199856253555334424807621 599973047541625204651429)
                    ·
                      rfl

theorem cell23_3505330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_3505330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505330 prefixEnd_3505330 := by exact prefixLift 3505330
  have htrace : WordTrace (prefixWord ++ tailWord_3505330) baseStart_3505330 baseEnd_3505330 := by
    simpa [prefixWord, tailWord_3505330, baseEnd_3505330] using wordTrace_append hprefix tailTrace_3505330
  have hstable : (prefixWord ++ tailWord_3505330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505330).length < 2 ^ (prefixWord ++ tailWord_3505330).sum := by decide
  have hdescent : baseEnd_3505330 < baseStart_3505330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505349 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_3505349 : Nat := 118140960795 + 3505349 * 2 ^ 59
def prefixEnd_3505349 : Nat := 4983230072969 + 3 ^ 40 * 3505349 * 2
def baseEnd_3505349 : Nat := 1799928898757311039616699

theorem tailTrace_3505349 : CollatzResearch.WordTrace tailWord_3505349 prefixEnd_3505349 1799928898757311039616699 := by
  unfold tailWord_3505349
  simp only [CollatzResearch.WordTrace]
  refine ⟨127850581377726713792079101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85233720918484475861386067 127850581377726713792079101)
  ·
    refine ⟨47943968016647517672029663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127850581377726713792079101 47943968016647517672029663)
    ·
      refine ⟨71915952024971276508044495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47943968016647517672029663 71915952024971276508044495)
      ·
        refine ⟨107873928037456914762066743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71915952024971276508044495 107873928037456914762066743)
        ·
          refine ⟨161810892056185372143100115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107873928037456914762066743 161810892056185372143100115)
          ·
            refine ⟨242716338084278058214650173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161810892056185372143100115 242716338084278058214650173)
            ·
              refine ⟨91018626781604271830493815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242716338084278058214650173 91018626781604271830493815)
              ·
                refine ⟨136527940172406407745740723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91018626781604271830493815 136527940172406407745740723)
                ·
                  refine ⟨204791910258609611618611085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136527940172406407745740723 204791910258609611618611085)
                  ·
                    refine ⟨76796966346978604356979157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 204791910258609611618611085 76796966346978604356979157)
                    ·
                      refine ⟨1799928898757311039616699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76796966346978604356979157 1799928898757311039616699)
                      ·
                        rfl

theorem cell23_3505349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_3505349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505349 prefixEnd_3505349 := by exact prefixLift 3505349
  have htrace : WordTrace (prefixWord ++ tailWord_3505349) baseStart_3505349 baseEnd_3505349 := by
    simpa [prefixWord, tailWord_3505349, baseEnd_3505349] using wordTrace_append hprefix tailTrace_3505349
  have hstable : (prefixWord ++ tailWord_3505349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505349).length < 2 ^ (prefixWord ++ tailWord_3505349).sum := by decide
  have hdescent : baseEnd_3505349 < baseStart_3505349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505357 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3505357 : Nat := 118140960795 + 3505357 * 2 ^ 59
def prefixEnd_3505357 : Nat := 4983230072969 + 3 ^ 40 * 3505357 * 2
def baseEnd_3505357 : Nat := 1799933006602547008316663

theorem tailTrace_3505357 : CollatzResearch.WordTrace tailWord_3505357 prefixEnd_3505357 1799933006602547008316663 := by
  unfold tailWord_3505357
  simp only [CollatzResearch.WordTrace]
  refine ⟨127850873161697731158370325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85233915441131820772246883 127850873161697731158370325)
  ·
    refine ⟨5993009679454581148048609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127850873161697731158370325 5993009679454581148048609)
    ·
      refine ⟨4494757259590935861036457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5993009679454581148048609 4494757259590935861036457)
      ·
        refine ⟨3371067944693201895777343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4494757259590935861036457 3371067944693201895777343)
        ·
          refine ⟨5056601917039802843666015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371067944693201895777343 5056601917039802843666015)
          ·
            refine ⟨7584902875559704265499023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056601917039802843666015 7584902875559704265499023)
            ·
              refine ⟨11377354313339556398248535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584902875559704265499023 11377354313339556398248535)
              ·
                refine ⟨17066031470009334597372803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11377354313339556398248535 17066031470009334597372803)
                ·
                  refine ⟨25599047205014001896059205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17066031470009334597372803 25599047205014001896059205)
                  ·
                    refine ⟨4799821350940125355511101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25599047205014001896059205 4799821350940125355511101)
                    ·
                      refine ⟨1799933006602547008316663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799821350940125355511101 1799933006602547008316663)
                      ·
                        rfl

theorem cell23_3505357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3505357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505357 prefixEnd_3505357 := by exact prefixLift 3505357
  have htrace : WordTrace (prefixWord ++ tailWord_3505357) baseStart_3505357 baseEnd_3505357 := by
    simpa [prefixWord, tailWord_3505357, baseEnd_3505357] using wordTrace_append hprefix tailTrace_3505357
  have hstable : (prefixWord ++ tailWord_3505357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505357).length < 2 ^ (prefixWord ++ tailWord_3505357).sum := by decide
  have hdescent : baseEnd_3505357 < baseStart_3505357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505364 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_3505364 : Nat := 118140960795 + 3505364 * 2 ^ 59
def prefixEnd_3505364 : Nat := 4983230072969 + 3 ^ 40 * 3505364 * 2
def baseEnd_3505364 : Nat := 599978866989042826976377

theorem tailTrace_3505364 : CollatzResearch.WordTrace tailWord_3505364 prefixEnd_3505364 599978866989042826976377 := by
  unfold tailWord_3505364
  simp only [CollatzResearch.WordTrace]
  refine ⟨63925564236336185676937573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85234085648448247569250097 63925564236336185676937573)
  ·
    refine ⟨11986043294313034814425795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63925564236336185676937573 11986043294313034814425795)
    ·
      refine ⟨17979064941469552221638693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11986043294313034814425795 17979064941469552221638693)
      ·
        refine ⟨3371074676525541041557255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17979064941469552221638693 3371074676525541041557255)
        ·
          refine ⟨5056612014788311562335883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3371074676525541041557255 5056612014788311562335883)
          ·
            refine ⟨7584918022182467343503825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056612014788311562335883 7584918022182467343503825)
            ·
              refine ⟨5688688516636850507627869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7584918022182467343503825 5688688516636850507627869)
              ·
                refine ⟨2133258193738818940360451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5688688516636850507627869 2133258193738818940360451)
                ·
                  refine ⟨3199887290608228410540677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133258193738818940360451 3199887290608228410540677)
                  ·
                    refine ⟨599978866989042826976377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3199887290608228410540677 599978866989042826976377)
                    ·
                      rfl

theorem cell23_3505364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_3505364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505364 prefixEnd_3505364 := by exact prefixLift 3505364
  have htrace : WordTrace (prefixWord ++ tailWord_3505364) baseStart_3505364 baseEnd_3505364 := by
    simpa [prefixWord, tailWord_3505364, baseEnd_3505364] using wordTrace_append hprefix tailTrace_3505364
  have hstable : (prefixWord ++ tailWord_3505364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505364).length < 2 ^ (prefixWord ++ tailWord_3505364).sum := by decide
  have hdescent : baseEnd_3505364 < baseStart_3505364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505438 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3505438 : Nat := 118140960795 + 3505438 * 2 ^ 59
def prefixEnd_3505438 : Nat := 4983230072969 + 3 ^ 40 * 3505438 * 2
def baseEnd_3505438 : Nat := 1799974598535561191403791

theorem tailTrace_3505438 : CollatzResearch.WordTrace tailWord_3505438 prefixEnd_3505438 1799974598535561191403791 := by
  unfold tailWord_3505438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981728434300535249008621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85235884982936187994712645 15981728434300535249008621)
  ·
    refine ⟨5993148162862700718378233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15981728434300535249008621 5993148162862700718378233)
    ·
      refine ⟨4494861122147025538783675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5993148162862700718378233 4494861122147025538783675)
      ·
        refine ⟨6742291683220538308175513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494861122147025538783675 6742291683220538308175513)
        ·
          refine ⟨5056718762415403731131635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742291683220538308175513 5056718762415403731131635)
          ·
            refine ⟨7585078143623105596697453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056718762415403731131635 7585078143623105596697453)
            ·
              refine ⟨2844404303858664598761545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7585078143623105596697453 2844404303858664598761545)
              ·
                refine ⟨2133303227893998449071159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844404303858664598761545 2133303227893998449071159)
                ·
                  refine ⟨3199954841840997673606739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133303227893998449071159 3199954841840997673606739)
                  ·
                    refine ⟨4799932262761496510410109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3199954841840997673606739 4799932262761496510410109)
                    ·
                      refine ⟨1799974598535561191403791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799932262761496510410109 1799974598535561191403791)
                      ·
                        rfl

theorem cell23_3505438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3505438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505438 prefixEnd_3505438 := by exact prefixLift 3505438
  have htrace : WordTrace (prefixWord ++ tailWord_3505438) baseStart_3505438 baseEnd_3505438 := by
    simpa [prefixWord, tailWord_3505438, baseEnd_3505438] using wordTrace_append hprefix tailTrace_3505438
  have hstable : (prefixWord ++ tailWord_3505438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505438).length < 2 ^ (prefixWord ++ tailWord_3505438).sum := by decide
  have hdescent : baseEnd_3505438 < baseStart_3505438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505460 : List Nat := [2, 5, 1, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3505460 : Nat := 118140960795 + 3505460 * 2 ^ 59
def prefixEnd_3505460 : Nat := 4983230072969 + 3 ^ 40 * 3505460 * 2
def baseEnd_3505460 : Nat := 1799985895109960105328689

theorem tailTrace_3505460 : CollatzResearch.WordTrace tailWord_3505460 prefixEnd_3505460 1799985895109960105328689 := by
  unfold tailWord_3505460
  simp only [CollatzResearch.WordTrace]
  refine ⟨63927314940162289874684917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85236419920216386499579889 63927314940162289874684917)
  ·
    refine ⟨5993185775640214675751711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63927314940162289874684917 5993185775640214675751711)
    ·
      refine ⟨8989778663460322013627567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993185775640214675751711 8989778663460322013627567)
      ·
        refine ⟨13484667995190483020441351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989778663460322013627567 13484667995190483020441351)
        ·
          refine ⟨20227001992785724530662027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13484667995190483020441351 20227001992785724530662027)
          ·
            refine ⟨30340502989178586795993041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20227001992785724530662027 30340502989178586795993041)
            ·
              refine ⟨22755377241883940096994781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30340502989178586795993041 22755377241883940096994781)
              ·
                refine ⟨8533266465706477536373043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22755377241883940096994781 8533266465706477536373043)
                ·
                  refine ⟨12799899698559716304559565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533266465706477536373043 12799899698559716304559565)
                  ·
                    refine ⟨4799962386959893614209837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12799899698559716304559565 4799962386959893614209837)
                    ·
                      refine ⟨1799985895109960105328689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4799962386959893614209837 1799985895109960105328689)
                      ·
                        rfl

theorem cell23_3505460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3505460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505460 prefixEnd_3505460 := by exact prefixLift 3505460
  have htrace : WordTrace (prefixWord ++ tailWord_3505460) baseStart_3505460 baseEnd_3505460 := by
    simpa [prefixWord, tailWord_3505460, baseEnd_3505460] using wordTrace_append hprefix tailTrace_3505460
  have hstable : (prefixWord ++ tailWord_3505460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505460).length < 2 ^ (prefixWord ++ tailWord_3505460).sum := by decide
  have hdescent : baseEnd_3505460 < baseStart_3505460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505517 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_3505517 : Nat := 118140960795 + 3505517 * 2 ^ 59
def prefixEnd_3505517 : Nat := 4983230072969 + 3 ^ 40 * 3505517 * 2
def baseEnd_3505517 : Nat := 1800015163507266382315927

theorem tailTrace_3505517 : CollatzResearch.WordTrace tailWord_3505517 prefixEnd_3505517 1800015163507266382315927 := by
  unfold tailWord_3505517
  simp only [CollatzResearch.WordTrace]
  refine ⟨127856708841118078484194805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85237805894078718989463203 127856708841118078484194805)
  ·
    refine ⟨11986566453854819857893263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127856708841118078484194805 11986566453854819857893263)
    ·
      refine ⟨17979849680782229786839895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11986566453854819857893263 17979849680782229786839895)
      ·
        refine ⟨26969774521173344680259843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17979849680782229786839895 26969774521173344680259843)
        ·
          refine ⟨40454661781760017020389765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26969774521173344680259843 40454661781760017020389765)
          ·
            refine ⟨7585249084080003191323081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40454661781760017020389765 7585249084080003191323081)
            ·
              refine ⟨5688936813060002393492311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7585249084080003191323081 5688936813060002393492311)
              ·
                refine ⟨8533405219590003590238467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688936813060002393492311 8533405219590003590238467)
                ·
                  refine ⟨12800107829385005385357701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533405219590003590238467 12800107829385005385357701)
                  ·
                    refine ⟨2400020218009688509754569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12800107829385005385357701 2400020218009688509754569)
                    ·
                      refine ⟨1800015163507266382315927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400020218009688509754569 1800015163507266382315927)
                      ·
                        rfl

theorem cell23_3505517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_3505517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505517 prefixEnd_3505517 := by exact prefixLift 3505517
  have htrace : WordTrace (prefixWord ++ tailWord_3505517) baseStart_3505517 baseEnd_3505517 := by
    simpa [prefixWord, tailWord_3505517, baseEnd_3505517] using wordTrace_append hprefix tailTrace_3505517
  have hstable : (prefixWord ++ tailWord_3505517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505517).length < 2 ^ (prefixWord ++ tailWord_3505517).sum := by decide
  have hdescent : baseEnd_3505517 < baseStart_3505517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505533 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_3505533 : Nat := 118140960795 + 3505533 * 2 ^ 59
def prefixEnd_3505533 : Nat := 4983230072969 + 3 ^ 40 * 3505533 * 2
def baseEnd_3505533 : Nat := 1800023379197738319715853

theorem tailTrace_3505533 : CollatzResearch.WordTrace tailWord_3505533 prefixEnd_3505533 1800023379197738319715853 := by
  unfold tailWord_3505533
  simp only [CollatzResearch.WordTrace]
  refine ⟨127857292409060113216777253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85238194939373408811184835 127857292409060113216777253)
  ·
    refine ⟨23973242326698771228145735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127857292409060113216777253 23973242326698771228145735)
    ·
      refine ⟨35959863490048156842218603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23973242326698771228145735 35959863490048156842218603)
      ·
        refine ⟨53939795235072235263327905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35959863490048156842218603 53939795235072235263327905)
        ·
          refine ⟨40454846426304176447495929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53939795235072235263327905 40454846426304176447495929)
          ·
            refine ⟨30341134819728132335621947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40454846426304176447495929 30341134819728132335621947)
            ·
              refine ⟨45511702229592198503432921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30341134819728132335621947 45511702229592198503432921)
              ·
                refine ⟨34133776672194148877574691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45511702229592198503432921 34133776672194148877574691)
                ·
                  refine ⟨51200665008291223316362037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34133776672194148877574691 51200665008291223316362037)
                  ·
                    refine ⟨4800062344527302185908941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51200665008291223316362037 4800062344527302185908941)
                    ·
                      refine ⟨1800023379197738319715853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4800062344527302185908941 1800023379197738319715853)
                      ·
                        rfl

theorem cell23_3505533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_3505533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505533 prefixEnd_3505533 := by exact prefixLift 3505533
  have htrace : WordTrace (prefixWord ++ tailWord_3505533) baseStart_3505533 baseEnd_3505533 := by
    simpa [prefixWord, tailWord_3505533, baseEnd_3505533] using wordTrace_append hprefix tailTrace_3505533
  have hstable : (prefixWord ++ tailWord_3505533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505533).length < 2 ^ (prefixWord ++ tailWord_3505533).sum := by decide
  have hdescent : baseEnd_3505533 < baseStart_3505533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505538 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3505538 : Nat := 118140960795 + 3505538 * 2 ^ 59
def prefixEnd_3505538 : Nat := 4983230072969 + 3 ^ 40 * 3505538 * 2
def baseEnd_3505538 : Nat := 1800025946601010800153331

theorem tailTrace_3505538 : CollatzResearch.WordTrace tailWord_3505538 prefixEnd_3505538 1800025946601010800153331 := by
  unfold tailWord_3505538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964368693510499767677317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85238316516027999380472845 31964368693510499767677317)
  ·
    refine ⟨5993319130033218706439497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31964368693510499767677317 5993319130033218706439497)
    ·
      refine ⟨4494989347524914029829623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5993319130033218706439497 4494989347524914029829623)
      ·
        refine ⟨6742484021287371044744435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494989347524914029829623 6742484021287371044744435)
        ·
          refine ⟨10113726031931056567116653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742484021287371044744435 10113726031931056567116653)
          ·
            refine ⟨3792647261974146212668745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10113726031931056567116653 3792647261974146212668745)
            ·
              refine ⟨2844485446480609659501559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792647261974146212668745 2844485446480609659501559)
              ·
                refine ⟨4266728169720914489252339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844485446480609659501559 4266728169720914489252339)
                ·
                  refine ⟨6400092254581371733878509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4266728169720914489252339 6400092254581371733878509)
                  ·
                    refine ⟨2400034595468014400204441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6400092254581371733878509 2400034595468014400204441)
                    ·
                      refine ⟨1800025946601010800153331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400034595468014400204441 1800025946601010800153331)
                      ·
                        rfl

theorem cell23_3505538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3505538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505538 prefixEnd_3505538 := by exact prefixLift 3505538
  have htrace : WordTrace (prefixWord ++ tailWord_3505538) baseStart_3505538 baseEnd_3505538 := by
    simpa [prefixWord, tailWord_3505538, baseEnd_3505538] using wordTrace_append hprefix tailTrace_3505538
  have hstable : (prefixWord ++ tailWord_3505538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505538).length < 2 ^ (prefixWord ++ tailWord_3505538).sum := by decide
  have hdescent : baseEnd_3505538 < baseStart_3505538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505540 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 5]
def baseStart_3505540 : Nat := 118140960795 + 3505540 * 2 ^ 59
def prefixEnd_3505540 : Nat := 4983230072969 + 3 ^ 40 * 3505540 * 2
def baseEnd_3505540 : Nat := 200002997062479976925369

theorem tailTrace_3505540 : CollatzResearch.WordTrace tailWord_3505540 prefixEnd_3505540 200002997062479976925369 := by
  unfold tailWord_3505540
  simp only [CollatzResearch.WordTrace]
  refine ⟨63928773860017376706141037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85238365146689835608188049 63928773860017376706141037)
  ·
    refine ⟨23973290197506516264802889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63928773860017376706141037 23973290197506516264802889)
    ·
      refine ⟨17979967648129887198602167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23973290197506516264802889 17979967648129887198602167)
      ·
        refine ⟨26969951472194830797903251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17979967648129887198602167 26969951472194830797903251)
        ·
          refine ⟨40454927208292246196854877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26969951472194830797903251 40454927208292246196854877)
          ·
            refine ⟨15170597703109592323820579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40454927208292246196854877 15170597703109592323820579)
            ·
              refine ⟨22755896554664388485730869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15170597703109592323820579 22755896554664388485730869)
              ·
                refine ⟨2133365301999786420537269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22755896554664388485730869 2133365301999786420537269)
                ·
                  refine ⟨200002997062479976925369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2133365301999786420537269 200002997062479976925369)
                  ·
                    rfl

theorem cell23_3505540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_3505540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505540 prefixEnd_3505540 := by exact prefixLift 3505540
  have htrace : WordTrace (prefixWord ++ tailWord_3505540) baseStart_3505540 baseEnd_3505540 := by
    simpa [prefixWord, tailWord_3505540, baseEnd_3505540] using wordTrace_append hprefix tailTrace_3505540
  have hstable : (prefixWord ++ tailWord_3505540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505540).length < 2 ^ (prefixWord ++ tailWord_3505540).sum := by decide
  have hdescent : baseEnd_3505540 < baseStart_3505540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505573 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_3505573 : Nat := 118140960795 + 3505573 * 2 ^ 59
def prefixEnd_3505573 : Nat := 4983230072969 + 3 ^ 40 * 3505573 * 2
def baseEnd_3505573 : Nat := 1800043918423918163215669

theorem tailTrace_3505573 : CollatzResearch.WordTrace tailWord_3505573 prefixEnd_3505573 1800043918423918163215669 := by
  unfold tailWord_3505573
  simp only [CollatzResearch.WordTrace]
  refine ⟨127858751328915200048233373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85239167552610133365488915 127858751328915200048233373)
  ·
    refine ⟨47947031748343200018087515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127858751328915200048233373 47947031748343200018087515)
    ·
      refine ⟨71920547622514800027131273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47947031748343200018087515 71920547622514800027131273)
      ·
        refine ⟨53940410716886100020348455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71920547622514800027131273 53940410716886100020348455)
        ·
          refine ⟨80910616075329150030522683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53940410716886100020348455 80910616075329150030522683)
          ·
            refine ⟨121365924112993725045784025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80910616075329150030522683 121365924112993725045784025)
            ·
              refine ⟨91024443084745293784338019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121365924112993725045784025 91024443084745293784338019)
              ·
                refine ⟨136536664627117940676507029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91024443084745293784338019 136536664627117940676507029)
                ·
                  refine ⟨6400156154396153469211267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136536664627117940676507029 6400156154396153469211267)
                  ·
                    refine ⟨9600234231594230203816901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6400156154396153469211267 9600234231594230203816901)
                    ·
                      refine ⟨1800043918423918163215669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9600234231594230203816901 1800043918423918163215669)
                      ·
                        rfl

theorem cell23_3505573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_3505573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505573 prefixEnd_3505573 := by exact prefixLift 3505573
  have htrace : WordTrace (prefixWord ++ tailWord_3505573) baseStart_3505573 baseEnd_3505573 := by
    simpa [prefixWord, tailWord_3505573, baseEnd_3505573] using wordTrace_append hprefix tailTrace_3505573
  have hstable : (prefixWord ++ tailWord_3505573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505573).length < 2 ^ (prefixWord ++ tailWord_3505573).sum := by decide
  have hdescent : baseEnd_3505573 < baseStart_3505573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505610 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_3505610 : Nat := 118140960795 + 3505610 * 2 ^ 59
def prefixEnd_3505610 : Nat := 4983230072969 + 3 ^ 40 * 3505610 * 2
def baseEnd_3505610 : Nat := 1800062917208134518452999

theorem tailTrace_3505610 : CollatzResearch.WordTrace tailWord_3505610 prefixEnd_3505610 1800062917208134518452999 := by
  unfold tailWord_3505610
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965025207445288841832571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85240067219854103578220189 31965025207445288841832571)
  ·
    refine ⟨47947537811167933262748857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31965025207445288841832571 47947537811167933262748857)
    ·
      refine ⟨35960653358375949947061643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47947537811167933262748857 35960653358375949947061643)
      ·
        refine ⟨53940980037563924920592465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35960653358375949947061643 53940980037563924920592465)
        ·
          refine ⟨40455735028172943690444349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53940980037563924920592465 40455735028172943690444349)
          ·
            refine ⟨15170900635564853883916631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40455735028172943690444349 15170900635564853883916631)
            ·
              refine ⟨22756350953347280825874947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15170900635564853883916631 22756350953347280825874947)
              ·
                refine ⟨34134526430020921238812421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22756350953347280825874947 34134526430020921238812421)
                ·
                  refine ⟨6400223705628922732277329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34134526430020921238812421 6400223705628922732277329)
                  ·
                    refine ⟨4800167779221692049207997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6400223705628922732277329 4800167779221692049207997)
                    ·
                      refine ⟨1800062917208134518452999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4800167779221692049207997 1800062917208134518452999)
                      ·
                        rfl

theorem cell23_3505610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_3505610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505610 prefixEnd_3505610 := by exact prefixLift 3505610
  have htrace : WordTrace (prefixWord ++ tailWord_3505610) baseStart_3505610 baseEnd_3505610 := by
    simpa [prefixWord, tailWord_3505610, baseEnd_3505610] using wordTrace_append hprefix tailTrace_3505610
  have hstable : (prefixWord ++ tailWord_3505610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505610).length < 2 ^ (prefixWord ++ tailWord_3505610).sum := by decide
  have hdescent : baseEnd_3505610 < baseStart_3505610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505660 : List Nat := [2, 2, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_3505660 : Nat := 118140960795 + 3505660 * 2 ^ 59
def prefixEnd_3505660 : Nat := 4983230072969 + 3 ^ 40 * 3505660 * 2
def baseEnd_3505660 : Nat := 600029530413619774275923

theorem tailTrace_3505660 : CollatzResearch.WordTrace tailWord_3505660 prefixEnd_3505660 600029530413619774275923 := by
  unfold tailWord_3505660
  simp only [CollatzResearch.WordTrace]
  refine ⟨63930962239800006953325217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85241282986400009271100289 63930962239800006953325217)
  ·
    refine ⟨47948221679850005214993913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63930962239800006953325217 47948221679850005214993913)
    ·
      refine ⟨35961166259887503911245435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47948221679850005214993913 35961166259887503911245435)
      ·
        refine ⟨53941749389831255866868153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35961166259887503911245435 53941749389831255866868153)
        ·
          refine ⟨40456312042373441900151115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53941749389831255866868153 40456312042373441900151115)
          ·
            refine ⟨60684468063560162850226673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40456312042373441900151115 60684468063560162850226673)
            ·
              refine ⟨45513351047670122137670005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60684468063560162850226673 45513351047670122137670005)
              ·
                refine ⟨4266876660719073950406563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45513351047670122137670005 4266876660719073950406563)
                ·
                  refine ⟨6400314991078610925609845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4266876660719073950406563 6400314991078610925609845)
                  ·
                    refine ⟨600029530413619774275923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6400314991078610925609845 600029530413619774275923)
                    ·
                      rfl

theorem cell23_3505660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_3505660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505660 prefixEnd_3505660 := by exact prefixLift 3505660
  have htrace : WordTrace (prefixWord ++ tailWord_3505660) baseStart_3505660 baseEnd_3505660 := by
    simpa [prefixWord, tailWord_3505660, baseEnd_3505660] using wordTrace_append hprefix tailTrace_3505660
  have hstable : (prefixWord ++ tailWord_3505660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505660).length < 2 ^ (prefixWord ++ tailWord_3505660).sum := by decide
  have hdescent : baseEnd_3505660 < baseStart_3505660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505668 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 1, 4]
def baseStart_3505668 : Nat := 118140960795 + 3505668 * 2 ^ 59
def prefixEnd_3505668 : Nat := 4983230072969 + 3 ^ 40 * 3505668 * 2
def baseEnd_3505668 : Nat := 600030899695365097175911

theorem tailTrace_3505668 : CollatzResearch.WordTrace tailWord_3505668 prefixEnd_3505668 600030899695365097175911 := by
  unfold tailWord_3505668
  simp only [CollatzResearch.WordTrace]
  refine ⟨63931108131785515636470829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85241477509047354181961105 63931108131785515636470829)
  ·
    refine ⟨23974165549419568363676561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63931108131785515636470829 23974165549419568363676561)
    ·
      refine ⟨17980624162064676272757421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23974165549419568363676561 17980624162064676272757421)
      ·
        refine ⟨6742734060774253602284033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17980624162064676272757421 6742734060774253602284033)
        ·
          refine ⟨5057050545580690201713025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742734060774253602284033 5057050545580690201713025)
          ·
            refine ⟨3792787909185517651284769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5057050545580690201713025 3792787909185517651284769)
            ·
              refine ⟨2844590931889138238463577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3792787909185517651284769 2844590931889138238463577)
              ·
                refine ⟨2133443198916853678847683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2844590931889138238463577 2133443198916853678847683)
                ·
                  refine ⟨3200164798375280518271525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133443198916853678847683 3200164798375280518271525)
                  ·
                    refine ⟨600030899695365097175911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200164798375280518271525 600030899695365097175911)
                    ·
                      rfl

theorem cell23_3505668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_3505668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505668 prefixEnd_3505668 := by exact prefixLift 3505668
  have htrace : WordTrace (prefixWord ++ tailWord_3505668) baseStart_3505668 baseEnd_3505668 := by
    simpa [prefixWord, tailWord_3505668, baseEnd_3505668] using wordTrace_append hprefix tailTrace_3505668
  have hstable : (prefixWord ++ tailWord_3505668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505668).length < 2 ^ (prefixWord ++ tailWord_3505668).sum := by decide
  have hdescent : baseEnd_3505668 < baseStart_3505668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505673 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_3505673 : Nat := 118140960795 + 3505673 * 2 ^ 59
def prefixEnd_3505673 : Nat := 4983230072969 + 3 ^ 40 * 3505673 * 2
def baseEnd_3505673 : Nat := 600031755496455923988403

theorem tailTrace_3505673 : CollatzResearch.WordTrace tailWord_3505673 prefixEnd_3505673 600031755496455923988403 := by
  unfold tailWord_3505673
  simp only [CollatzResearch.WordTrace]
  refine ⟨127862398628552917126873673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85241599085701944751249115 127862398628552917126873673)
  ·
    refine ⟨95896798971414687845155255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127862398628552917126873673 95896798971414687845155255)
    ·
      refine ⟨143845198457122031767732883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95896798971414687845155255 143845198457122031767732883)
      ·
        refine ⟨215767797685683047651599325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143845198457122031767732883 215767797685683047651599325)
        ·
          refine ⟨80912924132131142869349747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215767797685683047651599325 80912924132131142869349747)
          ·
            refine ⟨121369386198196714304024621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80912924132131142869349747 121369386198196714304024621)
            ·
              refine ⟨45513519824323767864009233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121369386198196714304024621 45513519824323767864009233)
              ·
                refine ⟨34135139868242825898006925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45513519824323767864009233 34135139868242825898006925)
                ·
                  refine ⟨12800677450591059711752597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34135139868242825898006925 12800677450591059711752597)
                  ·
                    refine ⟨600031755496455923988403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12800677450591059711752597 600031755496455923988403)
                    ·
                      rfl

theorem cell23_3505673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_3505673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505673 prefixEnd_3505673 := by exact prefixLift 3505673
  have htrace : WordTrace (prefixWord ++ tailWord_3505673) baseStart_3505673 baseEnd_3505673 := by
    simpa [prefixWord, tailWord_3505673, baseEnd_3505673] using wordTrace_append hprefix tailTrace_3505673
  have hstable : (prefixWord ++ tailWord_3505673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505673).length < 2 ^ (prefixWord ++ tailWord_3505673).sum := by decide
  have hdescent : baseEnd_3505673 < baseStart_3505673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505690 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_3505690 : Nat := 118140960795 + 3505690 * 2 ^ 59
def prefixEnd_3505690 : Nat := 4983230072969 + 3 ^ 40 * 3505690 * 2
def baseEnd_3505690 : Nat := 600034665220164735150877

theorem tailTrace_3505690 : CollatzResearch.WordTrace tailWord_3505690 prefixEnd_3505690 600034665220164735150877 := by
  unfold tailWord_3505690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965754667372832257560631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85242012446327552686828349 31965754667372832257560631)
  ·
    refine ⟨47948632001059248386340947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31965754667372832257560631 47948632001059248386340947)
    ·
      refine ⟨71922948001588872579511421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47948632001059248386340947 71922948001588872579511421)
      ·
        refine ⟨26971105500595827217316783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71922948001588872579511421 26971105500595827217316783)
        ·
          refine ⟨40456658250893740825975175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26971105500595827217316783 40456658250893740825975175)
          ·
            refine ⟨60684987376340611238962763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40456658250893740825975175 60684987376340611238962763)
            ·
              refine ⟨91027481064510916858444145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60684987376340611238962763 91027481064510916858444145)
              ·
                refine ⟨68270610798383187643833109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91027481064510916858444145 68270610798383187643833109)
                ·
                  refine ⟨3200184881174211920804677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68270610798383187643833109 3200184881174211920804677)
                  ·
                    refine ⟨600034665220164735150877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200184881174211920804677 600034665220164735150877)
                    ·
                      rfl

theorem cell23_3505690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_3505690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505690 prefixEnd_3505690 := by exact prefixLift 3505690
  have htrace : WordTrace (prefixWord ++ tailWord_3505690) baseStart_3505690 baseEnd_3505690 := by
    simpa [prefixWord, tailWord_3505690, baseEnd_3505690] using wordTrace_append hprefix tailTrace_3505690
  have hstable : (prefixWord ++ tailWord_3505690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505690).length < 2 ^ (prefixWord ++ tailWord_3505690).sum := by decide
  have hdescent : baseEnd_3505690 < baseStart_3505690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505741 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3505741 : Nat := 118140960795 + 3505741 * 2 ^ 59
def prefixEnd_3505741 : Nat := 4983230072969 + 3 ^ 40 * 3505741 * 2
def baseEnd_3505741 : Nat := 600043394391291168638299

theorem tailTrace_3505741 : CollatzResearch.WordTrace tailWord_3505741 prefixEnd_3505741 600043394391291168638299 := by
  unfold tailWord_3505741
  simp only [CollatzResearch.WordTrace]
  refine ⟨127864878792306564740349077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85243252528204376493566051 127864878792306564740349077)
  ·
    refine ⟨5993666193389370222203863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 127864878792306564740349077 5993666193389370222203863)
    ·
      refine ⟨8990499290084055333305795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993666193389370222203863 8990499290084055333305795)
      ·
        refine ⟨13485748935126082999958693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8990499290084055333305795 13485748935126082999958693)
        ·
          refine ⟨2528577925336140562492255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13485748935126082999958693 2528577925336140562492255)
          ·
            refine ⟨3792866888004210843738383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528577925336140562492255 3792866888004210843738383)
            ·
              refine ⟨5689300332006316265607575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792866888004210843738383 5689300332006316265607575)
              ·
                refine ⟨8533950498009474398411363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689300332006316265607575 8533950498009474398411363)
                ·
                  refine ⟨12800925747014211597617045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533950498009474398411363 12800925747014211597617045)
                  ·
                    refine ⟨600043394391291168638299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12800925747014211597617045 600043394391291168638299)
                    ·
                      rfl

theorem cell23_3505741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3505741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505741 prefixEnd_3505741 := by exact prefixLift 3505741
  have htrace : WordTrace (prefixWord ++ tailWord_3505741) baseStart_3505741 baseEnd_3505741 := by
    simpa [prefixWord, tailWord_3505741, baseEnd_3505741] using wordTrace_append hprefix tailTrace_3505741
  have hstable : (prefixWord ++ tailWord_3505741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505741).length < 2 ^ (prefixWord ++ tailWord_3505741).sum := by decide
  have hdescent : baseEnd_3505741 < baseStart_3505741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505827 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 5]
def baseStart_3505827 : Nat := 118140960795 + 3505827 * 2 ^ 59
def prefixEnd_3505827 : Nat := 4983230072969 + 3 ^ 40 * 3505827 * 2
def baseEnd_3505827 : Nat := 200019371390017796604389

theorem tailTrace_3505827 : CollatzResearch.WordTrace tailWord_3505827 prefixEnd_3505827 200019371390017796604389 := by
  unfold tailWord_3505827
  simp only [CollatzResearch.WordTrace]
  refine ⟨127868015469995001427979735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85245343646663334285319823 127868015469995001427979735)
  ·
    refine ⟨191802023204992502141969603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127868015469995001427979735 191802023204992502141969603)
    ·
      refine ⟨287703034807488753212954405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191802023204992502141969603 287703034807488753212954405)
      ·
        refine ⟨53944319026404141227428951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287703034807488753212954405 53944319026404141227428951)
        ·
          refine ⟨80916478539606211841143427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53944319026404141227428951 80916478539606211841143427)
          ·
            refine ⟨121374717809409317761715141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80916478539606211841143427 121374717809409317761715141)
            ·
              refine ⟨22757759589264247080321589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121374717809409317761715141 22757759589264247080321589)
              ·
                refine ⟨2133539961493523163780149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22757759589264247080321589 2133539961493523163780149)
                ·
                  refine ⟨200019371390017796604389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2133539961493523163780149 200019371390017796604389)
                  ·
                    rfl

theorem cell23_3505827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 5].length) (baseStart_3505827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505827 prefixEnd_3505827 := by exact prefixLift 3505827
  have htrace : WordTrace (prefixWord ++ tailWord_3505827) baseStart_3505827 baseEnd_3505827 := by
    simpa [prefixWord, tailWord_3505827, baseEnd_3505827] using wordTrace_append hprefix tailTrace_3505827
  have hstable : (prefixWord ++ tailWord_3505827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505827).length < 2 ^ (prefixWord ++ tailWord_3505827).sum := by decide
  have hdescent : baseEnd_3505827 < baseStart_3505827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505854 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_3505854 : Nat := 118140960795 + 3505854 * 2 ^ 59
def prefixEnd_3505854 : Nat := 4983230072969 + 3 ^ 40 * 3505854 * 2
def baseEnd_3505854 : Nat := 1800188206487831563801877

theorem tailTrace_3505854 : CollatzResearch.WordTrace tailWord_3505854 prefixEnd_3505854 1800188206487831563801877 := by
  unfold tailWord_3505854
  simp only [CollatzResearch.WordTrace]
  refine ⟨15983625030112148129901577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85246000160598123359475077 15983625030112148129901577)
  ·
    refine ⟨11987718772584111097426183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15983625030112148129901577 11987718772584111097426183)
    ·
      refine ⟨17981578158876166646139275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11987718772584111097426183 17981578158876166646139275)
      ·
        refine ⟨26972367238314249969208913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17981578158876166646139275 26972367238314249969208913)
        ·
          refine ⟨20229275428735687476906685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26972367238314249969208913 20229275428735687476906685)
          ·
            refine ⟨7585978285775882803840007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20229275428735687476906685 7585978285775882803840007)
            ·
              refine ⟨11378967428663824205760011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585978285775882803840007 11378967428663824205760011)
              ·
                refine ⟨17068451142995736308640017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11378967428663824205760011 17068451142995736308640017)
                ·
                  refine ⟨12801338357246802231480013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17068451142995736308640017 12801338357246802231480013)
                  ·
                    refine ⟨4800501883967550836805005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12801338357246802231480013 4800501883967550836805005)
                    ·
                      refine ⟨1800188206487831563801877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4800501883967550836805005 1800188206487831563801877)
                      ·
                        rfl

theorem cell23_3505854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_3505854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505854 prefixEnd_3505854 := by exact prefixLift 3505854
  have htrace : WordTrace (prefixWord ++ tailWord_3505854) baseStart_3505854 baseEnd_3505854 := by
    simpa [prefixWord, tailWord_3505854, baseEnd_3505854] using wordTrace_append hprefix tailTrace_3505854
  have hstable : (prefixWord ++ tailWord_3505854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505854).length < 2 ^ (prefixWord ++ tailWord_3505854).sum := by decide
  have hdescent : baseEnd_3505854 < baseStart_3505854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505874 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3505874 : Nat := 118140960795 + 3505874 * 2 ^ 59
def prefixEnd_3505874 : Nat := 4983230072969 + 3 ^ 40 * 3505874 * 2
def baseEnd_3505874 : Nat := 600066158700307161850595

theorem tailTrace_3505874 : CollatzResearch.WordTrace tailWord_3505874 prefixEnd_3505874 600066158700307161850595 := by
  unfold tailWord_3505874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31967432425206182113735169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85246486467216485636627117 31967432425206182113735169)
  ·
    refine ⟨23975574318904636585301377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31967432425206182113735169 23975574318904636585301377)
    ·
      refine ⟨17981680739178477438976033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23975574318904636585301377 17981680739178477438976033)
      ·
        refine ⟨13486260554383858079232025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17981680739178477438976033 13486260554383858079232025)
        ·
          refine ⟨10114695415787893559424019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13486260554383858079232025 10114695415787893559424019)
          ·
            refine ⟨15172043123681840339136029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114695415787893559424019 15172043123681840339136029)
            ·
              refine ⟨5689516171380690127176011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15172043123681840339136029 5689516171380690127176011)
              ·
                refine ⟨8534274257071035190764017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689516171380690127176011 8534274257071035190764017)
                ·
                  refine ⟨6400705692803276393073013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8534274257071035190764017 6400705692803276393073013)
                  ·
                    refine ⟨600066158700307161850595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6400705692803276393073013 600066158700307161850595)
                    ·
                      rfl

theorem cell23_3505874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3505874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505874 prefixEnd_3505874 := by exact prefixLift 3505874
  have htrace : WordTrace (prefixWord ++ tailWord_3505874) baseStart_3505874 baseEnd_3505874 := by
    simpa [prefixWord, tailWord_3505874, baseEnd_3505874] using wordTrace_append hprefix tailTrace_3505874
  have hstable : (prefixWord ++ tailWord_3505874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505874).length < 2 ^ (prefixWord ++ tailWord_3505874).sum := by decide
  have hdescent : baseEnd_3505874 < baseStart_3505874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505887 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 5, 4]
def baseStart_3505887 : Nat := 118140960795 + 3505887 * 2 ^ 59
def prefixEnd_3505887 : Nat := 4983230072969 + 3 ^ 40 * 3505887 * 2
def baseEnd_3505887 : Nat := 600068383783143311563075

theorem tailTrace_3505887 : CollatzResearch.WordTrace tailWord_3505887 prefixEnd_3505887 600068383783143311563075 := by
  unfold tailWord_3505887
  simp only [CollatzResearch.WordTrace]
  refine ⟨127870203849777631675163915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85246802566518421116775943 127870203849777631675163915)
  ·
    refine ⟨191805305774666447512745873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127870203849777631675163915 191805305774666447512745873)
    ·
      refine ⟨143853979330999835634559405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191805305774666447512745873 143853979330999835634559405)
      ·
        refine ⟨53945242249124938362959777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143853979330999835634559405 53945242249124938362959777)
        ·
          refine ⟨40458931686843703772219833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53945242249124938362959777 40458931686843703772219833)
          ·
            refine ⟨30344198765132777829164875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40458931686843703772219833 30344198765132777829164875)
            ·
              refine ⟨45516298147699166743747313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30344198765132777829164875 45516298147699166743747313)
              ·
                refine ⟨34137223610774375057810485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45516298147699166743747313 34137223610774375057810485)
                ·
                  refine ⟨3200364713510097661669733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34137223610774375057810485 3200364713510097661669733)
                  ·
                    refine ⟨600068383783143311563075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200364713510097661669733 600068383783143311563075)
                    ·
                      rfl

theorem cell23_3505887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_3505887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505887 prefixEnd_3505887 := by exact prefixLift 3505887
  have htrace : WordTrace (prefixWord ++ tailWord_3505887) baseStart_3505887 baseEnd_3505887 := by
    simpa [prefixWord, tailWord_3505887, baseEnd_3505887] using wordTrace_append hprefix tailTrace_3505887
  have hstable : (prefixWord ++ tailWord_3505887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505887).length < 2 ^ (prefixWord ++ tailWord_3505887).sum := by decide
  have hdescent : baseEnd_3505887 < baseStart_3505887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505897 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_3505897 : Nat := 118140960795 + 3505897 * 2 ^ 59
def prefixEnd_3505897 : Nat := 4983230072969 + 3 ^ 40 * 3505897 * 2
def baseEnd_3505897 : Nat := 1800210286155974895564179

theorem tailTrace_3505897 : CollatzResearch.WordTrace tailWord_3505897 prefixEnd_3505897 1800210286155974895564179 := by
  unfold tailWord_3505897
  simp only [CollatzResearch.WordTrace]
  refine ⟨127870568579741403383027945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85247045719827602255351963 127870568579741403383027945)
  ·
    refine ⟨95902926434806052537270959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127870568579741403383027945 95902926434806052537270959)
    ·
      refine ⟨143854389652209078805906439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95902926434806052537270959 143854389652209078805906439)
      ·
        refine ⟨215781584478313618208859659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143854389652209078805906439 215781584478313618208859659)
        ·
          refine ⟨323672376717470427313289489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215781584478313618208859659 323672376717470427313289489)
          ·
            refine ⟨242754282538102820484967117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323672376717470427313289489 242754282538102820484967117)
            ·
              refine ⟨91032855951788557681862669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242754282538102820484967117 91032855951788557681862669)
              ·
                refine ⟨34137320981920709130698501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91032855951788557681862669 34137320981920709130698501)
                ·
                  refine ⟨6400747684110132962005969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34137320981920709130698501 6400747684110132962005969)
                  ·
                    refine ⟨4800560763082599721504477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6400747684110132962005969 4800560763082599721504477)
                    ·
                      refine ⟨1800210286155974895564179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4800560763082599721504477 1800210286155974895564179)
                      ·
                        rfl

theorem cell23_3505897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_3505897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505897 prefixEnd_3505897 := by exact prefixLift 3505897
  have htrace : WordTrace (prefixWord ++ tailWord_3505897) baseStart_3505897 baseEnd_3505897 := by
    simpa [prefixWord, tailWord_3505897, baseEnd_3505897] using wordTrace_append hprefix tailTrace_3505897
  have hstable : (prefixWord ++ tailWord_3505897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505897).length < 2 ^ (prefixWord ++ tailWord_3505897).sum := by decide
  have hdescent : baseEnd_3505897 < baseStart_3505897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505944 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3505944 : Nat := 118140960795 + 3505944 * 2 ^ 59
def prefixEnd_3505944 : Nat := 4983230072969 + 3 ^ 40 * 3505944 * 2
def baseEnd_3505944 : Nat := 1800234419746736211676463

theorem tailTrace_3505944 : CollatzResearch.WordTrace tailWord_3505944 prefixEnd_3505944 1800234419746736211676463 := by
  unfold tailWord_3505944
  simp only [CollatzResearch.WordTrace]
  refine ⟨63936141405285565204994443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85248188540380753606659257 63936141405285565204994443)
  ·
    refine ⟨95904212107928347807491665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63936141405285565204994443 95904212107928347807491665)
    ·
      refine ⟨71928159080946260855618749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95904212107928347807491665 71928159080946260855618749)
      ·
        refine ⟨26973059655354847820857031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71928159080946260855618749 26973059655354847820857031)
        ·
          refine ⟨40459589483032271731285547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26973059655354847820857031 40459589483032271731285547)
          ·
            refine ⟨60689384224548407596928321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40459589483032271731285547 60689384224548407596928321)
            ·
              refine ⟨45517038168411305697696241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60689384224548407596928321 45517038168411305697696241)
              ·
                refine ⟨34137778626308479273272181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45517038168411305697696241 34137778626308479273272181)
                ·
                  refine ⟨3200416746216419931869267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34137778626308479273272181 3200416746216419931869267)
                  ·
                    refine ⟨4800625119324629897803901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3200416746216419931869267 4800625119324629897803901)
                    ·
                      refine ⟨1800234419746736211676463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4800625119324629897803901 1800234419746736211676463)
                      ·
                        rfl

theorem cell23_3505944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3505944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505944 prefixEnd_3505944 := by exact prefixLift 3505944
  have htrace : WordTrace (prefixWord ++ tailWord_3505944) baseStart_3505944 baseEnd_3505944 := by
    simpa [prefixWord, tailWord_3505944, baseEnd_3505944] using wordTrace_append hprefix tailTrace_3505944
  have hstable : (prefixWord ++ tailWord_3505944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505944).length < 2 ^ (prefixWord ++ tailWord_3505944).sum := by decide
  have hdescent : baseEnd_3505944 < baseStart_3505944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505967 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_3505967 : Nat := 118140960795 + 3505967 * 2 ^ 59
def prefixEnd_3505967 : Nat := 4983230072969 + 3 ^ 40 * 3505967 * 2
def baseEnd_3505967 : Nat := 1800246229801789621688857

theorem tailTrace_3505967 : CollatzResearch.WordTrace tailWord_3505967 prefixEnd_3505967 1800246229801789621688857 := by
  unfold tailWord_3505967
  simp only [CollatzResearch.WordTrace]
  refine ⟨127873121689487805338076155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85248747792991870225384103 127873121689487805338076155)
  ·
    refine ⟨191809682534231708007114233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127873121689487805338076155 191809682534231708007114233)
    ·
      refine ⟨143857261900673781005335675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191809682534231708007114233 143857261900673781005335675)
      ·
        refine ⟨215785892851010671508003513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143857261900673781005335675 215785892851010671508003513)
        ·
          refine ⟨161839419638258003631002635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215785892851010671508003513 161839419638258003631002635)
          ·
            refine ⟨242759129457387005446503953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161839419638258003631002635 242759129457387005446503953)
            ·
              refine ⟨182069347093040254084877965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242759129457387005446503953 182069347093040254084877965)
              ·
                refine ⟨68276005159890095281829237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182069347093040254084877965 68276005159890095281829237)
                ·
                  refine ⟨6400875483739696432671491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68276005159890095281829237 6400875483739696432671491)
                  ·
                    refine ⟨9601313225609544649007237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6400875483739696432671491 9601313225609544649007237)
                    ·
                      refine ⟨1800246229801789621688857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9601313225609544649007237 1800246229801789621688857)
                      ·
                        rfl

theorem cell23_3505967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_3505967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505967 prefixEnd_3505967 := by exact prefixLift 3505967
  have htrace : WordTrace (prefixWord ++ tailWord_3505967) baseStart_3505967 baseEnd_3505967 := by
    simpa [prefixWord, tailWord_3505967, baseEnd_3505967] using wordTrace_append hprefix tailTrace_3505967
  have hstable : (prefixWord ++ tailWord_3505967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505967).length < 2 ^ (prefixWord ++ tailWord_3505967).sum := by decide
  have hdescent : baseEnd_3505967 < baseStart_3505967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3505981 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_3505981 : Nat := 118140960795 + 3505981 * 2 ^ 59
def prefixEnd_3505981 : Nat := 4983230072969 + 3 ^ 40 * 3505981 * 2
def baseEnd_3505981 : Nat := 600084472843650855637931

theorem tailTrace_3505981 : CollatzResearch.WordTrace tailWord_3505981 prefixEnd_3505981 600084472843650855637931 := by
  unfold tailWord_3505981
  simp only [CollatzResearch.WordTrace]
  refine ⟨127873632311437085729085797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85249088207624723819390531 127873632311437085729085797)
  ·
    refine ⟨23976306058394453574203587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127873632311437085729085797 23976306058394453574203587)
    ·
      refine ⟨35964459087591680361305381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23976306058394453574203587 35964459087591680361305381)
      ·
        refine ⟨6743336078923440067744759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35964459087591680361305381 6743336078923440067744759)
        ·
          refine ⟨10115004118385160101617139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743336078923440067744759 10115004118385160101617139)
          ·
            refine ⟨15172506177577740152425709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115004118385160101617139 15172506177577740152425709)
            ·
              refine ⟨5689689816591652557159641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15172506177577740152425709 5689689816591652557159641)
              ·
                refine ⟨4267267362443739417869731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5689689816591652557159641 4267267362443739417869731)
                ·
                  refine ⟨6400901043665609126804597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267267362443739417869731 6400901043665609126804597)
                  ·
                    refine ⟨600084472843650855637931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6400901043665609126804597 600084472843650855637931)
                    ·
                      rfl

theorem cell23_3505981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_3505981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3505981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3505981 prefixEnd_3505981 := by exact prefixLift 3505981
  have htrace : WordTrace (prefixWord ++ tailWord_3505981) baseStart_3505981 baseEnd_3505981 := by
    simpa [prefixWord, tailWord_3505981, baseEnd_3505981] using wordTrace_append hprefix tailTrace_3505981
  have hstable : (prefixWord ++ tailWord_3505981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3505981).length < 2 ^ (prefixWord ++ tailWord_3505981).sum := by decide
  have hdescent : baseEnd_3505981 < baseStart_3505981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3505981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506007 : List Nat := [1, 1, 3, 2, 5, 11]
def baseStart_3506007 : Nat := 118140960795 + 3506007 * 2 ^ 59
def prefixEnd_3506007 : Nat := 4983230072969 + 3 ^ 40 * 3506007 * 2
def baseEnd_3506007 : Nat := 7408505222337322902011

theorem tailTrace_3506007 : CollatzResearch.WordTrace tailWord_3506007 prefixEnd_3506007 7408505222337322902011 := by
  unfold tailWord_3506007
  simp only [CollatzResearch.WordTrace]
  refine ⟨127874580609342892169532275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85249720406228594779688183 127874580609342892169532275)
  ·
    refine ⟨191811870914014338254298413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127874580609342892169532275 191811870914014338254298413)
    ·
      refine ⟨71929451592755376845361905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191811870914014338254298413 71929451592755376845361905)
      ·
        refine ⟨53947088694566532634021429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71929451592755376845361905 53947088694566532634021429)
        ·
          refine ⟨5057539565115612434439509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53947088694566532634021429 5057539565115612434439509)
          ·
            refine ⟨7408505222337322902011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5057539565115612434439509 7408505222337322902011)
            ·
              rfl

theorem cell23_3506007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 11].length) (baseStart_3506007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506007 prefixEnd_3506007 := by exact prefixLift 3506007
  have htrace : WordTrace (prefixWord ++ tailWord_3506007) baseStart_3506007 baseEnd_3506007 := by
    simpa [prefixWord, tailWord_3506007, baseEnd_3506007] using wordTrace_append hprefix tailTrace_3506007
  have hstable : (prefixWord ++ tailWord_3506007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506007).length < 2 ^ (prefixWord ++ tailWord_3506007).sum := by decide
  have hdescent : baseEnd_3506007 < baseStart_3506007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506047 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_3506047 : Nat := 118140960795 + 3506047 * 2 ^ 59
def prefixEnd_3506047 : Nat := 4983230072969 + 3 ^ 40 * 3506047 * 2
def baseEnd_3506047 : Nat := 1800287308254149308688489

theorem tailTrace_3506047 : CollatzResearch.WordTrace tailWord_3506047 prefixEnd_3506047 1800287308254149308688489 := by
  unfold tailWord_3506047
  simp only [CollatzResearch.WordTrace]
  refine ⟨127876039529197979000988395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85250693019465319333992263 127876039529197979000988395)
  ·
    refine ⟨191814059293796968501482593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127876039529197979000988395 191814059293796968501482593)
    ·
      refine ⟨143860544470347726376111945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191814059293796968501482593 143860544470347726376111945)
      ·
        refine ⟨107895408352760794782083959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143860544470347726376111945 107895408352760794782083959)
        ·
          refine ⟨161843112529141192173125939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107895408352760794782083959 161843112529141192173125939)
          ·
            refine ⟨242764668793711788259688909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161843112529141192173125939 242764668793711788259688909)
            ·
              refine ⟨91036750797641920597383341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242764668793711788259688909 91036750797641920597383341)
              ·
                refine ⟨34138781549115720224018753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91036750797641920597383341 34138781549115720224018753)
                ·
                  refine ⟨25604086161836790168014065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34138781549115720224018753 25604086161836790168014065)
                  ·
                    refine ⟨19203064621377592626010549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25604086161836790168014065 19203064621377592626010549)
                    ·
                      refine ⟨1800287308254149308688489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19203064621377592626010549 1800287308254149308688489)
                      ·
                        rfl

theorem cell23_3506047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_3506047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506047 prefixEnd_3506047 := by exact prefixLift 3506047
  have htrace : WordTrace (prefixWord ++ tailWord_3506047) baseStart_3506047 baseEnd_3506047 := by
    simpa [prefixWord, tailWord_3506047, baseEnd_3506047] using wordTrace_append hprefix tailTrace_3506047
  have hstable : (prefixWord ++ tailWord_3506047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506047).length < 2 ^ (prefixWord ++ tailWord_3506047).sum := by decide
  have hdescent : baseEnd_3506047 < baseStart_3506047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506055 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_3506055 : Nat := 118140960795 + 3506055 * 2 ^ 59
def prefixEnd_3506055 : Nat := 4983230072969 + 3 ^ 40 * 3506055 * 2
def baseEnd_3506055 : Nat := 1800291416099385277388453

theorem tailTrace_3506055 : CollatzResearch.WordTrace tailWord_3506055 prefixEnd_3506055 1800291416099385277388453 := by
  unfold tailWord_3506055
  simp only [CollatzResearch.WordTrace]
  refine ⟨127876331313168996367279619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85250887542112664244853079 127876331313168996367279619)
  ·
    refine ⟨191814496969753494550919429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127876331313168996367279619 191814496969753494550919429)
    ·
      refine ⟨35965218181828780228297393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191814496969753494550919429 35965218181828780228297393)
      ·
        refine ⟨26973913636371585171223045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35965218181828780228297393 26973913636371585171223045)
        ·
          refine ⟨5057608806819672219604321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26973913636371585171223045 5057608806819672219604321)
          ·
            refine ⟨3793206605114754164703241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5057608806819672219604321 3793206605114754164703241)
            ·
              refine ⟨2844904953836065623527431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3793206605114754164703241 2844904953836065623527431)
              ·
                refine ⟨4267357430754098435291147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2844904953836065623527431 4267357430754098435291147)
                ·
                  refine ⟨6401036146131147652936721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267357430754098435291147 6401036146131147652936721)
                  ·
                    refine ⟨4800777109598360739702541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6401036146131147652936721 4800777109598360739702541)
                    ·
                      refine ⟨1800291416099385277388453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4800777109598360739702541 1800291416099385277388453)
                      ·
                        rfl

theorem cell23_3506055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_3506055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506055 prefixEnd_3506055 := by exact prefixLift 3506055
  have htrace : WordTrace (prefixWord ++ tailWord_3506055) baseStart_3506055 baseEnd_3506055 := by
    simpa [prefixWord, tailWord_3506055, baseEnd_3506055] using wordTrace_append hprefix tailTrace_3506055
  have hstable : (prefixWord ++ tailWord_3506055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506055).length < 2 ^ (prefixWord ++ tailWord_3506055).sum := by decide
  have hdescent : baseEnd_3506055 < baseStart_3506055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506062 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_3506062 : Nat := 118140960795 + 3506062 * 2 ^ 59
def prefixEnd_3506062 : Nat := 4983230072969 + 3 ^ 40 * 3506062 * 2
def baseEnd_3506062 : Nat := 600098336821322250000307

theorem tailTrace_3506062 : CollatzResearch.WordTrace tailWord_3506062 prefixEnd_3506062 600098336821322250000307 := by
  unfold tailWord_3506062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15984573328017954570348055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85251057749429091041856293 15984573328017954570348055)
  ·
    refine ⟨23976859992026931855522083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15984573328017954570348055 23976859992026931855522083)
    ·
      refine ⟨35965289988040397783283125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23976859992026931855522083 35965289988040397783283125)
      ·
        refine ⟨3371745936378787292182793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35965289988040397783283125 3371745936378787292182793)
        ·
          refine ⟨2528809452284090469137095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3371745936378787292182793 2528809452284090469137095)
          ·
            refine ⟨3793214178426135703705643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2528809452284090469137095 3793214178426135703705643)
            ·
              refine ⟨5689821267639203555558465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3793214178426135703705643 5689821267639203555558465)
              ·
                refine ⟨4267365950729402666668849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5689821267639203555558465 4267365950729402666668849)
                ·
                  refine ⟨3200524463047052000001637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4267365950729402666668849 3200524463047052000001637)
                  ·
                    refine ⟨600098336821322250000307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200524463047052000001637 600098336821322250000307)
                    ·
                      rfl

theorem cell23_3506062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_3506062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506062 prefixEnd_3506062 := by exact prefixLift 3506062
  have htrace : WordTrace (prefixWord ++ tailWord_3506062) baseStart_3506062 baseEnd_3506062 := by
    simpa [prefixWord, tailWord_3506062, baseEnd_3506062] using wordTrace_append hprefix tailTrace_3506062
  have hstable : (prefixWord ++ tailWord_3506062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506062).length < 2 ^ (prefixWord ++ tailWord_3506062).sum := by decide
  have hdescent : baseEnd_3506062 < baseStart_3506062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506068 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_3506068 : Nat := 118140960795 + 3506068 * 2 ^ 59
def prefixEnd_3506068 : Nat := 4983230072969 + 3 ^ 40 * 3506068 * 2
def baseEnd_3506068 : Nat := 1800298091347893726525893

theorem tailTrace_3506068 : CollatzResearch.WordTrace tailWord_3506068 prefixEnd_3506068 1800298091347893726525893 := by
  unfold tailWord_3506068
  simp only [CollatzResearch.WordTrace]
  refine ⟨63938402731060949793751429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85251203641414599725001905 63938402731060949793751429)
  ·
    refine ⟨11988450512073928086328393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63938402731060949793751429 11988450512073928086328393)
    ·
      refine ⟨8991337884055446064746295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11988450512073928086328393 8991337884055446064746295)
      ·
        refine ⟨13487006826083169097119443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991337884055446064746295 13487006826083169097119443)
        ·
          refine ⟨20230510239124753645679165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487006826083169097119443 20230510239124753645679165)
          ·
            refine ⟨7586441339671782617129687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20230510239124753645679165 7586441339671782617129687)
            ·
              refine ⟨11379662009507673925694531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586441339671782617129687 11379662009507673925694531)
              ·
                refine ⟨17069493014261510888541797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379662009507673925694531 17069493014261510888541797)
                ·
                  refine ⟨3200529940174033291601587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17069493014261510888541797 3200529940174033291601587)
                  ·
                    refine ⟨4800794910261049937402381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3200529940174033291601587 4800794910261049937402381)
                    ·
                      refine ⟨1800298091347893726525893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4800794910261049937402381 1800298091347893726525893)
                      ·
                        rfl

theorem cell23_3506068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_3506068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506068 prefixEnd_3506068 := by exact prefixLift 3506068
  have htrace : WordTrace (prefixWord ++ tailWord_3506068) baseStart_3506068 baseEnd_3506068 := by
    simpa [prefixWord, tailWord_3506068, baseEnd_3506068] using wordTrace_append hprefix tailTrace_3506068
  have hstable : (prefixWord ++ tailWord_3506068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506068).length < 2 ^ (prefixWord ++ tailWord_3506068).sum := by decide
  have hdescent : baseEnd_3506068 < baseStart_3506068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506084 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_3506084 : Nat := 118140960795 + 3506084 * 2 ^ 59
def prefixEnd_3506084 : Nat := 4983230072969 + 3 ^ 40 * 3506084 * 2
def baseEnd_3506084 : Nat := 600102102346121887975273

theorem tailTrace_3506084 : CollatzResearch.WordTrace tailWord_3506084 prefixEnd_3506084 600102102346121887975273 := by
  unfold tailWord_3506084
  simp only [CollatzResearch.WordTrace]
  refine ⟨63938694515031967160042653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85251592686709289546723537 63938694515031967160042653)
  ·
    refine ⟨23977010443136987685015995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63938694515031967160042653 23977010443136987685015995)
    ·
      refine ⟨35965515664705481527523993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23977010443136987685015995 35965515664705481527523993)
      ·
        refine ⟨26974136748529111145642995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35965515664705481527523993 26974136748529111145642995)
        ·
          refine ⟨40461205122793666718464493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26974136748529111145642995 40461205122793666718464493)
          ·
            refine ⟨15172951921047625019424185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40461205122793666718464493 15172951921047625019424185)
            ·
              refine ⟨11379713940785718764568139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15172951921047625019424185 11379713940785718764568139)
              ·
                refine ⟨17069570911178578146852209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379713940785718764568139 17069570911178578146852209)
                ·
                  refine ⟨12802178183383933610139157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17069570911178578146852209 12802178183383933610139157)
                  ·
                    refine ⟨600102102346121887975273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12802178183383933610139157 600102102346121887975273)
                    ·
                      rfl

theorem cell23_3506084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_3506084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506084 prefixEnd_3506084 := by exact prefixLift 3506084
  have htrace : WordTrace (prefixWord ++ tailWord_3506084) baseStart_3506084 baseEnd_3506084 := by
    simpa [prefixWord, tailWord_3506084, baseEnd_3506084] using wordTrace_append hprefix tailTrace_3506084
  have hstable : (prefixWord ++ tailWord_3506084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506084).length < 2 ^ (prefixWord ++ tailWord_3506084).sum := by decide
  have hdescent : baseEnd_3506084 < baseStart_3506084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506091 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 8, 2, 2]
def baseStart_3506091 : Nat := 118140960795 + 3506091 * 2 ^ 59
def prefixEnd_3506091 : Nat := 4983230072969 + 3 ^ 40 * 3506091 * 2
def baseEnd_3506091 : Nat := 1800309901402947136538287

theorem tailTrace_3506091 : CollatzResearch.WordTrace tailWord_3506091 prefixEnd_3506091 1800309901402947136538287 := by
  unfold tailWord_3506091
  simp only [CollatzResearch.WordTrace]
  refine ⟨127877644341038574515590127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85251762894025716343726751 127877644341038574515590127)
  ·
    refine ⟨191816466511557861773385191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127877644341038574515590127 191816466511557861773385191)
    ·
      refine ⟨287724699767336792660077787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191816466511557861773385191 287724699767336792660077787)
      ·
        refine ⟨431587049651005188990116681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287724699767336792660077787 431587049651005188990116681)
        ·
          refine ⟨323690287238253891742587511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431587049651005188990116681 323690287238253891742587511)
          ·
            refine ⟨485535430857380837613881267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323690287238253891742587511 485535430857380837613881267)
            ·
              refine ⟨728303146286071256420821901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485535430857380837613881267 728303146286071256420821901)
              ·
                refine ⟨273113679857276721157808213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 728303146286071256420821901 273113679857276721157808213)
                ·
                  refine ⟨3200550935827461576068065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 273113679857276721157808213 3200550935827461576068065)
                  ·
                    refine ⟨2400413201870596182051049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3200550935827461576068065 2400413201870596182051049)
                    ·
                      refine ⟨1800309901402947136538287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2400413201870596182051049 1800309901402947136538287)
                      ·
                        rfl

theorem cell23_3506091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 2, 2].length) (baseStart_3506091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506091 prefixEnd_3506091 := by exact prefixLift 3506091
  have htrace : WordTrace (prefixWord ++ tailWord_3506091) baseStart_3506091 baseEnd_3506091 := by
    simpa [prefixWord, tailWord_3506091, baseEnd_3506091] using wordTrace_append hprefix tailTrace_3506091
  have hstable : (prefixWord ++ tailWord_3506091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506091).length < 2 ^ (prefixWord ++ tailWord_3506091).sum := by decide
  have hdescent : baseEnd_3506091 < baseStart_3506091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506107 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7]
def baseStart_3506107 : Nat := 118140960795 + 3506107 * 2 ^ 59
def prefixEnd_3506107 : Nat := 4983230072969 + 3 ^ 40 * 3506107 * 2
def baseEnd_3506107 : Nat := 1800318117093419073938213

theorem tailTrace_3506107 : CollatzResearch.WordTrace tailWord_3506107 prefixEnd_3506107 1800318117093419073938213 := by
  unfold tailWord_3506107
  simp only [CollatzResearch.WordTrace]
  refine ⟨127878227908980609248172575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85252151939320406165448383 127878227908980609248172575)
  ·
    refine ⟨191817341863470913872258863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127878227908980609248172575 191817341863470913872258863)
    ·
      refine ⟨287726012795206370808388295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191817341863470913872258863 287726012795206370808388295)
      ·
        refine ⟨431589019192809556212582443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287726012795206370808388295 431589019192809556212582443)
        ·
          refine ⟨647383528789214334318873665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431589019192809556212582443 647383528789214334318873665)
          ·
            refine ⟨485537646591910750739155249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647383528789214334318873665 485537646591910750739155249)
            ·
              refine ⟨364153234943933063054366437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485537646591910750739155249 364153234943933063054366437)
              ·
                refine ⟨68278731551987449322693707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364153234943933063054366437 68278731551987449322693707)
                ·
                  refine ⟨102418097327981173984040561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68278731551987449322693707 102418097327981173984040561)
                  ·
                    refine ⟨76813572995985880488030421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102418097327981173984040561 76813572995985880488030421)
                    ·
                      refine ⟨1800318117093419073938213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76813572995985880488030421 1800318117093419073938213)
                      ·
                        rfl

theorem cell23_3506107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_3506107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506107 prefixEnd_3506107 := by exact prefixLift 3506107
  have htrace : WordTrace (prefixWord ++ tailWord_3506107) baseStart_3506107 baseEnd_3506107 := by
    simpa [prefixWord, tailWord_3506107, baseEnd_3506107] using wordTrace_append hprefix tailTrace_3506107
  have hstable : (prefixWord ++ tailWord_3506107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506107).length < 2 ^ (prefixWord ++ tailWord_3506107).sum := by decide
  have hdescent : baseEnd_3506107 < baseStart_3506107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506154 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_3506154 : Nat := 118140960795 + 3506154 * 2 ^ 59
def prefixEnd_3506154 : Nat := 4983230072969 + 3 ^ 40 * 3506154 * 2
def baseEnd_3506154 : Nat := 1800342250684180390050497

theorem tailTrace_3506154 : CollatzResearch.WordTrace tailWord_3506154 prefixEnd_3506154 1800342250684180390050497 := by
  unfold tailWord_3506154
  simp only [CollatzResearch.WordTrace]
  refine ⟨31969985534952584068783379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85253294759873557516755677 31969985534952584068783379)
  ·
    refine ⟨47954978302428876103175069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31969985534952584068783379 47954978302428876103175069)
    ·
      refine ⟨17983116863410828538690651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47954978302428876103175069 17983116863410828538690651)
      ·
        refine ⟨26974675295116242808035977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17983116863410828538690651 26974675295116242808035977)
        ·
          refine ⟨20231006471337182106026983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26974675295116242808035977 20231006471337182106026983)
          ·
            refine ⟨30346509707005773159040475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231006471337182106026983 30346509707005773159040475)
            ·
              refine ⟨45519764560508659738560713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30346509707005773159040475 45519764560508659738560713)
              ·
                refine ⟨34139823420381494803920535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45519764560508659738560713 34139823420381494803920535)
                ·
                  refine ⟨51209735130572242205880803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34139823420381494803920535 51209735130572242205880803)
                  ·
                    refine ⟨76814602695858363308821205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51209735130572242205880803 76814602695858363308821205)
                    ·
                      refine ⟨1800342250684180390050497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 76814602695858363308821205 1800342250684180390050497)
                      ·
                        rfl

theorem cell23_3506154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_3506154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506154 prefixEnd_3506154 := by exact prefixLift 3506154
  have htrace : WordTrace (prefixWord ++ tailWord_3506154) baseStart_3506154 baseEnd_3506154 := by
    simpa [prefixWord, tailWord_3506154, baseEnd_3506154] using wordTrace_append hprefix tailTrace_3506154
  have hstable : (prefixWord ++ tailWord_3506154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506154).length < 2 ^ (prefixWord ++ tailWord_3506154).sum := by decide
  have hdescent : baseEnd_3506154 < baseStart_3506154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506181 : List Nat := [1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_3506181 : Nat := 118140960795 + 3506181 * 2 ^ 59
def prefixEnd_3506181 : Nat := 4983230072969 + 3 ^ 40 * 3506181 * 2
def baseEnd_3506181 : Nat := 1800356114661851784412873

theorem tailTrace_3506181 : CollatzResearch.WordTrace tailWord_3506181 prefixEnd_3506181 1800356114661851784412873 := by
  unfold tailWord_3506181
  simp only [CollatzResearch.WordTrace]
  refine ⟨127880926910712519886366397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85253951273808346590910931 127880926910712519886366397)
  ·
    refine ⟨47955347591517194957387399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127880926910712519886366397 47955347591517194957387399)
    ·
      refine ⟨71933021387275792436081099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47955347591517194957387399 71933021387275792436081099)
      ·
        refine ⟨107899532080913688654121649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71933021387275792436081099 107899532080913688654121649)
        ·
          refine ⟨80924649060685266490591237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107899532080913688654121649 80924649060685266490591237)
          ·
            refine ⟨15173371698878487466985857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80924649060685266490591237 15173371698878487466985857)
            ·
              refine ⟨11380028774158865600239393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15173371698878487466985857 11380028774158865600239393)
              ·
                refine ⟨8535021580619149200179545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11380028774158865600239393 8535021580619149200179545)
                ·
                  refine ⟨6401266185464361900134659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8535021580619149200179545 6401266185464361900134659)
                  ·
                    refine ⟨9601899278196542850201989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6401266185464361900134659 9601899278196542850201989)
                    ·
                      refine ⟨1800356114661851784412873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9601899278196542850201989 1800356114661851784412873)
                      ·
                        rfl

theorem cell23_3506181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_3506181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506181 prefixEnd_3506181 := by exact prefixLift 3506181
  have htrace : WordTrace (prefixWord ++ tailWord_3506181) baseStart_3506181 baseEnd_3506181 := by
    simpa [prefixWord, tailWord_3506181, baseEnd_3506181] using wordTrace_append hprefix tailTrace_3506181
  have hstable : (prefixWord ++ tailWord_3506181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506181).length < 2 ^ (prefixWord ++ tailWord_3506181).sum := by decide
  have hdescent : baseEnd_3506181 < baseStart_3506181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506184 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3506184 : Nat := 118140960795 + 3506184 * 2 ^ 59
def prefixEnd_3506184 : Nat := 4983230072969 + 3 ^ 40 * 3506184 * 2
def baseEnd_3506184 : Nat := 1800357655103815272675359

theorem tailTrace_3506184 : CollatzResearch.WordTrace tailWord_3506184 prefixEnd_3506184 1800357655103815272675359 := by
  unfold tailWord_3506184
  simp only [CollatzResearch.WordTrace]
  refine ⟨63940518164850825699362803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85254024219801100932483737 63940518164850825699362803)
  ·
    refine ⟨95910777247276238549044205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63940518164850825699362803 95910777247276238549044205)
    ·
      refine ⟨35966541467728589455891577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95910777247276238549044205 35966541467728589455891577)
      ·
        refine ⟨26974906100796442091918683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35966541467728589455891577 26974906100796442091918683)
        ·
          refine ⟨40462359151194663137878025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26974906100796442091918683 40462359151194663137878025)
          ·
            refine ⟨30346769363395997353408519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40462359151194663137878025 30346769363395997353408519)
            ·
              refine ⟨45520154045093996030112779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30346769363395997353408519 45520154045093996030112779)
              ·
                refine ⟨68280231067640994045169169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45520154045093996030112779 68280231067640994045169169)
                ·
                  refine ⟨51210173300730745533876877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68280231067640994045169169 51210173300730745533876877)
                  ·
                    refine ⟨19203814987774029575203829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51210173300730745533876877 19203814987774029575203829)
                    ·
                      refine ⟨1800357655103815272675359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19203814987774029575203829 1800357655103815272675359)
                      ·
                        rfl

theorem cell23_3506184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3506184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506184 prefixEnd_3506184 := by exact prefixLift 3506184
  have htrace : WordTrace (prefixWord ++ tailWord_3506184) baseStart_3506184 baseEnd_3506184 := by
    simpa [prefixWord, tailWord_3506184, baseEnd_3506184] using wordTrace_append hprefix tailTrace_3506184
  have hstable : (prefixWord ++ tailWord_3506184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506184).length < 2 ^ (prefixWord ++ tailWord_3506184).sum := by decide
  have hdescent : baseEnd_3506184 < baseStart_3506184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506218 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3506218 : Nat := 118140960795 + 3506218 * 2 ^ 59
def prefixEnd_3506218 : Nat := 4983230072969 + 3 ^ 40 * 3506218 * 2
def baseEnd_3506218 : Nat := 1800375113446068139650203

theorem tailTrace_3506218 : CollatzResearch.WordTrace tailWord_3506218 prefixEnd_3506218 1800375113446068139650203 := by
  unfold tailWord_3506218
  simp only [CollatzResearch.WordTrace]
  refine ⟨31970569102894618801365827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85254850941052316803642205 31970569102894618801365827)
  ·
    refine ⟨47955853654341928202048741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31970569102894618801365827 47955853654341928202048741)
    ·
      refine ⟨8991722560189111537884139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47955853654341928202048741 8991722560189111537884139)
      ·
        refine ⟨13487583840283667306826209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991722560189111537884139 13487583840283667306826209)
        ·
          refine ⟨10115687880212750480119657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13487583840283667306826209 10115687880212750480119657)
          ·
            refine ⟨7586765910159562860089743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10115687880212750480119657 7586765910159562860089743)
            ·
              refine ⟨11380148865239344290134615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586765910159562860089743 11380148865239344290134615)
              ·
                refine ⟨17070223297859016435201923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11380148865239344290134615 17070223297859016435201923)
                ·
                  refine ⟨25605334946788524652802885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17070223297859016435201923 25605334946788524652802885)
                  ·
                    refine ⟨4801000302522848372400541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25605334946788524652802885 4801000302522848372400541)
                    ·
                      refine ⟨1800375113446068139650203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4801000302522848372400541 1800375113446068139650203)
                      ·
                        rfl

theorem cell23_3506218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3506218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506218 prefixEnd_3506218 := by exact prefixLift 3506218
  have htrace : WordTrace (prefixWord ++ tailWord_3506218) baseStart_3506218 baseEnd_3506218 := by
    simpa [prefixWord, tailWord_3506218, baseEnd_3506218] using wordTrace_append hprefix tailTrace_3506218
  have hstable : (prefixWord ++ tailWord_3506218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506218).length < 2 ^ (prefixWord ++ tailWord_3506218).sum := by decide
  have hdescent : baseEnd_3506218 < baseStart_3506218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506225 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 1, 4]
def baseStart_3506225 : Nat := 118140960795 + 3506225 * 2 ^ 59
def prefixEnd_3506225 : Nat := 4983230072969 + 3 ^ 40 * 3506225 * 2
def baseEnd_3506225 : Nat := 600126235936883204087557

theorem tailTrace_3506225 : CollatzResearch.WordTrace tailWord_3506225 prefixEnd_3506225 600126235936883204087557 := by
  unfold tailWord_3506225
  simp only [CollatzResearch.WordTrace]
  refine ⟨127882531722553115400968129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85255021148368743600645419 127882531722553115400968129)
  ·
    refine ⟨95911898791914836550726097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127882531722553115400968129 95911898791914836550726097)
    ·
      refine ⟨71933924093936127413044573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95911898791914836550726097 71933924093936127413044573)
      ·
        refine ⟨26975221535226047779891715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71933924093936127413044573 26975221535226047779891715)
        ·
          refine ⟨40462832302839071669837573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26975221535226047779891715 40462832302839071669837573)
          ·
            refine ⟨7586781056782325938094545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40462832302839071669837573 7586781056782325938094545)
            ·
              refine ⟨5690085792586744453570909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7586781056782325938094545 5690085792586744453570909)
              ·
                refine ⟨2133782172220029170089091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5690085792586744453570909 2133782172220029170089091)
                ·
                  refine ⟨3200673258330043755133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2133782172220029170089091 3200673258330043755133637)
                  ·
                    refine ⟨600126235936883204087557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200673258330043755133637 600126235936883204087557)
                    ·
                      rfl

theorem cell23_3506225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_3506225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506225 prefixEnd_3506225 := by exact prefixLift 3506225
  have htrace : WordTrace (prefixWord ++ tailWord_3506225) baseStart_3506225 baseEnd_3506225 := by
    simpa [prefixWord, tailWord_3506225, baseEnd_3506225] using wordTrace_append hprefix tailTrace_3506225
  have hstable : (prefixWord ++ tailWord_3506225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506225).length < 2 ^ (prefixWord ++ tailWord_3506225).sum := by decide
  have hdescent : baseEnd_3506225 < baseStart_3506225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506238 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 8]
def baseStart_3506238 : Nat := 118140960795 + 3506238 * 2 ^ 59
def prefixEnd_3506238 : Nat := 4983230072969 + 3 ^ 40 * 3506238 * 2
def baseEnd_3506238 : Nat := 200042820339906451266679

theorem tailTrace_3506238 : CollatzResearch.WordTrace tailWord_3506238 prefixEnd_3506238 200042820339906451266679 := by
  unfold tailWord_3506238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985375733938252327648921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85255337247670679080794245 15985375733938252327648921)
  ·
    refine ⟨11989031800453689245736691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15985375733938252327648921 11989031800453689245736691)
    ·
      refine ⟨17983547700680533868605037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11989031800453689245736691 17983547700680533868605037)
      ·
        refine ⟨6743830387755200200726889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17983547700680533868605037 6743830387755200200726889)
        ·
          refine ⟨5057872790816400150545167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6743830387755200200726889 5057872790816400150545167)
          ·
            refine ⟨7586809186224600225817751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057872790816400150545167 7586809186224600225817751)
            ·
              refine ⟨11380213779336900338726627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586809186224600225817751 11380213779336900338726627)
              ·
                refine ⟨17070320669005350508089941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11380213779336900338726627 17070320669005350508089941)
                ·
                  refine ⟨200042820339906451266679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17070320669005350508089941 200042820339906451266679)
                  ·
                    rfl

theorem cell23_3506238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_3506238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506238 prefixEnd_3506238 := by exact prefixLift 3506238
  have htrace : WordTrace (prefixWord ++ tailWord_3506238) baseStart_3506238 baseEnd_3506238 := by
    simpa [prefixWord, tailWord_3506238, baseEnd_3506238] using wordTrace_append hprefix tailTrace_3506238
  have hstable : (prefixWord ++ tailWord_3506238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506238).length < 2 ^ (prefixWord ++ tailWord_3506238).sum := by decide
  have hdescent : baseEnd_3506238 < baseStart_3506238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506241 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3506241 : Nat := 118140960795 + 3506241 * 2 ^ 59
def prefixEnd_3506241 : Nat := 4983230072969 + 3 ^ 40 * 3506241 * 2
def baseEnd_3506241 : Nat := 1800386923501121549662597

theorem tailTrace_3506241 : CollatzResearch.WordTrace tailWord_3506241 prefixEnd_3506241 1800386923501121549662597 := by
  unfold tailWord_3506241
  simp only [CollatzResearch.WordTrace]
  refine ⟨127883115290495150133550577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85255410193663433422367051 127883115290495150133550577)
  ·
    refine ⟨95912336467871362600162933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127883115290495150133550577 95912336467871362600162933)
    ·
      refine ⟨8991781543862940243765275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95912336467871362600162933 8991781543862940243765275)
      ·
        refine ⟨13487672315794410365647913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991781543862940243765275 13487672315794410365647913)
        ·
          refine ⟨10115754236845807774235935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13487672315794410365647913 10115754236845807774235935)
          ·
            refine ⟨15173631355268711661353903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115754236845807774235935 15173631355268711661353903)
            ·
              refine ⟨22760447032903067492030855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15173631355268711661353903 22760447032903067492030855)
              ·
                refine ⟨34140670549354601238046283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22760447032903067492030855 34140670549354601238046283)
                ·
                  refine ⟨51211005824031901857069425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34140670549354601238046283 51211005824031901857069425)
                  ·
                    refine ⟨38408254368023926392802069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51211005824031901857069425 38408254368023926392802069)
                    ·
                      refine ⟨1800386923501121549662597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38408254368023926392802069 1800386923501121549662597)
                      ·
                        rfl

theorem cell23_3506241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3506241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506241 prefixEnd_3506241 := by exact prefixLift 3506241
  have htrace : WordTrace (prefixWord ++ tailWord_3506241) baseStart_3506241 baseEnd_3506241 := by
    simpa [prefixWord, tailWord_3506241, baseEnd_3506241] using wordTrace_append hprefix tailTrace_3506241
  have hstable : (prefixWord ++ tailWord_3506241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506241).length < 2 ^ (prefixWord ++ tailWord_3506241).sum := by decide
  have hdescent : baseEnd_3506241 < baseStart_3506241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506268 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3506268 : Nat := 118140960795 + 3506268 * 2 ^ 59
def prefixEnd_3506268 : Nat := 4983230072969 + 3 ^ 40 * 3506268 * 2
def baseEnd_3506268 : Nat := 600133595826264314674991

theorem tailTrace_3506268 : CollatzResearch.WordTrace tailWord_3506268 prefixEnd_3506268 600133595826264314674991 := by
  unfold tailWord_3506268
  simp only [CollatzResearch.WordTrace]
  refine ⟨63942050030698666872391729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85256066707598222496522305 63942050030698666872391729)
  ·
    refine ⟨47956537523024000154293797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63942050030698666872391729 47956537523024000154293797)
    ·
      refine ⟨8991850785567000028930087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47956537523024000154293797 8991850785567000028930087)
      ·
        refine ⟨13487776178350500043395131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8991850785567000028930087 13487776178350500043395131)
        ·
          refine ⟨20231664267525750065092697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487776178350500043395131 20231664267525750065092697)
          ·
            refine ⟨15173748200644312548819523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20231664267525750065092697 15173748200644312548819523)
            ·
              refine ⟨22760622300966468823229285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15173748200644312548819523 22760622300966468823229285)
              ·
                refine ⟨4267616681431212904355491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22760622300966468823229285 4267616681431212904355491)
                ·
                  refine ⟨6401425022146819356533237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267616681431212904355491 6401425022146819356533237)
                  ·
                    refine ⟨600133595826264314674991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6401425022146819356533237 600133595826264314674991)
                    ·
                      rfl

theorem cell23_3506268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3506268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506268 prefixEnd_3506268 := by exact prefixLift 3506268
  have htrace : WordTrace (prefixWord ++ tailWord_3506268) baseStart_3506268 baseEnd_3506268 := by
    simpa [prefixWord, tailWord_3506268, baseEnd_3506268] using wordTrace_append hprefix tailTrace_3506268
  have hstable : (prefixWord ++ tailWord_3506268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506268).length < 2 ^ (prefixWord ++ tailWord_3506268).sum := by decide
  have hdescent : baseEnd_3506268 < baseStart_3506268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3506281 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 6, 4]
def baseStart_3506281 : Nat := 118140960795 + 3506281 * 2 ^ 59
def prefixEnd_3506281 : Nat := 4983230072969 + 3 ^ 40 * 3506281 * 2
def baseEnd_3506281 : Nat := 600135820909100464387471

theorem tailTrace_3506281 : CollatzResearch.WordTrace tailWord_3506281 prefixEnd_3506281 600135820909100464387471 := by
  unfold tailWord_3506281
  simp only [CollatzResearch.WordTrace]
  refine ⟨127884574210350236965006697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85256382806900157976671131 127884574210350236965006697)
  ·
    refine ⟨95913430657762677723755023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127884574210350236965006697 95913430657762677723755023)
    ·
      refine ⟨143870145986644016585632535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95913430657762677723755023 143870145986644016585632535)
      ·
        refine ⟨215805218979966024878448803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143870145986644016585632535 215805218979966024878448803)
        ·
          refine ⟨323707828469949037317673205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215805218979966024878448803 323707828469949037317673205)
          ·
            refine ⟨30347608919057722248531863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 323707828469949037317673205 30347608919057722248531863)
            ·
              refine ⟨45521413378586583372797795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30347608919057722248531863 45521413378586583372797795)
              ·
                refine ⟨68282120067879875059196693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45521413378586583372797795 68282120067879875059196693)
                ·
                  refine ⟨3200724378181869143399845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68282120067879875059196693 3200724378181869143399845)
                  ·
                    refine ⟨600135820909100464387471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3200724378181869143399845 600135820909100464387471)
                    ·
                      rfl

theorem cell23_3506281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 4].length) (baseStart_3506281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3506281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3506281 prefixEnd_3506281 := by exact prefixLift 3506281
  have htrace : WordTrace (prefixWord ++ tailWord_3506281) baseStart_3506281 baseEnd_3506281 := by
    simpa [prefixWord, tailWord_3506281, baseEnd_3506281] using wordTrace_append hprefix tailTrace_3506281
  have hstable : (prefixWord ++ tailWord_3506281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3506281).length < 2 ^ (prefixWord ++ tailWord_3506281).sum := by decide
  have hdescent : baseEnd_3506281 < baseStart_3506281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3506281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
