import V185TrunkScan20Chunk000

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_5672 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 2]
def baseStart_5672 : Nat := 118140960795 + 5672 * 2 ^ 59
def prefixEnd_5672 : Nat := 4983230072969 + 3 ^ 40 * 5672 * 2
def baseEnd_5672 : Nat := 2588855353250703976819

theorem tailTrace_5672 : CollatzResearch.WordTrace tailWord_5672 prefixEnd_5672 2588855353250703976819 := by
  unfold tailWord_5672
  simp only [CollatzResearch.WordTrace]
  refine ⟨103437417729393772793635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137916556972525030391513 103437417729393772793635)
  ·
    refine ⟨155156126594090659190453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103437417729393772793635 155156126594090659190453)
    ·
      refine ⟨14545886868195999299105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155156126594090659190453 14545886868195999299105)
      ·
        refine ⟨10909415151146999474329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14545886868195999299105 10909415151146999474329)
        ·
          refine ⟨8182061363360249605747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10909415151146999474329 8182061363360249605747)
          ·
            refine ⟨12273092045040374408621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8182061363360249605747 12273092045040374408621)
            ·
              refine ⟨4602409516890140403233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12273092045040374408621 4602409516890140403233)
              ·
                refine ⟨3451807137667605302425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4602409516890140403233 3451807137667605302425)
                ·
                  refine ⟨2588855353250703976819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3451807137667605302425 2588855353250703976819)
                  ·
                    rfl

theorem cell20_5672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_5672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5672 prefixEnd_5672 := by exact prefixLift 5672
  have htrace : WordTrace (prefixWord ++ tailWord_5672) baseStart_5672 baseEnd_5672 := by
    simpa [prefixWord, tailWord_5672, baseEnd_5672] using wordTrace_append hprefix tailTrace_5672
  have hstable : (prefixWord ++ tailWord_5672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672).length < 2 ^ (prefixWord ++ tailWord_5672).sum := by decide
  have hdescent : baseEnd_5672 < baseStart_5672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687 : List Nat := [1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_5687 : Nat := 118140960795 + 5687 * 2 ^ 59
def prefixEnd_5687 : Nat := 4983230072969 + 3 ^ 40 * 5687 * 2
def baseEnd_5687 : Nat := 865233920659106158919

theorem tailTrace_5687 : CollatzResearch.WordTrace tailWord_5687 prefixEnd_5687 865233920659106158919 := by
  unfold tailWord_5687
  simp only [CollatzResearch.WordTrace]
  refine ⟨207421930404445107383315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138281286936296738255543 207421930404445107383315)
  ·
    refine ⟨311132895606667661074973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207421930404445107383315 311132895606667661074973)
    ·
      refine ⟨116674835852500372903115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311132895606667661074973 116674835852500372903115)
      ·
        refine ⟨175012253778750559354673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116674835852500372903115 175012253778750559354673)
        ·
          refine ⟨131259190334062919516005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175012253778750559354673 131259190334062919516005)
          ·
            refine ⟨24611098187636797409251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131259190334062919516005 24611098187636797409251)
            ·
              refine ⟨36916647281455196113877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24611098187636797409251 36916647281455196113877)
              ·
                refine ⟨865233920659106158919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36916647281455196113877 865233920659106158919)
                ·
                  rfl

theorem cell20_5687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_5687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5687 prefixEnd_5687 := by exact prefixLift 5687
  have htrace : WordTrace (prefixWord ++ tailWord_5687) baseStart_5687 baseEnd_5687 := by
    simpa [prefixWord, tailWord_5687, baseEnd_5687] using wordTrace_append hprefix tailTrace_5687
  have hstable : (prefixWord ++ tailWord_5687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687).length < 2 ^ (prefixWord ++ tailWord_5687).sum := by decide
  have hdescent : baseEnd_5687 < baseStart_5687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731 : List Nat := [1, 1, 1, 5, 1, 5, 2, 2, 2]
def baseStart_5731 : Nat := 118140960795 + 5731 * 2 ^ 59
def prefixEnd_5731 : Nat := 4983230072969 + 3 ^ 40 * 5731 * 2
def baseEnd_5731 : Nat := 2615784560908721009911

theorem tailTrace_5731 : CollatzResearch.WordTrace tailWord_5731 prefixEnd_5731 2615784560908721009911 := by
  unfold tailWord_5731
  simp only [CollatzResearch.WordTrace]
  refine ⟨209026742245040621985047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139351161496693747990031 209026742245040621985047)
  ·
    refine ⟨313540113367560932977571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209026742245040621985047 313540113367560932977571)
    ·
      refine ⟨470310170051341399466357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313540113367560932977571 470310170051341399466357)
      ·
        refine ⟨44091578442313256199971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 470310170051341399466357 44091578442313256199971)
        ·
          refine ⟨66137367663469884299957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44091578442313256199971 66137367663469884299957)
          ·
            refine ⟨6200378218450301653121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66137367663469884299957 6200378218450301653121)
            ·
              refine ⟨4650283663837726239841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200378218450301653121 4650283663837726239841)
              ·
                refine ⟨3487712747878294679881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650283663837726239841 3487712747878294679881)
                ·
                  refine ⟨2615784560908721009911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3487712747878294679881 2615784560908721009911)
                  ·
                    rfl

theorem cell20_5731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 2, 2].length) (baseStart_5731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5731 prefixEnd_5731 := by exact prefixLift 5731
  have htrace : WordTrace (prefixWord ++ tailWord_5731) baseStart_5731 baseEnd_5731 := by
    simpa [prefixWord, tailWord_5731, baseEnd_5731] using wordTrace_append hprefix tailTrace_5731
  have hstable : (prefixWord ++ tailWord_5731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731).length < 2 ^ (prefixWord ++ tailWord_5731).sum := by decide
  have hdescent : baseEnd_5731 < baseStart_5731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5790 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5790 : Nat := 118140960795 + 5790 * 2 ^ 59
def prefixEnd_5790 : Nat := 4983230072969 + 3 ^ 40 * 5790 * 2
def baseEnd_5790 : Nat := 2642713768566738043003

theorem tailTrace_5790 : CollatzResearch.WordTrace tailWord_5790 prefixEnd_5790 2642713768566738043003 := by
  unfold tailWord_5790
  simp only [CollatzResearch.WordTrace]
  refine ⟨26397331128911712297853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140785766020862465588549 26397331128911712297853)
  ·
    refine ⟨9898999173341892111695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26397331128911712297853 9898999173341892111695)
    ·
      refine ⟨14848498760012838167543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9898999173341892111695 14848498760012838167543)
      ·
        refine ⟨22272748140019257251315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14848498760012838167543 22272748140019257251315)
        ·
          refine ⟨33409122210028885876973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22272748140019257251315 33409122210028885876973)
          ·
            refine ⟨12528420828760832203865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33409122210028885876973 12528420828760832203865)
            ·
              refine ⟨9396315621570624152899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12528420828760832203865 9396315621570624152899)
              ·
                refine ⟨14094473432355936229349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9396315621570624152899 14094473432355936229349)
                ·
                  refine ⟨2642713768566738043003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14094473432355936229349 2642713768566738043003)
                  ·
                    rfl

theorem cell20_5790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5790 prefixEnd_5790 := by exact prefixLift 5790
  have htrace : WordTrace (prefixWord ++ tailWord_5790) baseStart_5790 baseEnd_5790 := by
    simpa [prefixWord, tailWord_5790, baseEnd_5790] using wordTrace_append hprefix tailTrace_5790
  have hstable : (prefixWord ++ tailWord_5790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5790).length < 2 ^ (prefixWord ++ tailWord_5790).sum := by decide
  have hdescent : baseEnd_5790 < baseStart_5790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5814 : List Nat := [5, 1, 3, 1, 1, 1, 4, 4]
def baseStart_5814 : Nat := 118140960795 + 5814 * 2 ^ 59
def prefixEnd_5814 : Nat := 4983230072969 + 3 ^ 40 * 5814 * 2
def baseEnd_5814 : Nat := 884556007509773747635

theorem tailTrace_5814 : CollatzResearch.WordTrace tailWord_5814 prefixEnd_5814 884556007509773747635 := by
  unfold tailWord_5814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253375059021612328531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141369333962897198170997 13253375059021612328531)
  ·
    refine ⟨19880062588532418492797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13253375059021612328531 19880062588532418492797)
    ·
      refine ⟨7455023470699656934799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19880062588532418492797 7455023470699656934799)
      ·
        refine ⟨11182535206049485402199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7455023470699656934799 11182535206049485402199)
        ·
          refine ⟨16773802809074228103299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11182535206049485402199 16773802809074228103299)
          ·
            refine ⟨25160704213611342154949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16773802809074228103299 25160704213611342154949)
            ·
              refine ⟨4717632040052126654053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25160704213611342154949 4717632040052126654053)
              ·
                refine ⟨884556007509773747635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4717632040052126654053 884556007509773747635)
                ·
                  rfl

theorem cell20_5814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_5814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5814 prefixEnd_5814 := by exact prefixLift 5814
  have htrace : WordTrace (prefixWord ++ tailWord_5814) baseStart_5814 baseEnd_5814 := by
    simpa [prefixWord, tailWord_5814, baseEnd_5814] using wordTrace_append hprefix tailTrace_5814
  have hstable : (prefixWord ++ tailWord_5814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5814).length < 2 ^ (prefixWord ++ tailWord_5814).sum := by decide
  have hdescent : baseEnd_5814 < baseStart_5814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5818 : List Nat := [3, 1, 1, 1, 2, 4, 4, 4]
def baseStart_5818 : Nat := 118140960795 + 5818 * 2 ^ 59
def prefixEnd_5818 : Nat := 4983230072969 + 3 ^ 40 * 5818 * 2
def baseEnd_5818 : Nat := 885164577174361703185

theorem tailTrace_5818 : CollatzResearch.WordTrace tailWord_5818 prefixEnd_5818 885164577174361703185 := by
  unfold tailWord_5818
  simp only [CollatzResearch.WordTrace]
  refine ⟨53049973232463620100527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141466595286569653601405 53049973232463620100527)
  ·
    refine ⟨79574959848695430150791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53049973232463620100527 79574959848695430150791)
    ·
      refine ⟨119362439773043145226187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79574959848695430150791 119362439773043145226187)
      ·
        refine ⟨179043659659564717839281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119362439773043145226187 179043659659564717839281)
        ·
          refine ⟨134282744744673538379461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179043659659564717839281 134282744744673538379461)
          ·
            refine ⟨25178014639626288446149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134282744744673538379461 25178014639626288446149)
            ·
              refine ⟨4720877744929929083653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25178014639626288446149 4720877744929929083653)
              ·
                refine ⟨885164577174361703185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4720877744929929083653 885164577174361703185)
                ·
                  rfl

theorem cell20_5818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_5818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5818 prefixEnd_5818 := by exact prefixLift 5818
  have htrace : WordTrace (prefixWord ++ tailWord_5818) baseStart_5818 baseEnd_5818 := by
    simpa [prefixWord, tailWord_5818, baseEnd_5818] using wordTrace_append hprefix tailTrace_5818
  have hstable : (prefixWord ++ tailWord_5818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5818).length < 2 ^ (prefixWord ++ tailWord_5818).sum := by decide
  have hdescent : baseEnd_5818 < baseStart_5818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5849 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 4]
def baseStart_5849 : Nat := 118140960795 + 5849 * 2 ^ 59
def prefixEnd_5849 : Nat := 4983230072969 + 3 ^ 40 * 5849 * 2
def baseEnd_5849 : Nat := 2669642976224755076095

theorem tailTrace_5849 : CollatzResearch.WordTrace tailWord_5849 prefixEnd_5849 2669642976224755076095 := by
  unfold tailWord_5849
  simp only [CollatzResearch.WordTrace]
  refine ⟨213330555817546774780601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142220370545031183187067 213330555817546774780601)
  ·
    refine ⟨159997916863160081085451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213330555817546774780601 159997916863160081085451)
    ·
      refine ⟨239996875294740121628177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159997916863160081085451 239996875294740121628177)
      ·
        refine ⟨179997656471055091221133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239996875294740121628177 179997656471055091221133)
        ·
          refine ⟨67499121176645659207925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179997656471055091221133 67499121176645659207925)
          ·
            refine ⟨6328042610310530550743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67499121176645659207925 6328042610310530550743)
            ·
              refine ⟨9492063915465795826115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6328042610310530550743 9492063915465795826115)
              ·
                refine ⟨14238095873198693739173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9492063915465795826115 14238095873198693739173)
                ·
                  refine ⟨2669642976224755076095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14238095873198693739173 2669642976224755076095)
                  ·
                    rfl

theorem cell20_5849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_5849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5849 prefixEnd_5849 := by exact prefixLift 5849
  have htrace : WordTrace (prefixWord ++ tailWord_5849) baseStart_5849 baseEnd_5849 := by
    simpa [prefixWord, tailWord_5849, baseEnd_5849] using wordTrace_append hprefix tailTrace_5849
  have hstable : (prefixWord ++ tailWord_5849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5849).length < 2 ^ (prefixWord ++ tailWord_5849).sum := by decide
  have hdescent : baseEnd_5849 < baseStart_5849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5870 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5870 : Nat := 118140960795 + 5870 * 2 ^ 59
def prefixEnd_5870 : Nat := 4983230072969 + 3 ^ 40 * 5870 * 2
def baseEnd_5870 : Nat := 2679227948442015376009

theorem tailTrace_5870 : CollatzResearch.WordTrace tailWord_5870 prefixEnd_5870 2679227948442015376009 := by
  unfold tailWord_5870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26762061092683420161883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142730992494311574196709 26762061092683420161883)
  ·
    refine ⟨40143091639025130242825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26762061092683420161883 40143091639025130242825)
    ·
      refine ⟨30107318729268847682119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40143091639025130242825 30107318729268847682119)
      ·
        refine ⟨45160978093903271523179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30107318729268847682119 45160978093903271523179)
        ·
          refine ⟨67741467140854907284769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45160978093903271523179 67741467140854907284769)
          ·
            refine ⟨50806100355641180463577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67741467140854907284769 50806100355641180463577)
            ·
              refine ⟨38104575266730885347683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50806100355641180463577 38104575266730885347683)
              ·
                refine ⟨57156862900096328021525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38104575266730885347683 57156862900096328021525)
                ·
                  refine ⟨2679227948442015376009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57156862900096328021525 2679227948442015376009)
                  ·
                    rfl

theorem cell20_5870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5870 prefixEnd_5870 := by exact prefixLift 5870
  have htrace : WordTrace (prefixWord ++ tailWord_5870) baseStart_5870 baseEnd_5870 := by
    simpa [prefixWord, tailWord_5870, baseEnd_5870] using wordTrace_append hprefix tailTrace_5870
  have hstable : (prefixWord ++ tailWord_5870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5870).length < 2 ^ (prefixWord ++ tailWord_5870).sum := by decide
  have hdescent : baseEnd_5870 < baseStart_5870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932 : List Nat := [2, 2, 1, 1, 1, 6, 3, 4]
def baseStart_5932 : Nat := 118140960795 + 5932 * 2 ^ 59
def prefixEnd_5932 : Nat := 4983230072969 + 3 ^ 40 * 5932 * 2
def baseEnd_5932 : Nat := 902508812615118436363

theorem tailTrace_5932 : CollatzResearch.WordTrace tailWord_5932 prefixEnd_5932 902508812615118436363 := by
  unfold tailWord_5932
  simp only [CollatzResearch.WordTrace]
  refine ⟨108178907258425975026025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144238543011234633368033 108178907258425975026025)
  ·
    refine ⟨81134180443819481269519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108178907258425975026025 81134180443819481269519)
    ·
      refine ⟨121701270665729221904279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81134180443819481269519 121701270665729221904279)
      ·
        refine ⟨182551905998593832856419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121701270665729221904279 182551905998593832856419)
        ·
          refine ⟨273827858997890749284629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182551905998593832856419 273827858997890749284629)
          ·
            refine ⟨12835680890526128872717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 273827858997890749284629 12835680890526128872717)
            ·
              refine ⟨4813380333947298327269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12835680890526128872717 4813380333947298327269)
              ·
                refine ⟨902508812615118436363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4813380333947298327269 902508812615118436363)
                ·
                  rfl

theorem cell20_5932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_5932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5932 prefixEnd_5932 := by exact prefixLift 5932
  have htrace : WordTrace (prefixWord ++ tailWord_5932) baseStart_5932 baseEnd_5932 := by
    simpa [prefixWord, tailWord_5932, baseEnd_5932] using wordTrace_append hprefix tailTrace_5932
  have hstable : (prefixWord ++ tailWord_5932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932).length < 2 ^ (prefixWord ++ tailWord_5932).sum := by decide
  have hdescent : baseEnd_5932 < baseStart_5932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5984 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_5984 : Nat := 118140960795 + 5984 * 2 ^ 59
def prefixEnd_5984 : Nat := 4983230072969 + 3 ^ 40 * 5984 * 2
def baseEnd_5984 : Nat := 2731260654764285575543

theorem tailTrace_5984 : CollatzResearch.WordTrace tailWord_5984 prefixEnd_5984 2731260654764285575543 := by
  unfold tailWord_5984
  simp only [CollatzResearch.WordTrace]
  refine ⟨109127205164232415472503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 145502940218976553963337 109127205164232415472503)
  ·
    refine ⟨163690807746348623208755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109127205164232415472503 163690807746348623208755)
    ·
      refine ⟨245536211619522934813133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163690807746348623208755 245536211619522934813133)
      ·
        refine ⟨92076079357321100554925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245536211619522934813133 92076079357321100554925)
        ·
          refine ⟨34528529758995412708097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92076079357321100554925 34528529758995412708097)
          ·
            refine ⟨25896397319246559531073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34528529758995412708097 25896397319246559531073)
            ·
              refine ⟨19422297989434919648305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25896397319246559531073 19422297989434919648305)
              ·
                refine ⟨14566723492076189736229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19422297989434919648305 14566723492076189736229)
                ·
                  refine ⟨2731260654764285575543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14566723492076189736229 2731260654764285575543)
                  ·
                    rfl

theorem cell20_5984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_5984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5984 prefixEnd_5984 := by exact prefixLift 5984
  have htrace : WordTrace (prefixWord ++ tailWord_5984) baseStart_5984 baseEnd_5984 := by
    simpa [prefixWord, tailWord_5984, baseEnd_5984] using wordTrace_append hprefix tailTrace_5984
  have hstable : (prefixWord ++ tailWord_5984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5984).length < 2 ^ (prefixWord ++ tailWord_5984).sum := by decide
  have hdescent : baseEnd_5984 < baseStart_5984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5987 : List Nat := [1, 1, 1, 5, 4, 2, 2, 4]
def baseStart_5987 : Nat := 118140960795 + 5987 * 2 ^ 59
def prefixEnd_5987 : Nat := 4983230072969 + 3 ^ 40 * 5987 * 2
def baseEnd_5987 : Nat := 910876645503202825177

theorem tailTrace_5987 : CollatzResearch.WordTrace tailWord_5987 prefixEnd_5987 910876645503202825177 := by
  unfold tailWord_5987
  simp only [CollatzResearch.WordTrace]
  refine ⟨218363829317596343304215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145575886211730895536143 218363829317596343304215)
  ·
    refine ⟨327545743976394514956323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218363829317596343304215 327545743976394514956323)
    ·
      refine ⟨491318615964591772434485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327545743976394514956323 491318615964591772434485)
      ·
        refine ⟨46061120246680478665733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 491318615964591772434485 46061120246680478665733)
        ·
          refine ⟨8636460046252589749825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46061120246680478665733 8636460046252589749825)
          ·
            refine ⟨6477345034689442312369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8636460046252589749825 6477345034689442312369)
            ·
              refine ⟨4858008776017081734277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6477345034689442312369 4858008776017081734277)
              ·
                refine ⟨910876645503202825177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4858008776017081734277 910876645503202825177)
                ·
                  rfl

theorem cell20_5987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_5987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5987 prefixEnd_5987 := by exact prefixLift 5987
  have htrace : WordTrace (prefixWord ++ tailWord_5987) baseStart_5987 baseEnd_5987 := by
    simpa [prefixWord, tailWord_5987, baseEnd_5987] using wordTrace_append hprefix tailTrace_5987
  have hstable : (prefixWord ++ tailWord_5987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5987).length < 2 ^ (prefixWord ++ tailWord_5987).sum := by decide
  have hdescent : baseEnd_5987 < baseStart_5987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5991 : List Nat := [1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_5991 : Nat := 118140960795 + 5991 * 2 ^ 59
def prefixEnd_5991 : Nat := 4983230072969 + 3 ^ 40 * 5991 * 2
def baseEnd_5991 : Nat := 911485215167790780727

theorem tailTrace_5991 : CollatzResearch.WordTrace tailWord_5991 prefixEnd_5991 911485215167790780727 := by
  unfold tailWord_5991
  simp only [CollatzResearch.WordTrace]
  refine ⟨218509721303105026449827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 145673147535403350966551 218509721303105026449827)
  ·
    refine ⟨327764581954657539674741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218509721303105026449827 327764581954657539674741)
    ·
      refine ⟨30727929558249144344507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 327764581954657539674741 30727929558249144344507)
      ·
        refine ⟨46091894337373716516761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30727929558249144344507 46091894337373716516761)
        ·
          refine ⟨34568920753030287387571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46091894337373716516761 34568920753030287387571)
          ·
            refine ⟨51853381129545431081357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34568920753030287387571 51853381129545431081357)
            ·
              refine ⟨19445017923579536655509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51853381129545431081357 19445017923579536655509)
              ·
                refine ⟨911485215167790780727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19445017923579536655509 911485215167790780727)
                ·
                  rfl

theorem cell20_5991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_5991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_5991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_5991 prefixEnd_5991 := by exact prefixLift 5991
  have htrace : WordTrace (prefixWord ++ tailWord_5991) baseStart_5991 baseEnd_5991 := by
    simpa [prefixWord, tailWord_5991, baseEnd_5991] using wordTrace_append hprefix tailTrace_5991
  have hstable : (prefixWord ++ tailWord_5991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5991).length < 2 ^ (prefixWord ++ tailWord_5991).sum := by decide
  have hdescent : baseEnd_5991 < baseStart_5991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6014 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6014 : Nat := 118140960795 + 6014 * 2 ^ 59
def prefixEnd_6014 : Nat := 4983230072969 + 3 ^ 40 * 6014 * 2
def baseEnd_6014 : Nat := 2744953472217514575421

theorem tailTrace_6014 : CollatzResearch.WordTrace tailWord_6014 prefixEnd_6014 2744953472217514575421 := by
  unfold tailWord_6014
  simp only [CollatzResearch.WordTrace]
  refine ⟨27418575027472494317137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146232400146519969691397 27418575027472494317137)
  ·
    refine ⟨20563931270604370737853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27418575027472494317137 20563931270604370737853)
    ·
      refine ⟨7711474226476639026695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20563931270604370737853 7711474226476639026695)
      ·
        refine ⟨11567211339714958540043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7711474226476639026695 11567211339714958540043)
        ·
          refine ⟨17350817009572437810065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11567211339714958540043 17350817009572437810065)
          ·
            refine ⟨13013112757179328357549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17350817009572437810065 13013112757179328357549)
            ·
              refine ⟨4879917283942248134081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13013112757179328357549 4879917283942248134081)
              ·
                refine ⟨3659937962956686100561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4879917283942248134081 3659937962956686100561)
                ·
                  refine ⟨2744953472217514575421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3659937962956686100561 2744953472217514575421)
                  ·
                    rfl

theorem cell20_6014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6014 prefixEnd_6014 := by exact prefixLift 6014
  have htrace : WordTrace (prefixWord ++ tailWord_6014) baseStart_6014 baseEnd_6014 := by
    simpa [prefixWord, tailWord_6014, baseEnd_6014] using wordTrace_append hprefix tailTrace_6014
  have hstable : (prefixWord ++ tailWord_6014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6014).length < 2 ^ (prefixWord ++ tailWord_6014).sum := by decide
  have hdescent : baseEnd_6014 < baseStart_6014 := by decide
  rcases family_descends (prefixWord ++ tailWord_6014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6115 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 2]
def baseStart_6115 : Nat := 118140960795 + 6115 * 2 ^ 59
def prefixEnd_6115 : Nat := 4983230072969 + 3 ^ 40 * 6115 * 2
def baseEnd_6115 : Nat := 2791052624310052208341

theorem tailTrace_6115 : CollatzResearch.WordTrace tailWord_6115 prefixEnd_6115 2791052624310052208341 := by
  unfold tailWord_6115
  simp only [CollatzResearch.WordTrace]
  refine ⟨223032372853874203963799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148688248569249469309199 223032372853874203963799)
  ·
    refine ⟨334548559280811305945699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223032372853874203963799 334548559280811305945699)
    ·
      refine ⟨501822838921216958918549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334548559280811305945699 501822838921216958918549)
      ·
        refine ⟨23522945574432044949307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 501822838921216958918549 23522945574432044949307)
        ·
          refine ⟨35284418361648067423961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23522945574432044949307 35284418361648067423961)
          ·
            refine ⟨26463313771236050567971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35284418361648067423961 26463313771236050567971)
            ·
              refine ⟨39694970656854075851957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26463313771236050567971 39694970656854075851957)
              ·
                refine ⟨3721403499080069611121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39694970656854075851957 3721403499080069611121)
                ·
                  refine ⟨2791052624310052208341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3721403499080069611121 2791052624310052208341)
                  ·
                    rfl

theorem cell20_6115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 2].length) (baseStart_6115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6115 prefixEnd_6115 := by exact prefixLift 6115
  have htrace : WordTrace (prefixWord ++ tailWord_6115) baseStart_6115 baseEnd_6115 := by
    simpa [prefixWord, tailWord_6115, baseEnd_6115] using wordTrace_append hprefix tailTrace_6115
  have hstable : (prefixWord ++ tailWord_6115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6115).length < 2 ^ (prefixWord ++ tailWord_6115).sum := by decide
  have hdescent : baseEnd_6115 < baseStart_6115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6129 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_6129 : Nat := 118140960795 + 6129 * 2 ^ 59
def prefixEnd_6129 : Nat := 4983230072969 + 3 ^ 40 * 6129 * 2
def baseEnd_6129 : Nat := 2797442605788225741617

theorem tailTrace_6129 : CollatzResearch.WordTrace tailWord_6129 prefixEnd_6129 2797442605788225741617 := by
  unfold tailWord_6129
  simp only [CollatzResearch.WordTrace]
  refine ⟨223542994803154594973441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149028663202103063315627 223542994803154594973441)
  ·
    refine ⟨167657246102365946230081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223542994803154594973441 167657246102365946230081)
    ·
      refine ⟨125742934576774459672561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167657246102365946230081 125742934576774459672561)
      ·
        refine ⟨94307200932580844754421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125742934576774459672561 94307200932580844754421)
        ·
          refine ⟨8841300087429454195727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94307200932580844754421 8841300087429454195727)
          ·
            refine ⟨13261950131144181293591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8841300087429454195727 13261950131144181293591)
            ·
              refine ⟨19892925196716271940387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13261950131144181293591 19892925196716271940387)
              ·
                refine ⟨29839387795074407910581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19892925196716271940387 29839387795074407910581)
                ·
                  refine ⟨2797442605788225741617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29839387795074407910581 2797442605788225741617)
                  ·
                    rfl

theorem cell20_6129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_6129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6129 prefixEnd_6129 := by exact prefixLift 6129
  have htrace : WordTrace (prefixWord ++ tailWord_6129) baseStart_6129 baseEnd_6129 := by
    simpa [prefixWord, tailWord_6129, baseEnd_6129] using wordTrace_append hprefix tailTrace_6129
  have hstable : (prefixWord ++ tailWord_6129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6129).length < 2 ^ (prefixWord ++ tailWord_6129).sum := by decide
  have hdescent : baseEnd_6129 < baseStart_6129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6170 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 2]
def baseStart_6170 : Nat := 118140960795 + 6170 * 2 ^ 59
def prefixEnd_6170 : Nat := 4983230072969 + 3 ^ 40 * 6170 * 2
def baseEnd_6170 : Nat := 2816156122974305374783

theorem tailTrace_6170 : CollatzResearch.WordTrace tailWord_6170 prefixEnd_6170 2816156122974305374783 := by
  unfold tailWord_6170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56259596913654649303991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150025591769745731477309 56259596913654649303991)
  ·
    refine ⟨84389395370481973955987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56259596913654649303991 84389395370481973955987)
    ·
      refine ⟨126584093055722960933981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84389395370481973955987 126584093055722960933981)
      ·
        refine ⟨47469034895896110350243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126584093055722960933981 47469034895896110350243)
        ·
          refine ⟨71203552343844165525365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47469034895896110350243 71203552343844165525365)
          ·
            refine ⟨6675333032235390518003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71203552343844165525365 6675333032235390518003)
            ·
              refine ⟨10012999548353085777005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6675333032235390518003 10012999548353085777005)
              ·
                refine ⟨3754874830632407166377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10012999548353085777005 3754874830632407166377)
                ·
                  refine ⟨2816156122974305374783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754874830632407166377 2816156122974305374783)
                  ·
                    rfl

theorem cell20_6170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 2].length) (baseStart_6170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6170 prefixEnd_6170 := by exact prefixLift 6170
  have htrace : WordTrace (prefixWord ++ tailWord_6170) baseStart_6170 baseEnd_6170 := by
    simpa [prefixWord, tailWord_6170, baseEnd_6170] using wordTrace_append hprefix tailTrace_6170
  have hstable : (prefixWord ++ tailWord_6170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6170).length < 2 ^ (prefixWord ++ tailWord_6170).sum := by decide
  have hdescent : baseEnd_6170 < baseStart_6170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181 : List Nat := [1, 3, 1, 2, 2, 5, 6]
def baseStart_6181 : Nat := 118140960795 + 6181 * 2 ^ 59
def prefixEnd_6181 : Nat := 4983230072969 + 3 ^ 40 * 6181 * 2
def baseEnd_6181 : Nat := 313464091411906223119

theorem tailTrace_6181 : CollatzResearch.WordTrace tailWord_6181 prefixEnd_6181 313464091411906223119 := by
  unfold tailWord_6181
  simp only [CollatzResearch.WordTrace]
  refine ⟨225439590614767475866397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150293060409844983910931 225439590614767475866397)
  ·
    refine ⟨84539846480537803449899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225439590614767475866397 84539846480537803449899)
    ·
      refine ⟨126809769720806705174849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84539846480537803449899 126809769720806705174849)
      ·
        refine ⟨95107327290605028881137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126809769720806705174849 95107327290605028881137)
        ·
          refine ⟨71330495467953771660853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95107327290605028881137 71330495467953771660853)
          ·
            refine ⟨6687233950120666093205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71330495467953771660853 6687233950120666093205)
            ·
              refine ⟨313464091411906223119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6687233950120666093205 313464091411906223119)
              ·
                rfl

theorem cell20_6181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 6].length) (baseStart_6181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6181 prefixEnd_6181 := by exact prefixLift 6181
  have htrace : WordTrace (prefixWord ++ tailWord_6181) baseStart_6181 baseEnd_6181 := by
    simpa [prefixWord, tailWord_6181, baseEnd_6181] using wordTrace_append hprefix tailTrace_6181
  have hstable : (prefixWord ++ tailWord_6181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181).length < 2 ^ (prefixWord ++ tailWord_6181).sum := by decide
  have hdescent : baseEnd_6181 < baseStart_6181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6198 : List Nat := [5, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6198 : Nat := 118140960795 + 6198 * 2 ^ 59
def prefixEnd_6198 : Nat := 4983230072969 + 3 ^ 40 * 6198 * 2
def baseEnd_6198 : Nat := 942978695310217480445

theorem tailTrace_6198 : CollatzResearch.WordTrace tailWord_6198 prefixEnd_6198 942978695310217480445 := by
  unfold tailWord_6198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14128726972073711202203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150706421035452919490165 14128726972073711202203)
  ·
    refine ⟨21193090458110566803305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14128726972073711202203 21193090458110566803305)
    ·
      refine ⟨15894817843582925102479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21193090458110566803305 15894817843582925102479)
      ·
        refine ⟨23842226765374387653719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15894817843582925102479 23842226765374387653719)
        ·
          refine ⟨35763340148061581480579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23842226765374387653719 35763340148061581480579)
          ·
            refine ⟨53645010222092372220869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35763340148061581480579 53645010222092372220869)
            ·
              refine ⟨10058439416642319791413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53645010222092372220869 10058439416642319791413)
              ·
                refine ⟨942978695310217480445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10058439416642319791413 942978695310217480445)
                ·
                  rfl

theorem cell20_6198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6198 prefixEnd_6198 := by exact prefixLift 6198
  have htrace : WordTrace (prefixWord ++ tailWord_6198) baseStart_6198 baseEnd_6198 := by
    simpa [prefixWord, tailWord_6198, baseEnd_6198] using wordTrace_append hprefix tailTrace_6198
  have hstable : (prefixWord ++ tailWord_6198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6198).length < 2 ^ (prefixWord ++ tailWord_6198).sum := by decide
  have hdescent : baseEnd_6198 < baseStart_6198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6201 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 3]
def baseStart_6201 : Nat := 118140960795 + 6201 * 2 ^ 59
def prefixEnd_6201 : Nat := 4983230072969 + 3 ^ 40 * 6201 * 2
def baseEnd_6201 : Nat := 2830305367675975341323

theorem tailTrace_6201 : CollatzResearch.WordTrace tailWord_6201 prefixEnd_6201 2830305367675975341323 := by
  unfold tailWord_6201
  simp only [CollatzResearch.WordTrace]
  refine ⟨226169050542310891594457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150779367028207261062971 226169050542310891594457)
  ·
    refine ⟨169626787906733168695843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226169050542310891594457 169626787906733168695843)
    ·
      refine ⟨254440181860099753043765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169626787906733168695843 254440181860099753043765)
      ·
        refine ⟨23853767049384351847853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254440181860099753043765 23853767049384351847853)
        ·
          refine ⟨8945162643519131942945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23853767049384351847853 8945162643519131942945)
          ·
            refine ⟨6708871982639348957209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8945162643519131942945 6708871982639348957209)
            ·
              refine ⟨5031653986979511717907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708871982639348957209 5031653986979511717907)
              ·
                refine ⟨7547480980469267576861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5031653986979511717907 7547480980469267576861)
                ·
                  refine ⟨2830305367675975341323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7547480980469267576861 2830305367675975341323)
                  ·
                    rfl

theorem cell20_6201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_6201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6201 prefixEnd_6201 := by exact prefixLift 6201
  have htrace : WordTrace (prefixWord ++ tailWord_6201) baseStart_6201 baseEnd_6201 := by
    simpa [prefixWord, tailWord_6201, baseEnd_6201] using wordTrace_append hprefix tailTrace_6201
  have hstable : (prefixWord ++ tailWord_6201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6201).length < 2 ^ (prefixWord ++ tailWord_6201).sum := by decide
  have hdescent : baseEnd_6201 < baseStart_6201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 3]
def baseStart_6205 : Nat := 118140960795 + 6205 * 2 ^ 59
def prefixEnd_6205 : Nat := 4983230072969 + 3 ^ 40 * 6205 * 2
def baseEnd_6205 : Nat := 2832131076669739207973

theorem tailTrace_6205 : CollatzResearch.WordTrace tailWord_6205 prefixEnd_6205 2832131076669739207973 := by
  unfold tailWord_6205
  simp only [CollatzResearch.WordTrace]
  refine ⟨226314942527819574740069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150876628351879716493379 226314942527819574740069)
  ·
    refine ⟨42434051723966170263763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226314942527819574740069 42434051723966170263763)
    ·
      refine ⟨63651077585949255395645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42434051723966170263763 63651077585949255395645)
      ·
        refine ⟨23869154094730970773367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63651077585949255395645 23869154094730970773367)
        ·
          refine ⟨35803731142096456160051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23869154094730970773367 35803731142096456160051)
          ·
            refine ⟨53705596713144684240077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35803731142096456160051 53705596713144684240077)
            ·
              refine ⟨20139598767429256590029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53705596713144684240077 20139598767429256590029)
              ·
                refine ⟨7552349537785971221261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20139598767429256590029 7552349537785971221261)
                ·
                  refine ⟨2832131076669739207973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7552349537785971221261 2832131076669739207973)
                  ·
                    rfl

theorem cell20_6205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_6205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6205 prefixEnd_6205 := by exact prefixLift 6205
  have htrace : WordTrace (prefixWord ++ tailWord_6205) baseStart_6205 baseEnd_6205 := by
    simpa [prefixWord, tailWord_6205, baseEnd_6205] using wordTrace_append hprefix tailTrace_6205
  have hstable : (prefixWord ++ tailWord_6205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205).length < 2 ^ (prefixWord ++ tailWord_6205).sum := by decide
  have hdescent : baseEnd_6205 < baseStart_6205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6238 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6238 : Nat := 118140960795 + 6238 * 2 ^ 59
def prefixEnd_6238 : Nat := 4983230072969 + 3 ^ 40 * 6238 * 2
def baseEnd_6238 : Nat := 2847193175868291107839

theorem tailTrace_6238 : CollatzResearch.WordTrace tailWord_6238 prefixEnd_6238 2847193175868291107839 := by
  unfold tailWord_6238
  simp only [CollatzResearch.WordTrace]
  refine ⟨28439818926033276336421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151679034272177473794245 28439818926033276336421)
  ·
    refine ⟨5332466048631239313079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28439818926033276336421 5332466048631239313079)
    ·
      refine ⟨7998699072946858969619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5332466048631239313079 7998699072946858969619)
      ·
        refine ⟨11998048609420288454429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7998699072946858969619 11998048609420288454429)
        ·
          refine ⟨4499268228532608170411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11998048609420288454429 4499268228532608170411)
          ·
            refine ⟨6748902342798912255617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499268228532608170411 6748902342798912255617)
            ·
              refine ⟨5061676757099184191713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6748902342798912255617 5061676757099184191713)
              ·
                refine ⟨3796257567824388143785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5061676757099184191713 3796257567824388143785)
                ·
                  refine ⟨2847193175868291107839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3796257567824388143785 2847193175868291107839)
                  ·
                    rfl

theorem cell20_6238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6238 prefixEnd_6238 := by exact prefixLift 6238
  have htrace : WordTrace (prefixWord ++ tailWord_6238) baseStart_6238 baseEnd_6238 := by
    simpa [prefixWord, tailWord_6238, baseEnd_6238] using wordTrace_append hprefix tailTrace_6238
  have hstable : (prefixWord ++ tailWord_6238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6238).length < 2 ^ (prefixWord ++ tailWord_6238).sum := by decide
  have hdescent : baseEnd_6238 < baseStart_6238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6240 : List Nat := [2, 1, 1, 3, 2, 11]
def baseStart_6240 : Nat := 118140960795 + 6240 * 2 ^ 59
def prefixEnd_6240 : Nat := 4983230072969 + 3 ^ 40 * 6240 * 2
def baseEnd_6240 : Nat := 105485408532043445969

theorem tailTrace_6240 : CollatzResearch.WordTrace tailWord_6240 prefixEnd_6240 105485408532043445969 := by
  unfold tailWord_6240
  simp only [CollatzResearch.WordTrace]
  refine ⟨113795748700510276132087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151727664934013701509449 113795748700510276132087)
  ·
    refine ⟨170693623050765414198131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113795748700510276132087 170693623050765414198131)
    ·
      refine ⟨256040434576148121297197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 170693623050765414198131 256040434576148121297197)
      ·
        refine ⟨96015162966055545486449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 256040434576148121297197 96015162966055545486449)
        ·
          refine ⟨72011372224541659114837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96015162966055545486449 72011372224541659114837)
          ·
            refine ⟨105485408532043445969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 72011372224541659114837 105485408532043445969)
            ·
              rfl

theorem cell20_6240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 11].length) (baseStart_6240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6240 prefixEnd_6240 := by exact prefixLift 6240
  have htrace : WordTrace (prefixWord ++ tailWord_6240) baseStart_6240 baseEnd_6240 := by
    simpa [prefixWord, tailWord_6240, baseEnd_6240] using wordTrace_append hprefix tailTrace_6240
  have hstable : (prefixWord ++ tailWord_6240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6240).length < 2 ^ (prefixWord ++ tailWord_6240).sum := by decide
  have hdescent : baseEnd_6240 < baseStart_6240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6242 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_6242 : Nat := 118140960795 + 6242 * 2 ^ 59
def prefixEnd_6242 : Nat := 4983230072969 + 3 ^ 40 * 6242 * 2
def baseEnd_6242 : Nat := 2849018884862054974489

theorem tailTrace_6242 : CollatzResearch.WordTrace tailWord_6242 prefixEnd_6242 2849018884862054974489 := by
  unfold tailWord_6242
  simp only [CollatzResearch.WordTrace]
  refine ⟨56916110848443723459245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151776295595849929224653 56916110848443723459245)
  ·
    refine ⟨21343541568166396297217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56916110848443723459245 21343541568166396297217)
    ·
      refine ⟨16007656176124797222913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21343541568166396297217 16007656176124797222913)
      ·
        refine ⟨12005742132093597917185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16007656176124797222913 12005742132093597917185)
        ·
          refine ⟨9004306599070198437889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12005742132093597917185 9004306599070198437889)
          ·
            refine ⟨6753229949302648828417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9004306599070198437889 6753229949302648828417)
            ·
              refine ⟨5064922461976986621313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6753229949302648828417 5064922461976986621313)
              ·
                refine ⟨3798691846482739965985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5064922461976986621313 3798691846482739965985)
                ·
                  refine ⟨2849018884862054974489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798691846482739965985 2849018884862054974489)
                  ·
                    rfl

theorem cell20_6242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_6242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6242 prefixEnd_6242 := by exact prefixLift 6242
  have htrace : WordTrace (prefixWord ++ tailWord_6242) baseStart_6242 baseEnd_6242 := by
    simpa [prefixWord, tailWord_6242, baseEnd_6242] using wordTrace_append hprefix tailTrace_6242
  have hstable : (prefixWord ++ tailWord_6242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6242).length < 2 ^ (prefixWord ++ tailWord_6242).sum := by decide
  have hdescent : baseEnd_6242 < baseStart_6242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6295 : List Nat := [1, 1, 3, 3, 4, 1, 7]
def baseStart_6295 : Nat := 118140960795 + 6295 * 2 ^ 59
def prefixEnd_6295 : Nat := 4983230072969 + 3 ^ 40 * 6295 * 2
def baseEnd_6295 : Nat := 319245503225491800845

theorem tailTrace_6295 : CollatzResearch.WordTrace tailWord_6295 prefixEnd_6295 319245503225491800845 := by
  unfold tailWord_6295
  simp only [CollatzResearch.WordTrace]
  refine ⟨229597512201764945516339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153065008134509963677559 229597512201764945516339)
  ·
    refine ⟨344396268302647418274509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229597512201764945516339 344396268302647418274509)
    ·
      refine ⟨129148600613492781852941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344396268302647418274509 129148600613492781852941)
      ·
        refine ⟨48430725230059793194853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129148600613492781852941 48430725230059793194853)
        ·
          refine ⟨9080760980636211224035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48430725230059793194853 9080760980636211224035)
          ·
            refine ⟨13621141470954316836053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9080760980636211224035 13621141470954316836053)
            ·
              refine ⟨319245503225491800845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13621141470954316836053 319245503225491800845)
              ·
                rfl

theorem cell20_6295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 7].length) (baseStart_6295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6295 prefixEnd_6295 := by exact prefixLift 6295
  have htrace : WordTrace (prefixWord ++ tailWord_6295) baseStart_6295 baseEnd_6295 := by
    simpa [prefixWord, tailWord_6295, baseEnd_6295] using wordTrace_append hprefix tailTrace_6295
  have hstable : (prefixWord ++ tailWord_6295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6295).length < 2 ^ (prefixWord ++ tailWord_6295).sum := by decide
  have hdescent : baseEnd_6295 < baseStart_6295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6305 : List Nat := [1, 2, 3, 3, 1, 2, 2, 4, 2]
def baseStart_6305 : Nat := 118140960795 + 6305 * 2 ^ 59
def prefixEnd_6305 : Nat := 4983230072969 + 3 ^ 40 * 6305 * 2
def baseEnd_6305 : Nat := 2877773801513835874231

theorem tailTrace_6305 : CollatzResearch.WordTrace tailWord_6305 prefixEnd_6305 2877773801513835874231 := by
  unfold tailWord_6305
  simp only [CollatzResearch.WordTrace]
  refine ⟨229962242165536653380369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153308161443691102253579 229962242165536653380369)
  ·
    refine ⟨172471681624152490035277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229962242165536653380369 172471681624152490035277)
    ·
      refine ⟨64676880609057183763229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172471681624152490035277 64676880609057183763229)
      ·
        refine ⟨24253830228396443911211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64676880609057183763229 24253830228396443911211)
        ·
          refine ⟨36380745342594665866817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24253830228396443911211 36380745342594665866817)
          ·
            refine ⟨27285559006945999400113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36380745342594665866817 27285559006945999400113)
            ·
              refine ⟨20464169255209499550085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27285559006945999400113 20464169255209499550085)
              ·
                refine ⟨3837031735351781165641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20464169255209499550085 3837031735351781165641)
                ·
                  refine ⟨2877773801513835874231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3837031735351781165641 2877773801513835874231)
                  ·
                    rfl

theorem cell20_6305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_6305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6305 prefixEnd_6305 := by exact prefixLift 6305
  have htrace : WordTrace (prefixWord ++ tailWord_6305) baseStart_6305 baseEnd_6305 := by
    simpa [prefixWord, tailWord_6305, baseEnd_6305] using wordTrace_append hprefix tailTrace_6305
  have hstable : (prefixWord ++ tailWord_6305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6305).length < 2 ^ (prefixWord ++ tailWord_6305).sum := by decide
  have hdescent : baseEnd_6305 < baseStart_6305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6360 : List Nat := [2, 1, 2, 2, 4, 2, 3, 2, 2]
def baseStart_6360 : Nat := 118140960795 + 6360 * 2 ^ 59
def prefixEnd_6360 : Nat := 4983230072969 + 3 ^ 40 * 6360 * 2
def baseEnd_6360 : Nat := 2902877300178089040673

theorem tailTrace_6360 : CollatzResearch.WordTrace tailWord_6360 prefixEnd_6360 2902877300178089040673 := by
  unfold tailWord_6360
  simp only [CollatzResearch.WordTrace]
  refine ⟨115984128483140523316267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154645504644187364421689 115984128483140523316267)
  ·
    refine ⟨173976192724710784974401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115984128483140523316267 173976192724710784974401)
    ·
      refine ⟨130482144543533088730801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173976192724710784974401 130482144543533088730801)
      ·
        refine ⟨97861608407649816548101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130482144543533088730801 97861608407649816548101)
        ·
          refine ⟨18349051576434340602769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97861608407649816548101 18349051576434340602769)
          ·
            refine ⟨13761788682325755452077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18349051576434340602769 13761788682325755452077)
            ·
              refine ⟨5160670755872158294529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13761788682325755452077 5160670755872158294529)
              ·
                refine ⟨3870503066904118720897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5160670755872158294529 3870503066904118720897)
                ·
                  refine ⟨2902877300178089040673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3870503066904118720897 2902877300178089040673)
                  ·
                    rfl

theorem cell20_6360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_6360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6360 prefixEnd_6360 := by exact prefixLift 6360
  have htrace : WordTrace (prefixWord ++ tailWord_6360) baseStart_6360 baseEnd_6360 := by
    simpa [prefixWord, tailWord_6360, baseEnd_6360] using wordTrace_append hprefix tailTrace_6360
  have hstable : (prefixWord ++ tailWord_6360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6360).length < 2 ^ (prefixWord ++ tailWord_6360).sum := by decide
  have hdescent : baseEnd_6360 < baseStart_6360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6370 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6370 : Nat := 118140960795 + 6370 * 2 ^ 59
def prefixEnd_6370 : Nat := 4983230072969 + 3 ^ 40 * 6370 * 2
def baseEnd_6370 : Nat := 2907441572662498707299

theorem tailTrace_6370 : CollatzResearch.WordTrace tailWord_6370 prefixEnd_6370 2907441572662498707299 := by
  unfold tailWord_6370
  simp only [CollatzResearch.WordTrace]
  refine ⟨58083246732513188624141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154888657953368502997709 58083246732513188624141)
  ·
    refine ⟨21781217524692445734053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58083246732513188624141 21781217524692445734053)
    ·
      refine ⟨4083978285879833575135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21781217524692445734053 4083978285879833575135)
      ·
        refine ⟨6125967428819750362703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083978285879833575135 6125967428819750362703)
        ·
          refine ⟨9188951143229625544055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125967428819750362703 9188951143229625544055)
          ·
            refine ⟨13783426714844438316083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9188951143229625544055 13783426714844438316083)
            ·
              refine ⟨20675140072266657474125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13783426714844438316083 20675140072266657474125)
              ·
                refine ⟨7753177527099996552797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20675140072266657474125 7753177527099996552797)
                ·
                  refine ⟨2907441572662498707299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7753177527099996552797 2907441572662498707299)
                  ·
                    rfl

theorem cell20_6370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6370 prefixEnd_6370 := by exact prefixLift 6370
  have htrace : WordTrace (prefixWord ++ tailWord_6370) baseStart_6370 baseEnd_6370 := by
    simpa [prefixWord, tailWord_6370, baseEnd_6370] using wordTrace_append hprefix tailTrace_6370
  have hstable : (prefixWord ++ tailWord_6370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6370).length < 2 ^ (prefixWord ++ tailWord_6370).sum := by decide
  have hdescent : baseEnd_6370 < baseStart_6370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6385 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_6385 : Nat := 118140960795 + 6385 * 2 ^ 59
def prefixEnd_6385 : Nat := 4983230072969 + 3 ^ 40 * 6385 * 2
def baseEnd_6385 : Nat := 2914287981389113207237

theorem tailTrace_6385 : CollatzResearch.WordTrace tailWord_6385 prefixEnd_6385 2914287981389113207237 := by
  unfold tailWord_6385
  simp only [CollatzResearch.WordTrace]
  refine ⟨232880081875710316292609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 155253387917140210861739 232880081875710316292609)
  ·
    refine ⟨174660061406782737219457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 232880081875710316292609 174660061406782737219457)
    ·
      refine ⟨130995046055087052914593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174660061406782737219457 130995046055087052914593)
      ·
        refine ⟨98246284541315289685945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130995046055087052914593 98246284541315289685945)
        ·
          refine ⟨73684713405986467264459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98246284541315289685945 73684713405986467264459)
          ·
            refine ⟨110527070108979700896689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73684713405986467264459 110527070108979700896689)
            ·
              refine ⟨82895302581734775672517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110527070108979700896689 82895302581734775672517)
              ·
                refine ⟨15542869234075270438597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82895302581734775672517 15542869234075270438597)
                ·
                  refine ⟨2914287981389113207237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15542869234075270438597 2914287981389113207237)
                  ·
                    rfl

theorem cell20_6385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_6385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6385 prefixEnd_6385 := by exact prefixLift 6385
  have htrace : WordTrace (prefixWord ++ tailWord_6385) baseStart_6385 baseEnd_6385 := by
    simpa [prefixWord, tailWord_6385, baseEnd_6385] using wordTrace_append hprefix tailTrace_6385
  have hstable : (prefixWord ++ tailWord_6385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6385).length < 2 ^ (prefixWord ++ tailWord_6385).sum := by decide
  have hdescent : baseEnd_6385 < baseStart_6385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6426 : List Nat := [3, 1, 1, 3, 4, 2, 1, 5]
def baseStart_6426 : Nat := 118140960795 + 6426 * 2 ^ 59
def prefixEnd_6426 : Nat := 4983230072969 + 3 ^ 40 * 6426 * 2
def baseEnd_6426 : Nat := 977667166191730946801

theorem tailTrace_6426 : CollatzResearch.WordTrace tailWord_6426 prefixEnd_6426 977667166191730946801 := by
  unfold tailWord_6426
  simp only [CollatzResearch.WordTrace]
  refine ⟨58593868681793579633783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156250316484782879023421 58593868681793579633783)
  ·
    refine ⟨87890803022690369450675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58593868681793579633783 87890803022690369450675)
    ·
      refine ⟨131836204534035554176013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87890803022690369450675 131836204534035554176013)
      ·
        refine ⟨49438576700263332816005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131836204534035554176013 49438576700263332816005)
        ·
          refine ⟨9269733131299374903001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49438576700263332816005 9269733131299374903001)
          ·
            refine ⟨6952299848474531177251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269733131299374903001 6952299848474531177251)
            ·
              refine ⟨10428449772711796765877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952299848474531177251 10428449772711796765877)
              ·
                refine ⟨977667166191730946801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10428449772711796765877 977667166191730946801)
                ·
                  rfl

theorem cell20_6426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_6426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6426 prefixEnd_6426 := by exact prefixLift 6426
  have htrace : WordTrace (prefixWord ++ tailWord_6426) baseStart_6426 baseEnd_6426 := by
    simpa [prefixWord, tailWord_6426, baseEnd_6426] using wordTrace_append hprefix tailTrace_6426
  have hstable : (prefixWord ++ tailWord_6426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6426).length < 2 ^ (prefixWord ++ tailWord_6426).sum := by decide
  have hdescent : baseEnd_6426 < baseStart_6426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6457 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 2]
def baseStart_6457 : Nat := 118140960795 + 6457 * 2 ^ 59
def prefixEnd_6457 : Nat := 4983230072969 + 3 ^ 40 * 6457 * 2
def baseEnd_6457 : Nat := 2947150743276862806943

theorem tailTrace_6457 : CollatzResearch.WordTrace tailWord_6457 prefixEnd_6457 2947150743276862806943 := by
  unfold tailWord_6457
  simp only [CollatzResearch.WordTrace]
  refine ⟨235506137614866612913625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157004091743244408609083 235506137614866612913625)
  ·
    refine ⟨176629603211149959685219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 235506137614866612913625 176629603211149959685219)
    ·
      refine ⟨264944404816724939527829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176629603211149959685219 264944404816724939527829)
      ·
        refine ⟨12419268975783981540367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 264944404816724939527829 12419268975783981540367)
        ·
          refine ⟨18628903463675972310551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12419268975783981540367 18628903463675972310551)
          ·
            refine ⟨27943355195513958465827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18628903463675972310551 27943355195513958465827)
            ·
              refine ⟨41915032793270937698741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27943355195513958465827 41915032793270937698741)
              ·
                refine ⟨3929534324369150409257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41915032793270937698741 3929534324369150409257)
                ·
                  refine ⟨2947150743276862806943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929534324369150409257 2947150743276862806943)
                  ·
                    rfl

theorem cell20_6457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_6457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6457 prefixEnd_6457 := by exact prefixLift 6457
  have htrace : WordTrace (prefixWord ++ tailWord_6457) baseStart_6457 baseEnd_6457 := by
    simpa [prefixWord, tailWord_6457, baseEnd_6457] using wordTrace_append hprefix tailTrace_6457
  have hstable : (prefixWord ++ tailWord_6457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6457).length < 2 ^ (prefixWord ++ tailWord_6457).sum := by decide
  have hdescent : baseEnd_6457 < baseStart_6457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494 : List Nat := [4, 4, 2, 1, 1, 2, 2, 4]
def baseStart_6494 : Nat := 118140960795 + 6494 * 2 ^ 59
def prefixEnd_6494 : Nat := 4983230072969 + 3 ^ 40 * 6494 * 2
def baseEnd_6494 : Nat := 988012850489726191153

theorem tailTrace_6494 : CollatzResearch.WordTrace tailWord_6494 prefixEnd_6494 988012850489726191153 := by
  unfold tailWord_6494
  simp only [CollatzResearch.WordTrace]
  refine ⟨29606954810102741501317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157903758987214621340357 29606954810102741501317)
  ·
    refine ⟨5551304026894264031497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29606954810102741501317 5551304026894264031497)
    ·
      refine ⟨4163478020170698023623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5551304026894264031497 4163478020170698023623)
      ·
        refine ⟨6245217030256047035435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163478020170698023623 6245217030256047035435)
        ·
          refine ⟨9367825545384070553153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245217030256047035435 9367825545384070553153)
          ·
            refine ⟨7025869159038052914865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9367825545384070553153 7025869159038052914865)
            ·
              refine ⟨5269401869278539686149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7025869159038052914865 5269401869278539686149)
              ·
                refine ⟨988012850489726191153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5269401869278539686149 988012850489726191153)
                ·
                  rfl

theorem cell20_6494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_6494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6494 prefixEnd_6494 := by exact prefixLift 6494
  have htrace : WordTrace (prefixWord ++ tailWord_6494) baseStart_6494 baseEnd_6494 := by
    simpa [prefixWord, tailWord_6494, baseEnd_6494] using wordTrace_append hprefix tailTrace_6494
  have hstable : (prefixWord ++ tailWord_6494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494).length < 2 ^ (prefixWord ++ tailWord_6494).sum := by decide
  have hdescent : baseEnd_6494 < baseStart_6494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_6499 : Nat := 118140960795 + 6499 * 2 ^ 59
def prefixEnd_6499 : Nat := 4983230072969 + 3 ^ 40 * 6499 * 2
def baseEnd_6499 : Nat := 2966320687711383406771

theorem tailTrace_6499 : CollatzResearch.WordTrace tailWord_6499 prefixEnd_6499 2966320687711383406771 := by
  unfold tailWord_6499
  simp only [CollatzResearch.WordTrace]
  refine ⟨237038003462707785942551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158025335641805190628367 237038003462707785942551)
  ·
    refine ⟨355557005194061678913827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237038003462707785942551 355557005194061678913827)
    ·
      refine ⟨533335507791092518370741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355557005194061678913827 533335507791092518370741)
      ·
        refine ⟨50000203855414923597257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 533335507791092518370741 50000203855414923597257)
        ·
          refine ⟨37500152891561192697943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50000203855414923597257 37500152891561192697943)
          ·
            refine ⟨56250229337341789046915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37500152891561192697943 56250229337341789046915)
            ·
              refine ⟨84375344006012683570373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56250229337341789046915 84375344006012683570373)
              ·
                refine ⟨15820377001127378169445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84375344006012683570373 15820377001127378169445)
                ·
                  refine ⟨2966320687711383406771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15820377001127378169445 2966320687711383406771)
                  ·
                    rfl

theorem cell20_6499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_6499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6499 prefixEnd_6499 := by exact prefixLift 6499
  have htrace : WordTrace (prefixWord ++ tailWord_6499) baseStart_6499 baseEnd_6499 := by
    simpa [prefixWord, tailWord_6499, baseEnd_6499] using wordTrace_append hprefix tailTrace_6499
  have hstable : (prefixWord ++ tailWord_6499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499).length < 2 ^ (prefixWord ++ tailWord_6499).sum := by decide
  have hdescent : baseEnd_6499 < baseStart_6499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6582 : List Nat := [5, 1, 14]
def baseStart_6582 : Nat := 118140960795 + 6582 * 2 ^ 59
def prefixEnd_6582 : Nat := 4983230072969 + 3 ^ 40 * 6582 * 2
def baseEnd_6582 : Nat := 4120993346134408285

theorem tailTrace_6582 : CollatzResearch.WordTrace tailWord_6582 prefixEnd_6582 4120993346134408285 := by
  unfold tailWord_6582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004078885125810075875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160043508108008640809333 15004078885125810075875)
  ·
    refine ⟨22506118327688715113813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15004078885125810075875 22506118327688715113813)
    ·
      refine ⟨4120993346134408285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 22506118327688715113813 4120993346134408285)
      ·
        rfl

theorem cell20_6582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 14].length) (baseStart_6582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6582 prefixEnd_6582 := by exact prefixLift 6582
  have htrace : WordTrace (prefixWord ++ tailWord_6582) baseStart_6582 baseEnd_6582 := by
    simpa [prefixWord, tailWord_6582, baseEnd_6582] using wordTrace_append hprefix tailTrace_6582
  have hstable : (prefixWord ++ tailWord_6582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6582).length < 2 ^ (prefixWord ++ tailWord_6582).sum := by decide
  have hdescent : baseEnd_6582 < baseStart_6582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6585 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 3]
def baseStart_6585 : Nat := 118140960795 + 6585 * 2 ^ 59
def prefixEnd_6585 : Nat := 4983230072969 + 3 ^ 40 * 6585 * 2
def baseEnd_6585 : Nat := 3005573431077306539753

theorem tailTrace_6585 : CollatzResearch.WordTrace tailWord_6585 prefixEnd_6585 3005573431077306539753 := by
  unfold tailWord_6585
  simp only [CollatzResearch.WordTrace]
  refine ⟨240174681151144473573209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160116454100762982382139 240174681151144473573209)
  ·
    refine ⟨180131010863358355179907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240174681151144473573209 180131010863358355179907)
    ·
      refine ⟨270196516295037532769861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180131010863358355179907 270196516295037532769861)
      ·
        refine ⟨50661846805319537394349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270196516295037532769861 50661846805319537394349)
        ·
          refine ⟨18998192551994826522881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50661846805319537394349 18998192551994826522881)
          ·
            refine ⟨14248644413996119892161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18998192551994826522881 14248644413996119892161)
            ·
              refine ⟨10686483310497089919121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14248644413996119892161 10686483310497089919121)
              ·
                refine ⟨8014862482872817439341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10686483310497089919121 8014862482872817439341)
                ·
                  refine ⟨3005573431077306539753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8014862482872817439341 3005573431077306539753)
                  ·
                    rfl

theorem cell20_6585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_6585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6585 prefixEnd_6585 := by exact prefixLift 6585
  have htrace : WordTrace (prefixWord ++ tailWord_6585) baseStart_6585 baseEnd_6585 := by
    simpa [prefixWord, tailWord_6585, baseEnd_6585] using wordTrace_append hprefix tailTrace_6585
  have hstable : (prefixWord ++ tailWord_6585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6585).length < 2 ^ (prefixWord ++ tailWord_6585).sum := by decide
  have hdescent : baseEnd_6585 < baseStart_6585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6588 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 2]
def baseStart_6588 : Nat := 118140960795 + 6588 * 2 ^ 59
def prefixEnd_6588 : Nat := 4983230072969 + 3 ^ 40 * 6588 * 2
def baseEnd_6588 : Nat := 3006942712822629439741

theorem tailTrace_6588 : CollatzResearch.WordTrace tailWord_6588 prefixEnd_6588 3006942712822629439741 := by
  unfold tailWord_6588
  simp only [CollatzResearch.WordTrace]
  refine ⟨120142050070137992966209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160189400093517323954945 120142050070137992966209)
  ·
    refine ⟨90106537552603494724657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120142050070137992966209 90106537552603494724657)
    ·
      refine ⟨67579903164452621043493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90106537552603494724657 67579903164452621043493)
      ·
        refine ⟨12671231843334866445655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67579903164452621043493 12671231843334866445655)
        ·
          refine ⟨19006847765002299668483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12671231843334866445655 19006847765002299668483)
          ·
            refine ⟨28510271647503449502725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19006847765002299668483 28510271647503449502725)
            ·
              refine ⟨5345675933906896781761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28510271647503449502725 5345675933906896781761)
              ·
                refine ⟨4009256950430172586321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5345675933906896781761 4009256950430172586321)
                ·
                  refine ⟨3006942712822629439741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4009256950430172586321 3006942712822629439741)
                  ·
                    rfl

theorem cell20_6588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_6588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6588 prefixEnd_6588 := by exact prefixLift 6588
  have htrace : WordTrace (prefixWord ++ tailWord_6588) baseStart_6588 baseEnd_6588 := by
    simpa [prefixWord, tailWord_6588, baseEnd_6588] using wordTrace_append hprefix tailTrace_6588
  have hstable : (prefixWord ++ tailWord_6588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6588).length < 2 ^ (prefixWord ++ tailWord_6588).sum := by decide
  have hdescent : baseEnd_6588 < baseStart_6588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6599 : List Nat := [1, 1, 4, 1, 1, 6, 1, 5]
def baseStart_6599 : Nat := 118140960795 + 6599 * 2 ^ 59
def prefixEnd_6599 : Nat := 4983230072969 + 3 ^ 40 * 6599 * 2
def baseEnd_6599 : Nat := 1003987804185160024343

theorem tailTrace_6599 : CollatzResearch.WordTrace tailWord_6599 prefixEnd_6599 1003987804185160024343 := by
  unfold tailWord_6599
  simp only [CollatzResearch.WordTrace]
  refine ⟨240685303100424864582851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160456868733616576388567 240685303100424864582851)
  ·
    refine ⟨361027954650637296874277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240685303100424864582851 361027954650637296874277)
    ·
      refine ⟨67692741496994493163927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361027954650637296874277 67692741496994493163927)
      ·
        refine ⟨101539112245491739745891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67692741496994493163927 101539112245491739745891)
        ·
          refine ⟨152308668368237609618837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101539112245491739745891 152308668368237609618837)
          ·
            refine ⟨7139468829761137950883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152308668368237609618837 7139468829761137950883)
            ·
              refine ⟨10709203244641706926325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7139468829761137950883 10709203244641706926325)
              ·
                refine ⟨1003987804185160024343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10709203244641706926325 1003987804185160024343)
                ·
                  rfl

theorem cell20_6599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_6599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6599 prefixEnd_6599 := by exact prefixLift 6599
  have htrace : WordTrace (prefixWord ++ tailWord_6599) baseStart_6599 baseEnd_6599 := by
    simpa [prefixWord, tailWord_6599, baseEnd_6599] using wordTrace_append hprefix tailTrace_6599
  have hstable : (prefixWord ++ tailWord_6599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6599).length < 2 ^ (prefixWord ++ tailWord_6599).sum := by decide
  have hdescent : baseEnd_6599 < baseStart_6599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_6613 : Nat := 118140960795 + 6613 * 2 ^ 59
def prefixEnd_6613 : Nat := 4983230072969 + 3 ^ 40 * 6613 * 2
def baseEnd_6613 : Nat := 3018353394033653606305

theorem tailTrace_6613 : CollatzResearch.WordTrace tailWord_6613 prefixEnd_6613 3018353394033653606305 := by
  unfold tailWord_6613
  simp only [CollatzResearch.WordTrace]
  refine ⟨241195925049705255592493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160797283366470170394995 241195925049705255592493)
  ·
    refine ⟨90448471893639470847185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241195925049705255592493 90448471893639470847185)
    ·
      refine ⟨67836353920229603135389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90448471893639470847185 67836353920229603135389)
      ·
        refine ⟨25438632720086101175771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67836353920229603135389 25438632720086101175771)
        ·
          refine ⟨38157949080129151763657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25438632720086101175771 38157949080129151763657)
          ·
            refine ⟨28618461810096863822743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38157949080129151763657 28618461810096863822743)
            ·
              refine ⟨42927692715145295734115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28618461810096863822743 42927692715145295734115)
              ·
                refine ⟨64391539072717943601173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42927692715145295734115 64391539072717943601173)
                ·
                  refine ⟨3018353394033653606305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64391539072717943601173 3018353394033653606305)
                  ·
                    rfl

theorem cell20_6613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_6613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6613 prefixEnd_6613 := by exact prefixLift 6613
  have htrace : WordTrace (prefixWord ++ tailWord_6613) baseStart_6613 baseEnd_6613 := by
    simpa [prefixWord, tailWord_6613, baseEnd_6613] using wordTrace_append hprefix tailTrace_6613
  have hstable : (prefixWord ++ tailWord_6613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613).length < 2 ^ (prefixWord ++ tailWord_6613).sum := by decide
  have hdescent : baseEnd_6613 < baseStart_6613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6637 : List Nat := [1, 5, 1, 3, 1, 2, 7]
def baseStart_6637 : Nat := 118140960795 + 6637 * 2 ^ 59
def prefixEnd_6637 : Nat := 4983230072969 + 3 ^ 40 * 6637 * 2
def baseEnd_6637 : Nat := 336589738666248534023

theorem tailTrace_6637 : CollatzResearch.WordTrace tailWord_6637 prefixEnd_6637 336589738666248534023 := by
  unfold tailWord_6637
  simp only [CollatzResearch.WordTrace]
  refine ⟨242071276962757354466165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161380851308504902977443 242071276962757354466165)
  ·
    refine ⟨22694182215258501981203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242071276962757354466165 22694182215258501981203)
    ·
      refine ⟨34041273322887752971805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22694182215258501981203 34041273322887752971805)
      ·
        refine ⟨12765477496082907364427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34041273322887752971805 12765477496082907364427)
        ·
          refine ⟨19148216244124361046641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12765477496082907364427 19148216244124361046641)
          ·
            refine ⟨14361162183093270784981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19148216244124361046641 14361162183093270784981)
            ·
              refine ⟨336589738666248534023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14361162183093270784981 336589738666248534023)
              ·
                rfl

theorem cell20_6637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_6637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6637 prefixEnd_6637 := by exact prefixLift 6637
  have htrace : WordTrace (prefixWord ++ tailWord_6637) baseStart_6637 baseEnd_6637 := by
    simpa [prefixWord, tailWord_6637, baseEnd_6637] using wordTrace_append hprefix tailTrace_6637
  have hstable : (prefixWord ++ tailWord_6637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6637).length < 2 ^ (prefixWord ++ tailWord_6637).sum := by decide
  have hdescent : baseEnd_6637 < baseStart_6637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_6672 : Nat := 118140960795 + 6672 * 2 ^ 59
def prefixEnd_6672 : Nat := 4983230072969 + 3 ^ 40 * 6672 * 2
def baseEnd_6672 : Nat := 3045282601691670639397

theorem tailTrace_6672 : CollatzResearch.WordTrace tailWord_6672 prefixEnd_6672 3045282601691670639397 := by
  unfold tailWord_6672
  simp only [CollatzResearch.WordTrace]
  refine ⟨121673915917979165995135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162231887890638887993513 121673915917979165995135)
  ·
    refine ⟨182510873876968748992703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121673915917979165995135 182510873876968748992703)
    ·
      refine ⟨273766310815453123489055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182510873876968748992703 273766310815453123489055)
      ·
        refine ⟨410649466223179685233583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273766310815453123489055 410649466223179685233583)
        ·
          refine ⟨615974199334769527850375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410649466223179685233583 615974199334769527850375)
          ·
            refine ⟨923961299002154291775563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615974199334769527850375 923961299002154291775563)
            ·
              refine ⟨1385941948503231437663345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923961299002154291775563 1385941948503231437663345)
              ·
                refine ⟨1039456461377423578247509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385941948503231437663345 1039456461377423578247509)
                ·
                  refine ⟨3045282601691670639397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1039456461377423578247509 3045282601691670639397)
                  ·
                    rfl

theorem cell20_6672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_6672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6672 prefixEnd_6672 := by exact prefixLift 6672
  have htrace : WordTrace (prefixWord ++ tailWord_6672) baseStart_6672 baseEnd_6672 := by
    simpa [prefixWord, tailWord_6672, baseEnd_6672] using wordTrace_append hprefix tailTrace_6672
  have hstable : (prefixWord ++ tailWord_6672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672).length < 2 ^ (prefixWord ++ tailWord_6672).sum := by decide
  have hdescent : baseEnd_6672 < baseStart_6672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6685 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 2]
def baseStart_6685 : Nat := 118140960795 + 6685 * 2 ^ 59
def prefixEnd_6685 : Nat := 4983230072969 + 3 ^ 40 * 6685 * 2
def baseEnd_6685 : Nat := 3051216155921403206011

theorem tailTrace_6685 : CollatzResearch.WordTrace tailWord_6685 prefixEnd_6685 3051216155921403206011 := by
  unfold tailWord_6685
  simp only [CollatzResearch.WordTrace]
  refine ⟨243821980788861552213509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162547987192574368142339 243821980788861552213509)
  ·
    refine ⟨45716621397911541040033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243821980788861552213509 45716621397911541040033)
    ·
      refine ⟨34287466048433655780025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45716621397911541040033 34287466048433655780025)
      ·
        refine ⟨25715599536325241835019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34287466048433655780025 25715599536325241835019)
        ·
          refine ⟨38573399304487862752529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25715599536325241835019 38573399304487862752529)
          ·
            refine ⟨28930049478365897064397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38573399304487862752529 28930049478365897064397)
            ·
              refine ⟨10848768554387211399149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28930049478365897064397 10848768554387211399149)
              ·
                refine ⟨4068288207895204274681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10848768554387211399149 4068288207895204274681)
                ·
                  refine ⟨3051216155921403206011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4068288207895204274681 3051216155921403206011)
                  ·
                    rfl

theorem cell20_6685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_6685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6685 prefixEnd_6685 := by exact prefixLift 6685
  have htrace : WordTrace (prefixWord ++ tailWord_6685) baseStart_6685 baseEnd_6685 := by
    simpa [prefixWord, tailWord_6685, baseEnd_6685] using wordTrace_append hprefix tailTrace_6685
  have hstable : (prefixWord ++ tailWord_6685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6685).length < 2 ^ (prefixWord ++ tailWord_6685).sum := by decide
  have hdescent : baseEnd_6685 < baseStart_6685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6692 : List Nat := [2, 3, 1, 5, 1, 2, 6]
def baseStart_6692 : Nat := 118140960795 + 6692 * 2 ^ 59
def prefixEnd_6692 : Nat := 4983230072969 + 3 ^ 40 * 6692 * 2
def baseEnd_6692 : Nat := 339379016295609996961

theorem tailTrace_6692 : CollatzResearch.WordTrace tailWord_6692 prefixEnd_6692 339379016295609996961 := by
  unfold tailWord_6692
  simp only [CollatzResearch.WordTrace]
  refine ⟨122038645881750873859165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162718194509001165145553 122038645881750873859165)
  ·
    refine ⟨45764492205656577697187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122038645881750873859165 45764492205656577697187)
    ·
      refine ⟨68646738308484866545781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45764492205656577697187 68646738308484866545781)
      ·
        refine ⟨6435631716420456238667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68646738308484866545781 6435631716420456238667)
        ·
          refine ⟨9653447574630684358001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435631716420456238667 9653447574630684358001)
          ·
            refine ⟨7240085680973013268501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9653447574630684358001 7240085680973013268501)
            ·
              refine ⟨339379016295609996961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7240085680973013268501 339379016295609996961)
              ·
                rfl

theorem cell20_6692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 6].length) (baseStart_6692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6692 prefixEnd_6692 := by exact prefixLift 6692
  have htrace : WordTrace (prefixWord ++ tailWord_6692) baseStart_6692 baseEnd_6692 := by
    simpa [prefixWord, tailWord_6692, baseEnd_6692] using wordTrace_append hprefix tailTrace_6692
  have hstable : (prefixWord ++ tailWord_6692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6692).length < 2 ^ (prefixWord ++ tailWord_6692).sum := by decide
  have hdescent : baseEnd_6692 < baseStart_6692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6702 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_6702 : Nat := 118140960795 + 6702 * 2 ^ 59
def prefixEnd_6702 : Nat := 4983230072969 + 3 ^ 40 * 6702 * 2
def baseEnd_6702 : Nat := 3058975419144899639275

theorem tailTrace_6702 : CollatzResearch.WordTrace tailWord_6702 prefixEnd_6702 3058975419144899639275 := by
  unfold tailWord_6702
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555252715909181947795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162961347818182303721573 30555252715909181947795)
  ·
    refine ⟨45832879073863772921693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30555252715909181947795 45832879073863772921693)
    ·
      refine ⟨17187329652698914845635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45832879073863772921693 17187329652698914845635)
      ·
        refine ⟨25780994479048372268453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17187329652698914845635 25780994479048372268453)
        ·
          refine ⟨4833936464821569800335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25780994479048372268453 4833936464821569800335)
          ·
            refine ⟨7250904697232354700503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833936464821569800335 7250904697232354700503)
            ·
              refine ⟨10876357045848532050755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250904697232354700503 10876357045848532050755)
              ·
                refine ⟨16314535568772798076133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10876357045848532050755 16314535568772798076133)
                ·
                  refine ⟨3058975419144899639275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16314535568772798076133 3058975419144899639275)
                  ·
                    rfl

theorem cell20_6702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_6702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6702 prefixEnd_6702 := by exact prefixLift 6702
  have htrace : WordTrace (prefixWord ++ tailWord_6702) baseStart_6702 baseEnd_6702 := by
    simpa [prefixWord, tailWord_6702, baseEnd_6702] using wordTrace_append hprefix tailTrace_6702
  have hstable : (prefixWord ++ tailWord_6702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6702).length < 2 ^ (prefixWord ++ tailWord_6702).sum := by decide
  have hdescent : baseEnd_6702 < baseStart_6702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6706 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_6706 : Nat := 118140960795 + 6706 * 2 ^ 59
def prefixEnd_6706 : Nat := 4983230072969 + 3 ^ 40 * 6706 * 2
def baseEnd_6706 : Nat := 3060801128138663505925

theorem tailTrace_6706 : CollatzResearch.WordTrace tailWord_6706 prefixEnd_6706 3060801128138663505925 := by
  unfold tailWord_6706
  simp only [CollatzResearch.WordTrace]
  refine ⟨61146978428195534681993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 163058609141854759151981 61146978428195534681993)
  ·
    refine ⟨45860233821146651011495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61146978428195534681993 45860233821146651011495)
    ·
      refine ⟨68790350731719976517243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45860233821146651011495 68790350731719976517243)
      ·
        refine ⟨103185526097579964775865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68790350731719976517243 103185526097579964775865)
        ·
          refine ⟨77389144573184973581899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103185526097579964775865 77389144573184973581899)
          ·
            refine ⟨116083716859777460372849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77389144573184973581899 116083716859777460372849)
            ·
              refine ⟨87062787644833095279637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116083716859777460372849 87062787644833095279637)
              ·
                refine ⟨4081068170851551341233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87062787644833095279637 4081068170851551341233)
                ·
                  refine ⟨3060801128138663505925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4081068170851551341233 3060801128138663505925)
                  ·
                    rfl

theorem cell20_6706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_6706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6706 prefixEnd_6706 := by exact prefixLift 6706
  have htrace : WordTrace (prefixWord ++ tailWord_6706) baseStart_6706 baseEnd_6706 := by
    simpa [prefixWord, tailWord_6706, baseEnd_6706] using wordTrace_append hprefix tailTrace_6706
  have hstable : (prefixWord ++ tailWord_6706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6706).length < 2 ^ (prefixWord ++ tailWord_6706).sum := by decide
  have hdescent : baseEnd_6706 < baseStart_6706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6716 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_6716 : Nat := 118140960795 + 6716 * 2 ^ 59
def prefixEnd_6716 : Nat := 4983230072969 + 3 ^ 40 * 6716 * 2
def baseEnd_6716 : Nat := 3065365400623073172551

theorem tailTrace_6716 : CollatzResearch.WordTrace tailWord_6716 prefixEnd_6716 3065365400623073172551 := by
  unfold tailWord_6716
  simp only [CollatzResearch.WordTrace]
  refine ⟨122476321838276923296001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 163301762451035897728001 122476321838276923296001)
  ·
    refine ⟨91857241378707692472001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122476321838276923296001 91857241378707692472001)
    ·
      refine ⟨68892931034030769354001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91857241378707692472001 68892931034030769354001)
      ·
        refine ⟨51669698275523077015501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68892931034030769354001 51669698275523077015501)
        ·
          refine ⟨19376136853321153880813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51669698275523077015501 19376136853321153880813)
          ·
            refine ⟨7266051319995432705305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19376136853321153880813 7266051319995432705305)
            ·
              refine ⟨5449538489996574528979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7266051319995432705305 5449538489996574528979)
              ·
                refine ⟨8174307734994861793469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449538489996574528979 8174307734994861793469)
                ·
                  refine ⟨3065365400623073172551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8174307734994861793469 3065365400623073172551)
                  ·
                    rfl

theorem cell20_6716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_6716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6716 prefixEnd_6716 := by exact prefixLift 6716
  have htrace : WordTrace (prefixWord ++ tailWord_6716) baseStart_6716 baseEnd_6716 := by
    simpa [prefixWord, tailWord_6716, baseEnd_6716] using wordTrace_append hprefix tailTrace_6716
  have hstable : (prefixWord ++ tailWord_6716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6716).length < 2 ^ (prefixWord ++ tailWord_6716).sum := by decide
  have hdescent : baseEnd_6716 < baseStart_6716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6734 : List Nat := [4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_6734 : Nat := 118140960795 + 6734 * 2 ^ 59
def prefixEnd_6734 : Nat := 4983230072969 + 3 ^ 40 * 6734 * 2
def baseEnd_6734 : Nat := 1024527030365003524159

theorem tailTrace_6734 : CollatzResearch.WordTrace tailWord_6734 prefixEnd_6734 1024527030365003524159 := by
  unfold tailWord_6734
  simp only [CollatzResearch.WordTrace]
  refine ⟨30701144701417865093407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 163739438407561947164837 30701144701417865093407)
  ·
    refine ⟨46051717052126797640111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30701144701417865093407 46051717052126797640111)
    ·
      refine ⟨69077575578190196460167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46051717052126797640111 69077575578190196460167)
      ·
        refine ⟨103616363367285294690251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69077575578190196460167 103616363367285294690251)
        ·
          refine ⟨155424545050927942035377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103616363367285294690251 155424545050927942035377)
          ·
            refine ⟨116568408788195956526533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155424545050927942035377 116568408788195956526533)
            ·
              refine ⟨21856576647786741848725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116568408788195956526533 21856576647786741848725)
              ·
                refine ⟨1024527030365003524159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21856576647786741848725 1024527030365003524159)
                ·
                  rfl

theorem cell20_6734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_6734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6734 prefixEnd_6734 := by exact prefixLift 6734
  have htrace : WordTrace (prefixWord ++ tailWord_6734) baseStart_6734 baseEnd_6734 := by
    simpa [prefixWord, tailWord_6734, baseEnd_6734] using wordTrace_append hprefix tailTrace_6734
  have hstable : (prefixWord ++ tailWord_6734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6734).length < 2 ^ (prefixWord ++ tailWord_6734).sum := by decide
  have hdescent : baseEnd_6734 < baseStart_6734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6741 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_6741 : Nat := 118140960795 + 6741 * 2 ^ 59
def prefixEnd_6741 : Nat := 4983230072969 + 3 ^ 40 * 6741 * 2
def baseEnd_6741 : Nat := 3076776081834097339115

theorem tailTrace_6741 : CollatzResearch.WordTrace tailWord_6741 prefixEnd_6741 3076776081834097339115 := by
  unfold tailWord_6741
  simp only [CollatzResearch.WordTrace]
  refine ⟨245864468585983116252077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 163909645723988744168051 245864468585983116252077)
  ·
    refine ⟨92199175719743668594529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 245864468585983116252077 92199175719743668594529)
    ·
      refine ⟨69149381789807751445897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92199175719743668594529 69149381789807751445897)
      ·
        refine ⟨51862036342355813584423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69149381789807751445897 51862036342355813584423)
        ·
          refine ⟨77793054513533720376635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51862036342355813584423 77793054513533720376635)
          ·
            refine ⟨116689581770300580564953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77793054513533720376635 116689581770300580564953)
            ·
              refine ⟨87517186327725435423715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116689581770300580564953 87517186327725435423715)
              ·
                refine ⟨131275779491588153135573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87517186327725435423715 131275779491588153135573)
                ·
                  refine ⟨3076776081834097339115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 131275779491588153135573 3076776081834097339115)
                  ·
                    rfl

theorem cell20_6741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_6741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6741 prefixEnd_6741 := by exact prefixLift 6741
  have htrace : WordTrace (prefixWord ++ tailWord_6741) baseStart_6741 baseEnd_6741 := by
    simpa [prefixWord, tailWord_6741, baseEnd_6741] using wordTrace_append hprefix tailTrace_6741
  have hstable : (prefixWord ++ tailWord_6741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6741).length < 2 ^ (prefixWord ++ tailWord_6741).sum := by decide
  have hdescent : baseEnd_6741 < baseStart_6741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6750 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6750 : Nat := 118140960795 + 6750 * 2 ^ 59
def prefixEnd_6750 : Nat := 4983230072969 + 3 ^ 40 * 6750 * 2
def baseEnd_6750 : Nat := 3080883927070066039079

theorem tailTrace_6750 : CollatzResearch.WordTrace tailWord_6750 prefixEnd_6750 3080883927070066039079 := by
  unfold tailWord_6750
  simp only [CollatzResearch.WordTrace]
  refine ⟨30774090694172206666213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 164128483702251768886469 30774090694172206666213)
  ·
    refine ⟨5770142005157288749915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30774090694172206666213 5770142005157288749915)
    ·
      refine ⟨8655213007735933124873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5770142005157288749915 8655213007735933124873)
      ·
        refine ⟨6491409755801949843655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8655213007735933124873 6491409755801949843655)
        ·
          refine ⟨9737114633702924765483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6491409755801949843655 9737114633702924765483)
          ·
            refine ⟨14605671950554387148225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9737114633702924765483 14605671950554387148225)
            ·
              refine ⟨10954253962915790361169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14605671950554387148225 10954253962915790361169)
              ·
                refine ⟨8215690472186842770877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10954253962915790361169 8215690472186842770877)
                ·
                  refine ⟨3080883927070066039079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8215690472186842770877 3080883927070066039079)
                  ·
                    rfl

theorem cell20_6750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6750 prefixEnd_6750 := by exact prefixLift 6750
  have htrace : WordTrace (prefixWord ++ tailWord_6750) baseStart_6750 baseEnd_6750 := by
    simpa [prefixWord, tailWord_6750, baseEnd_6750] using wordTrace_append hprefix tailTrace_6750
  have hstable : (prefixWord ++ tailWord_6750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6750).length < 2 ^ (prefixWord ++ tailWord_6750).sum := by decide
  have hdescent : baseEnd_6750 < baseStart_6750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6757 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 2]
def baseStart_6757 : Nat := 118140960795 + 6757 * 2 ^ 59
def prefixEnd_6757 : Nat := 4983230072969 + 3 ^ 40 * 6757 * 2
def baseEnd_6757 : Nat := 3084078917809152805717

theorem tailTrace_6757 : CollatzResearch.WordTrace tailWord_6757 prefixEnd_6757 3084078917809152805717 := by
  unfold tailWord_6757
  simp only [CollatzResearch.WordTrace]
  refine ⟨246448036528017848834525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 164298691018678565889683 246448036528017848834525)
  ·
    refine ⟨92418013698006693312947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 246448036528017848834525 92418013698006693312947)
    ·
      refine ⟨138627020547010039969421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92418013698006693312947 138627020547010039969421)
      ·
        refine ⟨51985132705128764988533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138627020547010039969421 51985132705128764988533)
        ·
          refine ⟨4873606191105821717675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51985132705128764988533 4873606191105821717675)
          ·
            refine ⟨7310409286658732576513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873606191105821717675 7310409286658732576513)
            ·
              refine ⟨5482806964994049432385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310409286658732576513 5482806964994049432385)
              ·
                refine ⟨4112105223745537074289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5482806964994049432385 4112105223745537074289)
                ·
                  refine ⟨3084078917809152805717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112105223745537074289 3084078917809152805717)
                  ·
                    rfl

theorem cell20_6757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_6757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6757 prefixEnd_6757 := by exact prefixLift 6757
  have htrace : WordTrace (prefixWord ++ tailWord_6757) baseStart_6757 baseEnd_6757 := by
    simpa [prefixWord, tailWord_6757, baseEnd_6757] using wordTrace_append hprefix tailTrace_6757
  have hstable : (prefixWord ++ tailWord_6757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6757).length < 2 ^ (prefixWord ++ tailWord_6757).sum := by decide
  have hdescent : baseEnd_6757 < baseStart_6757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6768 : List Nat := [2, 1, 1, 1, 8, 1, 1, 5]
def baseStart_6768 : Nat := 118140960795 + 6768 * 2 ^ 59
def prefixEnd_6768 : Nat := 4983230072969 + 3 ^ 40 * 6768 * 2
def baseEnd_6768 : Nat := 1029699872514001146335

theorem tailTrace_6768 : CollatzResearch.WordTrace tailWord_6768 prefixEnd_6768 1029699872514001146335 := by
  unfold tailWord_6768
  simp only [CollatzResearch.WordTrace]
  refine ⟨123424619744083363742479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 164566159658777818323305 123424619744083363742479)
  ·
    refine ⟨185136929616125045613719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123424619744083363742479 185136929616125045613719)
    ·
      refine ⟨277705394424187568420579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185136929616125045613719 277705394424187568420579)
      ·
        refine ⟨416558091636281352630869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277705394424187568420579 416558091636281352630869)
        ·
          refine ⟨4881540136362672101143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 416558091636281352630869 4881540136362672101143)
          ·
            refine ⟨7322310204544008151715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881540136362672101143 7322310204544008151715)
            ·
              refine ⟨10983465306816012227573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322310204544008151715 10983465306816012227573)
              ·
                refine ⟨1029699872514001146335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10983465306816012227573 1029699872514001146335)
                ·
                  rfl

theorem cell20_6768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_6768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6768 prefixEnd_6768 := by exact prefixLift 6768
  have htrace : WordTrace (prefixWord ++ tailWord_6768) baseStart_6768 baseEnd_6768 := by
    simpa [prefixWord, tailWord_6768, baseEnd_6768] using wordTrace_append hprefix tailTrace_6768
  have hstable : (prefixWord ++ tailWord_6768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6768).length < 2 ^ (prefixWord ++ tailWord_6768).sum := by decide
  have hdescent : baseEnd_6768 < baseStart_6768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6789 : List Nat := [1, 3, 1, 1, 4, 3, 3, 4]
def baseStart_6789 : Nat := 118140960795 + 6789 * 2 ^ 59
def prefixEnd_6789 : Nat := 4983230072969 + 3 ^ 40 * 6789 * 2
def baseEnd_6789 : Nat := 1032894863253087912973

theorem tailTrace_6789 : CollatzResearch.WordTrace tailWord_6789 prefixEnd_6789 1032894863253087912973 := by
  unfold tailWord_6789
  simp only [CollatzResearch.WordTrace]
  refine ⟨247615172412087313999421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165076781608058209332947 247615172412087313999421)
  ·
    refine ⟨92855689654532742749783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247615172412087313999421 92855689654532742749783)
    ·
      refine ⟨139283534481799114124675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92855689654532742749783 139283534481799114124675)
      ·
        refine ⟨208925301722698671187013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139283534481799114124675 208925301722698671187013)
        ·
          refine ⟨39173494073006000847565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208925301722698671187013 39173494073006000847565)
          ·
            refine ⟨14690060277377250317837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39173494073006000847565 14690060277377250317837)
            ·
              refine ⟨5508772604016468869189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14690060277377250317837 5508772604016468869189)
              ·
                refine ⟨1032894863253087912973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5508772604016468869189 1032894863253087912973)
                ·
                  rfl

theorem cell20_6789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_6789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6789 prefixEnd_6789 := by exact prefixLift 6789
  have htrace : WordTrace (prefixWord ++ tailWord_6789) baseStart_6789 baseEnd_6789 := by
    simpa [prefixWord, tailWord_6789, baseEnd_6789] using wordTrace_append hprefix tailTrace_6789
  have hstable : (prefixWord ++ tailWord_6789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6789).length < 2 ^ (prefixWord ++ tailWord_6789).sum := by decide
  have hdescent : baseEnd_6789 < baseStart_6789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6820 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 2]
def baseStart_6820 : Nat := 118140960795 + 6820 * 2 ^ 59
def prefixEnd_6820 : Nat := 4983230072969 + 3 ^ 40 * 6820 * 2
def baseEnd_6820 : Nat := 3112833834460933705459

theorem tailTrace_6820 : CollatzResearch.WordTrace tailWord_6820 prefixEnd_6820 3112833834460933705459 := by
  unfold tailWord_6820
  simp only [CollatzResearch.WordTrace]
  refine ⟨124372917649889804188957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165830556866519738918609 124372917649889804188957)
  ·
    refine ⟨46639844118708676570859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124372917649889804188957 46639844118708676570859)
    ·
      refine ⟨69959766178063014856289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46639844118708676570859 69959766178063014856289)
      ·
        refine ⟨52469824633547261142217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69959766178063014856289 52469824633547261142217)
        ·
          refine ⟨39352368475160445856663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52469824633547261142217 39352368475160445856663)
          ·
            refine ⟨59028552712740668784995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39352368475160445856663 59028552712740668784995)
            ·
              refine ⟨88542829069111003177493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59028552712740668784995 88542829069111003177493)
              ·
                refine ⟨4150445112614578273945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88542829069111003177493 4150445112614578273945)
                ·
                  refine ⟨3112833834460933705459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150445112614578273945 3112833834460933705459)
                  ·
                    rfl

theorem cell20_6820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_6820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6820 prefixEnd_6820 := by exact prefixLift 6820
  have htrace : WordTrace (prefixWord ++ tailWord_6820) baseStart_6820 baseEnd_6820 := by
    simpa [prefixWord, tailWord_6820, baseEnd_6820] using wordTrace_append hprefix tailTrace_6820
  have hstable : (prefixWord ++ tailWord_6820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6820).length < 2 ^ (prefixWord ++ tailWord_6820).sum := by decide
  have hdescent : baseEnd_6820 < baseStart_6820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6848 : List Nat := [2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_6848 : Nat := 118140960795 + 6848 * 2 ^ 59
def prefixEnd_6848 : Nat := 4983230072969 + 3 ^ 40 * 6848 * 2
def baseEnd_6848 : Nat := 1041871265805760257337

theorem tailTrace_6848 : CollatzResearch.WordTrace tailWord_6848 prefixEnd_6848 1041871265805760257337 := by
  unfold tailWord_6848
  simp only [CollatzResearch.WordTrace]
  refine ⟨124883539599170195198599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166511386132226926931465 124883539599170195198599)
  ·
    refine ⟨187325309398755292797899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124883539599170195198599 187325309398755292797899)
    ·
      refine ⟨280987964098132939196849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187325309398755292797899 280987964098132939196849)
      ·
        refine ⟨210740973073599704397637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280987964098132939196849 210740973073599704397637)
        ·
          refine ⟨39513932451299944574557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210740973073599704397637 39513932451299944574557)
          ·
            refine ⟨14817724669237479215459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39513932451299944574557 14817724669237479215459)
            ·
              refine ⟨22226587003856218823189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14817724669237479215459 22226587003856218823189)
              ·
                refine ⟨1041871265805760257337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22226587003856218823189 1041871265805760257337)
                ·
                  rfl

theorem cell20_6848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_6848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6848 prefixEnd_6848 := by exact prefixLift 6848
  have htrace : WordTrace (prefixWord ++ tailWord_6848) baseStart_6848 baseEnd_6848 := by
    simpa [prefixWord, tailWord_6848, baseEnd_6848] using wordTrace_append hprefix tailTrace_6848
  have hstable : (prefixWord ++ tailWord_6848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6848).length < 2 ^ (prefixWord ++ tailWord_6848).sum := by decide
  have hdescent : baseEnd_6848 < baseStart_6848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6861 : List Nat := [1, 6, 2, 1, 3, 1, 6]
def baseStart_6861 : Nat := 118140960795 + 6861 * 2 ^ 59
def prefixEnd_6861 : Nat := 4983230072969 + 3 ^ 40 * 6861 * 2
def baseEnd_6861 : Nat := 347949705738557037625

theorem tailTrace_6861 : CollatzResearch.WordTrace tailWord_6861 prefixEnd_6861 347949705738557037625 := by
  unfold tailWord_6861
  simp only [CollatzResearch.WordTrace]
  refine ⟨250241228151243610620437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166827485434162407080291 250241228151243610620437)
  ·
    refine ⟨11730057569589544247833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250241228151243610620437 11730057569589544247833)
    ·
      refine ⟨8797543177192158185875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11730057569589544247833 8797543177192158185875)
      ·
        refine ⟨13196314765788237278813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8797543177192158185875 13196314765788237278813)
        ·
          refine ⟨4948618037170588979555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13196314765788237278813 4948618037170588979555)
          ·
            refine ⟨7422927055755883469333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948618037170588979555 7422927055755883469333)
            ·
              refine ⟨347949705738557037625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7422927055755883469333 347949705738557037625)
              ·
                rfl

theorem cell20_6861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 6].length) (baseStart_6861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6861 prefixEnd_6861 := by exact prefixLift 6861
  have htrace : WordTrace (prefixWord ++ tailWord_6861) baseStart_6861 baseEnd_6861 := by
    simpa [prefixWord, tailWord_6861, baseEnd_6861] using wordTrace_append hprefix tailTrace_6861
  have hstable : (prefixWord ++ tailWord_6861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6861).length < 2 ^ (prefixWord ++ tailWord_6861).sum := by decide
  have hdescent : baseEnd_6861 < baseStart_6861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_6879 : Nat := 118140960795 + 6879 * 2 ^ 59
def prefixEnd_6879 : Nat := 4983230072969 + 3 ^ 40 * 6879 * 2
def baseEnd_6879 : Nat := 3139763042118950738551

theorem tailTrace_6879 : CollatzResearch.WordTrace tailWord_6879 prefixEnd_6879 3139763042118950738551 := by
  unfold tailWord_6879
  simp only [CollatzResearch.WordTrace]
  refine ⟨250897742086032684775691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167265161390688456517127 250897742086032684775691)
  ·
    refine ⟨376346613129049027163537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250897742086032684775691 376346613129049027163537)
    ·
      refine ⟨282259959846786770372653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376346613129049027163537 282259959846786770372653)
      ·
        refine ⟨105847484942545038889745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282259959846786770372653 105847484942545038889745)
        ·
          refine ⟨79385613706908779167309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105847484942545038889745 79385613706908779167309)
          ·
            refine ⟨29769605140090792187741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79385613706908779167309 29769605140090792187741)
            ·
              refine ⟨11163601927534047070403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29769605140090792187741 11163601927534047070403)
              ·
                refine ⟨16745402891301070605605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163601927534047070403 16745402891301070605605)
                ·
                  refine ⟨3139763042118950738551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16745402891301070605605 3139763042118950738551)
                  ·
                    rfl

theorem cell20_6879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_6879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6879 prefixEnd_6879 := by exact prefixLift 6879
  have htrace : WordTrace (prefixWord ++ tailWord_6879) baseStart_6879 baseEnd_6879 := by
    simpa [prefixWord, tailWord_6879, baseEnd_6879] using wordTrace_append hprefix tailTrace_6879
  have hstable : (prefixWord ++ tailWord_6879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879).length < 2 ^ (prefixWord ++ tailWord_6879).sum := by decide
  have hdescent : baseEnd_6879 < baseStart_6879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930 : List Nat := [3, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_6930 : Nat := 118140960795 + 6930 * 2 ^ 59
def prefixEnd_6930 : Nat := 4983230072969 + 3 ^ 40 * 6930 * 2
def baseEnd_6930 : Nat := 3163040831789440038343

theorem tailTrace_6930 : CollatzResearch.WordTrace tailWord_6930 prefixEnd_6930 3163040831789440038343 := by
  unfold tailWord_6930
  simp only [CollatzResearch.WordTrace]
  refine ⟨63189466225317098720561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168505243267512263254829 63189466225317098720561)
  ·
    refine ⟨47392099668987824040421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63189466225317098720561 47392099668987824040421)
    ·
      refine ⟨8886018687935217007579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47392099668987824040421 8886018687935217007579)
      ·
        refine ⟨13329028031902825511369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8886018687935217007579 13329028031902825511369)
        ·
          refine ⟨9996771023927119133527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13329028031902825511369 9996771023927119133527)
          ·
            refine ⟨14995156535890678700291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9996771023927119133527 14995156535890678700291)
            ·
              refine ⟨22492734803836018050437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14995156535890678700291 22492734803836018050437)
              ·
                refine ⟨4217387775719253384457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22492734803836018050437 4217387775719253384457)
                ·
                  refine ⟨3163040831789440038343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4217387775719253384457 3163040831789440038343)
                  ·
                    rfl

theorem cell20_6930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_6930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6930 prefixEnd_6930 := by exact prefixLift 6930
  have htrace : WordTrace (prefixWord ++ tailWord_6930) baseStart_6930 baseEnd_6930 := by
    simpa [prefixWord, tailWord_6930, baseEnd_6930] using wordTrace_append hprefix tailTrace_6930
  have hstable : (prefixWord ++ tailWord_6930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930).length < 2 ^ (prefixWord ++ tailWord_6930).sum := by decide
  have hdescent : baseEnd_6930 < baseStart_6930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6958 : List Nat := [4, 1, 3, 2, 1, 2, 3, 4]
def baseStart_6958 : Nat := 118140960795 + 6958 * 2 ^ 59
def prefixEnd_6958 : Nat := 4983230072969 + 3 ^ 40 * 6958 * 2
def baseEnd_6958 : Nat := 1058606931581929034965

theorem tailTrace_6958 : CollatzResearch.WordTrace tailWord_6958 prefixEnd_6958 1058606931581929034965 := by
  unfold tailWord_6958
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722388599978647112691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169186072533219451267685 31722388599978647112691)
  ·
    refine ⟨47583582899967970669037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31722388599978647112691 47583582899967970669037)
    ·
      refine ⟨17843843587487989000889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47583582899967970669037 17843843587487989000889)
      ·
        refine ⟨13382882690615991750667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17843843587487989000889 13382882690615991750667)
        ·
          refine ⟨20074324035923987626001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13382882690615991750667 20074324035923987626001)
          ·
            refine ⟨15055743026942990719501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20074324035923987626001 15055743026942990719501)
            ·
              refine ⟨5645903635103621519813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15055743026942990719501 5645903635103621519813)
              ·
                refine ⟨1058606931581929034965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5645903635103621519813 1058606931581929034965)
                ·
                  rfl

theorem cell20_6958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_6958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6958 prefixEnd_6958 := by exact prefixLift 6958
  have htrace : WordTrace (prefixWord ++ tailWord_6958) baseStart_6958 baseEnd_6958 := by
    simpa [prefixWord, tailWord_6958, baseEnd_6958] using wordTrace_append hprefix tailTrace_6958
  have hstable : (prefixWord ++ tailWord_6958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6958).length < 2 ^ (prefixWord ++ tailWord_6958).sum := by decide
  have hdescent : baseEnd_6958 < baseStart_6958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6982 : Nat := 118140960795 + 6982 * 2 ^ 59
def prefixEnd_6982 : Nat := 4983230072969 + 3 ^ 40 * 6982 * 2
def baseEnd_6982 : Nat := 3186775048708370304797

theorem tailTrace_6982 : CollatzResearch.WordTrace tailWord_6982 prefixEnd_6982 3186775048708370304797 := by
  unfold tailWord_6982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957951897277539867975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169769640475254183850133 7957951897277539867975)
  ·
    refine ⟨11936927845916309801963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7957951897277539867975 11936927845916309801963)
    ·
      refine ⟨17905391768874464702945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936927845916309801963 17905391768874464702945)
      ·
        refine ⟨13429043826655848527209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17905391768874464702945 13429043826655848527209)
        ·
          refine ⟨10071782869991886395407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13429043826655848527209 10071782869991886395407)
          ·
            refine ⟨15107674304987829593111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071782869991886395407 15107674304987829593111)
            ·
              refine ⟨22661511457481744389667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15107674304987829593111 22661511457481744389667)
              ·
                refine ⟨33992267186222616584501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22661511457481744389667 33992267186222616584501)
                ·
                  refine ⟨3186775048708370304797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33992267186222616584501 3186775048708370304797)
                  ·
                    rfl

theorem cell20_6982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6982 prefixEnd_6982 := by exact prefixLift 6982
  have htrace : WordTrace (prefixWord ++ tailWord_6982) baseStart_6982 baseEnd_6982 := by
    simpa [prefixWord, tailWord_6982, baseEnd_6982] using wordTrace_append hprefix tailTrace_6982
  have hstable : (prefixWord ++ tailWord_6982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982).length < 2 ^ (prefixWord ++ tailWord_6982).sum := by decide
  have hdescent : baseEnd_6982 < baseStart_6982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6989 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_6989 : Nat := 118140960795 + 6989 * 2 ^ 59
def prefixEnd_6989 : Nat := 4983230072969 + 3 ^ 40 * 6989 * 2
def baseEnd_6989 : Nat := 3189970039447457071435

theorem tailTrace_6989 : CollatzResearch.WordTrace tailWord_6989 prefixEnd_6989 3189970039447457071435 := by
  unfold tailWord_6989
  simp only [CollatzResearch.WordTrace]
  refine ⟨254909771687521471280021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169939847791680980853347 254909771687521471280021)
  ·
    refine ⟨11948895547852568966251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 254909771687521471280021 11948895547852568966251)
    ·
      refine ⟨17923343321778853449377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11948895547852568966251 17923343321778853449377)
      ·
        refine ⟨13442507491334140087033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17923343321778853449377 13442507491334140087033)
        ·
          refine ⟨10081880618500605065275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13442507491334140087033 10081880618500605065275)
          ·
            refine ⟨15122820927750907597913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10081880618500605065275 15122820927750907597913)
            ·
              refine ⟨11342115695813180698435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15122820927750907597913 11342115695813180698435)
              ·
                refine ⟨17013173543719771047653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11342115695813180698435 17013173543719771047653)
                ·
                  refine ⟨3189970039447457071435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17013173543719771047653 3189970039447457071435)
                  ·
                    rfl

theorem cell20_6989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_6989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_6989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_6989 prefixEnd_6989 := by exact prefixLift 6989
  have htrace : WordTrace (prefixWord ++ tailWord_6989) baseStart_6989 baseEnd_6989 := by
    simpa [prefixWord, tailWord_6989, baseEnd_6989] using wordTrace_append hprefix tailTrace_6989
  have hstable : (prefixWord ++ tailWord_6989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6989).length < 2 ^ (prefixWord ++ tailWord_6989).sum := by decide
  have hdescent : baseEnd_6989 < baseStart_6989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7045 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_7045 : Nat := 118140960795 + 7045 * 2 ^ 59
def prefixEnd_7045 : Nat := 4983230072969 + 3 ^ 40 * 7045 * 2
def baseEnd_7045 : Nat := 3215529965360151204539

theorem tailTrace_7045 : CollatzResearch.WordTrace tailWord_7045 prefixEnd_7045 3215529965360151204539 := by
  unfold tailWord_7045
  simp only [CollatzResearch.WordTrace]
  refine ⟨256952259484643035318589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 171301506323095356879059 256952259484643035318589)
  ·
    refine ⟨96357097306741138244471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256952259484643035318589 96357097306741138244471)
    ·
      refine ⟨144535645960111707366707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96357097306741138244471 144535645960111707366707)
      ·
        refine ⟨216803468940167561050061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144535645960111707366707 216803468940167561050061)
        ·
          refine ⟨81301300852562835393773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216803468940167561050061 81301300852562835393773)
          ·
            refine ⟨30487987819711063272665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81301300852562835393773 30487987819711063272665)
            ·
              refine ⟨22865990864783297454499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30487987819711063272665 22865990864783297454499)
              ·
                refine ⟨34298986297174946181749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22865990864783297454499 34298986297174946181749)
                ·
                  refine ⟨3215529965360151204539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34298986297174946181749 3215529965360151204539)
                  ·
                    rfl

theorem cell20_7045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_7045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7045 prefixEnd_7045 := by exact prefixLift 7045
  have htrace : WordTrace (prefixWord ++ tailWord_7045) baseStart_7045 baseEnd_7045 := by
    simpa [prefixWord, tailWord_7045, baseEnd_7045] using wordTrace_append hprefix tailTrace_7045
  have hstable : (prefixWord ++ tailWord_7045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7045).length < 2 ^ (prefixWord ++ tailWord_7045).sum := by decide
  have hdescent : baseEnd_7045 < baseStart_7045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7048 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_7048 : Nat := 118140960795 + 7048 * 2 ^ 59
def prefixEnd_7048 : Nat := 4983230072969 + 3 ^ 40 * 7048 * 2
def baseEnd_7048 : Nat := 3216899247105474104527

theorem tailTrace_7048 : CollatzResearch.WordTrace tailWord_7048 prefixEnd_7048 3216899247105474104527 := by
  unfold tailWord_7048
  simp only [CollatzResearch.WordTrace]
  refine ⟨128530839236887273838899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 171374452315849698451865 128530839236887273838899)
  ·
    refine ⟨192796258855330910758349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128530839236887273838899 192796258855330910758349)
    ·
      refine ⟨72298597070749091534381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192796258855330910758349 72298597070749091534381)
      ·
        refine ⟨27111973901530909325393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72298597070749091534381 27111973901530909325393)
        ·
          refine ⟨20333980426148181994045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27111973901530909325393 20333980426148181994045)
          ·
            refine ⟨7625242659805568247767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20333980426148181994045 7625242659805568247767)
            ·
              refine ⟨11437863989708352371651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625242659805568247767 11437863989708352371651)
              ·
                refine ⟨17156795984562528557477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11437863989708352371651 17156795984562528557477)
                ·
                  refine ⟨3216899247105474104527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17156795984562528557477 3216899247105474104527)
                  ·
                    rfl

theorem cell20_7048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_7048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7048 prefixEnd_7048 := by exact prefixLift 7048
  have htrace : WordTrace (prefixWord ++ tailWord_7048) baseStart_7048 baseEnd_7048 := by
    simpa [prefixWord, tailWord_7048, baseEnd_7048] using wordTrace_append hprefix tailTrace_7048
  have hstable : (prefixWord ++ tailWord_7048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7048).length < 2 ^ (prefixWord ++ tailWord_7048).sum := by decide
  have hdescent : baseEnd_7048 < baseStart_7048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7097 : List Nat := [1, 2, 1, 4, 2, 10]
def baseStart_7097 : Nat := 118140960795 + 7097 * 2 ^ 59
def prefixEnd_7097 : Nat := 4983230072969 + 3 ^ 40 * 7097 * 2
def baseEnd_7097 : Nat := 119972747491817832259

theorem tailTrace_7097 : CollatzResearch.WordTrace tailWord_7097 prefixEnd_7097 119972747491817832259 := by
  unfold tailWord_7097
  simp only [CollatzResearch.WordTrace]
  refine ⟨258848855296255916211545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172565903530837277474363 258848855296255916211545)
  ·
    refine ⟨194136641472191937158659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 258848855296255916211545 194136641472191937158659)
    ·
      refine ⟨291204962208287905737989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194136641472191937158659 291204962208287905737989)
      ·
        refine ⟨54600930414053982325873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291204962208287905737989 54600930414053982325873)
        ·
          refine ⟨40950697810540486744405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54600930414053982325873 40950697810540486744405)
          ·
            refine ⟨119972747491817832259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 40950697810540486744405 119972747491817832259)
            ·
              rfl

theorem cell20_7097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 10].length) (baseStart_7097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7097 prefixEnd_7097 := by exact prefixLift 7097
  have htrace : WordTrace (prefixWord ++ tailWord_7097) baseStart_7097 baseEnd_7097 := by
    simpa [prefixWord, tailWord_7097, baseEnd_7097] using wordTrace_append hprefix tailTrace_7097
  have hstable : (prefixWord ++ tailWord_7097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7097).length < 2 ^ (prefixWord ++ tailWord_7097).sum := by decide
  have hdescent : baseEnd_7097 < baseStart_7097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 2]
def baseStart_7107 : Nat := 118140960795 + 7107 * 2 ^ 59
def prefixEnd_7107 : Nat := 4983230072969 + 3 ^ 40 * 7107 * 2
def baseEnd_7107 : Nat := 3243828454763491137619

theorem tailTrace_7107 : CollatzResearch.WordTrace tailWord_7107 prefixEnd_7107 3243828454763491137619 := by
  unfold tailWord_7107
  simp only [CollatzResearch.WordTrace]
  refine ⟨259213585260027624075575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172809056840018416050383 259213585260027624075575)
  ·
    refine ⟨388820377890041436113363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259213585260027624075575 388820377890041436113363)
    ·
      refine ⟨583230566835062154170045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388820377890041436113363 583230566835062154170045)
      ·
        refine ⟨218711462563148307813767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583230566835062154170045 218711462563148307813767)
        ·
          refine ⟨328067193844722461720651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218711462563148307813767 328067193844722461720651)
          ·
            refine ⟨492100790767083692580977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328067193844722461720651 492100790767083692580977)
            ·
              refine ⟨369075593075312769435733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492100790767083692580977 369075593075312769435733)
              ·
                refine ⟨4325104606351321516825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 369075593075312769435733 4325104606351321516825)
                ·
                  refine ⟨3243828454763491137619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4325104606351321516825 3243828454763491137619)
                  ·
                    rfl

theorem cell20_7107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 2].length) (baseStart_7107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7107 prefixEnd_7107 := by exact prefixLift 7107
  have htrace : WordTrace (prefixWord ++ tailWord_7107) baseStart_7107 baseEnd_7107 := by
    simpa [prefixWord, tailWord_7107, baseEnd_7107] using wordTrace_append hprefix tailTrace_7107
  have hstable : (prefixWord ++ tailWord_7107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107).length < 2 ^ (prefixWord ++ tailWord_7107).sum := by decide
  have hdescent : baseEnd_7107 < baseStart_7107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7121 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_7121 : Nat := 118140960795 + 7121 * 2 ^ 59
def prefixEnd_7121 : Nat := 4983230072969 + 3 ^ 40 * 7121 * 2
def baseEnd_7121 : Nat := 3250218436241664670895

theorem tailTrace_7121 : CollatzResearch.WordTrace tailWord_7121 prefixEnd_7121 3250218436241664670895 := by
  unfold tailWord_7121
  simp only [CollatzResearch.WordTrace]
  refine ⟨259724207209308015085217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 173149471472872010056811 259724207209308015085217)
  ·
    refine ⟨194793155406981011313913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259724207209308015085217 194793155406981011313913)
    ·
      refine ⟨146094866555235758485435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194793155406981011313913 146094866555235758485435)
      ·
        refine ⟨219142299832853637728153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146094866555235758485435 219142299832853637728153)
        ·
          refine ⟨164356724874640228296115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219142299832853637728153 164356724874640228296115)
          ·
            refine ⟨246535087311960342444173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164356724874640228296115 246535087311960342444173)
            ·
              refine ⟨92450657741985128416565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246535087311960342444173 92450657741985128416565)
              ·
                refine ⟨8667249163311105789053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92450657741985128416565 8667249163311105789053)
                ·
                  refine ⟨3250218436241664670895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8667249163311105789053 3250218436241664670895)
                  ·
                    rfl

theorem cell20_7121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_7121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7121 prefixEnd_7121 := by exact prefixLift 7121
  have htrace : WordTrace (prefixWord ++ tailWord_7121) baseStart_7121 baseEnd_7121 := by
    simpa [prefixWord, tailWord_7121, baseEnd_7121] using wordTrace_append hprefix tailTrace_7121
  have hstable : (prefixWord ++ tailWord_7121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7121).length < 2 ^ (prefixWord ++ tailWord_7121).sum := by decide
  have hdescent : baseEnd_7121 < baseStart_7121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7128 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_7128 : Nat := 118140960795 + 7128 * 2 ^ 59
def prefixEnd_7128 : Nat := 4983230072969 + 3 ^ 40 * 7128 * 2
def baseEnd_7128 : Nat := 3253413426980751437533

theorem tailTrace_7128 : CollatzResearch.WordTrace tailWord_7128 prefixEnd_7128 3253413426980751437533 := by
  unfold tailWord_7128
  simp only [CollatzResearch.WordTrace]
  refine ⟨129989759091974105295019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 173319678789298807060025 129989759091974105295019)
  ·
    refine ⟨194984638637961157942529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129989759091974105295019 194984638637961157942529)
    ·
      refine ⟨146238478978470868456897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194984638637961157942529 146238478978470868456897)
      ·
        refine ⟨109678859233853151342673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146238478978470868456897 109678859233853151342673)
        ·
          refine ⟨82259144425389863507005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109678859233853151342673 82259144425389863507005)
          ·
            refine ⟨30847179159521198815127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82259144425389863507005 30847179159521198815127)
            ·
              refine ⟨46270768739281798222691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30847179159521198815127 46270768739281798222691)
              ·
                refine ⟨69406153108922697334037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46270768739281798222691 69406153108922697334037)
                ·
                  refine ⟨3253413426980751437533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69406153108922697334037 3253413426980751437533)
                  ·
                    rfl

theorem cell20_7128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_7128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7128 prefixEnd_7128 := by exact prefixLift 7128
  have htrace : WordTrace (prefixWord ++ tailWord_7128) baseStart_7128 baseEnd_7128 := by
    simpa [prefixWord, tailWord_7128, baseEnd_7128] using wordTrace_append hprefix tailTrace_7128
  have hstable : (prefixWord ++ tailWord_7128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7128).length < 2 ^ (prefixWord ++ tailWord_7128).sum := by decide
  have hdescent : baseEnd_7128 < baseStart_7128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7173 : List Nat := [1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_7173 : Nat := 118140960795 + 7173 * 2 ^ 59
def prefixEnd_7173 : Nat := 4983230072969 + 3 ^ 40 * 7173 * 2
def baseEnd_7173 : Nat := 1091317551053531645783

theorem tailTrace_7173 : CollatzResearch.WordTrace tailWord_7173 prefixEnd_7173 1091317551053531645783 := by
  unfold tailWord_7173
  simp only [CollatzResearch.WordTrace]
  refine ⟨261620803020920895978173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174413868680613930652115 261620803020920895978173)
  ·
    refine ⟨98107801132845335991815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261620803020920895978173 98107801132845335991815)
    ·
      refine ⟨147161701699268003987723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98107801132845335991815 147161701699268003987723)
      ·
        refine ⟨220742552548902005981585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147161701699268003987723 220742552548902005981585)
        ·
          refine ⟨165556914411676504486189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220742552548902005981585 165556914411676504486189)
          ·
            refine ⟨62083842904378689182321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165556914411676504486189 62083842904378689182321)
            ·
              refine ⟨46562882178284016886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62083842904378689182321 46562882178284016886741)
              ·
                refine ⟨1091317551053531645783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 46562882178284016886741 1091317551053531645783)
                ·
                  rfl

theorem cell20_7173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_7173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7173 prefixEnd_7173 := by exact prefixLift 7173
  have htrace : WordTrace (prefixWord ++ tailWord_7173) baseStart_7173 baseEnd_7173 := by
    simpa [prefixWord, tailWord_7173, baseEnd_7173] using wordTrace_append hprefix tailTrace_7173
  have hstable : (prefixWord ++ tailWord_7173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7173).length < 2 ^ (prefixWord ++ tailWord_7173).sum := by decide
  have hdescent : baseEnd_7173 < baseStart_7173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7196 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 2]
def baseStart_7196 : Nat := 118140960795 + 7196 * 2 ^ 59
def prefixEnd_7196 : Nat := 4983230072969 + 3 ^ 40 * 7196 * 2
def baseEnd_7196 : Nat := 3284450479874737170589

theorem tailTrace_7196 : CollatzResearch.WordTrace tailWord_7196 prefixEnd_7196 3284450479874737170589 := by
  unfold tailWord_7196
  simp only [CollatzResearch.WordTrace]
  refine ⟨131229840968797912032721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174973121291730549376961 131229840968797912032721)
  ·
    refine ⟨98422380726598434024541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131229840968797912032721 98422380726598434024541)
    ·
      refine ⟨36908392772474412759203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98422380726598434024541 36908392772474412759203)
      ·
        refine ⟨55362589158711619138805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36908392772474412759203 55362589158711619138805)
        ·
          refine ⟨5190242733629214294263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55362589158711619138805 5190242733629214294263)
          ·
            refine ⟨7785364100443821441395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5190242733629214294263 7785364100443821441395)
            ·
              refine ⟨11678046150665732162093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7785364100443821441395 11678046150665732162093)
              ·
                refine ⟨4379267306499649560785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11678046150665732162093 4379267306499649560785)
                ·
                  refine ⟨3284450479874737170589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4379267306499649560785 3284450479874737170589)
                  ·
                    rfl

theorem cell20_7196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_7196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7196 prefixEnd_7196 := by exact prefixLift 7196
  have htrace : WordTrace (prefixWord ++ tailWord_7196) baseStart_7196 baseEnd_7196 := by
    simpa [prefixWord, tailWord_7196, baseEnd_7196] using wordTrace_append hprefix tailTrace_7196
  have hstable : (prefixWord ++ tailWord_7196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7196).length < 2 ^ (prefixWord ++ tailWord_7196).sum := by decide
  have hdescent : baseEnd_7196 < baseStart_7196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7207 : List Nat := [1, 1, 7, 1, 1, 3, 6]
def baseStart_7207 : Nat := 118140960795 + 7207 * 2 ^ 59
def prefixEnd_7207 : Nat := 4983230072969 + 3 ^ 40 * 7207 * 2
def baseEnd_7207 : Nat := 365496797734176422653

theorem tailTrace_7207 : CollatzResearch.WordTrace tailWord_7207 prefixEnd_7207 365496797734176422653 := by
  unfold tailWord_7207
  simp only [CollatzResearch.WordTrace]
  refine ⟨262860884897744702715875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175240589931829801810583 262860884897744702715875)
  ·
    refine ⟨394291327346617054073813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262860884897744702715875 394291327346617054073813)
    ·
      refine ⟨9241202984686337204855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 394291327346617054073813 9241202984686337204855)
      ·
        refine ⟨13861804477029505807283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9241202984686337204855 13861804477029505807283)
        ·
          refine ⟨20792706715544258710925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13861804477029505807283 20792706715544258710925)
          ·
            refine ⟨7797265018329097016597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20792706715544258710925 7797265018329097016597)
            ·
              refine ⟨365496797734176422653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7797265018329097016597 365496797734176422653)
              ·
                rfl

theorem cell20_7207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 6].length) (baseStart_7207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7207 prefixEnd_7207 := by exact prefixLift 7207
  have htrace : WordTrace (prefixWord ++ tailWord_7207) baseStart_7207 baseEnd_7207 := by
    simpa [prefixWord, tailWord_7207, baseEnd_7207] using wordTrace_append hprefix tailTrace_7207
  have hstable : (prefixWord ++ tailWord_7207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7207).length < 2 ^ (prefixWord ++ tailWord_7207).sum := by decide
  have hdescent : baseEnd_7207 < baseStart_7207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7214 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_7214 : Nat := 118140960795 + 7214 * 2 ^ 59
def prefixEnd_7214 : Nat := 4983230072969 + 3 ^ 40 * 7214 * 2
def baseEnd_7214 : Nat := 3292666170346674570515

theorem tailTrace_7214 : CollatzResearch.WordTrace tailWord_7214 prefixEnd_7214 3292666170346674570515 := by
  unfold tailWord_7214
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889524484048112277587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175410797248256598813797 32889524484048112277587)
  ·
    refine ⟨49334286726072168416381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32889524484048112277587 49334286726072168416381)
    ·
      refine ⟨18500357522277063156143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49334286726072168416381 18500357522277063156143)
      ·
        refine ⟨27750536283415594734215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500357522277063156143 27750536283415594734215)
        ·
          refine ⟨41625804425123392101323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27750536283415594734215 41625804425123392101323)
          ·
            refine ⟨62438706637685088151985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41625804425123392101323 62438706637685088151985)
            ·
              refine ⟨46829029978263816113989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62438706637685088151985 46829029978263816113989)
              ·
                refine ⟨8780443120924465521373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46829029978263816113989 8780443120924465521373)
                ·
                  refine ⟨3292666170346674570515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8780443120924465521373 3292666170346674570515)
                  ·
                    rfl

theorem cell20_7214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_7214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7214 prefixEnd_7214 := by exact prefixLift 7214
  have htrace : WordTrace (prefixWord ++ tailWord_7214) baseStart_7214 baseEnd_7214 := by
    simpa [prefixWord, tailWord_7214, baseEnd_7214] using wordTrace_append hprefix tailTrace_7214
  have hstable : (prefixWord ++ tailWord_7214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7214).length < 2 ^ (prefixWord ++ tailWord_7214).sum := by decide
  have hdescent : baseEnd_7214 < baseStart_7214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7228 : List Nat := [2, 2, 2, 2, 2, 3, 2, 5]
def baseStart_7228 : Nat := 118140960795 + 7228 * 2 ^ 59
def prefixEnd_7228 : Nat := 4983230072969 + 3 ^ 40 * 7228 * 2
def baseEnd_7228 : Nat := 1099685383941616034597

theorem tailTrace_7228 : CollatzResearch.WordTrace tailWord_7228 prefixEnd_7228 1099685383941616034597 := by
  unfold tailWord_7228
  simp only [CollatzResearch.WordTrace]
  refine ⟨131813408910832644615169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175751211881110192820225 131813408910832644615169)
  ·
    refine ⟨98860056683124483461377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131813408910832644615169 98860056683124483461377)
    ·
      refine ⟨74145042512343362596033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98860056683124483461377 74145042512343362596033)
      ·
        refine ⟨55608781884257521947025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74145042512343362596033 55608781884257521947025)
        ·
          refine ⟨41706586413193141460269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55608781884257521947025 41706586413193141460269)
          ·
            refine ⟨15639969904947428047601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41706586413193141460269 15639969904947428047601)
            ·
              refine ⟨11729977428710571035701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15639969904947428047601 11729977428710571035701)
              ·
                refine ⟨1099685383941616034597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11729977428710571035701 1099685383941616034597)
                ·
                  rfl

theorem cell20_7228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_7228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7228 prefixEnd_7228 := by exact prefixLift 7228
  have htrace : WordTrace (prefixWord ++ tailWord_7228) baseStart_7228 baseEnd_7228 := by
    simpa [prefixWord, tailWord_7228, baseEnd_7228] using wordTrace_append hprefix tailTrace_7228
  have hstable : (prefixWord ++ tailWord_7228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7228).length < 2 ^ (prefixWord ++ tailWord_7228).sum := by decide
  have hdescent : baseEnd_7228 < baseStart_7228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_7235 : Nat := 118140960795 + 7235 * 2 ^ 59
def prefixEnd_7235 : Nat := 4983230072969 + 3 ^ 40 * 7235 * 2
def baseEnd_7235 : Nat := 3302251142563934870429

theorem tailTrace_7235 : CollatzResearch.WordTrace tailWord_7235 prefixEnd_7235 3302251142563934870429 := by
  unfold tailWord_7235
  simp only [CollatzResearch.WordTrace]
  refine ⟨263882128796305484735159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175921419197536989823439 263882128796305484735159)
  ·
    refine ⟨395823193194458227102739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263882128796305484735159 395823193194458227102739)
    ·
      refine ⟨593734789791687340654109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395823193194458227102739 593734789791687340654109)
      ·
        refine ⟨222650546171882752745291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593734789791687340654109 222650546171882752745291)
        ·
          refine ⟨333975819257824129117937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222650546171882752745291 333975819257824129117937)
          ·
            refine ⟨250481864443368096838453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333975819257824129117937 250481864443368096838453)
            ·
              refine ⟨23482674791565759078605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250481864443368096838453 23482674791565759078605)
              ·
                refine ⟨8806003046837159654477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23482674791565759078605 8806003046837159654477)
                ·
                  refine ⟨3302251142563934870429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8806003046837159654477 3302251142563934870429)
                  ·
                    rfl

theorem cell20_7235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_7235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7235 prefixEnd_7235 := by exact prefixLift 7235
  have htrace : WordTrace (prefixWord ++ tailWord_7235) baseStart_7235 baseEnd_7235 := by
    simpa [prefixWord, tailWord_7235, baseEnd_7235] using wordTrace_append hprefix tailTrace_7235
  have hstable : (prefixWord ++ tailWord_7235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235).length < 2 ^ (prefixWord ++ tailWord_7235).sum := by decide
  have hdescent : baseEnd_7235 < baseStart_7235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7242 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_7242 : Nat := 118140960795 + 7242 * 2 ^ 59
def prefixEnd_7242 : Nat := 4983230072969 + 3 ^ 40 * 7242 * 2
def baseEnd_7242 : Nat := 3305446133303021637067

theorem tailTrace_7242 : CollatzResearch.WordTrace tailWord_7242 prefixEnd_7242 3305446133303021637067 := by
  unfold tailWord_7242
  simp only [CollatzResearch.WordTrace]
  refine ⟨66034359942736420059995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176091626513963786826653 66034359942736420059995)
  ·
    refine ⟨99051539914104630089993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66034359942736420059995 99051539914104630089993)
    ·
      refine ⟨74288654935578472567495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99051539914104630089993 74288654935578472567495)
      ·
        refine ⟨111432982403367708851243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74288654935578472567495 111432982403367708851243)
        ·
          refine ⟨167149473605051563276865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111432982403367708851243 167149473605051563276865)
          ·
            refine ⟨125362105203788672457649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167149473605051563276865 125362105203788672457649)
            ·
              refine ⟨94021578902841504343237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125362105203788672457649 94021578902841504343237)
              ·
                refine ⟨17629046044282782064357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94021578902841504343237 17629046044282782064357)
                ·
                  refine ⟨3305446133303021637067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17629046044282782064357 3305446133303021637067)
                  ·
                    rfl

theorem cell20_7242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_7242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7242 prefixEnd_7242 := by exact prefixLift 7242
  have htrace : WordTrace (prefixWord ++ tailWord_7242) baseStart_7242 baseEnd_7242 := by
    simpa [prefixWord, tailWord_7242, baseEnd_7242] using wordTrace_append hprefix tailTrace_7242
  have hstable : (prefixWord ++ tailWord_7242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7242).length < 2 ^ (prefixWord ++ tailWord_7242).sum := by decide
  have hdescent : baseEnd_7242 < baseStart_7242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7249 : List Nat := [1, 2, 2, 1, 3, 1, 4, 6]
def baseStart_7249 : Nat := 118140960795 + 7249 * 2 ^ 59
def prefixEnd_7249 : Nat := 4983230072969 + 3 ^ 40 * 7249 * 2
def baseEnd_7249 : Nat := 1102880374680702801235

theorem tailTrace_7249 : CollatzResearch.WordTrace tailWord_7249 prefixEnd_7249 1102880374680702801235 := by
  unfold tailWord_7249
  simp only [CollatzResearch.WordTrace]
  refine ⟨264392750745585875744801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176261833830390583829867 264392750745585875744801)
  ·
    refine ⟨198294563059189406808601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264392750745585875744801 198294563059189406808601)
    ·
      refine ⟨148720922294392055106451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198294563059189406808601 148720922294392055106451)
      ·
        refine ⟨223081383441588082659677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148720922294392055106451 223081383441588082659677)
        ·
          refine ⟨83655518790595530997379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223081383441588082659677 83655518790595530997379)
          ·
            refine ⟨125483278185893296496069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83655518790595530997379 125483278185893296496069)
            ·
              refine ⟨23528114659854993093013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125483278185893296496069 23528114659854993093013)
              ·
                refine ⟨1102880374680702801235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23528114659854993093013 1102880374680702801235)
                ·
                  rfl

theorem cell20_7249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_7249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7249 prefixEnd_7249 := by exact prefixLift 7249
  have htrace : WordTrace (prefixWord ++ tailWord_7249) baseStart_7249 baseEnd_7249 := by
    simpa [prefixWord, tailWord_7249, baseEnd_7249] using wordTrace_append hprefix tailTrace_7249
  have hstable : (prefixWord ++ tailWord_7249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7249).length < 2 ^ (prefixWord ++ tailWord_7249).sum := by decide
  have hdescent : baseEnd_7249 < baseStart_7249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7266 : List Nat := [3, 3, 2, 2, 1, 9]
def baseStart_7266 : Nat := 118140960795 + 7266 * 2 ^ 59
def prefixEnd_7266 : Nat := 4983230072969 + 3 ^ 40 * 7266 * 2
def baseEnd_7266 : Nat := 122829643972800179147

theorem tailTrace_7266 : CollatzResearch.WordTrace tailWord_7266 prefixEnd_7266 122829643972800179147 := by
  unfold tailWord_7266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66253197920999444778413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176675194455998519409101 66253197920999444778413)
  ·
    refine ⟨24844949220374791791905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66253197920999444778413 24844949220374791791905)
    ·
      refine ⟨18633711915281093843929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24844949220374791791905 18633711915281093843929)
      ·
        refine ⟨13975283936460820382947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18633711915281093843929 13975283936460820382947)
        ·
          refine ⟨20962925904691230574421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13975283936460820382947 20962925904691230574421)
          ·
            refine ⟨122829643972800179147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 20962925904691230574421 122829643972800179147)
            ·
              rfl

theorem cell20_7266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 9].length) (baseStart_7266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7266 prefixEnd_7266 := by exact prefixLift 7266
  have htrace : WordTrace (prefixWord ++ tailWord_7266) baseStart_7266 baseEnd_7266 := by
    simpa [prefixWord, tailWord_7266, baseEnd_7266] using wordTrace_append hprefix tailTrace_7266
  have hstable : (prefixWord ++ tailWord_7266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7266).length < 2 ^ (prefixWord ++ tailWord_7266).sum := by decide
  have hdescent : baseEnd_7266 < baseStart_7266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7273 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_7273 : Nat := 118140960795 + 7273 * 2 ^ 59
def prefixEnd_7273 : Nat := 4983230072969 + 3 ^ 40 * 7273 * 2
def baseEnd_7273 : Nat := 3319595378004691603607

theorem tailTrace_7273 : CollatzResearch.WordTrace tailWord_7273 prefixEnd_7273 3319595378004691603607 := by
  unfold tailWord_7273
  simp only [CollatzResearch.WordTrace]
  refine ⟨265268102658637974618473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176845401772425316412315 265268102658637974618473)
  ·
    refine ⟨198951076993978480963855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265268102658637974618473 198951076993978480963855)
    ·
      refine ⟨298426615490967721445783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198951076993978480963855 298426615490967721445783)
      ·
        refine ⟨447639923236451582168675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298426615490967721445783 447639923236451582168675)
        ·
          refine ⟨671459884854677373253013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447639923236451582168675 671459884854677373253013)
          ·
            refine ⟨31474682102563001871235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 671459884854677373253013 31474682102563001871235)
            ·
              refine ⟨47212023153844502806853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31474682102563001871235 47212023153844502806853)
              ·
                refine ⟨8852254341345844276285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47212023153844502806853 8852254341345844276285)
                ·
                  refine ⟨3319595378004691603607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8852254341345844276285 3319595378004691603607)
                  ·
                    rfl

theorem cell20_7273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_7273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7273 prefixEnd_7273 := by exact prefixLift 7273
  have htrace : WordTrace (prefixWord ++ tailWord_7273) baseStart_7273 baseEnd_7273 := by
    simpa [prefixWord, tailWord_7273, baseEnd_7273] using wordTrace_append hprefix tailTrace_7273
  have hstable : (prefixWord ++ tailWord_7273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7273).length < 2 ^ (prefixWord ++ tailWord_7273).sum := by decide
  have hdescent : baseEnd_7273 < baseStart_7273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7280 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_7280 : Nat := 118140960795 + 7280 * 2 ^ 59
def prefixEnd_7280 : Nat := 4983230072969 + 3 ^ 40 * 7280 * 2
def baseEnd_7280 : Nat := 3322790368743778370245

theorem tailTrace_7280 : CollatzResearch.WordTrace tailWord_7280 prefixEnd_7280 3322790368743778370245 := by
  unfold tailWord_7280
  simp only [CollatzResearch.WordTrace]
  refine ⟨132761706816639085061647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 177015609088852113415529 132761706816639085061647)
  ·
    refine ⟨199142560224958627592471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132761706816639085061647 199142560224958627592471)
    ·
      refine ⟨298713840337437941388707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199142560224958627592471 298713840337437941388707)
      ·
        refine ⟨448070760506156912083061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298713840337437941388707 448070760506156912083061)
        ·
          refine ⟨42006633797452210507787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 448070760506156912083061 42006633797452210507787)
          ·
            refine ⟨63009950696178315761681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42006633797452210507787 63009950696178315761681)
            ·
              refine ⟨47257463022133736821261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63009950696178315761681 47257463022133736821261)
              ·
                refine ⟨17721548633300151307973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47257463022133736821261 17721548633300151307973)
                ·
                  refine ⟨3322790368743778370245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17721548633300151307973 3322790368743778370245)
                  ·
                    rfl

theorem cell20_7280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_7280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7280 prefixEnd_7280 := by exact prefixLift 7280
  have htrace : WordTrace (prefixWord ++ tailWord_7280) baseStart_7280 baseEnd_7280 := by
    simpa [prefixWord, tailWord_7280, baseEnd_7280] using wordTrace_append hprefix tailTrace_7280
  have hstable : (prefixWord ++ tailWord_7280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7280).length < 2 ^ (prefixWord ++ tailWord_7280).sum := by decide
  have hdescent : baseEnd_7280 < baseStart_7280 := by decide
  rcases family_descends (prefixWord ++ tailWord_7280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7297 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_7297 : Nat := 118140960795 + 7297 * 2 ^ 59
def prefixEnd_7297 : Nat := 4983230072969 + 3 ^ 40 * 7297 * 2
def baseEnd_7297 : Nat := 3330549631967274803509

theorem tailTrace_7297 : CollatzResearch.WordTrace tailWord_7297 prefixEnd_7297 3330549631967274803509 := by
  unfold tailWord_7297
  simp only [CollatzResearch.WordTrace]
  refine ⟨266143454571690073492145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 177428969714460048994763 266143454571690073492145)
  ·
    refine ⟨199607590928767555119109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266143454571690073492145 199607590928767555119109)
    ·
      refine ⟨37426423299143916584833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199607590928767555119109 37426423299143916584833)
      ·
        refine ⟨28069817474357937438625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37426423299143916584833 28069817474357937438625)
        ·
          refine ⟨21052363105768453078969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28069817474357937438625 21052363105768453078969)
          ·
            refine ⟨15789272329326339809227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21052363105768453078969 15789272329326339809227)
            ·
              refine ⟨23683908493989509713841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789272329326339809227 23683908493989509713841)
              ·
                refine ⟨17762931370492132285381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23683908493989509713841 17762931370492132285381)
                ·
                  refine ⟨3330549631967274803509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17762931370492132285381 3330549631967274803509)
                  ·
                    rfl

theorem cell20_7297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_7297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7297 prefixEnd_7297 := by exact prefixLift 7297
  have htrace : WordTrace (prefixWord ++ tailWord_7297) baseStart_7297 baseEnd_7297 := by
    simpa [prefixWord, tailWord_7297, baseEnd_7297] using wordTrace_append hprefix tailTrace_7297
  have hstable : (prefixWord ++ tailWord_7297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7297).length < 2 ^ (prefixWord ++ tailWord_7297).sum := by decide
  have hdescent : baseEnd_7297 < baseStart_7297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7314 : List Nat := [3, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_7314 : Nat := 118140960795 + 7314 * 2 ^ 59
def prefixEnd_7314 : Nat := 4983230072969 + 3 ^ 40 * 7314 * 2
def baseEnd_7314 : Nat := 3338308895190771236773

theorem tailTrace_7314 : CollatzResearch.WordTrace tailWord_7314 prefixEnd_7314 3338308895190771236773 := by
  unfold tailWord_7314
  simp only [CollatzResearch.WordTrace]
  refine ⟨66690873877525494215249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 177842330340067984573997 66690873877525494215249)
  ·
    refine ⟨50018155408144120661437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66690873877525494215249 50018155408144120661437)
    ·
      refine ⟨18756808278054045248039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50018155408144120661437 18756808278054045248039)
      ·
        refine ⟨28135212417081067872059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18756808278054045248039 28135212417081067872059)
        ·
          refine ⟨42202818625621601808089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28135212417081067872059 42202818625621601808089)
          ·
            refine ⟨31652113969216201356067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42202818625621601808089 31652113969216201356067)
            ·
              refine ⟨47478170953824302034101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31652113969216201356067 47478170953824302034101)
              ·
                refine ⟨4451078526921028315697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47478170953824302034101 4451078526921028315697)
                ·
                  refine ⟨3338308895190771236773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451078526921028315697 3338308895190771236773)
                  ·
                    rfl

theorem cell20_7314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_7314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7314 prefixEnd_7314 := by exact prefixLift 7314
  have htrace : WordTrace (prefixWord ++ tailWord_7314) baseStart_7314 baseEnd_7314 := by
    simpa [prefixWord, tailWord_7314, baseEnd_7314] using wordTrace_append hprefix tailTrace_7314
  have hstable : (prefixWord ++ tailWord_7314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7314).length < 2 ^ (prefixWord ++ tailWord_7314).sum := by decide
  have hdescent : baseEnd_7314 < baseStart_7314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7325 : List Nat := [1, 4, 2, 1, 1, 2, 9]
def baseStart_7325 : Nat := 118140960795 + 7325 * 2 ^ 59
def prefixEnd_7325 : Nat := 4983230072969 + 3 ^ 40 * 7325 * 2
def baseEnd_7325 : Nat := 371481066102624652229

theorem tailTrace_7325 : CollatzResearch.WordTrace tailWord_7325 prefixEnd_7325 371481066102624652229 := by
  unfold tailWord_7325
  simp only [CollatzResearch.WordTrace]
  refine ⟨267164698470250855511429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178109798980167237007619 267164698470250855511429)
  ·
    refine ⟨50093380963172035408393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267164698470250855511429 50093380963172035408393)
    ·
      refine ⟨37570035722379026556295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50093380963172035408393 37570035722379026556295)
      ·
        refine ⟨56355053583568539834443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37570035722379026556295 56355053583568539834443)
        ·
          refine ⟨84532580375352809751665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56355053583568539834443 84532580375352809751665)
          ·
            refine ⟨63399435281514607313749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84532580375352809751665 63399435281514607313749)
            ·
              refine ⟨371481066102624652229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 63399435281514607313749 371481066102624652229)
              ·
                rfl

theorem cell20_7325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_7325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7325 prefixEnd_7325 := by exact prefixLift 7325
  have htrace : WordTrace (prefixWord ++ tailWord_7325) baseStart_7325 baseEnd_7325 := by
    simpa [prefixWord, tailWord_7325, baseEnd_7325] using wordTrace_append hprefix tailTrace_7325
  have hstable : (prefixWord ++ tailWord_7325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7325).length < 2 ^ (prefixWord ++ tailWord_7325).sum := by decide
  have hdescent : baseEnd_7325 < baseStart_7325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_7335 : Nat := 118140960795 + 7335 * 2 ^ 59
def prefixEnd_7335 : Nat := 4983230072969 + 3 ^ 40 * 7335 * 2
def baseEnd_7335 : Nat := 3347893867408031536687

theorem tailTrace_7335 : CollatzResearch.WordTrace tailWord_7335 prefixEnd_7335 3347893867408031536687 := by
  unfold tailWord_7335
  simp only [CollatzResearch.WordTrace]
  refine ⟨267529428434022563375459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178352952289348375583639 267529428434022563375459)
  ·
    refine ⟨401294142651033845063189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267529428434022563375459 401294142651033845063189)
    ·
      refine ⟨18810662936767211487337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401294142651033845063189 18810662936767211487337)
      ·
        refine ⟨14107997202575408615503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18810662936767211487337 14107997202575408615503)
        ·
          refine ⟨21161995803863112923255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14107997202575408615503 21161995803863112923255)
          ·
            refine ⟨31742993705794669384883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21161995803863112923255 31742993705794669384883)
            ·
              refine ⟨47614490558692004077325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31742993705794669384883 47614490558692004077325)
              ·
                refine ⟨17855433959509501528997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47614490558692004077325 17855433959509501528997)
                ·
                  refine ⟨3347893867408031536687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17855433959509501528997 3347893867408031536687)
                  ·
                    rfl

theorem cell20_7335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_7335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7335 prefixEnd_7335 := by exact prefixLift 7335
  have htrace : WordTrace (prefixWord ++ tailWord_7335) baseStart_7335 baseEnd_7335 := by
    simpa [prefixWord, tailWord_7335, baseEnd_7335] using wordTrace_append hprefix tailTrace_7335
  have hstable : (prefixWord ++ tailWord_7335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335).length < 2 ^ (prefixWord ++ tailWord_7335).sum := by decide
  have hdescent : baseEnd_7335 < baseStart_7335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7345 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 3]
def baseStart_7345 : Nat := 118140960795 + 7345 * 2 ^ 59
def prefixEnd_7345 : Nat := 4983230072969 + 3 ^ 40 * 7345 * 2
def baseEnd_7345 : Nat := 3352458139892441203313

theorem tailTrace_7345 : CollatzResearch.WordTrace tailWord_7345 prefixEnd_7345 3352458139892441203313 := by
  unfold tailWord_7345
  simp only [CollatzResearch.WordTrace]
  refine ⟨267894158397794271239489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178596105598529514159659 267894158397794271239489)
  ·
    refine ⟨200920618798345703429617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267894158397794271239489 200920618798345703429617)
    ·
      refine ⟨150690464098759277572213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200920618798345703429617 150690464098759277572213)
      ·
        refine ⟨14127231009258682272395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150690464098759277572213 14127231009258682272395)
        ·
          refine ⟨21190846513888023408593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127231009258682272395 21190846513888023408593)
          ·
            refine ⟨15893134885416017556445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21190846513888023408593 15893134885416017556445)
            ·
              refine ⟨5959925582031006583667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15893134885416017556445 5959925582031006583667)
              ·
                refine ⟨8939888373046509875501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959925582031006583667 8939888373046509875501)
                ·
                  refine ⟨3352458139892441203313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8939888373046509875501 3352458139892441203313)
                  ·
                    rfl

theorem cell20_7345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_7345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7345 prefixEnd_7345 := by exact prefixLift 7345
  have htrace : WordTrace (prefixWord ++ tailWord_7345) baseStart_7345 baseEnd_7345 := by
    simpa [prefixWord, tailWord_7345, baseEnd_7345] using wordTrace_append hprefix tailTrace_7345
  have hstable : (prefixWord ++ tailWord_7345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7345).length < 2 ^ (prefixWord ++ tailWord_7345).sum := by decide
  have hdescent : baseEnd_7345 < baseStart_7345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7404 : List Nat := [2, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_7404 : Nat := 118140960795 + 7404 * 2 ^ 59
def prefixEnd_7404 : Nat := 4983230072969 + 3 ^ 40 * 7404 * 2
def baseEnd_7404 : Nat := 3379387347550458236405

theorem tailTrace_7404 : CollatzResearch.WordTrace tailWord_7404 prefixEnd_7404 3379387347550458236405 := by
  unfold tailWord_7404
  simp only [CollatzResearch.WordTrace]
  refine ⟨135023032592023673818633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180030710122698231758177 135023032592023673818633)
  ·
    refine ⟨101267274444017755363975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135023032592023673818633 101267274444017755363975)
    ·
      refine ⟨151900911666026633045963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101267274444017755363975 151900911666026633045963)
      ·
        refine ⟨227851367499039949568945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151900911666026633045963 227851367499039949568945)
        ·
          refine ⟨170888525624279962176709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227851367499039949568945 170888525624279962176709)
          ·
            refine ⟨32041598554552492908133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170888525624279962176709 32041598554552492908133)
            ·
              refine ⟨6007799728978592420275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32041598554552492908133 6007799728978592420275)
              ·
                refine ⟨9011699593467888630413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6007799728978592420275 9011699593467888630413)
                ·
                  refine ⟨3379387347550458236405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9011699593467888630413 3379387347550458236405)
                  ·
                    rfl

theorem cell20_7404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_7404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7404 prefixEnd_7404 := by exact prefixLift 7404
  have htrace : WordTrace (prefixWord ++ tailWord_7404) baseStart_7404 baseEnd_7404 := by
    simpa [prefixWord, tailWord_7404, baseEnd_7404] using wordTrace_append hprefix tailTrace_7404
  have hstable : (prefixWord ++ tailWord_7404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7404).length < 2 ^ (prefixWord ++ tailWord_7404).sum := by decide
  have hdescent : baseEnd_7404 < baseStart_7404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7487 : List Nat := [1, 1, 2, 2, 4, 2, 1, 5, 2]
def baseStart_7487 : Nat := 118140960795 + 7487 * 2 ^ 59
def prefixEnd_7487 : Nat := 4983230072969 + 3 ^ 40 * 7487 * 2
def baseEnd_7487 : Nat := 3417270809171058469399

theorem tailTrace_7487 : CollatzResearch.WordTrace tailWord_7487 prefixEnd_7487 3417270809171058469399 := by
  unfold tailWord_7487
  simp only [CollatzResearch.WordTrace]
  refine ⟨273073323883352522908715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182048882588901681939143 273073323883352522908715)
  ·
    refine ⟨409609985825028784363073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273073323883352522908715 409609985825028784363073)
    ·
      refine ⟨307207489368771588272305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 409609985825028784363073 307207489368771588272305)
      ·
        refine ⟨230405617026578691204229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307207489368771588272305 230405617026578691204229)
        ·
          refine ⟨43201053192483504600793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230405617026578691204229 43201053192483504600793)
          ·
            refine ⟨32400789894362628450595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43201053192483504600793 32400789894362628450595)
            ·
              refine ⟨48601184841543942675893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32400789894362628450595 48601184841543942675893)
              ·
                refine ⟨4556361078894744625865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48601184841543942675893 4556361078894744625865)
                ·
                  refine ⟨3417270809171058469399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4556361078894744625865 3417270809171058469399)
                  ·
                    rfl

theorem cell20_7487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 2].length) (baseStart_7487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7487 prefixEnd_7487 := by exact prefixLift 7487
  have htrace : WordTrace (prefixWord ++ tailWord_7487) baseStart_7487 baseEnd_7487 := by
    simpa [prefixWord, tailWord_7487, baseEnd_7487] using wordTrace_append hprefix tailTrace_7487
  have hstable : (prefixWord ++ tailWord_7487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7487).length < 2 ^ (prefixWord ++ tailWord_7487).sum := by decide
  have hdescent : baseEnd_7487 < baseStart_7487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7491 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_7491 : Nat := 118140960795 + 7491 * 2 ^ 59
def prefixEnd_7491 : Nat := 4983230072969 + 3 ^ 40 * 7491 * 2
def baseEnd_7491 : Nat := 3419096518164822336049

theorem tailTrace_7491 : CollatzResearch.WordTrace tailWord_7491 prefixEnd_7491 3419096518164822336049 := by
  unfold tailWord_7491
  simp only [CollatzResearch.WordTrace]
  refine ⟨273219215868861206054327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 182146143912574137369551 273219215868861206054327)
  ·
    refine ⟨409828823803291809081491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273219215868861206054327 409828823803291809081491)
    ·
      refine ⟨614743235704937713622237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409828823803291809081491 614743235704937713622237)
      ·
        refine ⟨230528713389351642608339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 614743235704937713622237 230528713389351642608339)
        ·
          refine ⟨345793070084027463912509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230528713389351642608339 345793070084027463912509)
          ·
            refine ⟨129672401281510298967191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345793070084027463912509 129672401281510298967191)
            ·
              refine ⟨194508601922265448450787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129672401281510298967191 194508601922265448450787)
              ·
                refine ⟨291762902883398172676181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194508601922265448450787 291762902883398172676181)
                ·
                  refine ⟨3419096518164822336049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 291762902883398172676181 3419096518164822336049)
                  ·
                    rfl

theorem cell20_7491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_7491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7491 prefixEnd_7491 := by exact prefixLift 7491
  have htrace : WordTrace (prefixWord ++ tailWord_7491) baseStart_7491 baseEnd_7491 := by
    simpa [prefixWord, tailWord_7491, baseEnd_7491] using wordTrace_append hprefix tailTrace_7491
  have hstable : (prefixWord ++ tailWord_7491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7491).length < 2 ^ (prefixWord ++ tailWord_7491).sum := by decide
  have hdescent : baseEnd_7491 < baseStart_7491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7510 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7510 : Nat := 118140960795 + 7510 * 2 ^ 59
def prefixEnd_7510 : Nat := 4983230072969 + 3 ^ 40 * 7510 * 2
def baseEnd_7510 : Nat := 3427768635885200702639

theorem tailTrace_7510 : CollatzResearch.WordTrace tailWord_7510 prefixEnd_7510 3427768635885200702639 := by
  unfold tailWord_7510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119512675001715687249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 182608135200018300663989 17119512675001715687249)
  ·
    refine ⟨12839634506251286765437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17119512675001715687249 12839634506251286765437)
    ·
      refine ⟨4814862939844232537039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12839634506251286765437 4814862939844232537039)
      ·
        refine ⟨7222294409766348805559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4814862939844232537039 7222294409766348805559)
        ·
          refine ⟨10833441614649523208339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222294409766348805559 10833441614649523208339)
          ·
            refine ⟨16250162421974284812509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833441614649523208339 16250162421974284812509)
            ·
              refine ⟨6093810908240356804691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16250162421974284812509 6093810908240356804691)
              ·
                refine ⟨9140716362360535207037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6093810908240356804691 9140716362360535207037)
                ·
                  refine ⟨3427768635885200702639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9140716362360535207037 3427768635885200702639)
                  ·
                    rfl

theorem cell20_7510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7510 prefixEnd_7510 := by exact prefixLift 7510
  have htrace : WordTrace (prefixWord ++ tailWord_7510) baseStart_7510 baseEnd_7510 := by
    simpa [prefixWord, tailWord_7510, baseEnd_7510] using wordTrace_append hprefix tailTrace_7510
  have hstable : (prefixWord ++ tailWord_7510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7510).length < 2 ^ (prefixWord ++ tailWord_7510).sum := by decide
  have hdescent : baseEnd_7510 < baseStart_7510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7528 : List Nat := [2, 1, 4, 2, 4, 1, 2, 4]
def baseStart_7528 : Nat := 118140960795 + 7528 * 2 ^ 59
def prefixEnd_7528 : Nat := 4983230072969 + 3 ^ 40 * 7528 * 2
def baseEnd_7528 : Nat := 1145328108785712700855

theorem tailTrace_7528 : CollatzResearch.WordTrace tailWord_7528 prefixEnd_7528 1145328108785712700855 := by
  unfold tailWord_7528
  simp only [CollatzResearch.WordTrace]
  refine ⟨137284358367408262575619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183045811156544350100825 137284358367408262575619)
  ·
    refine ⟨205926537551112393863429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137284358367408262575619 205926537551112393863429)
    ·
      refine ⟨38611225790833573849393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205926537551112393863429 38611225790833573849393)
      ·
        refine ⟨28958419343125180387045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38611225790833573849393 28958419343125180387045)
        ·
          refine ⟨5429703626835971322571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28958419343125180387045 5429703626835971322571)
          ·
            refine ⟨8144555440253956983857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429703626835971322571 8144555440253956983857)
            ·
              refine ⟨6108416580190467737893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8144555440253956983857 6108416580190467737893)
              ·
                refine ⟨1145328108785712700855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6108416580190467737893 1145328108785712700855)
                ·
                  rfl

theorem cell20_7528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_7528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7528 prefixEnd_7528 := by exact prefixLift 7528
  have htrace : WordTrace (prefixWord ++ tailWord_7528) baseStart_7528 baseEnd_7528 := by
    simpa [prefixWord, tailWord_7528, baseEnd_7528] using wordTrace_append hprefix tailTrace_7528
  have hstable : (prefixWord ++ tailWord_7528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7528).length < 2 ^ (prefixWord ++ tailWord_7528).sum := by decide
  have hdescent : baseEnd_7528 < baseStart_7528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7529 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_7529 : Nat := 118140960795 + 7529 * 2 ^ 59
def prefixEnd_7529 : Nat := 4983230072969 + 3 ^ 40 * 7529 * 2
def baseEnd_7529 : Nat := 3436440753605579069227

theorem tailTrace_7529 : CollatzResearch.WordTrace tailWord_7529 prefixEnd_7529 3436440753605579069227 := by
  unfold tailWord_7529
  simp only [CollatzResearch.WordTrace]
  refine ⟨274605189731193695937641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 183070126487462463958427 274605189731193695937641)
  ·
    refine ⟨205953892298395271953231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 274605189731193695937641 205953892298395271953231)
    ·
      refine ⟨308930838447592907929847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205953892298395271953231 308930838447592907929847)
      ·
        refine ⟨463396257671389361894771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308930838447592907929847 463396257671389361894771)
        ·
          refine ⟨695094386507084042842157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463396257671389361894771 695094386507084042842157)
          ·
            refine ⟨260660394940156516065809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695094386507084042842157 260660394940156516065809)
            ·
              refine ⟨195495296205117387049357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260660394940156516065809 195495296205117387049357)
              ·
                refine ⟨73310736076919020143509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195495296205117387049357 73310736076919020143509)
                ·
                  refine ⟨3436440753605579069227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73310736076919020143509 3436440753605579069227)
                  ·
                    rfl

theorem cell20_7529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_7529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7529 prefixEnd_7529 := by exact prefixLift 7529
  have htrace : WordTrace (prefixWord ++ tailWord_7529) baseStart_7529 baseEnd_7529 := by
    simpa [prefixWord, tailWord_7529, baseEnd_7529] using wordTrace_append hprefix tailTrace_7529
  have hstable : (prefixWord ++ tailWord_7529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7529).length < 2 ^ (prefixWord ++ tailWord_7529).sum := by decide
  have hdescent : baseEnd_7529 < baseStart_7529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7532 : List Nat := [2, 2, 1, 1, 5, 1, 4, 4]
def baseStart_7532 : Nat := 118140960795 + 7532 * 2 ^ 59
def prefixEnd_7532 : Nat := 4983230072969 + 3 ^ 40 * 7532 * 2
def baseEnd_7532 : Nat := 1145936678450300656405

theorem tailTrace_7532 : CollatzResearch.WordTrace tailWord_7532 prefixEnd_7532 1145936678450300656405 := by
  unfold tailWord_7532
  simp only [CollatzResearch.WordTrace]
  refine ⟨137357304360162604148425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 183143072480216805531233 137357304360162604148425)
  ·
    refine ⟨103017978270121953111319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137357304360162604148425 103017978270121953111319)
    ·
      refine ⟨154526967405182929666979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103017978270121953111319 154526967405182929666979)
      ·
        refine ⟨231790451107774394500469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154526967405182929666979 231790451107774394500469)
        ·
          refine ⟨21730354791353849484419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231790451107774394500469 21730354791353849484419)
          ·
            refine ⟨32595532187030774226629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730354791353849484419 32595532187030774226629)
            ·
              refine ⟨6111662285068270167493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32595532187030774226629 6111662285068270167493)
              ·
                refine ⟨1145936678450300656405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6111662285068270167493 1145936678450300656405)
                ·
                  rfl

theorem cell20_7532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_7532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7532 prefixEnd_7532 := by exact prefixLift 7532
  have htrace : WordTrace (prefixWord ++ tailWord_7532) baseStart_7532 baseEnd_7532 := by
    simpa [prefixWord, tailWord_7532, baseEnd_7532] using wordTrace_append hprefix tailTrace_7532
  have hstable : (prefixWord ++ tailWord_7532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7532).length < 2 ^ (prefixWord ++ tailWord_7532).sum := by decide
  have hdescent : baseEnd_7532 < baseStart_7532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7577 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 3]
def baseStart_7577 : Nat := 118140960795 + 7577 * 2 ^ 59
def prefixEnd_7577 : Nat := 4983230072969 + 3 ^ 40 * 7577 * 2
def baseEnd_7577 : Nat := 3458349261530745469031

theorem tailTrace_7577 : CollatzResearch.WordTrace tailWord_7577 prefixEnd_7577 3458349261530745469031 := by
  unfold tailWord_7577
  simp only [CollatzResearch.WordTrace]
  refine ⟨276355893557297893684985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184237262371531929123323 276355893557297893684985)
  ·
    refine ⟨207266920167973420263739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 276355893557297893684985 207266920167973420263739)
    ·
      refine ⟨310900380251960130395609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207266920167973420263739 310900380251960130395609)
      ·
        refine ⟨233175285188970097796707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 310900380251960130395609 233175285188970097796707)
        ·
          refine ⟨349762927783455146695061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233175285188970097796707 349762927783455146695061)
          ·
            refine ⟨16395137239849460001331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 349762927783455146695061 16395137239849460001331)
            ·
              refine ⟨24592705859774190001997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16395137239849460001331 24592705859774190001997)
              ·
                refine ⟨9222264697415321250749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24592705859774190001997 9222264697415321250749)
                ·
                  refine ⟨3458349261530745469031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9222264697415321250749 3458349261530745469031)
                  ·
                    rfl

theorem cell20_7577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_7577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7577 prefixEnd_7577 := by exact prefixLift 7577
  have htrace : WordTrace (prefixWord ++ tailWord_7577) baseStart_7577 baseEnd_7577 := by
    simpa [prefixWord, tailWord_7577, baseEnd_7577] using wordTrace_append hprefix tailTrace_7577
  have hstable : (prefixWord ++ tailWord_7577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7577).length < 2 ^ (prefixWord ++ tailWord_7577).sum := by decide
  have hdescent : baseEnd_7577 < baseStart_7577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7591 : List Nat := [1, 1, 6, 1, 1, 1, 1, 8]
def baseStart_7591 : Nat := 118140960795 + 7591 * 2 ^ 59
def prefixEnd_7591 : Nat := 4983230072969 + 3 ^ 40 * 7591 * 2
def baseEnd_7591 : Nat := 1154913081002973000769

theorem tailTrace_7591 : CollatzResearch.WordTrace tailWord_7591 prefixEnd_7591 1154913081002973000769 := by
  unfold tailWord_7591
  simp only [CollatzResearch.WordTrace]
  refine ⟨276866515506578284694627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184577677004385523129751 276866515506578284694627)
  ·
    refine ⟨415299773259867427041941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276866515506578284694627 415299773259867427041941)
    ·
      refine ⟨19467176871556285642591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 415299773259867427041941 19467176871556285642591)
      ·
        refine ⟨29200765307334428463887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19467176871556285642591 29200765307334428463887)
        ·
          refine ⟨43801147961001642695831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29200765307334428463887 43801147961001642695831)
          ·
            refine ⟨65701721941502464043747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43801147961001642695831 65701721941502464043747)
            ·
              refine ⟨98552582912253696065621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65701721941502464043747 98552582912253696065621)
              ·
                refine ⟨1154913081002973000769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 98552582912253696065621 1154913081002973000769)
                ·
                  rfl

theorem cell20_7591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_7591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7591 prefixEnd_7591 := by exact prefixLift 7591
  have htrace : WordTrace (prefixWord ++ tailWord_7591) baseStart_7591 baseEnd_7591 := by
    simpa [prefixWord, tailWord_7591, baseEnd_7591] using wordTrace_append hprefix tailTrace_7591
  have hstable : (prefixWord ++ tailWord_7591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7591).length < 2 ^ (prefixWord ++ tailWord_7591).sum := by decide
  have hdescent : baseEnd_7591 < baseStart_7591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601 : List Nat := [1, 2, 2, 4, 1, 1, 2, 5, 2]
def baseStart_7601 : Nat := 118140960795 + 7601 * 2 ^ 59
def prefixEnd_7601 : Nat := 4983230072969 + 3 ^ 40 * 7601 * 2
def baseEnd_7601 : Nat := 3469303515493328668933

theorem tailTrace_7601 : CollatzResearch.WordTrace tailWord_7601 prefixEnd_7601 3469303515493328668933 := by
  unfold tailWord_7601
  simp only [CollatzResearch.WordTrace]
  refine ⟨277231245470349992558657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184820830313566661705771 277231245470349992558657)
  ·
    refine ⟨207923434102762494418993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277231245470349992558657 207923434102762494418993)
    ·
      refine ⟨155942575577071870814245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207923434102762494418993 155942575577071870814245)
      ·
        refine ⟨29239232920700975777671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155942575577071870814245 29239232920700975777671)
        ·
          refine ⟨43858849381051463666507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29239232920700975777671 43858849381051463666507)
          ·
            refine ⟨65788274071577195499761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43858849381051463666507 65788274071577195499761)
            ·
              refine ⟨49341205553682896624821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65788274071577195499761 49341205553682896624821)
              ·
                refine ⟨4625738020657771558577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49341205553682896624821 4625738020657771558577)
                ·
                  refine ⟨3469303515493328668933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4625738020657771558577 3469303515493328668933)
                  ·
                    rfl

theorem cell20_7601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_7601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7601 prefixEnd_7601 := by exact prefixLift 7601
  have htrace : WordTrace (prefixWord ++ tailWord_7601) baseStart_7601 baseEnd_7601 := by
    simpa [prefixWord, tailWord_7601, baseEnd_7601] using wordTrace_append hprefix tailTrace_7601
  have hstable : (prefixWord ++ tailWord_7601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601).length < 2 ^ (prefixWord ++ tailWord_7601).sum := by decide
  have hdescent : baseEnd_7601 < baseStart_7601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7670 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_7670 : Nat := 118140960795 + 7670 * 2 ^ 59
def prefixEnd_7670 : Nat := 4983230072969 + 3 ^ 40 * 7670 * 2
def baseEnd_7670 : Nat := 3500796995635755368651

theorem tailTrace_7670 : CollatzResearch.WordTrace tailWord_7670 prefixEnd_7670 3500796995635755368651 := by
  unfold tailWord_7670
  simp only [CollatzResearch.WordTrace]
  refine ⟨17484242638773423551279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186498588146916517880309 17484242638773423551279)
  ·
    refine ⟨26226363958160135326919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17484242638773423551279 26226363958160135326919)
    ·
      refine ⟨39339545937240202990379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26226363958160135326919 39339545937240202990379)
      ·
        refine ⟨59009318905860304485569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39339545937240202990379 59009318905860304485569)
        ·
          refine ⟨44256989179395228364177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59009318905860304485569 44256989179395228364177)
          ·
            refine ⟨33192741884546421273133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44256989179395228364177 33192741884546421273133)
            ·
              refine ⟨12447278206704907977425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33192741884546421273133 12447278206704907977425)
              ·
                refine ⟨9335458655028680983069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12447278206704907977425 9335458655028680983069)
                ·
                  refine ⟨3500796995635755368651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9335458655028680983069 3500796995635755368651)
                  ·
                    rfl

theorem cell20_7670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_7670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7670 prefixEnd_7670 := by exact prefixLift 7670
  have htrace : WordTrace (prefixWord ++ tailWord_7670) baseStart_7670 baseEnd_7670 := by
    simpa [prefixWord, tailWord_7670, baseEnd_7670] using wordTrace_append hprefix tailTrace_7670
  have hstable : (prefixWord ++ tailWord_7670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7670).length < 2 ^ (prefixWord ++ tailWord_7670).sum := by decide
  have hdescent : baseEnd_7670 < baseStart_7670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7674 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_7674 : Nat := 118140960795 + 7674 * 2 ^ 59
def prefixEnd_7674 : Nat := 4983230072969 + 3 ^ 40 * 7674 * 2
def baseEnd_7674 : Nat := 3502622704629519235301

theorem tailTrace_7674 : CollatzResearch.WordTrace tailWord_7674 prefixEnd_7674 3502622704629519235301 := by
  unfold tailWord_7674
  simp only [CollatzResearch.WordTrace]
  refine ⟨69973443551470864991519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186595849470588973310717 69973443551470864991519)
  ·
    refine ⟨104960165327206297487279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69973443551470864991519 104960165327206297487279)
    ·
      refine ⟨157440247990809446230919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104960165327206297487279 157440247990809446230919)
      ·
        refine ⟨236160371986214169346379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157440247990809446230919 236160371986214169346379)
        ·
          refine ⟨354240557979321254019569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236160371986214169346379 354240557979321254019569)
          ·
            refine ⟨265680418484490940514677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354240557979321254019569 265680418484490940514677)
            ·
              refine ⟨24907539232921025673251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 265680418484490940514677 24907539232921025673251)
              ·
                refine ⟨37361308849381538509877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24907539232921025673251 37361308849381538509877)
                ·
                  refine ⟨3502622704629519235301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37361308849381538509877 3502622704629519235301)
                  ·
                    rfl

theorem cell20_7674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_7674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7674 prefixEnd_7674 := by exact prefixLift 7674
  have htrace : WordTrace (prefixWord ++ tailWord_7674) baseStart_7674 baseEnd_7674 := by
    simpa [prefixWord, tailWord_7674, baseEnd_7674] using wordTrace_append hprefix tailTrace_7674
  have hstable : (prefixWord ++ tailWord_7674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7674).length < 2 ^ (prefixWord ++ tailWord_7674).sum := by decide
  have hdescent : baseEnd_7674 < baseStart_7674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 2]
def baseStart_7677 : Nat := 118140960795 + 7677 * 2 ^ 59
def prefixEnd_7677 : Nat := 4983230072969 + 3 ^ 40 * 7677 * 2
def baseEnd_7677 : Nat := 3503991986374842135289

theorem tailTrace_7677 : CollatzResearch.WordTrace tailWord_7677 prefixEnd_7677 3503991986374842135289 := by
  unfold tailWord_7677
  simp only [CollatzResearch.WordTrace]
  refine ⟨280003193195014972325285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186668795463343314883523 280003193195014972325285)
  ·
    refine ⟨52500598724065307310991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280003193195014972325285 52500598724065307310991)
    ·
      refine ⟨78750898086097960966487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52500598724065307310991 78750898086097960966487)
      ·
        refine ⟨118126347129146941449731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78750898086097960966487 118126347129146941449731)
        ·
          refine ⟨177189520693720412174597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118126347129146941449731 177189520693720412174597)
          ·
            refine ⟨33223035130072577282737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177189520693720412174597 33223035130072577282737)
            ·
              refine ⟨24917276347554432962053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33223035130072577282737 24917276347554432962053)
              ·
                refine ⟨4671989315166456180385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24917276347554432962053 4671989315166456180385)
                ·
                  refine ⟨3503991986374842135289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671989315166456180385 3503991986374842135289)
                  ·
                    rfl

theorem cell20_7677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_7677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7677 prefixEnd_7677 := by exact prefixLift 7677
  have htrace : WordTrace (prefixWord ++ tailWord_7677) baseStart_7677 baseEnd_7677 := by
    simpa [prefixWord, tailWord_7677, baseEnd_7677] using wordTrace_append hprefix tailTrace_7677
  have hstable : (prefixWord ++ tailWord_7677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677).length < 2 ^ (prefixWord ++ tailWord_7677).sum := by decide
  have hdescent : baseEnd_7677 < baseStart_7677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_7736 : Nat := 118140960795 + 7736 * 2 ^ 59
def prefixEnd_7736 : Nat := 4983230072969 + 3 ^ 40 * 7736 * 2
def baseEnd_7736 : Nat := 3530921194032859168381

theorem tailTrace_7736 : CollatzResearch.WordTrace tailWord_7736 prefixEnd_7736 3530921194032859168381 := by
  unfold tailWord_7736
  simp only [CollatzResearch.WordTrace]
  refine ⟨141077549990634024361531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188103399987512032482041 141077549990634024361531)
  ·
    refine ⟨211616324985951036542297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141077549990634024361531 211616324985951036542297)
    ·
      refine ⟨158712243739463277406723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211616324985951036542297 158712243739463277406723)
      ·
        refine ⟨238068365609194916110085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158712243739463277406723 238068365609194916110085)
        ·
          refine ⟨44637818551724046770641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238068365609194916110085 44637818551724046770641)
          ·
            refine ⟨33478363913793035077981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44637818551724046770641 33478363913793035077981)
            ·
              refine ⟨12554386467672388154243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33478363913793035077981 12554386467672388154243)
              ·
                refine ⟨18831579701508582231365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554386467672388154243 18831579701508582231365)
                ·
                  refine ⟨3530921194032859168381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18831579701508582231365 3530921194032859168381)
                  ·
                    rfl

theorem cell20_7736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_7736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7736 prefixEnd_7736 := by exact prefixLift 7736
  have htrace : WordTrace (prefixWord ++ tailWord_7736) baseStart_7736 baseEnd_7736 := by
    simpa [prefixWord, tailWord_7736, baseEnd_7736] using wordTrace_append hprefix tailTrace_7736
  have hstable : (prefixWord ++ tailWord_7736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736).length < 2 ^ (prefixWord ++ tailWord_7736).sum := by decide
  have hdescent : baseEnd_7736 < baseStart_7736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7743 : List Nat := [1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_7743 : Nat := 118140960795 + 7743 * 2 ^ 59
def prefixEnd_7743 : Nat := 4983230072969 + 3 ^ 40 * 7743 * 2
def baseEnd_7743 : Nat := 1178038728257315311673

theorem tailTrace_7743 : CollatzResearch.WordTrace tailWord_7743 prefixEnd_7743 1178038728257315311673 := by
  unfold tailWord_7743
  simp only [CollatzResearch.WordTrace]
  refine ⟨282410410955908244227883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188273607303938829485255 282410410955908244227883)
  ·
    refine ⟨423615616433862366341825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282410410955908244227883 423615616433862366341825)
    ·
      refine ⟨317711712325396774756369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423615616433862366341825 317711712325396774756369)
      ·
        refine ⟨238283784244047581067277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317711712325396774756369 238283784244047581067277)
        ·
          refine ⟨89356419091517842900229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238283784244047581067277 89356419091517842900229)
          ·
            refine ⟨16754328579659595543793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89356419091517842900229 16754328579659595543793)
            ·
              refine ⟨12565746434744696657845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16754328579659595543793 12565746434744696657845)
              ·
                refine ⟨1178038728257315311673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12565746434744696657845 1178038728257315311673)
                ·
                  rfl

theorem cell20_7743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_7743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7743 prefixEnd_7743 := by exact prefixLift 7743
  have htrace : WordTrace (prefixWord ++ tailWord_7743) baseStart_7743 baseEnd_7743 := by
    simpa [prefixWord, tailWord_7743, baseEnd_7743] using wordTrace_append hprefix tailTrace_7743
  have hstable : (prefixWord ++ tailWord_7743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7743).length < 2 ^ (prefixWord ++ tailWord_7743).sum := by decide
  have hdescent : baseEnd_7743 < baseStart_7743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7784 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 3]
def baseStart_7784 : Nat := 118140960795 + 7784 * 2 ^ 59
def prefixEnd_7784 : Nat := 4983230072969 + 3 ^ 40 * 7784 * 2
def baseEnd_7784 : Nat := 3552829701958025568185

theorem tailTrace_7784 : CollatzResearch.WordTrace tailWord_7784 prefixEnd_7784 3552829701958025568185 := by
  unfold tailWord_7784
  simp only [CollatzResearch.WordTrace]
  refine ⟨141952901903686123235203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189270535871581497646937 141952901903686123235203)
  ·
    refine ⟨212929352855529184852805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141952901903686123235203 212929352855529184852805)
    ·
      refine ⟨39924253660411722159901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212929352855529184852805 39924253660411722159901)
      ·
        refine ⟨14971595122654395809963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39924253660411722159901 14971595122654395809963)
        ·
          refine ⟨22457392683981593714945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14971595122654395809963 22457392683981593714945)
          ·
            refine ⟨16843044512986195286209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22457392683981593714945 16843044512986195286209)
            ·
              refine ⟨12632283384739646464657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16843044512986195286209 12632283384739646464657)
              ·
                refine ⟨9474212538554734848493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12632283384739646464657 9474212538554734848493)
                ·
                  refine ⟨3552829701958025568185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9474212538554734848493 3552829701958025568185)
                  ·
                    rfl

theorem cell20_7784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_7784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7784 prefixEnd_7784 := by exact prefixLift 7784
  have htrace : WordTrace (prefixWord ++ tailWord_7784) baseStart_7784 baseEnd_7784 := by
    simpa [prefixWord, tailWord_7784, baseEnd_7784] using wordTrace_append hprefix tailTrace_7784
  have hstable : (prefixWord ++ tailWord_7784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7784).length < 2 ^ (prefixWord ++ tailWord_7784).sum := by decide
  have hdescent : baseEnd_7784 < baseStart_7784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7798 : List Nat := [5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_7798 : Nat := 118140960795 + 7798 * 2 ^ 59
def prefixEnd_7798 : Nat := 4983230072969 + 3 ^ 40 * 7798 * 2
def baseEnd_7798 : Nat := 1186406561145399700487

theorem tailTrace_7798 : CollatzResearch.WordTrace tailWord_7798 prefixEnd_7798 1186406561145399700487 := by
  unfold tailWord_7798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17776026609790789842503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189610950504435091653365 17776026609790789842503)
  ·
    refine ⟨26664039914686184763755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17776026609790789842503 26664039914686184763755)
    ·
      refine ⟨39996059872029277145633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26664039914686184763755 39996059872029277145633)
      ·
        refine ⟨29997044904021957859225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39996059872029277145633 29997044904021957859225)
        ·
          refine ⟨22497783678016468394419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29997044904021957859225 22497783678016468394419)
          ·
            refine ⟨33746675517024702591629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22497783678016468394419 33746675517024702591629)
            ·
              refine ⟨12655003318884263471861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33746675517024702591629 12655003318884263471861)
              ·
                refine ⟨1186406561145399700487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12655003318884263471861 1186406561145399700487)
                ·
                  rfl

theorem cell20_7798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_7798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7798 prefixEnd_7798 := by exact prefixLift 7798
  have htrace : WordTrace (prefixWord ++ tailWord_7798) baseStart_7798 baseEnd_7798 := by
    simpa [prefixWord, tailWord_7798, baseEnd_7798] using wordTrace_append hprefix tailTrace_7798
  have hstable : (prefixWord ++ tailWord_7798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7798).length < 2 ^ (prefixWord ++ tailWord_7798).sum := by decide
  have hdescent : baseEnd_7798 < baseStart_7798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802 : List Nat := [3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7802 : Nat := 118140960795 + 7802 * 2 ^ 59
def prefixEnd_7802 : Nat := 4983230072969 + 3 ^ 40 * 7802 * 2
def baseEnd_7802 : Nat := 1187015130809987656037

theorem tailTrace_7802 : CollatzResearch.WordTrace tailWord_7802 prefixEnd_7802 1187015130809987656037 := by
  unfold tailWord_7802
  simp only [CollatzResearch.WordTrace]
  refine ⟨71140579435540330156415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189708211828107547083773 71140579435540330156415)
  ·
    refine ⟨106710869153310495234623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71140579435540330156415 106710869153310495234623)
    ·
      refine ⟨160066303729965742851935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106710869153310495234623 160066303729965742851935)
      ·
        refine ⟨240099455594948614277903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160066303729965742851935 240099455594948614277903)
        ·
          refine ⟨360149183392422921416855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240099455594948614277903 360149183392422921416855)
          ·
            refine ⟨540223775088634382125283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360149183392422921416855 540223775088634382125283)
            ·
              refine ⟨810335662632951573187925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540223775088634382125283 810335662632951573187925)
              ·
                refine ⟨1187015130809987656037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 810335662632951573187925 1187015130809987656037)
                ·
                  rfl

theorem cell20_7802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7802 prefixEnd_7802 := by exact prefixLift 7802
  have htrace : WordTrace (prefixWord ++ tailWord_7802) baseStart_7802 baseEnd_7802 := by
    simpa [prefixWord, tailWord_7802, baseEnd_7802] using wordTrace_append hprefix tailTrace_7802
  have hstable : (prefixWord ++ tailWord_7802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802).length < 2 ^ (prefixWord ++ tailWord_7802).sum := by decide
  have hdescent : baseEnd_7802 < baseStart_7802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_7805 : Nat := 118140960795 + 7805 * 2 ^ 59
def prefixEnd_7805 : Nat := 4983230072969 + 3 ^ 40 * 7805 * 2
def baseEnd_7805 : Nat := 3562414674175285868099

theorem tailTrace_7805 : CollatzResearch.WordTrace tailWord_7805 prefixEnd_7805 3562414674175285868099 := by
  unfold tailWord_7805
  simp only [CollatzResearch.WordTrace]
  refine ⟨284671736731292832984869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189781157820861888656579 284671736731292832984869)
  ·
    refine ⟨53375950637117406184663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284671736731292832984869 53375950637117406184663)
    ·
      refine ⟨80063925955676109276995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53375950637117406184663 80063925955676109276995)
      ·
        refine ⟨120095888933514163915493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80063925955676109276995 120095888933514163915493)
        ·
          refine ⟨22517979175033905734155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120095888933514163915493 22517979175033905734155)
          ·
            refine ⟨33776968762550858601233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22517979175033905734155 33776968762550858601233)
            ·
              refine ⟨25332726571913143950925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33776968762550858601233 25332726571913143950925)
              ·
                refine ⟨9499772464467428981597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25332726571913143950925 9499772464467428981597)
                ·
                  refine ⟨3562414674175285868099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9499772464467428981597 3562414674175285868099)
                  ·
                    rfl

theorem cell20_7805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_7805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7805 prefixEnd_7805 := by exact prefixLift 7805
  have htrace : WordTrace (prefixWord ++ tailWord_7805) baseStart_7805 baseEnd_7805 := by
    simpa [prefixWord, tailWord_7805, baseEnd_7805] using wordTrace_append hprefix tailTrace_7805
  have hstable : (prefixWord ++ tailWord_7805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805).length < 2 ^ (prefixWord ++ tailWord_7805).sum := by decide
  have hdescent : baseEnd_7805 < baseStart_7805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7819 : List Nat := [1, 1, 1, 1, 4, 1, 7, 4]
def baseStart_7819 : Nat := 118140960795 + 7819 * 2 ^ 59
def prefixEnd_7819 : Nat := 4983230072969 + 3 ^ 40 * 7819 * 2
def baseEnd_7819 : Nat := 1189601551884486467125

theorem tailTrace_7819 : CollatzResearch.WordTrace tailWord_7819 prefixEnd_7819 1189601551884486467125 := by
  unfold tailWord_7819
  simp only [CollatzResearch.WordTrace]
  refine ⟨285182358680573223994511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190121572453715482663007 285182358680573223994511)
  ·
    refine ⟨427773538020859835991767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285182358680573223994511 427773538020859835991767)
    ·
      refine ⟨641660307031289753987651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427773538020859835991767 641660307031289753987651)
      ·
        refine ⟨962490460546934630981477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641660307031289753987651 962490460546934630981477)
        ·
          refine ⟨180466961352550243309027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 962490460546934630981477 180466961352550243309027)
          ·
            refine ⟨270700442028825364963541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180466961352550243309027 270700442028825364963541)
            ·
              refine ⟨6344541610050594491333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 270700442028825364963541 6344541610050594491333)
              ·
                refine ⟨1189601551884486467125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6344541610050594491333 1189601551884486467125)
                ·
                  rfl

theorem cell20_7819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 4].length) (baseStart_7819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7819 prefixEnd_7819 := by exact prefixLift 7819
  have htrace : WordTrace (prefixWord ++ tailWord_7819) baseStart_7819 baseEnd_7819 := by
    simpa [prefixWord, tailWord_7819, baseEnd_7819] using wordTrace_append hprefix tailTrace_7819
  have hstable : (prefixWord ++ tailWord_7819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7819).length < 2 ^ (prefixWord ++ tailWord_7819).sum := by decide
  have hdescent : baseEnd_7819 < baseStart_7819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 3]
def baseStart_7839 : Nat := 118140960795 + 7839 * 2 ^ 59
def prefixEnd_7839 : Nat := 4983230072969 + 3 ^ 40 * 7839 * 2
def baseEnd_7839 : Nat := 3577933200622278734627

theorem tailTrace_7839 : CollatzResearch.WordTrace tailWord_7839 prefixEnd_7839 3577933200622278734627 := by
  unfold tailWord_7839
  simp only [CollatzResearch.WordTrace]
  refine ⟨285911818608116639722571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190607879072077759815047 285911818608116639722571)
  ·
    refine ⟨428867727912174959583857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285911818608116639722571 428867727912174959583857)
    ·
      refine ⟨321650795934131219687893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428867727912174959583857 321650795934131219687893)
      ·
        refine ⟨7538690529706200461435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 321650795934131219687893 7538690529706200461435)
        ·
          refine ⟨11308035794559300692153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7538690529706200461435 11308035794559300692153)
          ·
            refine ⟨8481026845919475519115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11308035794559300692153 8481026845919475519115)
            ·
              refine ⟨12721540268879213278673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481026845919475519115 12721540268879213278673)
              ·
                refine ⟨9541155201659409959005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12721540268879213278673 9541155201659409959005)
                ·
                  refine ⟨3577933200622278734627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9541155201659409959005 3577933200622278734627)
                  ·
                    rfl

theorem cell20_7839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_7839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7839 prefixEnd_7839 := by exact prefixLift 7839
  have htrace : WordTrace (prefixWord ++ tailWord_7839) baseStart_7839 baseEnd_7839 := by
    simpa [prefixWord, tailWord_7839, baseEnd_7839] using wordTrace_append hprefix tailTrace_7839
  have hstable : (prefixWord ++ tailWord_7839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839).length < 2 ^ (prefixWord ++ tailWord_7839).sum := by decide
  have hdescent : baseEnd_7839 < baseStart_7839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7864 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_7864 : Nat := 118140960795 + 7864 * 2 ^ 59
def prefixEnd_7864 : Nat := 4983230072969 + 3 ^ 40 * 7864 * 2
def baseEnd_7864 : Nat := 3589343881833302901191

theorem tailTrace_7864 : CollatzResearch.WordTrace tailWord_7864 prefixEnd_7864 3589343881833302901191 := by
  unfold tailWord_7864
  simp only [CollatzResearch.WordTrace]
  refine ⟨143411821758772954691323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191215762345030606255097 143411821758772954691323)
  ·
    refine ⟨215117732638159432036985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143411821758772954691323 215117732638159432036985)
    ·
      refine ⟨161338299478619574027739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 215117732638159432036985 161338299478619574027739)
      ·
        refine ⟨242007449217929361041609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161338299478619574027739 242007449217929361041609)
        ·
          refine ⟨181505586913447020781207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242007449217929361041609 181505586913447020781207)
          ·
            refine ⟨272258380370170531171811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181505586913447020781207 272258380370170531171811)
            ·
              refine ⟨408387570555255796757717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272258380370170531171811 408387570555255796757717)
              ·
                refine ⟨9571583684888807736509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 408387570555255796757717 9571583684888807736509)
                ·
                  refine ⟨3589343881833302901191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9571583684888807736509 3589343881833302901191)
                  ·
                    rfl

theorem cell20_7864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_7864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7864 prefixEnd_7864 := by exact prefixLift 7864
  have htrace : WordTrace (prefixWord ++ tailWord_7864) baseStart_7864 baseEnd_7864 := by
    simpa [prefixWord, tailWord_7864, baseEnd_7864] using wordTrace_append hprefix tailTrace_7864
  have hstable : (prefixWord ++ tailWord_7864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7864).length < 2 ^ (prefixWord ++ tailWord_7864).sum := by decide
  have hdescent : baseEnd_7864 < baseStart_7864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7871 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_7871 : Nat := 118140960795 + 7871 * 2 ^ 59
def prefixEnd_7871 : Nat := 4983230072969 + 3 ^ 40 * 7871 * 2
def baseEnd_7871 : Nat := 3592538872572389667829

theorem tailTrace_7871 : CollatzResearch.WordTrace tailWord_7871 prefixEnd_7871 3592538872572389667829 := by
  unfold tailWord_7871
  simp only [CollatzResearch.WordTrace]
  refine ⟨287078954492186104887467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 191385969661457403258311 287078954492186104887467)
  ·
    refine ⟨430618431738279157331201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287078954492186104887467 430618431738279157331201)
    ·
      refine ⟨322963823803709367998401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 430618431738279157331201 322963823803709367998401)
      ·
        refine ⟨242222867852782025998801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322963823803709367998401 242222867852782025998801)
        ·
          refine ⟨181667150889586519499101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242222867852782025998801 181667150889586519499101)
          ·
            refine ⟨68125181583594944812163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181667150889586519499101 68125181583594944812163)
            ·
              refine ⟨102187772375392417218245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68125181583594944812163 102187772375392417218245)
              ·
                refine ⟨19160207320386078228421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102187772375392417218245 19160207320386078228421)
                ·
                  refine ⟨3592538872572389667829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19160207320386078228421 3592538872572389667829)
                  ·
                    rfl

theorem cell20_7871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_7871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7871 prefixEnd_7871 := by exact prefixLift 7871
  have htrace : WordTrace (prefixWord ++ tailWord_7871) baseStart_7871 baseEnd_7871 := by
    simpa [prefixWord, tailWord_7871, baseEnd_7871] using wordTrace_append hprefix tailTrace_7871
  have hstable : (prefixWord ++ tailWord_7871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7871).length < 2 ^ (prefixWord ++ tailWord_7871).sum := by decide
  have hdescent : baseEnd_7871 < baseStart_7871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7888 : List Nat := [2, 1, 1, 1, 1, 2, 1, 9, 2]
def baseStart_7888 : Nat := 118140960795 + 7888 * 2 ^ 59
def prefixEnd_7888 : Nat := 4983230072969 + 3 ^ 40 * 7888 * 2
def baseEnd_7888 : Nat := 3600298135795886101093

theorem tailTrace_7888 : CollatzResearch.WordTrace tailWord_7888 prefixEnd_7888 3600298135795886101093 := by
  unfold tailWord_7888
  simp only [CollatzResearch.WordTrace]
  refine ⟨143849497715299004128159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 191799330287065338837545 143849497715299004128159)
  ·
    refine ⟨215774246572948506192239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143849497715299004128159 215774246572948506192239)
    ·
      refine ⟨323661369859422759288359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215774246572948506192239 323661369859422759288359)
      ·
        refine ⟨485492054789134138932539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323661369859422759288359 485492054789134138932539)
        ·
          refine ⟨728238082183701208398809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485492054789134138932539 728238082183701208398809)
          ·
            refine ⟨546178561637775906299107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728238082183701208398809 546178561637775906299107)
            ·
              refine ⟨819267842456663859448661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546178561637775906299107 819267842456663859448661)
              ·
                refine ⟨4800397514394514801457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 819267842456663859448661 4800397514394514801457)
                ·
                  refine ⟨3600298135795886101093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4800397514394514801457 3600298135795886101093)
                  ·
                    rfl

theorem cell20_7888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 9, 2].length) (baseStart_7888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7888 prefixEnd_7888 := by exact prefixLift 7888
  have htrace : WordTrace (prefixWord ++ tailWord_7888) baseStart_7888 baseEnd_7888 := by
    simpa [prefixWord, tailWord_7888, baseEnd_7888] using wordTrace_append hprefix tailTrace_7888
  have hstable : (prefixWord ++ tailWord_7888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7888).length < 2 ^ (prefixWord ++ tailWord_7888).sum := by decide
  have hdescent : baseEnd_7888 < baseStart_7888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7901 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7901 : Nat := 118140960795 + 7901 * 2 ^ 59
def prefixEnd_7901 : Nat := 4983230072969 + 3 ^ 40 * 7901 * 2
def baseEnd_7901 : Nat := 3606231690025618667707

theorem tailTrace_7901 : CollatzResearch.WordTrace tailWord_7901 prefixEnd_7901 3606231690025618667707 := by
  unfold tailWord_7901
  simp only [CollatzResearch.WordTrace]
  refine ⟨288173144383501228479557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192115429589000818986371 288173144383501228479557)
  ·
    refine ⟨54032464571906480339917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 288173144383501228479557 54032464571906480339917)
    ·
      refine ⟨20262174214464930127469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54032464571906480339917 20262174214464930127469)
      ·
        refine ⟨7598315330424348797801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20262174214464930127469 7598315330424348797801)
        ·
          refine ⟨5698736497818261598351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7598315330424348797801 5698736497818261598351)
          ·
            refine ⟨8548104746727392397527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5698736497818261598351 8548104746727392397527)
            ·
              refine ⟨12822157120091088596291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8548104746727392397527 12822157120091088596291)
              ·
                refine ⟨19233235680136632894437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12822157120091088596291 19233235680136632894437)
                ·
                  refine ⟨3606231690025618667707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19233235680136632894437 3606231690025618667707)
                  ·
                    rfl

theorem cell20_7901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7901 prefixEnd_7901 := by exact prefixLift 7901
  have htrace : WordTrace (prefixWord ++ tailWord_7901) baseStart_7901 baseEnd_7901 := by
    simpa [prefixWord, tailWord_7901, baseEnd_7901] using wordTrace_append hprefix tailTrace_7901
  have hstable : (prefixWord ++ tailWord_7901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7901).length < 2 ^ (prefixWord ++ tailWord_7901).sum := by decide
  have hdescent : baseEnd_7901 < baseStart_7901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7905 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 4]
def baseStart_7905 : Nat := 118140960795 + 7905 * 2 ^ 59
def prefixEnd_7905 : Nat := 4983230072969 + 3 ^ 40 * 7905 * 2
def baseEnd_7905 : Nat := 3608057399019382534357

theorem tailTrace_7905 : CollatzResearch.WordTrace tailWord_7905 prefixEnd_7905 3608057399019382534357 := by
  unfold tailWord_7905
  simp only [CollatzResearch.WordTrace]
  refine ⟨288319036369009911625169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 192212690912673274416779 288319036369009911625169)
  ·
    refine ⟨216239277276757433718877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288319036369009911625169 216239277276757433718877)
    ·
      refine ⟨81089728978784037644579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 216239277276757433718877 81089728978784037644579)
      ·
        refine ⟨121634593468176056466869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81089728978784037644579 121634593468176056466869)
        ·
          refine ⟨11403243137641505293769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 121634593468176056466869 11403243137641505293769)
          ·
            refine ⟨8552432353231128970327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11403243137641505293769 8552432353231128970327)
            ·
              refine ⟨12828648529846693455491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8552432353231128970327 12828648529846693455491)
              ·
                refine ⟨19242972794770040183237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12828648529846693455491 19242972794770040183237)
                ·
                  refine ⟨3608057399019382534357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19242972794770040183237 3608057399019382534357)
                  ·
                    rfl

theorem cell20_7905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_7905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7905 prefixEnd_7905 := by exact prefixLift 7905
  have htrace : WordTrace (prefixWord ++ tailWord_7905) baseStart_7905 baseEnd_7905 := by
    simpa [prefixWord, tailWord_7905, baseEnd_7905] using wordTrace_append hprefix tailTrace_7905
  have hstable : (prefixWord ++ tailWord_7905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7905).length < 2 ^ (prefixWord ++ tailWord_7905).sum := by decide
  have hdescent : baseEnd_7905 < baseStart_7905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7916 : List Nat := [2, 2, 1, 1, 2, 2, 3, 7]
def baseStart_7916 : Nat := 118140960795 + 7916 * 2 ^ 59
def prefixEnd_7916 : Nat := 4983230072969 + 3 ^ 40 * 7916 * 2
def baseEnd_7916 : Nat := 1204359366250744389215

theorem tailTrace_7916 : CollatzResearch.WordTrace tailWord_7916 prefixEnd_7916 1204359366250744389215 := by
  unfold tailWord_7916
  simp only [CollatzResearch.WordTrace]
  refine ⟨144360119664579395137801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 192480159552772526850401 144360119664579395137801)
  ·
    refine ⟨108270089748434546353351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 144360119664579395137801 108270089748434546353351)
    ·
      refine ⟨162405134622651819530027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108270089748434546353351 162405134622651819530027)
      ·
        refine ⟨243607701933977729295041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162405134622651819530027 243607701933977729295041)
        ·
          refine ⟨182705776450483296971281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243607701933977729295041 182705776450483296971281)
          ·
            refine ⟨137029332337862472728461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 182705776450483296971281 137029332337862472728461)
            ·
              refine ⟨51385999626698427273173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137029332337862472728461 51385999626698427273173)
              ·
                refine ⟨1204359366250744389215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51385999626698427273173 1204359366250744389215)
                ·
                  rfl

theorem cell20_7916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_7916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7916 prefixEnd_7916 := by exact prefixLift 7916
  have htrace : WordTrace (prefixWord ++ tailWord_7916) baseStart_7916 baseEnd_7916 := by
    simpa [prefixWord, tailWord_7916, baseEnd_7916] using wordTrace_append hprefix tailTrace_7916
  have hstable : (prefixWord ++ tailWord_7916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7916).length < 2 ^ (prefixWord ++ tailWord_7916).sum := by decide
  have hdescent : baseEnd_7916 < baseStart_7916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7949 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7949 : Nat := 118140960795 + 7949 * 2 ^ 59
def prefixEnd_7949 : Nat := 4983230072969 + 3 ^ 40 * 7949 * 2
def baseEnd_7949 : Nat := 3628140197950785067511

theorem tailTrace_7949 : CollatzResearch.WordTrace tailWord_7949 prefixEnd_7949 3628140197950785067511 := by
  unfold tailWord_7949
  simp only [CollatzResearch.WordTrace]
  refine ⟨289923848209605426226901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193282565473070284151267 289923848209605426226901)
  ·
    refine ⟨6795090192412627177193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 289923848209605426226901 6795090192412627177193)
    ·
      refine ⟨5096317644309470382895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6795090192412627177193 5096317644309470382895)
      ·
        refine ⟨7644476466464205574343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096317644309470382895 7644476466464205574343)
        ·
          refine ⟨11466714699696308361515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644476466464205574343 11466714699696308361515)
          ·
            refine ⟨17200072049544462542273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11466714699696308361515 17200072049544462542273)
            ·
              refine ⟨12900054037158346906705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17200072049544462542273 12900054037158346906705)
              ·
                refine ⟨9675040527868760180029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12900054037158346906705 9675040527868760180029)
                ·
                  refine ⟨3628140197950785067511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9675040527868760180029 3628140197950785067511)
                  ·
                    rfl

theorem cell20_7949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7949 prefixEnd_7949 := by exact prefixLift 7949
  have htrace : WordTrace (prefixWord ++ tailWord_7949) baseStart_7949 baseEnd_7949 := by
    simpa [prefixWord, tailWord_7949, baseEnd_7949] using wordTrace_append hprefix tailTrace_7949
  have hstable : (prefixWord ++ tailWord_7949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7949).length < 2 ^ (prefixWord ++ tailWord_7949).sum := by decide
  have hdescent : baseEnd_7949 < baseStart_7949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7956 : List Nat := [2, 4, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7956 : Nat := 118140960795 + 7956 * 2 ^ 59
def prefixEnd_7956 : Nat := 4983230072969 + 3 ^ 40 * 7956 * 2
def baseEnd_7956 : Nat := 3631335188689871834149

theorem tailTrace_7956 : CollatzResearch.WordTrace tailWord_7956 prefixEnd_7956 3631335188689871834149 := by
  unfold tailWord_7956
  simp only [CollatzResearch.WordTrace]
  refine ⟨145089579592122810865861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 193452772789497081154481 145089579592122810865861)
  ·
    refine ⟨27204296173523027037349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 145089579592122810865861 27204296173523027037349)
    ·
      refine ⟨5100805532535567569503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27204296173523027037349 5100805532535567569503)
      ·
        refine ⟨7651208298803351354255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5100805532535567569503 7651208298803351354255)
        ·
          refine ⟨11476812448205027031383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7651208298803351354255 11476812448205027031383)
          ·
            refine ⟨17215218672307540547075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11476812448205027031383 17215218672307540547075)
            ·
              refine ⟨25822828008461310820613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17215218672307540547075 25822828008461310820613)
              ·
                refine ⟨4841780251586495778865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25822828008461310820613 4841780251586495778865)
                ·
                  refine ⟨3631335188689871834149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4841780251586495778865 3631335188689871834149)
                  ·
                    rfl

theorem cell20_7956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7956 prefixEnd_7956 := by exact prefixLift 7956
  have htrace : WordTrace (prefixWord ++ tailWord_7956) baseStart_7956 baseEnd_7956 := by
    simpa [prefixWord, tailWord_7956, baseEnd_7956] using wordTrace_append hprefix tailTrace_7956
  have hstable : (prefixWord ++ tailWord_7956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7956).length < 2 ^ (prefixWord ++ tailWord_7956).sum := by decide
  have hdescent : baseEnd_7956 < baseStart_7956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7957 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_7957 : Nat := 118140960795 + 7957 * 2 ^ 59
def prefixEnd_7957 : Nat := 4983230072969 + 3 ^ 40 * 7957 * 2
def baseEnd_7957 : Nat := 3631791615938312800811

theorem tailTrace_7957 : CollatzResearch.WordTrace tailWord_7957 prefixEnd_7957 3631791615938312800811 := by
  unfold tailWord_7957
  simp only [CollatzResearch.WordTrace]
  refine ⟨290215632180622792518125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193477088120415195012083 290215632180622792518125)
  ·
    refine ⟨108830862067733547194297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 290215632180622792518125 108830862067733547194297)
    ·
      refine ⟨81623146550800160395723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108830862067733547194297 81623146550800160395723)
      ·
        refine ⟨122434719826200240593585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81623146550800160395723 122434719826200240593585)
        ·
          refine ⟨91826039869650180445189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122434719826200240593585 91826039869650180445189)
          ·
            refine ⟨17217382475559408833473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91826039869650180445189 17217382475559408833473)
            ·
              refine ⟨12913036856669556625105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17217382475559408833473 12913036856669556625105)
              ·
                refine ⟨9684777642502167468829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12913036856669556625105 9684777642502167468829)
                ·
                  refine ⟨3631791615938312800811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9684777642502167468829 3631791615938312800811)
                  ·
                    rfl

theorem cell20_7957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_7957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7957 prefixEnd_7957 := by exact prefixLift 7957
  have htrace : WordTrace (prefixWord ++ tailWord_7957) baseStart_7957 baseEnd_7957 := by
    simpa [prefixWord, tailWord_7957, baseEnd_7957] using wordTrace_append hprefix tailTrace_7957
  have hstable : (prefixWord ++ tailWord_7957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7957).length < 2 ^ (prefixWord ++ tailWord_7957).sum := by decide
  have hdescent : baseEnd_7957 < baseStart_7957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7961 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_7961 : Nat := 118140960795 + 7961 * 2 ^ 59
def prefixEnd_7961 : Nat := 4983230072969 + 3 ^ 40 * 7961 * 2
def baseEnd_7961 : Nat := 3633617324932076667461

theorem tailTrace_7961 : CollatzResearch.WordTrace tailWord_7961 prefixEnd_7961 3633617324932076667461 := by
  unfold tailWord_7961
  simp only [CollatzResearch.WordTrace]
  refine ⟨290361524166131475663737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 193574349444087650442491 290361524166131475663737)
  ·
    refine ⟨217771143124598606747803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 290361524166131475663737 217771143124598606747803)
    ·
      refine ⟨326656714686897910121705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 217771143124598606747803 326656714686897910121705)
      ·
        refine ⟨244992536015173432591279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 326656714686897910121705 244992536015173432591279)
        ·
          refine ⟨367488804022760148886919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244992536015173432591279 367488804022760148886919)
          ·
            refine ⟨551233206034140223330379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367488804022760148886919 551233206034140223330379)
            ·
              refine ⟨826849809051210334995569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551233206034140223330379 826849809051210334995569)
              ·
                refine ⟨620137356788407751246677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826849809051210334995569 620137356788407751246677)
                ·
                  refine ⟨3633617324932076667461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 620137356788407751246677 3633617324932076667461)
                  ·
                    rfl

theorem cell20_7961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_7961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7961 prefixEnd_7961 := by exact prefixLift 7961
  have htrace : WordTrace (prefixWord ++ tailWord_7961) baseStart_7961 baseEnd_7961 := by
    simpa [prefixWord, tailWord_7961, baseEnd_7961] using wordTrace_append hprefix tailTrace_7961
  have hstable : (prefixWord ++ tailWord_7961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7961).length < 2 ^ (prefixWord ++ tailWord_7961).sum := by decide
  have hdescent : baseEnd_7961 < baseStart_7961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7985 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_7985 : Nat := 118140960795 + 7985 * 2 ^ 59
def prefixEnd_7985 : Nat := 4983230072969 + 3 ^ 40 * 7985 * 2
def baseEnd_7985 : Nat := 3644571578894659867363

theorem tailTrace_7985 : CollatzResearch.WordTrace tailWord_7985 prefixEnd_7985 3644571578894659867363 := by
  unfold tailWord_7985
  simp only [CollatzResearch.WordTrace]
  refine ⟨291236876079183574537409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 194157917386122383024939 291236876079183574537409)
  ·
    refine ⟨218427657059387680903057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 291236876079183574537409 218427657059387680903057)
    ·
      refine ⟨163820742794540760677293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 218427657059387680903057 163820742794540760677293)
      ·
        refine ⟨61432778547952785253985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 163820742794540760677293 61432778547952785253985)
        ·
          refine ⟨46074583910964588940489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61432778547952785253985 46074583910964588940489)
          ·
            refine ⟨34555937933223441705367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46074583910964588940489 34555937933223441705367)
            ·
              refine ⟨51833906899835162558051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34555937933223441705367 51833906899835162558051)
              ·
                refine ⟨77750860349752743837077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51833906899835162558051 77750860349752743837077)
                ·
                  refine ⟨3644571578894659867363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 77750860349752743837077 3644571578894659867363)
                  ·
                    rfl

theorem cell20_7985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_7985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7985 prefixEnd_7985 := by exact prefixLift 7985
  have htrace : WordTrace (prefixWord ++ tailWord_7985) baseStart_7985 baseEnd_7985 := by
    simpa [prefixWord, tailWord_7985, baseEnd_7985] using wordTrace_append hprefix tailTrace_7985
  have hstable : (prefixWord ++ tailWord_7985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7985).length < 2 ^ (prefixWord ++ tailWord_7985).sum := by decide
  have hdescent : baseEnd_7985 < baseStart_7985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7998 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7998 : Nat := 118140960795 + 7998 * 2 ^ 59
def prefixEnd_7998 : Nat := 4983230072969 + 3 ^ 40 * 7998 * 2
def baseEnd_7998 : Nat := 3650505133124392433977

theorem tailTrace_7998 : CollatzResearch.WordTrace tailWord_7998 prefixEnd_7998 3650505133124392433977 := by
  unfold tailWord_7998
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463878129010849345081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 194474016688057863173765 36463878129010849345081)
  ·
    refine ⟨27347908596758137008811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36463878129010849345081 27347908596758137008811)
    ·
      refine ⟨41021862895137205513217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27347908596758137008811 41021862895137205513217)
      ·
        refine ⟨30766397171352904134913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41021862895137205513217 30766397171352904134913)
        ·
          refine ⟨23074797878514678101185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30766397171352904134913 23074797878514678101185)
          ·
            refine ⟨17306098408886008575889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23074797878514678101185 17306098408886008575889)
            ·
              refine ⟨12979573806664506431917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17306098408886008575889 12979573806664506431917)
              ·
                refine ⟨4867340177499189911969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12979573806664506431917 4867340177499189911969)
                ·
                  refine ⟨3650505133124392433977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4867340177499189911969 3650505133124392433977)
                  ·
                    rfl

theorem cell20_7998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_7998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_7998 prefixEnd_7998 := by exact prefixLift 7998
  have htrace : WordTrace (prefixWord ++ tailWord_7998) baseStart_7998 baseEnd_7998 := by
    simpa [prefixWord, tailWord_7998, baseEnd_7998] using wordTrace_append hprefix tailTrace_7998
  have hstable : (prefixWord ++ tailWord_7998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7998).length < 2 ^ (prefixWord ++ tailWord_7998).sum := by decide
  have hdescent : baseEnd_7998 < baseStart_7998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8012 : List Nat := [2, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_8012 : Nat := 118140960795 + 8012 * 2 ^ 59
def prefixEnd_8012 : Nat := 4983230072969 + 3 ^ 40 * 8012 * 2
def baseEnd_8012 : Nat := 3656895114602565967253

theorem tailTrace_8012 : CollatzResearch.WordTrace tailWord_8012 prefixEnd_8012 3656895114602565967253 := by
  unfold tailWord_8012
  simp only [CollatzResearch.WordTrace]
  refine ⟨146110823490683592885145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 194814431320911457180193 146110823490683592885145)
  ·
    refine ⟨109583117618012694663859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146110823490683592885145 109583117618012694663859)
    ·
      refine ⟨164374676427019041995789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109583117618012694663859 164374676427019041995789)
      ·
        refine ⟨61640503660132140748421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164374676427019041995789 61640503660132140748421)
        ·
          refine ⟨11557594436274776390329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61640503660132140748421 11557594436274776390329)
          ·
            refine ⟨8668195827206082292747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11557594436274776390329 8668195827206082292747)
            ·
              refine ⟨13002293740809123439121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8668195827206082292747 13002293740809123439121)
              ·
                refine ⟨9751720305606842579341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13002293740809123439121 9751720305606842579341)
                ·
                  refine ⟨3656895114602565967253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9751720305606842579341 3656895114602565967253)
                  ·
                    rfl

theorem cell20_8012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_8012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8012 prefixEnd_8012 := by exact prefixLift 8012
  have htrace : WordTrace (prefixWord ++ tailWord_8012) baseStart_8012 baseEnd_8012 := by
    simpa [prefixWord, tailWord_8012, baseEnd_8012] using wordTrace_append hprefix tailTrace_8012
  have hstable : (prefixWord ++ tailWord_8012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8012).length < 2 ^ (prefixWord ++ tailWord_8012).sum := by decide
  have hdescent : baseEnd_8012 < baseStart_8012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8033 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 3]
def baseStart_8033 : Nat := 118140960795 + 8033 * 2 ^ 59
def prefixEnd_8033 : Nat := 4983230072969 + 3 ^ 40 * 8033 * 2
def baseEnd_8033 : Nat := 3666480086819826267167

theorem tailTrace_8033 : CollatzResearch.WordTrace tailWord_8033 prefixEnd_8033 3666480086819826267167 := by
  unfold tailWord_8033
  simp only [CollatzResearch.WordTrace]
  refine ⟨292987579905287772284753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195325053270191848189835 292987579905287772284753)
  ·
    refine ⟨219740684928965829213565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 292987579905287772284753 219740684928965829213565)
    ·
      refine ⟨82402756848362185955087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219740684928965829213565 82402756848362185955087)
      ·
        refine ⟨123604135272543278932631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82402756848362185955087 123604135272543278932631)
        ·
          refine ⟨185406202908814918398947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123604135272543278932631 185406202908814918398947)
          ·
            refine ⟨278109304363222377598421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185406202908814918398947 278109304363222377598421)
            ·
              refine ⟨6518186821013024474963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278109304363222377598421 6518186821013024474963)
              ·
                refine ⟨9777280231519536712445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518186821013024474963 9777280231519536712445)
                ·
                  refine ⟨3666480086819826267167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9777280231519536712445 3666480086819826267167)
                  ·
                    rfl

theorem cell20_8033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_8033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8033 prefixEnd_8033 := by exact prefixLift 8033
  have htrace : WordTrace (prefixWord ++ tailWord_8033) baseStart_8033 baseEnd_8033 := by
    simpa [prefixWord, tailWord_8033, baseEnd_8033] using wordTrace_append hprefix tailTrace_8033
  have hstable : (prefixWord ++ tailWord_8033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8033).length < 2 ^ (prefixWord ++ tailWord_8033).sum := by decide
  have hdescent : baseEnd_8033 < baseStart_8033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8068 : List Nat := [2, 3, 2, 1, 1, 1, 10]
def baseStart_8068 : Nat := 118140960795 + 8068 * 2 ^ 59
def prefixEnd_8068 : Nat := 4983230072969 + 3 ^ 40 * 8068 * 2
def baseEnd_8068 : Nat := 409161671168362233373

theorem tailTrace_8068 : CollatzResearch.WordTrace tailWord_8068 prefixEnd_8068 409161671168362233373 := by
  unfold tailWord_8068
  simp only [CollatzResearch.WordTrace]
  refine ⟨147132067389244374904429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196176089852325833205905 147132067389244374904429)
  ·
    refine ⟨55174525270966640589161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147132067389244374904429 55174525270966640589161)
    ·
      refine ⟨41380893953224980441871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55174525270966640589161 41380893953224980441871)
      ·
        refine ⟨62071340929837470662807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41380893953224980441871 62071340929837470662807)
        ·
          refine ⟨93107011394756205994211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62071340929837470662807 93107011394756205994211)
          ·
            refine ⟨139660517092134308991317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93107011394756205994211 139660517092134308991317)
            ·
              refine ⟨409161671168362233373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 139660517092134308991317 409161671168362233373)
              ·
                rfl

theorem cell20_8068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_8068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8068 prefixEnd_8068 := by exact prefixLift 8068
  have htrace : WordTrace (prefixWord ++ tailWord_8068) baseStart_8068 baseEnd_8068 := by
    simpa [prefixWord, tailWord_8068, baseEnd_8068] using wordTrace_append hprefix tailTrace_8068
  have hstable : (prefixWord ++ tailWord_8068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8068).length < 2 ^ (prefixWord ++ tailWord_8068).sum := by decide
  have hdescent : baseEnd_8068 < baseStart_8068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_8074 : Nat := 118140960795 + 8074 * 2 ^ 59
def prefixEnd_8074 : Nat := 4983230072969 + 3 ^ 40 * 8074 * 2
def baseEnd_8074 : Nat := 3685193604005905900333

theorem tailTrace_8074 : CollatzResearch.WordTrace tailWord_8074 prefixEnd_8074 3685193604005905900333 := by
  unfold tailWord_8074
  simp only [CollatzResearch.WordTrace]
  refine ⟨73620743189187943631819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196321981837834516351517 73620743189187943631819)
  ·
    refine ⟨110431114783781915447729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73620743189187943631819 110431114783781915447729)
    ·
      refine ⟨82823336087836436585797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110431114783781915447729 82823336087836436585797)
      ·
        refine ⟨15529375516469331859837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82823336087836436585797 15529375516469331859837)
        ·
          refine ⟨5823515818675999447439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15529375516469331859837 5823515818675999447439)
          ·
            refine ⟨8735273728013999171159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823515818675999447439 8735273728013999171159)
            ·
              refine ⟨13102910592020998756739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735273728013999171159 13102910592020998756739)
              ·
                refine ⟨19654365888031498135109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13102910592020998756739 19654365888031498135109)
                ·
                  refine ⟨3685193604005905900333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19654365888031498135109 3685193604005905900333)
                  ·
                    rfl

theorem cell20_8074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_8074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8074 prefixEnd_8074 := by exact prefixLift 8074
  have htrace : WordTrace (prefixWord ++ tailWord_8074) baseStart_8074 baseEnd_8074 := by
    simpa [prefixWord, tailWord_8074, baseEnd_8074] using wordTrace_append hprefix tailTrace_8074
  have hstable : (prefixWord ++ tailWord_8074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074).length < 2 ^ (prefixWord ++ tailWord_8074).sum := by decide
  have hdescent : baseEnd_8074 < baseStart_8074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8088 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_8088 : Nat := 118140960795 + 8088 * 2 ^ 59
def prefixEnd_8088 : Nat := 4983230072969 + 3 ^ 40 * 8088 * 2
def baseEnd_8088 : Nat := 3691583585484079433609

theorem tailTrace_8088 : CollatzResearch.WordTrace tailWord_8088 prefixEnd_8088 3691583585484079433609 := by
  unfold tailWord_8088
  simp only [CollatzResearch.WordTrace]
  refine ⟨147496797353016082768459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196662396470688110357945 147496797353016082768459)
  ·
    refine ⟨221245196029524124152689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147496797353016082768459 221245196029524124152689)
    ·
      refine ⟨165933897022143093114517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221245196029524124152689 165933897022143093114517)
      ·
        refine ⟨7778151422912957489743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165933897022143093114517 7778151422912957489743)
        ·
          refine ⟨11667227134369436234615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778151422912957489743 11667227134369436234615)
          ·
            refine ⟨17500840701554154351923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11667227134369436234615 17500840701554154351923)
            ·
              refine ⟨26251261052331231527885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500840701554154351923 26251261052331231527885)
              ·
                refine ⟨9844222894624211822957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26251261052331231527885 9844222894624211822957)
                ·
                  refine ⟨3691583585484079433609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9844222894624211822957 3691583585484079433609)
                  ·
                    rfl

theorem cell20_8088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_8088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8088 prefixEnd_8088 := by exact prefixLift 8088
  have htrace : WordTrace (prefixWord ++ tailWord_8088) baseStart_8088 baseEnd_8088 := by
    simpa [prefixWord, tailWord_8088, baseEnd_8088] using wordTrace_append hprefix tailTrace_8088
  have hstable : (prefixWord ++ tailWord_8088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8088).length < 2 ^ (prefixWord ++ tailWord_8088).sum := by decide
  have hdescent : baseEnd_8088 < baseStart_8088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8144 : List Nat := [2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_8144 : Nat := 118140960795 + 8144 * 2 ^ 59
def prefixEnd_8144 : Nat := 4983230072969 + 3 ^ 40 * 8144 * 2
def baseEnd_8144 : Nat := 1239047837132257855571

theorem tailTrace_8144 : CollatzResearch.WordTrace tailWord_8144 prefixEnd_8144 1239047837132257855571 := by
  unfold tailWord_8144
  simp only [CollatzResearch.WordTrace]
  refine ⟨148518041251576864787743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 198024055002102486383657 148518041251576864787743)
  ·
    refine ⟨222777061877365297181615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148518041251576864787743 222777061877365297181615)
    ·
      refine ⟨334165592816047945772423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222777061877365297181615 334165592816047945772423)
      ·
        refine ⟨501248389224071918658635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334165592816047945772423 501248389224071918658635)
        ·
          refine ⟨751872583836107877987953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501248389224071918658635 751872583836107877987953)
          ·
            refine ⟨563904437877080908490965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751872583836107877987953 563904437877080908490965)
            ·
              refine ⟨13216510262744083792757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 563904437877080908490965 13216510262744083792757)
              ·
                refine ⟨1239047837132257855571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13216510262744083792757 1239047837132257855571)
                ·
                  rfl

theorem cell20_8144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_8144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8144 prefixEnd_8144 := by exact prefixLift 8144
  have htrace : WordTrace (prefixWord ++ tailWord_8144) baseStart_8144 baseEnd_8144 := by
    simpa [prefixWord, tailWord_8144, baseEnd_8144] using wordTrace_append hprefix tailTrace_8144
  have hstable : (prefixWord ++ tailWord_8144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8144).length < 2 ^ (prefixWord ++ tailWord_8144).sum := by decide
  have hdescent : baseEnd_8144 < baseStart_8144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8154 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_8154 : Nat := 118140960795 + 8154 * 2 ^ 59
def prefixEnd_8154 : Nat := 4983230072969 + 3 ^ 40 * 8154 * 2
def baseEnd_8154 : Nat := 3721707783881183233339

theorem tailTrace_8154 : CollatzResearch.WordTrace tailWord_8154 prefixEnd_8154 3721707783881183233339 := by
  unfold tailWord_8154
  simp only [CollatzResearch.WordTrace]
  refine ⟨74350203116731359359879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 198267208311283624959677 74350203116731359359879)
  ·
    refine ⟨111525304675097039039819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74350203116731359359879 111525304675097039039819)
    ·
      refine ⟨167287957012645558559729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111525304675097039039819 167287957012645558559729)
      ·
        refine ⟨125465967759484168919797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167287957012645558559729 125465967759484168919797)
        ·
          refine ⟨11762434477451640836231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125465967759484168919797 11762434477451640836231)
          ·
            refine ⟨17643651716177461254347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11762434477451640836231 17643651716177461254347)
            ·
              refine ⟨26465477574266191881521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643651716177461254347 26465477574266191881521)
              ·
                refine ⟨19849108180699643911141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26465477574266191881521 19849108180699643911141)
                ·
                  refine ⟨3721707783881183233339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19849108180699643911141 3721707783881183233339)
                  ·
                    rfl

theorem cell20_8154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_8154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8154 prefixEnd_8154 := by exact prefixLift 8154
  have htrace : WordTrace (prefixWord ++ tailWord_8154) baseStart_8154 baseEnd_8154 := by
    simpa [prefixWord, tailWord_8154, baseEnd_8154] using wordTrace_append hprefix tailTrace_8154
  have hstable : (prefixWord ++ tailWord_8154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8154).length < 2 ^ (prefixWord ++ tailWord_8154).sum := by decide
  have hdescent : baseEnd_8154 < baseStart_8154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 3]
def baseStart_8185 : Nat := 118140960795 + 8185 * 2 ^ 59
def prefixEnd_8185 : Nat := 4983230072969 + 3 ^ 40 * 8185 * 2
def baseEnd_8185 : Nat := 3735857028582853199879

theorem tailTrace_8185 : CollatzResearch.WordTrace tailWord_8185 prefixEnd_8185 3735857028582853199879 := by
  unfold tailWord_8185
  simp only [CollatzResearch.WordTrace]
  refine ⟨298531475354617731818009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199020983569745154545339 298531475354617731818009)
  ·
    refine ⟨223898606515963298863507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298531475354617731818009 223898606515963298863507)
    ·
      refine ⟨335847909773944948295261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223898606515963298863507 335847909773944948295261)
      ·
        refine ⟨125942966165229355610723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335847909773944948295261 125942966165229355610723)
        ·
          refine ⟨188914449247844033416085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125942966165229355610723 188914449247844033416085)
          ·
            refine ⟨8855364808492689066379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188914449247844033416085 8855364808492689066379)
            ·
              refine ⟨13283047212739033599569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855364808492689066379 13283047212739033599569)
              ·
                refine ⟨9962285409554275199677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13283047212739033599569 9962285409554275199677)
                ·
                  refine ⟨3735857028582853199879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9962285409554275199677 3735857028582853199879)
                  ·
                    rfl

theorem cell20_8185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_8185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8185 prefixEnd_8185 := by exact prefixLift 8185
  have htrace : WordTrace (prefixWord ++ tailWord_8185) baseStart_8185 baseEnd_8185 := by
    simpa [prefixWord, tailWord_8185, baseEnd_8185] using wordTrace_append hprefix tailTrace_8185
  have hstable : (prefixWord ++ tailWord_8185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185).length < 2 ^ (prefixWord ++ tailWord_8185).sum := by decide
  have hdescent : baseEnd_8185 < baseStart_8185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_8202 : Nat := 118140960795 + 8202 * 2 ^ 59
def prefixEnd_8202 : Nat := 4983230072969 + 3 ^ 40 * 8202 * 2
def baseEnd_8202 : Nat := 3743616291806349633143

theorem tailTrace_8202 : CollatzResearch.WordTrace tailWord_8202 prefixEnd_8202 3743616291806349633143 := by
  unfold tailWord_8202
  simp only [CollatzResearch.WordTrace]
  refine ⟨74787879073257408796715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199434344195353090124573 74787879073257408796715)
  ·
    refine ⟨112181818609886113195073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74787879073257408796715 112181818609886113195073)
    ·
      refine ⟨84136363957414584896305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112181818609886113195073 84136363957414584896305)
      ·
        refine ⟨63102272968060938672229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84136363957414584896305 63102272968060938672229)
        ·
          refine ⟨11831676181511426001043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63102272968060938672229 11831676181511426001043)
          ·
            refine ⟨17747514272267139001565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831676181511426001043 17747514272267139001565)
            ·
              refine ⟨6655317852100177125587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17747514272267139001565 6655317852100177125587)
              ·
                refine ⟨9982976778150265688381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655317852100177125587 9982976778150265688381)
                ·
                  refine ⟨3743616291806349633143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9982976778150265688381 3743616291806349633143)
                  ·
                    rfl

theorem cell20_8202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_8202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8202 prefixEnd_8202 := by exact prefixLift 8202
  have htrace : WordTrace (prefixWord ++ tailWord_8202) baseStart_8202 baseEnd_8202 := by
    simpa [prefixWord, tailWord_8202, baseEnd_8202] using wordTrace_append hprefix tailTrace_8202
  have hstable : (prefixWord ++ tailWord_8202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202).length < 2 ^ (prefixWord ++ tailWord_8202).sum := by decide
  have hdescent : baseEnd_8202 < baseStart_8202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8212 : List Nat := [2, 4, 3, 2, 1, 2, 2, 4]
def baseStart_8212 : Nat := 118140960795 + 8212 * 2 ^ 59
def prefixEnd_8212 : Nat := 4983230072969 + 3 ^ 40 * 8212 * 2
def baseEnd_8212 : Nat := 1249393521430253099923

theorem tailTrace_8212 : CollatzResearch.WordTrace tailWord_8212 prefixEnd_8212 1249393521430253099923 := by
  unfold tailWord_8212
  simp only [CollatzResearch.WordTrace]
  refine ⟨149758123128400671525445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199677497504534228700593 149758123128400671525445)
  ·
    refine ⟨28079648086575125911021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149758123128400671525445 28079648086575125911021)
    ·
      refine ⟨10529868032465672216633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28079648086575125911021 10529868032465672216633)
      ·
        refine ⟨7897401024349254162475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10529868032465672216633 7897401024349254162475)
        ·
          refine ⟨11846101536523881243713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7897401024349254162475 11846101536523881243713)
          ·
            refine ⟨8884576152392910932785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11846101536523881243713 8884576152392910932785)
            ·
              refine ⟨6663432114294683199589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884576152392910932785 6663432114294683199589)
              ·
                refine ⟨1249393521430253099923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6663432114294683199589 1249393521430253099923)
                ·
                  rfl

theorem cell20_8212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 4].length) (baseStart_8212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8212 prefixEnd_8212 := by exact prefixLift 8212
  have htrace : WordTrace (prefixWord ++ tailWord_8212) baseStart_8212 baseEnd_8212 := by
    simpa [prefixWord, tailWord_8212, baseEnd_8212] using wordTrace_append hprefix tailTrace_8212
  have hstable : (prefixWord ++ tailWord_8212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8212).length < 2 ^ (prefixWord ++ tailWord_8212).sum := by decide
  have hdescent : baseEnd_8212 < baseStart_8212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8227 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_8227 : Nat := 118140960795 + 8227 * 2 ^ 59
def prefixEnd_8227 : Nat := 4983230072969 + 3 ^ 40 * 8227 * 2
def baseEnd_8227 : Nat := 3755026973017373799707

theorem tailTrace_8227 : CollatzResearch.WordTrace tailWord_8227 prefixEnd_8227 3755026973017373799707 := by
  unfold tailWord_8227
  simp only [CollatzResearch.WordTrace]
  refine ⟨300063341202458904846935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 200042227468305936564623 300063341202458904846935)
  ·
    refine ⟨450095011803688357270403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300063341202458904846935 450095011803688357270403)
    ·
      refine ⟨675142517705532535905605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450095011803688357270403 675142517705532535905605)
      ·
        refine ⟨126589222069787350482301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 675142517705532535905605 126589222069787350482301)
        ·
          refine ⟨47470958276170256430863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126589222069787350482301 47470958276170256430863)
          ·
            refine ⟨71206437414255384646295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47470958276170256430863 71206437414255384646295)
            ·
              refine ⟨106809656121383076969443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71206437414255384646295 106809656121383076969443)
              ·
                refine ⟨160214484182074615454165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106809656121383076969443 160214484182074615454165)
                ·
                  refine ⟨3755026973017373799707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 160214484182074615454165 3755026973017373799707)
                  ·
                    rfl

theorem cell20_8227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_8227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8227 prefixEnd_8227 := by exact prefixLift 8227
  have htrace : WordTrace (prefixWord ++ tailWord_8227) baseStart_8227 baseEnd_8227 := by
    simpa [prefixWord, tailWord_8227, baseEnd_8227] using wordTrace_append hprefix tailTrace_8227
  have hstable : (prefixWord ++ tailWord_8227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8227).length < 2 ^ (prefixWord ++ tailWord_8227).sum := by decide
  have hdescent : baseEnd_8227 < baseStart_8227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8254 : List Nat := [4, 2, 1, 3, 2, 1, 2, 5]
def baseStart_8254 : Nat := 118140960795 + 8254 * 2 ^ 59
def prefixEnd_8254 : Nat := 4983230072969 + 3 ^ 40 * 8254 * 2
def baseEnd_8254 : Nat := 1255783502908426633199

theorem tailTrace_8254 : CollatzResearch.WordTrace tailWord_8254 prefixEnd_8254 1255783502908426633199 := by
  unfold tailWord_8254
  simp only [CollatzResearch.WordTrace]
  refine ⟨37631014013080314509977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 200698741403095010719877 37631014013080314509977)
  ·
    refine ⟨28223260509810235882483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37631014013080314509977 28223260509810235882483)
    ·
      refine ⟨42334890764715353823725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28223260509810235882483 42334890764715353823725)
      ·
        refine ⟨15875584036768257683897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42334890764715353823725 15875584036768257683897)
        ·
          refine ⟨11906688027576193262923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15875584036768257683897 11906688027576193262923)
          ·
            refine ⟨17860032041364289894385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11906688027576193262923 17860032041364289894385)
            ·
              refine ⟨13395024031023217420789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17860032041364289894385 13395024031023217420789)
              ·
                refine ⟨1255783502908426633199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13395024031023217420789 1255783502908426633199)
                ·
                  rfl

theorem cell20_8254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_8254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8254 prefixEnd_8254 := by exact prefixLift 8254
  have htrace : WordTrace (prefixWord ++ tailWord_8254) baseStart_8254 baseEnd_8254 := by
    simpa [prefixWord, tailWord_8254, baseEnd_8254] using wordTrace_append hprefix tailTrace_8254
  have hstable : (prefixWord ++ tailWord_8254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8254).length < 2 ^ (prefixWord ++ tailWord_8254).sum := by decide
  have hdescent : baseEnd_8254 < baseStart_8254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8313 : List Nat := [1, 2, 1, 3, 4, 3, 1, 5]
def baseStart_8313 : Nat := 118140960795 + 8313 * 2 ^ 59
def prefixEnd_8313 : Nat := 4983230072969 + 3 ^ 40 * 8313 * 2
def baseEnd_8313 : Nat := 1264759905461098977563

theorem tailTrace_8313 : CollatzResearch.WordTrace tailWord_8313 prefixEnd_8313 1264759905461098977563 := by
  unfold tailWord_8313
  simp only [CollatzResearch.WordTrace]
  refine ⟨303200018890895592477593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202133345927263728318395 303200018890895592477593)
  ·
    refine ⟨227400014168171694358195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303200018890895592477593 227400014168171694358195)
    ·
      refine ⟨341100021252257541537293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227400014168171694358195 341100021252257541537293)
      ·
        refine ⟨127912507969596578076485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341100021252257541537293 127912507969596578076485)
        ·
          refine ⟨23983595244299358389341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127912507969596578076485 23983595244299358389341)
          ·
            refine ⟨8993848216612259396003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23983595244299358389341 8993848216612259396003)
            ·
              refine ⟨13490772324918389094005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993848216612259396003 13490772324918389094005)
              ·
                refine ⟨1264759905461098977563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13490772324918389094005 1264759905461098977563)
                ·
                  rfl

theorem cell20_8313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 5].length) (baseStart_8313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8313 prefixEnd_8313 := by exact prefixLift 8313
  have htrace : WordTrace (prefixWord ++ tailWord_8313) baseStart_8313 baseEnd_8313 := by
    simpa [prefixWord, tailWord_8313, baseEnd_8313] using wordTrace_append hprefix tailTrace_8313
  have hstable : (prefixWord ++ tailWord_8313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8313).length < 2 ^ (prefixWord ++ tailWord_8313).sum := by decide
  have hdescent : baseEnd_8313 < baseStart_8313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8341 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_8341 : Nat := 118140960795 + 8341 * 2 ^ 59
def prefixEnd_8341 : Nat := 4983230072969 + 3 ^ 40 * 8341 * 2
def baseEnd_8341 : Nat := 3807059679339643999241

theorem tailTrace_8341 : CollatzResearch.WordTrace tailWord_8341 prefixEnd_8341 3807059679339643999241 := by
  unfold tailWord_8341
  simp only [CollatzResearch.WordTrace]
  refine ⟨304221262789456374496877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202814175192970916331251 304221262789456374496877)
  ·
    refine ⟨114082973546046140436329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304221262789456374496877 114082973546046140436329)
    ·
      refine ⟨85562230159534605327247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114082973546046140436329 85562230159534605327247)
      ·
        refine ⟨128343345239301907990871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85562230159534605327247 128343345239301907990871)
        ·
          refine ⟨192515017858952861986307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128343345239301907990871 192515017858952861986307)
          ·
            refine ⟨288772526788429292979461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192515017858952861986307 288772526788429292979461)
            ·
              refine ⟨54144848772830492433649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288772526788429292979461 54144848772830492433649)
              ·
                refine ⟨40608636579622869325237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54144848772830492433649 40608636579622869325237)
                ·
                  refine ⟨3807059679339643999241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40608636579622869325237 3807059679339643999241)
                  ·
                    rfl

theorem cell20_8341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_8341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8341 prefixEnd_8341 := by exact prefixLift 8341
  have htrace : WordTrace (prefixWord ++ tailWord_8341) baseStart_8341 baseEnd_8341 := by
    simpa [prefixWord, tailWord_8341, baseEnd_8341] using wordTrace_append hprefix tailTrace_8341
  have hstable : (prefixWord ++ tailWord_8341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8341).length < 2 ^ (prefixWord ++ tailWord_8341).sum := by decide
  have hdescent : baseEnd_8341 < baseStart_8341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8354 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_8354 : Nat := 118140960795 + 8354 * 2 ^ 59
def prefixEnd_8354 : Nat := 4983230072969 + 3 ^ 40 * 8354 * 2
def baseEnd_8354 : Nat := 3812993233569376565855

theorem tailTrace_8354 : CollatzResearch.WordTrace tailWord_8354 prefixEnd_8354 3812993233569376565855 := by
  unfold tailWord_8354
  simp only [CollatzResearch.WordTrace]
  refine ⟨76173852935589898680029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203130274494906396480077 76173852935589898680029)
  ·
    refine ⟨28565194850846212005011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76173852935589898680029 28565194850846212005011)
    ·
      refine ⟨42847792276269318007517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28565194850846212005011 42847792276269318007517)
      ·
        refine ⟨16067922103600994252819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42847792276269318007517 16067922103600994252819)
        ·
          refine ⟨24101883155401491379229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16067922103600994252819 24101883155401491379229)
          ·
            refine ⟨9038206183275559267211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24101883155401491379229 9038206183275559267211)
            ·
              refine ⟨13557309274913338900817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9038206183275559267211 13557309274913338900817)
              ·
                refine ⟨10167981956185004175613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13557309274913338900817 10167981956185004175613)
                ·
                  refine ⟨3812993233569376565855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10167981956185004175613 3812993233569376565855)
                  ·
                    rfl

theorem cell20_8354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_8354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8354 prefixEnd_8354 := by exact prefixLift 8354
  have htrace : WordTrace (prefixWord ++ tailWord_8354) baseStart_8354 baseEnd_8354 := by
    simpa [prefixWord, tailWord_8354, baseEnd_8354] using wordTrace_append hprefix tailTrace_8354
  have hstable : (prefixWord ++ tailWord_8354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8354).length < 2 ^ (prefixWord ++ tailWord_8354).sum := by decide
  have hdescent : baseEnd_8354 < baseStart_8354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8375 : List Nat := [1, 1, 3, 1, 4, 3, 3, 1, 3]
def baseStart_8375 : Nat := 118140960795 + 8375 * 2 ^ 59
def prefixEnd_8375 : Nat := 4983230072969 + 3 ^ 40 * 8375 * 2
def baseEnd_8375 : Nat := 3822578205786636865769

theorem tailTrace_8375 : CollatzResearch.WordTrace tailWord_8375 prefixEnd_8375 3822578205786636865769 := by
  unfold tailWord_8375
  simp only [CollatzResearch.WordTrace]
  refine ⟨305461344666280181234579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203640896444186787489719 305461344666280181234579)
  ·
    refine ⟨458192016999420271851869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305461344666280181234579 458192016999420271851869)
    ·
      refine ⟨171822006374782601944451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458192016999420271851869 171822006374782601944451)
      ·
        refine ⟨257733009562173902916677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171822006374782601944451 257733009562173902916677)
        ·
          refine ⟨48324939292907606796877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257733009562173902916677 48324939292907606796877)
          ·
            refine ⟨18121852234840352548829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48324939292907606796877 18121852234840352548829)
            ·
              refine ⟨6795694588065132205811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18121852234840352548829 6795694588065132205811)
              ·
                refine ⟨10193541882097698308717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6795694588065132205811 10193541882097698308717)
                ·
                  refine ⟨3822578205786636865769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10193541882097698308717 3822578205786636865769)
                  ·
                    rfl

theorem cell20_8375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_8375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8375 prefixEnd_8375 := by exact prefixLift 8375
  have htrace : WordTrace (prefixWord ++ tailWord_8375) baseStart_8375 baseEnd_8375 := by
    simpa [prefixWord, tailWord_8375, baseEnd_8375] using wordTrace_append hprefix tailTrace_8375
  have hstable : (prefixWord ++ tailWord_8375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8375).length < 2 ^ (prefixWord ++ tailWord_8375).sum := by decide
  have hdescent : baseEnd_8375 < baseStart_8375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385 : List Nat := [1, 2, 6, 1, 2, 2, 2, 4]
def baseStart_8385 : Nat := 118140960795 + 8385 * 2 ^ 59
def prefixEnd_8385 : Nat := 4983230072969 + 3 ^ 40 * 8385 * 2
def baseEnd_8385 : Nat := 1275714159423682177465

theorem tailTrace_8385 : CollatzResearch.WordTrace tailWord_8385 prefixEnd_8385 1275714159423682177465 := by
  unfold tailWord_8385
  simp only [CollatzResearch.WordTrace]
  refine ⟨305826074630051889098609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203884049753367926065739 305826074630051889098609)
  ·
    refine ⟨229369555972538916823957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305826074630051889098609 229369555972538916823957)
    ·
      refine ⟨10751697936212761726123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229369555972538916823957 10751697936212761726123)
      ·
        refine ⟨16127546904319142589185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751697936212761726123 16127546904319142589185)
        ·
          refine ⟨12095660178239356941889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16127546904319142589185 12095660178239356941889)
          ·
            refine ⟨9071745133679517706417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12095660178239356941889 9071745133679517706417)
            ·
              refine ⟨6803808850259638279813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9071745133679517706417 6803808850259638279813)
              ·
                refine ⟨1275714159423682177465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6803808850259638279813 1275714159423682177465)
                ·
                  rfl

theorem cell20_8385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 4].length) (baseStart_8385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8385 prefixEnd_8385 := by exact prefixLift 8385
  have htrace : WordTrace (prefixWord ++ tailWord_8385) baseStart_8385 baseEnd_8385 := by
    simpa [prefixWord, tailWord_8385, baseEnd_8385] using wordTrace_append hprefix tailTrace_8385
  have hstable : (prefixWord ++ tailWord_8385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385).length < 2 ^ (prefixWord ++ tailWord_8385).sum := by decide
  have hdescent : baseEnd_8385 < baseStart_8385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8406 : List Nat := [5, 2, 1, 2, 1, 3, 6]
def baseStart_8406 : Nat := 118140960795 + 8406 * 2 ^ 59
def prefixEnd_8406 : Nat := 4983230072969 + 3 ^ 40 * 8406 * 2
def baseEnd_8406 : Nat := 426303050054256314701

theorem tailTrace_8406 : CollatzResearch.WordTrace tailWord_8406 prefixEnd_8406 426303050054256314701 := by
  unfold tailWord_8406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19162000472123279725817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 204394671702648317075381 19162000472123279725817)
  ·
    refine ⟨14371500354092459794363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19162000472123279725817 14371500354092459794363)
    ·
      refine ⟨21557250531138689691545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14371500354092459794363 21557250531138689691545)
      ·
        refine ⟨16167937898354017268659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21557250531138689691545 16167937898354017268659)
        ·
          refine ⟨24251906847531025902989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16167937898354017268659 24251906847531025902989)
          ·
            refine ⟨9094465067824134713621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24251906847531025902989 9094465067824134713621)
            ·
              refine ⟨426303050054256314701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9094465067824134713621 426303050054256314701)
              ·
                rfl

theorem cell20_8406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 6].length) (baseStart_8406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8406 prefixEnd_8406 := by exact prefixLift 8406
  have htrace : WordTrace (prefixWord ++ tailWord_8406) baseStart_8406 baseEnd_8406 := by
    simpa [prefixWord, tailWord_8406, baseEnd_8406] using wordTrace_append hprefix tailTrace_8406
  have hstable : (prefixWord ++ tailWord_8406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8406).length < 2 ^ (prefixWord ++ tailWord_8406).sum := by decide
  have hdescent : baseEnd_8406 < baseStart_8406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8417 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_8417 : Nat := 118140960795 + 8417 * 2 ^ 59
def prefixEnd_8417 : Nat := 4983230072969 + 3 ^ 40 * 8417 * 2
def baseEnd_8417 : Nat := 3841748150221157465597

theorem tailTrace_8417 : CollatzResearch.WordTrace tailWord_8417 prefixEnd_8417 3841748150221157465597 := by
  unfold tailWord_8417
  simp only [CollatzResearch.WordTrace]
  refine ⟨306993210514121354263505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 204662140342747569509003 306993210514121354263505)
  ·
    refine ⟨230244907885591015697629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 306993210514121354263505 230244907885591015697629)
    ·
      refine ⟨86341840457096630886611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230244907885591015697629 86341840457096630886611)
      ·
        refine ⟨129512760685644946329917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86341840457096630886611 129512760685644946329917)
        ·
          refine ⟨48567285257116854873719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129512760685644946329917 48567285257116854873719)
          ·
            refine ⟨72850927885675282310579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48567285257116854873719 72850927885675282310579)
            ·
              refine ⟨109276391828512923465869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72850927885675282310579 109276391828512923465869)
              ·
                refine ⟨40978646935692346299701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109276391828512923465869 40978646935692346299701)
                ·
                  refine ⟨3841748150221157465597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40978646935692346299701 3841748150221157465597)
                  ·
                    rfl

theorem cell20_8417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_8417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8417 prefixEnd_8417 := by exact prefixLift 8417
  have htrace : WordTrace (prefixWord ++ tailWord_8417) baseStart_8417 baseEnd_8417 := by
    simpa [prefixWord, tailWord_8417, baseEnd_8417] using wordTrace_append hprefix tailTrace_8417
  have hstable : (prefixWord ++ tailWord_8417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8417).length < 2 ^ (prefixWord ++ tailWord_8417).sum := by decide
  have hdescent : baseEnd_8417 < baseStart_8417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8472 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_8472 : Nat := 118140960795 + 8472 * 2 ^ 59
def prefixEnd_8472 : Nat := 4983230072969 + 3 ^ 40 * 8472 * 2
def baseEnd_8472 : Nat := 3866851648885410632039

theorem tailTrace_8472 : CollatzResearch.WordTrace tailWord_8472 prefixEnd_8472 3866851648885410632039 := by
  unfold tailWord_8472
  simp only [CollatzResearch.WordTrace]
  refine ⟨154499612657432873757835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 205999483543243831677113 154499612657432873757835)
  ·
    refine ⟨231749418986149310636753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154499612657432873757835 231749418986149310636753)
    ·
      refine ⟨173812064239611982977565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231749418986149310636753 173812064239611982977565)
      ·
        refine ⟨65179524089854493616587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173812064239611982977565 65179524089854493616587)
        ·
          refine ⟨97769286134781740424881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65179524089854493616587 97769286134781740424881)
          ·
            refine ⟨73326964601086305318661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97769286134781740424881 73326964601086305318661)
            ·
              refine ⟨13748805862703682247249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73326964601086305318661 13748805862703682247249)
              ·
                refine ⟨10311604397027761685437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13748805862703682247249 10311604397027761685437)
                ·
                  refine ⟨3866851648885410632039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10311604397027761685437 3866851648885410632039)
                  ·
                    rfl

theorem cell20_8472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_8472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8472 prefixEnd_8472 := by exact prefixLift 8472
  have htrace : WordTrace (prefixWord ++ tailWord_8472) baseStart_8472 baseEnd_8472 := by
    simpa [prefixWord, tailWord_8472, baseEnd_8472] using wordTrace_append hprefix tailTrace_8472
  have hstable : (prefixWord ++ tailWord_8472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8472).length < 2 ^ (prefixWord ++ tailWord_8472).sum := by decide
  have hdescent : baseEnd_8472 < baseStart_8472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8531 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 3]
def baseStart_8531 : Nat := 118140960795 + 8531 * 2 ^ 59
def prefixEnd_8531 : Nat := 4983230072969 + 3 ^ 40 * 8531 * 2
def baseEnd_8531 : Nat := 3893780856543427665131

theorem tailTrace_8531 : CollatzResearch.WordTrace tailWord_8531 prefixEnd_8531 3893780856543427665131 := by
  unfold tailWord_8531
  simp only [CollatzResearch.WordTrace]
  refine ⟨311151132101118823913447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 207434088067412549275631 311151132101118823913447)
  ·
    refine ⟨466726698151678235870171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 311151132101118823913447 466726698151678235870171)
    ·
      refine ⟨700090047227517353805257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466726698151678235870171 700090047227517353805257)
      ·
        refine ⟨525067535420638015353943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700090047227517353805257 525067535420638015353943)
        ·
          refine ⟨787601303130957023030915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525067535420638015353943 787601303130957023030915)
          ·
            refine ⟨1181401954696435534546373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787601303130957023030915 1181401954696435534546373)
            ·
              refine ⟨221512866505581662727445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1181401954696435534546373 221512866505581662727445)
              ·
                refine ⟨10383415617449140440349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221512866505581662727445 10383415617449140440349)
                ·
                  refine ⟨3893780856543427665131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10383415617449140440349 3893780856543427665131)
                  ·
                    rfl

theorem cell20_8531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 3].length) (baseStart_8531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8531 prefixEnd_8531 := by exact prefixLift 8531
  have htrace : WordTrace (prefixWord ++ tailWord_8531) baseStart_8531 baseEnd_8531 := by
    simpa [prefixWord, tailWord_8531, baseEnd_8531] using wordTrace_append hprefix tailTrace_8531
  have hstable : (prefixWord ++ tailWord_8531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8531).length < 2 ^ (prefixWord ++ tailWord_8531).sum := by decide
  have hdescent : baseEnd_8531 < baseStart_8531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8562 : List Nat := [3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_8562 : Nat := 118140960795 + 8562 * 2 ^ 59
def prefixEnd_8562 : Nat := 4983230072969 + 3 ^ 40 * 8562 * 2
def baseEnd_8562 : Nat := 1302643367081699210557

theorem tailTrace_8562 : CollatzResearch.WordTrace tailWord_8562 prefixEnd_8562 1302643367081699210557 := by
  unfold tailWord_8562
  simp only [CollatzResearch.WordTrace]
  refine ⟨78070448747202779572985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 208187863325874078861293 78070448747202779572985)
  ·
    refine ⟨58552836560402084679739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78070448747202779572985 58552836560402084679739)
    ·
      refine ⟨87829254840603127019609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58552836560402084679739 87829254840603127019609)
      ·
        refine ⟨65871941130452345264707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 87829254840603127019609 65871941130452345264707)
        ·
          refine ⟨98807911695678517897061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65871941130452345264707 98807911695678517897061)
          ·
            refine ⟨18526483442939722105699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 98807911695678517897061 18526483442939722105699)
            ·
              refine ⟨27789725164409583158549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18526483442939722105699 27789725164409583158549)
              ·
                refine ⟨1302643367081699210557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27789725164409583158549 1302643367081699210557)
                ·
                  rfl

theorem cell20_8562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_8562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8562 prefixEnd_8562 := by exact prefixLift 8562
  have htrace : WordTrace (prefixWord ++ tailWord_8562) baseStart_8562 baseEnd_8562 := by
    simpa [prefixWord, tailWord_8562, baseEnd_8562] using wordTrace_append hprefix tailTrace_8562
  have hstable : (prefixWord ++ tailWord_8562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8562).length < 2 ^ (prefixWord ++ tailWord_8562).sum := by decide
  have hdescent : baseEnd_8562 < baseStart_8562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8579 : List Nat := [1, 1, 1, 3, 7, 1, 6]
def baseStart_8579 : Nat := 118140960795 + 8579 * 2 ^ 59
def prefixEnd_8579 : Nat := 4983230072969 + 3 ^ 40 * 8579 * 2
def baseEnd_8579 : Nat := 435076596052066007215

theorem tailTrace_8579 : CollatzResearch.WordTrace tailWord_8579 prefixEnd_8579 435076596052066007215 := by
  unfold tailWord_8579
  simp only [CollatzResearch.WordTrace]
  refine ⟨312901835927223021660791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 208601223951482014440527 312901835927223021660791)
  ·
    refine ⟨469352753890834532491187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312901835927223021660791 469352753890834532491187)
    ·
      refine ⟨704029130836251798736781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469352753890834532491187 704029130836251798736781)
      ·
        refine ⟨264010924063594424526293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 704029130836251798736781 264010924063594424526293)
        ·
          refine ⟨6187756032740494324835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 264010924063594424526293 6187756032740494324835)
          ·
            refine ⟨9281634049110741487253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6187756032740494324835 9281634049110741487253)
            ·
              refine ⟨435076596052066007215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9281634049110741487253 435076596052066007215)
              ·
                rfl

theorem cell20_8579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 6].length) (baseStart_8579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8579 prefixEnd_8579 := by exact prefixLift 8579
  have htrace : WordTrace (prefixWord ++ tailWord_8579) baseStart_8579 baseEnd_8579 := by
    simpa [prefixWord, tailWord_8579, baseEnd_8579] using wordTrace_append hprefix tailTrace_8579
  have hstable : (prefixWord ++ tailWord_8579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8579).length < 2 ^ (prefixWord ++ tailWord_8579).sum := by decide
  have hdescent : baseEnd_8579 < baseStart_8579 := by decide
  rcases family_descends (prefixWord ++ tailWord_8579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8600 : List Nat := [2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_8600 : Nat := 118140960795 + 8600 * 2 ^ 59
def prefixEnd_8600 : Nat := 4983230072969 + 3 ^ 40 * 8600 * 2
def baseEnd_8600 : Nat := 1308424778895284788283

theorem tailTrace_8600 : CollatzResearch.WordTrace tailWord_8600 prefixEnd_8600 1308424778895284788283 := by
  unfold tailWord_8600
  simp only [CollatzResearch.WordTrace]
  refine ⟨156833884425571804087627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 209111845900762405450169 156833884425571804087627)
  ·
    refine ⟨235250826638357706131441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156833884425571804087627 235250826638357706131441)
    ·
      refine ⟨176438119978768279598581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235250826638357706131441 176438119978768279598581)
      ·
        refine ⟨16541073748009526212367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176438119978768279598581 16541073748009526212367)
        ·
          refine ⟨24811610622014289318551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16541073748009526212367 24811610622014289318551)
          ·
            refine ⟨37217415933021433977827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24811610622014289318551 37217415933021433977827)
            ·
              refine ⟨55826123899532150966741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37217415933021433977827 55826123899532150966741)
              ·
                refine ⟨1308424778895284788283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 55826123899532150966741 1308424778895284788283)
                ·
                  rfl

theorem cell20_8600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_8600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8600 prefixEnd_8600 := by exact prefixLift 8600
  have htrace : WordTrace (prefixWord ++ tailWord_8600) baseStart_8600 baseEnd_8600 := by
    simpa [prefixWord, tailWord_8600, baseEnd_8600] using wordTrace_append hprefix tailTrace_8600
  have hstable : (prefixWord ++ tailWord_8600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8600).length < 2 ^ (prefixWord ++ tailWord_8600).sum := by decide
  have hdescent : baseEnd_8600 < baseStart_8600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8648 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 2]
def baseStart_8648 : Nat := 118140960795 + 8648 * 2 ^ 59
def prefixEnd_8648 : Nat := 4983230072969 + 3 ^ 40 * 8648 * 2
def baseEnd_8648 : Nat := 3947182844611020764653

theorem tailTrace_8648 : CollatzResearch.WordTrace tailWord_8648 prefixEnd_8648 3947182844611020764653 := by
  unfold tailWord_8648
  simp only [CollatzResearch.WordTrace]
  refine ⟨157709236338623902961299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 210278981784831870615065 157709236338623902961299)
  ·
    refine ⟨236563854507935854441949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157709236338623902961299 236563854507935854441949)
    ·
      refine ⟨88711445440475945415731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236563854507935854441949 88711445440475945415731)
      ·
        refine ⟨133067168160713918123597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88711445440475945415731 133067168160713918123597)
        ·
          refine ⟨49900188060267719296349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133067168160713918123597 49900188060267719296349)
          ·
            refine ⟨18712570522600394736131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49900188060267719296349 18712570522600394736131)
            ·
              refine ⟨28068855783900592104197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18712570522600394736131 28068855783900592104197)
              ·
                refine ⟨5262910459481361019537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28068855783900592104197 5262910459481361019537)
                ·
                  refine ⟨3947182844611020764653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5262910459481361019537 3947182844611020764653)
                  ·
                    rfl

theorem cell20_8648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 2].length) (baseStart_8648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8648 prefixEnd_8648 := by exact prefixLift 8648
  have htrace : WordTrace (prefixWord ++ tailWord_8648) baseStart_8648 baseEnd_8648 := by
    simpa [prefixWord, tailWord_8648, baseEnd_8648] using wordTrace_append hprefix tailTrace_8648
  have hstable : (prefixWord ++ tailWord_8648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8648).length < 2 ^ (prefixWord ++ tailWord_8648).sum := by decide
  have hdescent : baseEnd_8648 < baseStart_8648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8669 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_8669 : Nat := 118140960795 + 8669 * 2 ^ 59
def prefixEnd_8669 : Nat := 4983230072969 + 3 ^ 40 * 8669 * 2
def baseEnd_8669 : Nat := 3956767816828281064567

theorem tailTrace_8669 : CollatzResearch.WordTrace tailWord_8669 prefixEnd_8669 3956767816828281064567 := by
  unfold tailWord_8669
  simp only [CollatzResearch.WordTrace]
  refine ⟨316184405601168392437061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 210789603734112261624707 316184405601168392437061)
  ·
    refine ⟨59284576050219073581949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 316184405601168392437061 59284576050219073581949)
    ·
      refine ⟨22231716018832152593231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59284576050219073581949 22231716018832152593231)
      ·
        refine ⟨33347574028248228889847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22231716018832152593231 33347574028248228889847)
        ·
          refine ⟨50021361042372343334771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33347574028248228889847 50021361042372343334771)
          ·
            refine ⟨75032041563558515002157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50021361042372343334771 75032041563558515002157)
            ·
              refine ⟨28137015586334443125809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75032041563558515002157 28137015586334443125809)
              ·
                refine ⟨21102761689750832344357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28137015586334443125809 21102761689750832344357)
                ·
                  refine ⟨3956767816828281064567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21102761689750832344357 3956767816828281064567)
                  ·
                    rfl

theorem cell20_8669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_8669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8669 prefixEnd_8669 := by exact prefixLift 8669
  have htrace : WordTrace (prefixWord ++ tailWord_8669) baseStart_8669 baseEnd_8669 := by
    simpa [prefixWord, tailWord_8669, baseEnd_8669] using wordTrace_append hprefix tailTrace_8669
  have hstable : (prefixWord ++ tailWord_8669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8669).length < 2 ^ (prefixWord ++ tailWord_8669).sum := by decide
  have hdescent : baseEnd_8669 < baseStart_8669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8686 : List Nat := [4, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_8686 : Nat := 118140960795 + 8686 * 2 ^ 59
def prefixEnd_8686 : Nat := 4983230072969 + 3 ^ 40 * 8686 * 2
def baseEnd_8686 : Nat := 3964527080051777497831

theorem tailTrace_8686 : CollatzResearch.WordTrace tailWord_8686 prefixEnd_8686 3964527080051777497831 := by
  unfold tailWord_8686
  simp only [CollatzResearch.WordTrace]
  refine ⟨39600555817447536975739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 211202964359720197203941 39600555817447536975739)
  ·
    refine ⟨59400833726171305463609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39600555817447536975739 59400833726171305463609)
    ·
      refine ⟨44550625294628479097707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59400833726171305463609 44550625294628479097707)
      ·
        refine ⟨66825937941942718646561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44550625294628479097707 66825937941942718646561)
        ·
          refine ⟨50119453456457038984921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66825937941942718646561 50119453456457038984921)
          ·
            refine ⟨37589590092342779238691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50119453456457038984921 37589590092342779238691)
            ·
              refine ⟨56384385138514168858037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37589590092342779238691 56384385138514168858037)
              ·
                refine ⟨5286036106735703330441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56384385138514168858037 5286036106735703330441)
                ·
                  refine ⟨3964527080051777497831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5286036106735703330441 3964527080051777497831)
                  ·
                    rfl

theorem cell20_8686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_8686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8686 prefixEnd_8686 := by exact prefixLift 8686
  have htrace : WordTrace (prefixWord ++ tailWord_8686) baseStart_8686 baseEnd_8686 := by
    simpa [prefixWord, tailWord_8686, baseEnd_8686] using wordTrace_append hprefix tailTrace_8686
  have hstable : (prefixWord ++ tailWord_8686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8686).length < 2 ^ (prefixWord ++ tailWord_8686).sum := by decide
  have hdescent : baseEnd_8686 < baseStart_8686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8693 : List Nat := [1, 3, 5, 1, 2, 1, 7]
def baseStart_8693 : Nat := 118140960795 + 8693 * 2 ^ 59
def prefixEnd_8693 : Nat := 4983230072969 + 3 ^ 40 * 8693 * 2
def baseEnd_8693 : Nat := 440858007865651584941

theorem tailTrace_8693 : CollatzResearch.WordTrace tailWord_8693 prefixEnd_8693 440858007865651584941 := by
  unfold tailWord_8693
  simp only [CollatzResearch.WordTrace]
  refine ⟨317059757514220491310733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 211373171676146994207155 317059757514220491310733)
  ·
    refine ⟨118897409067832684241525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 317059757514220491310733 118897409067832684241525)
    ·
      refine ⟨11146632100109314147643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118897409067832684241525 11146632100109314147643)
      ·
        refine ⟨16719948150163971221465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11146632100109314147643 16719948150163971221465)
        ·
          refine ⟨12539961112622978416099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16719948150163971221465 12539961112622978416099)
          ·
            refine ⟨18809941668934467624149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12539961112622978416099 18809941668934467624149)
            ·
              refine ⟨440858007865651584941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18809941668934467624149 440858007865651584941)
              ·
                rfl

theorem cell20_8693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_8693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8693 prefixEnd_8693 := by exact prefixLift 8693
  have htrace : WordTrace (prefixWord ++ tailWord_8693) baseStart_8693 baseEnd_8693 := by
    simpa [prefixWord, tailWord_8693, baseEnd_8693] using wordTrace_append hprefix tailTrace_8693
  have hstable : (prefixWord ++ tailWord_8693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8693).length < 2 ^ (prefixWord ++ tailWord_8693).sum := by decide
  have hdescent : baseEnd_8693 < baseStart_8693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8707 : List Nat := [1, 1, 1, 3, 2, 1, 3, 6, 2]
def baseStart_8707 : Nat := 118140960795 + 8707 * 2 ^ 59
def prefixEnd_8707 : Nat := 4983230072969 + 3 ^ 40 * 8707 * 2
def baseEnd_8707 : Nat := 3974112052269037797745

theorem tailTrace_8707 : CollatzResearch.WordTrace tailWord_8707 prefixEnd_8707 3974112052269037797745 := by
  unfold tailWord_8707
  simp only [CollatzResearch.WordTrace]
  refine ⟨317570379463500882320375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 211713586309000588213583 317570379463500882320375)
  ·
    refine ⟨476355569195251323480563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317570379463500882320375 476355569195251323480563)
    ·
      refine ⟨714533353792876985220845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476355569195251323480563 714533353792876985220845)
      ·
        refine ⟨267950007672328869457817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 714533353792876985220845 267950007672328869457817)
        ·
          refine ⟨200962505754246652093363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267950007672328869457817 200962505754246652093363)
          ·
            refine ⟨301443758631369978140045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200962505754246652093363 301443758631369978140045)
            ·
              refine ⟨113041409486763741802517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301443758631369978140045 113041409486763741802517)
              ·
                refine ⟨5298816069692050396993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113041409486763741802517 5298816069692050396993)
                ·
                  refine ⟨3974112052269037797745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5298816069692050396993 3974112052269037797745)
                  ·
                    rfl

theorem cell20_8707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 6, 2].length) (baseStart_8707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8707 prefixEnd_8707 := by exact prefixLift 8707
  have htrace : WordTrace (prefixWord ++ tailWord_8707) baseStart_8707 baseEnd_8707 := by
    simpa [prefixWord, tailWord_8707, baseEnd_8707] using wordTrace_append hprefix tailTrace_8707
  have hstable : (prefixWord ++ tailWord_8707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8707).length < 2 ^ (prefixWord ++ tailWord_8707).sum := by decide
  have hdescent : baseEnd_8707 < baseStart_8707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8724 : List Nat := [2, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_8724 : Nat := 118140960795 + 8724 * 2 ^ 59
def prefixEnd_8724 : Nat := 4983230072969 + 3 ^ 40 * 8724 * 2
def baseEnd_8724 : Nat := 3981871315492534231009

theorem tailTrace_8724 : CollatzResearch.WordTrace tailWord_8724 prefixEnd_8724 3981871315492534231009 := by
  unfold tailWord_8724
  simp only [CollatzResearch.WordTrace]
  refine ⟨159095210200956392844613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 212126946934608523792817 159095210200956392844613)
  ·
    refine ⟨29830351912679323658365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159095210200956392844613 29830351912679323658365)
    ·
      refine ⟨11186381967254746371887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29830351912679323658365 11186381967254746371887)
      ·
        refine ⟨16779572950882119557831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11186381967254746371887 16779572950882119557831)
        ·
          refine ⟨25169359426323179336747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16779572950882119557831 25169359426323179336747)
          ·
            refine ⟨37754039139484769005121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25169359426323179336747 37754039139484769005121)
            ·
              refine ⟨28315529354613576753841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37754039139484769005121 28315529354613576753841)
              ·
                refine ⟨21236647015960182565381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28315529354613576753841 21236647015960182565381)
                ·
                  refine ⟨3981871315492534231009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21236647015960182565381 3981871315492534231009)
                  ·
                    rfl

theorem cell20_8724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_8724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8724 prefixEnd_8724 := by exact prefixLift 8724
  have htrace : WordTrace (prefixWord ++ tailWord_8724) baseStart_8724 baseEnd_8724 := by
    simpa [prefixWord, tailWord_8724, baseEnd_8724] using wordTrace_append hprefix tailTrace_8724
  have hstable : (prefixWord ++ tailWord_8724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8724).length < 2 ^ (prefixWord ++ tailWord_8724).sum := by decide
  have hdescent : baseEnd_8724 < baseStart_8724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8727 : List Nat := [1, 1, 3, 6, 2, 1, 2, 4]
def baseStart_8727 : Nat := 118140960795 + 8727 * 2 ^ 59
def prefixEnd_8727 : Nat := 4983230072969 + 3 ^ 40 * 8727 * 2
def baseEnd_8727 : Nat := 1327746865745952376999

theorem tailTrace_8727 : CollatzResearch.WordTrace tailWord_8727 prefixEnd_8727 1327746865745952376999 := by
  unfold tailWord_8727
  simp only [CollatzResearch.WordTrace]
  refine ⟨318299839391044298048435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 212199892927362865365623 318299839391044298048435)
  ·
    refine ⟨477449759086566447072653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 318299839391044298048435 477449759086566447072653)
    ·
      refine ⟨179043659657462417652245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 477449759086566447072653 179043659657462417652245)
      ·
        refine ⟨8392671546443550827449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 179043659657462417652245 8392671546443550827449)
        ·
          refine ⟨6294503659832663120587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8392671546443550827449 6294503659832663120587)
          ·
            refine ⟨9441755489748994680881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294503659832663120587 9441755489748994680881)
            ·
              refine ⟨7081316617311746010661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9441755489748994680881 7081316617311746010661)
              ·
                refine ⟨1327746865745952376999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7081316617311746010661 1327746865745952376999)
                ·
                  rfl

theorem cell20_8727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 4].length) (baseStart_8727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8727 prefixEnd_8727 := by exact prefixLift 8727
  have htrace : WordTrace (prefixWord ++ tailWord_8727) baseStart_8727 baseEnd_8727 := by
    simpa [prefixWord, tailWord_8727, baseEnd_8727] using wordTrace_append hprefix tailTrace_8727
  have hstable : (prefixWord ++ tailWord_8727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8727).length < 2 ^ (prefixWord ++ tailWord_8727).sum := by decide
  have hdescent : baseEnd_8727 < baseStart_8727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8758 : List Nat := [5, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_8758 : Nat := 118140960795 + 8758 * 2 ^ 59
def prefixEnd_8758 : Nat := 4983230072969 + 3 ^ 40 * 8758 * 2
def baseEnd_8758 : Nat := 3997389841939527097537

theorem tailTrace_8758 : CollatzResearch.WordTrace tailWord_8758 prefixEnd_8758 3997389841939527097537 := by
  unfold tailWord_8758
  simp only [CollatzResearch.WordTrace]
  refine ⟨19964406392421037026683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 212953668185824394951285 19964406392421037026683)
  ·
    refine ⟨29946609588631555540025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19964406392421037026683 29946609588631555540025)
    ·
      refine ⟨22459957191473666655019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29946609588631555540025 22459957191473666655019)
      ·
        refine ⟨33689935787210499982529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22459957191473666655019 33689935787210499982529)
        ·
          refine ⟨25267451840407874986897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33689935787210499982529 25267451840407874986897)
          ·
            refine ⟨18950588880305906240173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25267451840407874986897 18950588880305906240173)
            ·
              refine ⟨7106470830114714840065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18950588880305906240173 7106470830114714840065)
              ·
                refine ⟨5329853122586036130049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7106470830114714840065 5329853122586036130049)
                ·
                  refine ⟨3997389841939527097537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5329853122586036130049 3997389841939527097537)
                  ·
                    rfl

theorem cell20_8758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_8758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8758 prefixEnd_8758 := by exact prefixLift 8758
  have htrace : WordTrace (prefixWord ++ tailWord_8758) baseStart_8758 baseEnd_8758 := by
    simpa [prefixWord, tailWord_8758, baseEnd_8758] using wordTrace_append hprefix tailTrace_8758
  have hstable : (prefixWord ++ tailWord_8758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8758).length < 2 ^ (prefixWord ++ tailWord_8758).sum := by decide
  have hdescent : baseEnd_8758 < baseStart_8758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8759 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_8759 : Nat := 118140960795 + 8759 * 2 ^ 59
def prefixEnd_8759 : Nat := 4983230072969 + 3 ^ 40 * 8759 * 2
def baseEnd_8759 : Nat := 3997846269187968064199

theorem tailTrace_8759 : CollatzResearch.WordTrace tailWord_8759 prefixEnd_8759 3997846269187968064199 := by
  unfold tailWord_8759
  simp only [CollatzResearch.WordTrace]
  refine ⟨319466975275113763213331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 212977983516742508808887 319466975275113763213331)
  ·
    refine ⟨479200462912670644819997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319466975275113763213331 479200462912670644819997)
    ·
      refine ⟨179700173592251491807499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 479200462912670644819997 179700173592251491807499)
      ·
        refine ⟨269550260388377237711249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179700173592251491807499 269550260388377237711249)
        ·
          refine ⟨202162695291282928283437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269550260388377237711249 202162695291282928283437)
          ·
            refine ⟨75811010734231098106289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202162695291282928283437 75811010734231098106289)
            ·
              refine ⟨56858258050673323579717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75811010734231098106289 56858258050673323579717)
              ·
                refine ⟨10660923384501248171197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56858258050673323579717 10660923384501248171197)
                ·
                  refine ⟨3997846269187968064199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10660923384501248171197 3997846269187968064199)
                  ·
                    rfl

theorem cell20_8759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_8759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8759 prefixEnd_8759 := by exact prefixLift 8759
  have htrace : WordTrace (prefixWord ++ tailWord_8759) baseStart_8759 baseEnd_8759 := by
    simpa [prefixWord, tailWord_8759, baseEnd_8759] using wordTrace_append hprefix tailTrace_8759
  have hstable : (prefixWord ++ tailWord_8759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8759).length < 2 ^ (prefixWord ++ tailWord_8759).sum := by decide
  have hdescent : baseEnd_8759 < baseStart_8759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8773 : List Nat := [1, 3, 1, 1, 1, 5, 1, 7]
def baseStart_8773 : Nat := 118140960795 + 8773 * 2 ^ 59
def prefixEnd_8773 : Nat := 4983230072969 + 3 ^ 40 * 8773 * 2
def baseEnd_8773 : Nat := 1334745416888713865825

theorem tailTrace_8773 : CollatzResearch.WordTrace tailWord_8773 prefixEnd_8773 1334745416888713865825 := by
  unfold tailWord_8773
  simp only [CollatzResearch.WordTrace]
  refine ⟨319977597224394154222973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 213318398149596102815315 319977597224394154222973)
  ·
    refine ⟨119991598959147807833615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 319977597224394154222973 119991598959147807833615)
    ·
      refine ⟨179987398438721711750423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119991598959147807833615 179987398438721711750423)
      ·
        refine ⟨269981097658082567625635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179987398438721711750423 269981097658082567625635)
        ·
          refine ⟨404971646487123851438453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269981097658082567625635 404971646487123851438453)
          ·
            refine ⟨37966091858167861072355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 404971646487123851438453 37966091858167861072355)
            ·
              refine ⟨56949137787251791608533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37966091858167861072355 56949137787251791608533)
              ·
                refine ⟨1334745416888713865825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56949137787251791608533 1334745416888713865825)
                ·
                  rfl

theorem cell20_8773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_8773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8773 prefixEnd_8773 := by exact prefixLift 8773
  have htrace : WordTrace (prefixWord ++ tailWord_8773) baseStart_8773 baseEnd_8773 := by
    simpa [prefixWord, tailWord_8773, baseEnd_8773] using wordTrace_append hprefix tailTrace_8773
  have hstable : (prefixWord ++ tailWord_8773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8773).length < 2 ^ (prefixWord ++ tailWord_8773).sum := by decide
  have hdescent : baseEnd_8773 < baseStart_8773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8814 : List Nat := [4, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_8814 : Nat := 118140960795 + 8814 * 2 ^ 59
def prefixEnd_8814 : Nat := 4983230072969 + 3 ^ 40 * 8814 * 2
def baseEnd_8814 : Nat := 4022949767852221230641

theorem tailTrace_8814 : CollatzResearch.WordTrace tailWord_8814 prefixEnd_8814 4022949767852221230641 := by
  unfold tailWord_8814
  simp only [CollatzResearch.WordTrace]
  refine ⟨40184123759482269558187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 214315326717238770976997 40184123759482269558187)
  ·
    refine ⟨60276185639223404337281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40184123759482269558187 60276185639223404337281)
    ·
      refine ⟨45207139229417553252961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60276185639223404337281 45207139229417553252961)
      ·
        refine ⟨33905354422063164939721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45207139229417553252961 33905354422063164939721)
        ·
          refine ⟨25429015816547373704791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33905354422063164939721 25429015816547373704791)
          ·
            refine ⟨38143523724821060557187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25429015816547373704791 38143523724821060557187)
            ·
              refine ⟨57215285587231590835781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38143523724821060557187 57215285587231590835781)
              ·
                refine ⟨10727866047605923281709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57215285587231590835781 10727866047605923281709)
                ·
                  refine ⟨4022949767852221230641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10727866047605923281709 4022949767852221230641)
                  ·
                    rfl

theorem cell20_8814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_8814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8814 prefixEnd_8814 := by exact prefixLift 8814
  have htrace : WordTrace (prefixWord ++ tailWord_8814) baseStart_8814 baseEnd_8814 := by
    simpa [prefixWord, tailWord_8814, baseEnd_8814] using wordTrace_append hprefix tailTrace_8814
  have hstable : (prefixWord ++ tailWord_8814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8814).length < 2 ^ (prefixWord ++ tailWord_8814).sum := by decide
  have hdescent : baseEnd_8814 < baseStart_8814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8834 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_8834 : Nat := 118140960795 + 8834 * 2 ^ 59
def prefixEnd_8834 : Nat := 4983230072969 + 3 ^ 40 * 8834 * 2
def baseEnd_8834 : Nat := 4032078312821040563893

theorem tailTrace_8834 : CollatzResearch.WordTrace tailWord_8834 prefixEnd_8834 4032078312821040563893 := by
  unfold tailWord_8834
  simp only [CollatzResearch.WordTrace]
  refine ⟨80550612500850393048389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 214801633335601048129037 80550612500850393048389)
  ·
    refine ⟨15103239843909448696573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80550612500850393048389 15103239843909448696573)
    ·
      refine ⟨5663714941466043261215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15103239843909448696573 5663714941466043261215)
      ·
        refine ⟨8495572412199064891823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5663714941466043261215 8495572412199064891823)
        ·
          refine ⟨12743358618298597337735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8495572412199064891823 12743358618298597337735)
          ·
            refine ⟨19115037927447896006603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12743358618298597337735 19115037927447896006603)
            ·
              refine ⟨28672556891171844009905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19115037927447896006603 28672556891171844009905)
              ·
                refine ⟨21504417668378883007429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28672556891171844009905 21504417668378883007429)
                ·
                  refine ⟨4032078312821040563893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21504417668378883007429 4032078312821040563893)
                  ·
                    rfl

theorem cell20_8834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_8834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8834 prefixEnd_8834 := by exact prefixLift 8834
  have htrace : WordTrace (prefixWord ++ tailWord_8834) baseStart_8834 baseEnd_8834 := by
    simpa [prefixWord, tailWord_8834, baseEnd_8834] using wordTrace_append hprefix tailTrace_8834
  have hstable : (prefixWord ++ tailWord_8834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8834).length < 2 ^ (prefixWord ++ tailWord_8834).sum := by decide
  have hdescent : baseEnd_8834 < baseStart_8834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8835 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 3]
def baseStart_8835 : Nat := 118140960795 + 8835 * 2 ^ 59
def prefixEnd_8835 : Nat := 4983230072969 + 3 ^ 40 * 8835 * 2
def baseEnd_8835 : Nat := 4032534740069481530555

theorem tailTrace_8835 : CollatzResearch.WordTrace tailWord_8835 prefixEnd_8835 4032534740069481530555 := by
  unfold tailWord_8835
  simp only [CollatzResearch.WordTrace]
  refine ⟨322238922999778742979959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 214825948666519161986639 322238922999778742979959)
  ·
    refine ⟨483358384499668114469939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322238922999778742979959 483358384499668114469939)
    ·
      refine ⟨725037576749502171704909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 483358384499668114469939 725037576749502171704909)
      ·
        refine ⟨271889091281063314389341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 725037576749502171704909 271889091281063314389341)
        ·
          refine ⟨101958409230398742896003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271889091281063314389341 101958409230398742896003)
          ·
            refine ⟨152937613845598114344005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101958409230398742896003 152937613845598114344005)
            ·
              refine ⟨28675802596049646439501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152937613845598114344005 28675802596049646439501)
              ·
                refine ⟨10753425973518617414813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28675802596049646439501 10753425973518617414813)
                ·
                  refine ⟨4032534740069481530555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10753425973518617414813 4032534740069481530555)
                  ·
                    rfl

theorem cell20_8835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 3].length) (baseStart_8835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8835 prefixEnd_8835 := by exact prefixLift 8835
  have htrace : WordTrace (prefixWord ++ tailWord_8835) baseStart_8835 baseEnd_8835 := by
    simpa [prefixWord, tailWord_8835, baseEnd_8835] using wordTrace_append hprefix tailTrace_8835
  have hstable : (prefixWord ++ tailWord_8835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8835).length < 2 ^ (prefixWord ++ tailWord_8835).sum := by decide
  have hdescent : baseEnd_8835 < baseStart_8835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8890 : List Nat := [3, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_8890 : Nat := 118140960795 + 8890 * 2 ^ 59
def prefixEnd_8890 : Nat := 4983230072969 + 3 ^ 40 * 8890 * 2
def baseEnd_8890 : Nat := 4057638238733734696997

theorem tailTrace_8890 : CollatzResearch.WordTrace tailWord_8890 prefixEnd_8890 4057638238733734696997 := by
  unfold tailWord_8890
  simp only [CollatzResearch.WordTrace]
  refine ⟨81061234450130784058031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 216163291867015424154749 81061234450130784058031)
  ·
    refine ⟨121591851675196176087047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81061234450130784058031 121591851675196176087047)
    ·
      refine ⟨182387777512794264130571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 121591851675196176087047 182387777512794264130571)
      ·
        refine ⟨273581666269191396195857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182387777512794264130571 273581666269191396195857)
        ·
          refine ⟨205186249701893547146893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 273581666269191396195857 205186249701893547146893)
          ·
            refine ⟨76944843638210080180085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 205186249701893547146893 76944843638210080180085)
            ·
              refine ⟨7213579091082195016883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76944843638210080180085 7213579091082195016883)
              ·
                refine ⟨10820368636623292525325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213579091082195016883 10820368636623292525325)
                ·
                  refine ⟨4057638238733734696997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10820368636623292525325 4057638238733734696997)
                  ·
                    rfl

theorem cell20_8890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_8890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8890 prefixEnd_8890 := by exact prefixLift 8890
  have htrace : WordTrace (prefixWord ++ tailWord_8890) baseStart_8890 baseEnd_8890 := by
    simpa [prefixWord, tailWord_8890, baseEnd_8890] using wordTrace_append hprefix tailTrace_8890
  have hstable : (prefixWord ++ tailWord_8890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8890).length < 2 ^ (prefixWord ++ tailWord_8890).sum := by decide
  have hdescent : baseEnd_8890 < baseStart_8890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8904 : List Nat := [2, 1, 3, 1, 2, 3, 4, 4]
def baseStart_8904 : Nat := 118140960795 + 8904 * 2 ^ 59
def prefixEnd_8904 : Nat := 4983230072969 + 3 ^ 40 * 8904 * 2
def baseEnd_8904 : Nat := 1354676073403969410091

theorem tailTrace_8904 : CollatzResearch.WordTrace tailWord_8904 prefixEnd_8904 1354676073403969410091 := by
  unfold tailWord_8904
  simp only [CollatzResearch.WordTrace]
  refine ⟨162377779874901763620883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 216503706499869018161177 162377779874901763620883)
  ·
    refine ⟨243566669812352645431325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162377779874901763620883 243566669812352645431325)
    ·
      refine ⟨91337501179632242036747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 243566669812352645431325 91337501179632242036747)
      ·
        refine ⟨137006251769448363055121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91337501179632242036747 137006251769448363055121)
        ·
          refine ⟨102754688827086272291341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137006251769448363055121 102754688827086272291341)
          ·
            refine ⟨38533008310157352109253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 102754688827086272291341 38533008310157352109253)
            ·
              refine ⟨7224939058154503520485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38533008310157352109253 7224939058154503520485)
              ·
                refine ⟨1354676073403969410091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7224939058154503520485 1354676073403969410091)
                ·
                  rfl

theorem cell20_8904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_8904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8904 prefixEnd_8904 := by exact prefixLift 8904
  have htrace : WordTrace (prefixWord ++ tailWord_8904) baseStart_8904 baseEnd_8904 := by
    simpa [prefixWord, tailWord_8904, baseEnd_8904] using wordTrace_append hprefix tailTrace_8904
  have hstable : (prefixWord ++ tailWord_8904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8904).length < 2 ^ (prefixWord ++ tailWord_8904).sum := by decide
  have hdescent : baseEnd_8904 < baseStart_8904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8931 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 2]
def baseStart_8931 : Nat := 118140960795 + 8931 * 2 ^ 59
def prefixEnd_8931 : Nat := 4983230072969 + 3 ^ 40 * 8931 * 2
def baseEnd_8931 : Nat := 4076351755919814330163

theorem tailTrace_8931 : CollatzResearch.WordTrace tailWord_8931 prefixEnd_8931 4076351755919814330163 := by
  unfold tailWord_8931
  simp only [CollatzResearch.WordTrace]
  refine ⟨325740330651987138474647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 217160220434658092316431 325740330651987138474647)
  ·
    refine ⟨488610495977980707711971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 325740330651987138474647 488610495977980707711971)
    ·
      refine ⟨732915743966971061567957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 488610495977980707711971 732915743966971061567957)
      ·
        refine ⟨17177712749225884255499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 732915743966971061567957 17177712749225884255499)
        ·
          refine ⟨25766569123838826383249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17177712749225884255499 25766569123838826383249)
          ·
            refine ⟨19324926842879119787437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25766569123838826383249 19324926842879119787437)
            ·
              refine ⟨7246847566079669920289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19324926842879119787437 7246847566079669920289)
              ·
                refine ⟨5435135674559752440217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7246847566079669920289 5435135674559752440217)
                ·
                  refine ⟨4076351755919814330163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5435135674559752440217 4076351755919814330163)
                  ·
                    rfl

theorem cell20_8931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 2].length) (baseStart_8931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8931 prefixEnd_8931 := by exact prefixLift 8931
  have htrace : WordTrace (prefixWord ++ tailWord_8931) baseStart_8931 baseEnd_8931 := by
    simpa [prefixWord, tailWord_8931, baseEnd_8931] using wordTrace_append hprefix tailTrace_8931
  have hstable : (prefixWord ++ tailWord_8931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8931).length < 2 ^ (prefixWord ++ tailWord_8931).sum := by decide
  have hdescent : baseEnd_8931 < baseStart_8931 := by decide
  rcases family_descends (prefixWord ++ tailWord_8931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8942 : List Nat := [4, 1, 2, 1, 1, 4, 2, 5]
def baseStart_8942 : Nat := 118140960795 + 8942 * 2 ^ 59
def prefixEnd_8942 : Nat := 4983230072969 + 3 ^ 40 * 8942 * 2
def baseEnd_8942 : Nat := 1360457485217554987817

theorem tailTrace_8942 : CollatzResearch.WordTrace tailWord_8942 prefixEnd_8942 1360457485217554987817 := by
  unfold tailWord_8942
  simp only [CollatzResearch.WordTrace]
  refine ⟨40767691701517002140635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 217427689074757344750053 40767691701517002140635)
  ·
    refine ⟨61151537552275503210953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40767691701517002140635 61151537552275503210953)
    ·
      refine ⟨45863653164206627408215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61151537552275503210953 45863653164206627408215)
      ·
        refine ⟨68795479746309941112323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45863653164206627408215 68795479746309941112323)
        ·
          refine ⟨103193219619464911668485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68795479746309941112323 103193219619464911668485)
          ·
            refine ⟨19348728678649670937841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103193219619464911668485 19348728678649670937841)
            ·
              refine ⟨14511546508987253203381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19348728678649670937841 14511546508987253203381)
              ·
                refine ⟨1360457485217554987817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14511546508987253203381 1360457485217554987817)
                ·
                  rfl

theorem cell20_8942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_8942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8942 prefixEnd_8942 := by exact prefixLift 8942
  have htrace : WordTrace (prefixWord ++ tailWord_8942) baseStart_8942 baseEnd_8942 := by
    simpa [prefixWord, tailWord_8942, baseEnd_8942] using wordTrace_append hprefix tailTrace_8942
  have hstable : (prefixWord ++ tailWord_8942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8942).length < 2 ^ (prefixWord ++ tailWord_8942).sum := by decide
  have hdescent : baseEnd_8942 < baseStart_8942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8980 : List Nat := [2, 4, 4, 10]
def baseStart_8980 : Nat := 118140960795 + 8980 * 2 ^ 59
def prefixEnd_8980 : Nat := 4983230072969 + 3 ^ 40 * 8980 * 2
def baseEnd_8980 : Nat := 16867146876927661303

theorem tailTrace_8980 : CollatzResearch.WordTrace tailWord_8980 prefixEnd_8980 16867146876927661303 := by
  unfold tailWord_8980
  simp only [CollatzResearch.WordTrace]
  refine ⟨163763753737234253504197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 218351671649645671338929 163763753737234253504197)
  ·
    refine ⟨30705703825731422532037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163763753737234253504197 30705703825731422532037)
    ·
      refine ⟨5757319467324641724757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30705703825731422532037 5757319467324641724757)
      ·
        refine ⟨16867146876927661303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 5757319467324641724757 16867146876927661303)
        ·
          rfl

theorem cell20_8980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 10].length) (baseStart_8980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_8980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_8980 prefixEnd_8980 := by exact prefixLift 8980
  have htrace : WordTrace (prefixWord ++ tailWord_8980) baseStart_8980 baseEnd_8980 := by
    simpa [prefixWord, tailWord_8980, baseEnd_8980] using wordTrace_append hprefix tailTrace_8980
  have hstable : (prefixWord ++ tailWord_8980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8980).length < 2 ^ (prefixWord ++ tailWord_8980).sum := by decide
  have hdescent : baseEnd_8980 < baseStart_8980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9014 : List Nat := [5, 1, 2, 2, 2, 1, 3, 4]
def baseStart_9014 : Nat := 118140960795 + 9014 * 2 ^ 59
def prefixEnd_9014 : Nat := 4983230072969 + 3 ^ 40 * 9014 * 2
def baseEnd_9014 : Nat := 1371411739180138187719

theorem tailTrace_9014 : CollatzResearch.WordTrace tailWord_9014 prefixEnd_9014 1371411739180138187719 := by
  unfold tailWord_9014
  simp only [CollatzResearch.WordTrace]
  refine ⟨20547974334455769609131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 219178392900861542497397 20547974334455769609131)
  ·
    refine ⟨30821961501683654413697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20547974334455769609131 30821961501683654413697)
    ·
      refine ⟨23116471126262740810273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30821961501683654413697 23116471126262740810273)
      ·
        refine ⟨17337353344697055607705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23116471126262740810273 17337353344697055607705)
        ·
          refine ⟨13003015008522791705779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17337353344697055607705 13003015008522791705779)
          ·
            refine ⟨19504522512784187558669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13003015008522791705779 19504522512784187558669)
            ·
              refine ⟨7314195942294070334501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19504522512784187558669 7314195942294070334501)
              ·
                refine ⟨1371411739180138187719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7314195942294070334501 1371411739180138187719)
                ·
                  rfl

theorem cell20_9014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_9014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9014 prefixEnd_9014 := by exact prefixLift 9014
  have htrace : WordTrace (prefixWord ++ tailWord_9014) baseStart_9014 baseEnd_9014 := by
    simpa [prefixWord, tailWord_9014, baseEnd_9014] using wordTrace_append hprefix tailTrace_9014
  have hstable : (prefixWord ++ tailWord_9014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9014).length < 2 ^ (prefixWord ++ tailWord_9014).sum := by decide
  have hdescent : baseEnd_9014 < baseStart_9014 := by decide
  rcases family_descends (prefixWord ++ tailWord_9014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9049 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 2]
def baseStart_9049 : Nat := 118140960795 + 9049 * 2 ^ 59
def prefixEnd_9049 : Nat := 4983230072969 + 3 ^ 40 * 9049 * 2
def baseEnd_9049 : Nat := 4130210171235848396347

theorem tailTrace_9049 : CollatzResearch.WordTrace tailWord_9049 prefixEnd_9049 4130210171235848396347 := by
  unfold tailWord_9049
  simp only [CollatzResearch.WordTrace]
  refine ⟨330044144224493291270201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 220029429482995527513467 330044144224493291270201)
  ·
    refine ⟨247533108168369968452651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 330044144224493291270201 247533108168369968452651)
    ·
      refine ⟨371299662252554952678977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247533108168369968452651 371299662252554952678977)
      ·
        refine ⟨278474746689416214509233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371299662252554952678977 278474746689416214509233)
        ·
          refine ⟨208856060017062160881925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 278474746689416214509233 208856060017062160881925)
          ·
            refine ⟨39160511253199155165361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 208856060017062160881925 39160511253199155165361)
            ·
              refine ⟨29370383439899366374021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39160511253199155165361 29370383439899366374021)
              ·
                refine ⟨5506946894981131195129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29370383439899366374021 5506946894981131195129)
                ·
                  refine ⟨4130210171235848396347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5506946894981131195129 4130210171235848396347)
                  ·
                    rfl

theorem cell20_9049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_9049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9049 prefixEnd_9049 := by exact prefixLift 9049
  have htrace : WordTrace (prefixWord ++ tailWord_9049) baseStart_9049 baseEnd_9049 := by
    simpa [prefixWord, tailWord_9049, baseEnd_9049] using wordTrace_append hprefix tailTrace_9049
  have hstable : (prefixWord ++ tailWord_9049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9049).length < 2 ^ (prefixWord ++ tailWord_9049).sum := by decide
  have hdescent : baseEnd_9049 < baseStart_9049 := by decide
  rcases family_descends (prefixWord ++ tailWord_9049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9087 : List Nat := [1, 1, 2, 2, 1, 1, 7, 3, 2]
def baseStart_9087 : Nat := 118140960795 + 9087 * 2 ^ 59
def prefixEnd_9087 : Nat := 4983230072969 + 3 ^ 40 * 9087 * 2
def baseEnd_9087 : Nat := 4147554406676605129525

theorem tailTrace_9087 : CollatzResearch.WordTrace tailWord_9087 prefixEnd_9087 4147554406676605129525 := by
  unfold tailWord_9087
  simp only [CollatzResearch.WordTrace]
  refine ⟨331430118086825781153515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 220953412057883854102343 331430118086825781153515)
  ·
    refine ⟨497145177130238671730273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 331430118086825781153515 497145177130238671730273)
    ·
      refine ⟨372858882847679003797705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 497145177130238671730273 372858882847679003797705)
      ·
        refine ⟨279644162135759252848279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372858882847679003797705 279644162135759252848279)
        ·
          refine ⟨419466243203638879272419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279644162135759252848279 419466243203638879272419)
          ·
            refine ⟨629199364805458318908629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419466243203638879272419 629199364805458318908629)
            ·
              refine ⟨14746860112627929349421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 629199364805458318908629 14746860112627929349421)
              ·
                refine ⟨5530072542235473506033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14746860112627929349421 5530072542235473506033)
                ·
                  refine ⟨4147554406676605129525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5530072542235473506033 4147554406676605129525)
                  ·
                    rfl

theorem cell20_9087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 3, 2].length) (baseStart_9087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9087 prefixEnd_9087 := by exact prefixLift 9087
  have htrace : WordTrace (prefixWord ++ tailWord_9087) baseStart_9087 baseEnd_9087 := by
    simpa [prefixWord, tailWord_9087, baseEnd_9087] using wordTrace_append hprefix tailTrace_9087
  have hstable : (prefixWord ++ tailWord_9087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9087).length < 2 ^ (prefixWord ++ tailWord_9087).sum := by decide
  have hdescent : baseEnd_9087 < baseStart_9087 := by decide
  rcases family_descends (prefixWord ++ tailWord_9087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9090 : List Nat := [3, 4, 2, 2, 1, 2, 6]
def baseStart_9090 : Nat := 118140960795 + 9090 * 2 ^ 59
def prefixEnd_9090 : Nat := 4983230072969 + 3 ^ 40 * 9090 * 2
def baseEnd_9090 : Nat := 460991520935769781057

theorem tailTrace_9090 : CollatzResearch.WordTrace tailWord_9090 prefixEnd_9090 460991520935769781057 := by
  unfold tailWord_9090
  simp only [CollatzResearch.WordTrace]
  refine ⟨82884884268989323378181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 221026358050638195675149 82884884268989323378181)
  ·
    refine ⟨15540915800435498133409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82884884268989323378181 15540915800435498133409)
    ·
      refine ⟨11655686850326623600057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15540915800435498133409 11655686850326623600057)
      ·
        refine ⟨8741765137744967700043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11655686850326623600057 8741765137744967700043)
        ·
          refine ⟨13112647706617451550065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8741765137744967700043 13112647706617451550065)
          ·
            refine ⟨9834485779963088662549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13112647706617451550065 9834485779963088662549)
            ·
              refine ⟨460991520935769781057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9834485779963088662549 460991520935769781057)
              ·
                rfl

theorem cell20_9090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 6].length) (baseStart_9090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9090 prefixEnd_9090 := by exact prefixLift 9090
  have htrace : WordTrace (prefixWord ++ tailWord_9090) baseStart_9090 baseEnd_9090 := by
    simpa [prefixWord, tailWord_9090, baseEnd_9090] using wordTrace_append hprefix tailTrace_9090
  have hstable : (prefixWord ++ tailWord_9090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9090).length < 2 ^ (prefixWord ++ tailWord_9090).sum := by decide
  have hdescent : baseEnd_9090 < baseStart_9090 := by decide
  rcases family_descends (prefixWord ++ tailWord_9090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9114 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_9114 : Nat := 118140960795 + 9114 * 2 ^ 59
def prefixEnd_9114 : Nat := 4983230072969 + 3 ^ 40 * 9114 * 2
def baseEnd_9114 : Nat := 4159877942384511229415

theorem tailTrace_9114 : CollatzResearch.WordTrace tailWord_9114 prefixEnd_9114 4159877942384511229415 := by
  unfold tailWord_9114
  simp only [CollatzResearch.WordTrace]
  refine ⟨83103722247252348096599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 221609925992672928257597 83103722247252348096599)
  ·
    refine ⟨124655583370878522144899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83103722247252348096599 124655583370878522144899)
    ·
      refine ⟨186983375056317783217349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124655583370878522144899 186983375056317783217349)
      ·
        refine ⟨35059382823059584353253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186983375056317783217349 35059382823059584353253)
        ·
          refine ⟨6573634279323672066235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35059382823059584353253 6573634279323672066235)
          ·
            refine ⟨9860451418985508099353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573634279323672066235 9860451418985508099353)
            ·
              refine ⟨7395338564239131074515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9860451418985508099353 7395338564239131074515)
              ·
                refine ⟨11093007846358696611773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7395338564239131074515 11093007846358696611773)
                ·
                  refine ⟨4159877942384511229415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11093007846358696611773 4159877942384511229415)
                  ·
                    rfl

theorem cell20_9114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_9114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9114 prefixEnd_9114 := by exact prefixLift 9114
  have htrace : WordTrace (prefixWord ++ tailWord_9114) baseStart_9114 baseEnd_9114 := by
    simpa [prefixWord, tailWord_9114, baseEnd_9114] using wordTrace_append hprefix tailTrace_9114
  have hstable : (prefixWord ++ tailWord_9114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9114).length < 2 ^ (prefixWord ++ tailWord_9114).sum := by decide
  have hdescent : baseEnd_9114 < baseStart_9114 := by decide
  rcases family_descends (prefixWord ++ tailWord_9114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9129 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_9129 : Nat := 118140960795 + 9129 * 2 ^ 59
def prefixEnd_9129 : Nat := 4983230072969 + 3 ^ 40 * 9129 * 2
def baseEnd_9129 : Nat := 4166724351111125729353

theorem tailTrace_9129 : CollatzResearch.WordTrace tailWord_9129 prefixEnd_9129 4166724351111125729353 := by
  unfold tailWord_9129
  simp only [CollatzResearch.WordTrace]
  refine ⟨332961983934666954182441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 221974655956444636121627 332961983934666954182441)
  ·
    refine ⟨249721487951000215636831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 332961983934666954182441 249721487951000215636831)
    ·
      refine ⟨374582231926500323455247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249721487951000215636831 374582231926500323455247)
      ·
        refine ⟨561873347889750485182871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374582231926500323455247 561873347889750485182871)
        ·
          refine ⟨842810021834625727774307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 561873347889750485182871 842810021834625727774307)
          ·
            refine ⟨1264215032751938591661461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 842810021834625727774307 1264215032751938591661461)
            ·
              refine ⟨59260079660247121484131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1264215032751938591661461 59260079660247121484131)
              ·
                refine ⟨88890119490370682226197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59260079660247121484131 88890119490370682226197)
                ·
                  refine ⟨4166724351111125729353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88890119490370682226197 4166724351111125729353)
                  ·
                    rfl

theorem cell20_9129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_9129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9129 prefixEnd_9129 := by exact prefixLift 9129
  have htrace : WordTrace (prefixWord ++ tailWord_9129) baseStart_9129 baseEnd_9129 := by
    simpa [prefixWord, tailWord_9129, baseEnd_9129] using wordTrace_append hprefix tailTrace_9129
  have hstable : (prefixWord ++ tailWord_9129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9129).length < 2 ^ (prefixWord ++ tailWord_9129).sum := by decide
  have hdescent : baseEnd_9129 < baseStart_9129 := by decide
  rcases family_descends (prefixWord ++ tailWord_9129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9163 : List Nat := [1, 1, 1, 1, 3, 6, 1, 4, 2]
def baseStart_9163 : Nat := 118140960795 + 9163 * 2 ^ 59
def prefixEnd_9163 : Nat := 4983230072969 + 3 ^ 40 * 9163 * 2
def baseEnd_9163 : Nat := 4182242877558118595881

theorem tailTrace_9163 : CollatzResearch.WordTrace tailWord_9163 prefixEnd_9163 4182242877558118595881 := by
  unfold tailWord_9163
  simp only [CollatzResearch.WordTrace]
  refine ⟨334202065811490760920143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 222801377207660507280095 334202065811490760920143)
  ·
    refine ⟨501303098717236141380215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334202065811490760920143 501303098717236141380215)
    ·
      refine ⟨751954648075854212070323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501303098717236141380215 751954648075854212070323)
      ·
        refine ⟨1127931972113781318105485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751954648075854212070323 1127931972113781318105485)
        ·
          refine ⟨422974489542667994289557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1127931972113781318105485 422974489542667994289557)
          ·
            refine ⟨19826929197312562232323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 422974489542667994289557 19826929197312562232323)
            ·
              refine ⟨29740393795968843348485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19826929197312562232323 29740393795968843348485)
              ·
                refine ⟨5576323836744158127841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29740393795968843348485 5576323836744158127841)
                ·
                  refine ⟨4182242877558118595881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576323836744158127841 4182242877558118595881)
                  ·
                    rfl

theorem cell20_9163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 4, 2].length) (baseStart_9163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9163 prefixEnd_9163 := by exact prefixLift 9163
  have htrace : WordTrace (prefixWord ++ tailWord_9163) baseStart_9163 baseEnd_9163 := by
    simpa [prefixWord, tailWord_9163, baseEnd_9163] using wordTrace_append hprefix tailTrace_9163
  have hstable : (prefixWord ++ tailWord_9163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9163).length < 2 ^ (prefixWord ++ tailWord_9163).sum := by decide
  have hdescent : baseEnd_9163 < baseStart_9163 := by decide
  rcases family_descends (prefixWord ++ tailWord_9163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9170 : List Nat := [3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_9170 : Nat := 118140960795 + 9170 * 2 ^ 59
def prefixEnd_9170 : Nat := 4983230072969 + 3 ^ 40 * 9170 * 2
def baseEnd_9170 : Nat := 1395145956099068454173

theorem tailTrace_9170 : CollatzResearch.WordTrace tailWord_9170 prefixEnd_9170 1395145956099068454173 := by
  unfold tailWord_9170
  simp only [CollatzResearch.WordTrace]
  refine ⟨83614344196532739106241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 222971584524087304283309 83614344196532739106241)
  ·
    refine ⟨62710758147399554329681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83614344196532739106241 62710758147399554329681)
    ·
      refine ⟨47033068610549665747261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62710758147399554329681 47033068610549665747261)
      ·
        refine ⟨17637400728956124655223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47033068610549665747261 17637400728956124655223)
        ·
          refine ⟨26456101093434186982835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17637400728956124655223 26456101093434186982835)
          ·
            refine ⟨39684151640151280474253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26456101093434186982835 39684151640151280474253)
            ·
              refine ⟨14881556865056730177845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39684151640151280474253 14881556865056730177845)
              ·
                refine ⟨1395145956099068454173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14881556865056730177845 1395145956099068454173)
                ·
                  rfl

theorem cell20_9170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_9170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9170 prefixEnd_9170 := by exact prefixLift 9170
  have htrace : WordTrace (prefixWord ++ tailWord_9170) baseStart_9170 baseEnd_9170 := by
    simpa [prefixWord, tailWord_9170, baseEnd_9170] using wordTrace_append hprefix tailTrace_9170
  have hstable : (prefixWord ++ tailWord_9170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9170).length < 2 ^ (prefixWord ++ tailWord_9170).sum := by decide
  have hdescent : baseEnd_9170 < baseStart_9170 := by decide
  rcases family_descends (prefixWord ++ tailWord_9170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9177 : List Nat := [1, 2, 1, 2, 5, 1, 2, 3, 3]
def baseStart_9177 : Nat := 118140960795 + 9177 * 2 ^ 59
def prefixEnd_9177 : Nat := 4983230072969 + 3 ^ 40 * 9177 * 2
def baseEnd_9177 : Nat := 4188632859036292129157

theorem tailTrace_9177 : CollatzResearch.WordTrace tailWord_9177 prefixEnd_9177 4188632859036292129157 := by
  unfold tailWord_9177
  simp only [CollatzResearch.WordTrace]
  refine ⟨334712687760771151929785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 223141791840514101286523 334712687760771151929785)
  ·
    refine ⟨251034515820578363947339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 334712687760771151929785 251034515820578363947339)
    ·
      refine ⟨376551773730867545921009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251034515820578363947339 376551773730867545921009)
      ·
        refine ⟨282413830298150659440757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376551773730867545921009 282413830298150659440757)
        ·
          refine ⟨26476296590451624322571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282413830298150659440757 26476296590451624322571)
          ·
            refine ⟨39714444885677436483857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26476296590451624322571 39714444885677436483857)
            ·
              refine ⟨29785833664258077362893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39714444885677436483857 29785833664258077362893)
              ·
                refine ⟨11169687624096779011085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29785833664258077362893 11169687624096779011085)
                ·
                  refine ⟨4188632859036292129157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11169687624096779011085 4188632859036292129157)
                  ·
                    rfl

theorem cell20_9177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_9177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9177 prefixEnd_9177 := by exact prefixLift 9177
  have htrace : WordTrace (prefixWord ++ tailWord_9177) baseStart_9177 baseEnd_9177 := by
    simpa [prefixWord, tailWord_9177, baseEnd_9177] using wordTrace_append hprefix tailTrace_9177
  have hstable : (prefixWord ++ tailWord_9177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9177).length < 2 ^ (prefixWord ++ tailWord_9177).sum := by decide
  have hdescent : baseEnd_9177 < baseStart_9177 := by decide
  rcases family_descends (prefixWord ++ tailWord_9177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9201 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 2]
def baseStart_9201 : Nat := 118140960795 + 9201 * 2 ^ 59
def prefixEnd_9201 : Nat := 4983230072969 + 3 ^ 40 * 9201 * 2
def baseEnd_9201 : Nat := 4199587112998875329059

theorem tailTrace_9201 : CollatzResearch.WordTrace tailWord_9201 prefixEnd_9201 4199587112998875329059 := by
  unfold tailWord_9201
  simp only [CollatzResearch.WordTrace]
  refine ⟨335588039673823250803457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 223725359782548833868971 335588039673823250803457)
  ·
    refine ⟨251691029755367438102593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 335588039673823250803457 251691029755367438102593)
    ·
      refine ⟨188768272316525578576945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251691029755367438102593 188768272316525578576945)
      ·
        refine ⟨141576204237394183932709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188768272316525578576945 141576204237394183932709)
        ·
          refine ⟨26545538294511409487383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141576204237394183932709 26545538294511409487383)
          ·
            refine ⟨39818307441767114231075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26545538294511409487383 39818307441767114231075)
            ·
              refine ⟨59727461162650671346613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39818307441767114231075 59727461162650671346613)
              ·
                refine ⟨5599449483998500438745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59727461162650671346613 5599449483998500438745)
                ·
                  refine ⟨4199587112998875329059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5599449483998500438745 4199587112998875329059)
                  ·
                    rfl

theorem cell20_9201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_9201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9201 prefixEnd_9201 := by exact prefixLift 9201
  have htrace : WordTrace (prefixWord ++ tailWord_9201) baseStart_9201 baseEnd_9201 := by
    simpa [prefixWord, tailWord_9201, baseEnd_9201] using wordTrace_append hprefix tailTrace_9201
  have hstable : (prefixWord ++ tailWord_9201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9201).length < 2 ^ (prefixWord ++ tailWord_9201).sum := by decide
  have hdescent : baseEnd_9201 < baseStart_9201 := by decide
  rcases family_descends (prefixWord ++ tailWord_9201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9274 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_9274 : Nat := 118140960795 + 9274 * 2 ^ 59
def prefixEnd_9274 : Nat := 4983230072969 + 3 ^ 40 * 9274 * 2
def baseEnd_9274 : Nat := 4232906302135065895427

theorem tailTrace_9274 : CollatzResearch.WordTrace tailWord_9274 prefixEnd_9274 4232906302135065895427 := by
  unfold tailWord_9274
  simp only [CollatzResearch.WordTrace]
  refine ⟨84562642102339179552719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 225500378939571145473917 84562642102339179552719)
  ·
    refine ⟨126843963153508769329079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84562642102339179552719 126843963153508769329079)
    ·
      refine ⟨190265944730263153993619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126843963153508769329079 190265944730263153993619)
      ·
        refine ⟨285398917095394730990429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190265944730263153993619 285398917095394730990429)
        ·
          refine ⟨107024593910773024121411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285398917095394730990429 107024593910773024121411)
          ·
            refine ⟨160536890866159536182117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107024593910773024121411 160536890866159536182117)
            ·
              refine ⟨30100667037404913034147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160536890866159536182117 30100667037404913034147)
              ·
                refine ⟨45151000556107369551221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30100667037404913034147 45151000556107369551221)
                ·
                  refine ⟨4232906302135065895427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45151000556107369551221 4232906302135065895427)
                  ·
                    rfl

theorem cell20_9274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_9274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9274 prefixEnd_9274 := by exact prefixLift 9274
  have htrace : WordTrace (prefixWord ++ tailWord_9274) baseStart_9274 baseEnd_9274 := by
    simpa [prefixWord, tailWord_9274, baseEnd_9274] using wordTrace_append hprefix tailTrace_9274
  have hstable : (prefixWord ++ tailWord_9274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9274).length < 2 ^ (prefixWord ++ tailWord_9274).sum := by decide
  have hdescent : baseEnd_9274 < baseStart_9274 := by decide
  rcases family_descends (prefixWord ++ tailWord_9274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9277 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 4]
def baseStart_9277 : Nat := 118140960795 + 9277 * 2 ^ 59
def prefixEnd_9277 : Nat := 4983230072969 + 3 ^ 40 * 9277 * 2
def baseEnd_9277 : Nat := 4234275583880388795415

theorem tailTrace_9277 : CollatzResearch.WordTrace tailWord_9277 prefixEnd_9277 4234275583880388795415 := by
  unfold tailWord_9277
  simp only [CollatzResearch.WordTrace]
  refine ⟨338359987398488230570085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 225573324932325487046723 338359987398488230570085)
  ·
    refine ⟨63442497637216543231891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 338359987398488230570085 63442497637216543231891)
    ·
      refine ⟨95163746455824814847837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63442497637216543231891 95163746455824814847837)
      ·
        refine ⟨35686404920934305567939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95163746455824814847837 35686404920934305567939)
        ·
          refine ⟨53529607381401458351909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35686404920934305567939 53529607381401458351909)
          ·
            refine ⟨10036801384012773440983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53529607381401458351909 10036801384012773440983)
            ·
              refine ⟨15055202076019160161475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10036801384012773440983 15055202076019160161475)
              ·
                refine ⟨22582803114028740242213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15055202076019160161475 22582803114028740242213)
                ·
                  refine ⟨4234275583880388795415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22582803114028740242213 4234275583880388795415)
                  ·
                    rfl

theorem cell20_9277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_9277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9277 prefixEnd_9277 := by exact prefixLift 9277
  have htrace : WordTrace (prefixWord ++ tailWord_9277) baseStart_9277 baseEnd_9277 := by
    simpa [prefixWord, tailWord_9277, baseEnd_9277] using wordTrace_append hprefix tailTrace_9277
  have hstable : (prefixWord ++ tailWord_9277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9277).length < 2 ^ (prefixWord ++ tailWord_9277).sum := by decide
  have hdescent : baseEnd_9277 < baseStart_9277 := by decide
  rcases family_descends (prefixWord ++ tailWord_9277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9370 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_9370 : Nat := 118140960795 + 9370 * 2 ^ 59
def prefixEnd_9370 : Nat := 4983230072969 + 3 ^ 40 * 9370 * 2
def baseEnd_9370 : Nat := 4276723317985398695035

theorem tailTrace_9370 : CollatzResearch.WordTrace tailWord_9370 prefixEnd_9370 4276723317985398695035 := by
  unfold tailWord_9370
  simp only [CollatzResearch.WordTrace]
  refine ⟨85437994015391278426391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 227834650707710075803709 85437994015391278426391)
  ·
    refine ⟨128156991023086917639587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85437994015391278426391 128156991023086917639587)
    ·
      refine ⟨192235486534630376459381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128156991023086917639587 192235486534630376459381)
      ·
        refine ⟨18022076862621597793067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 192235486534630376459381 18022076862621597793067)
        ·
          refine ⟨27033115293932396689601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18022076862621597793067 27033115293932396689601)
          ·
            refine ⟨20274836470449297517201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27033115293932396689601 20274836470449297517201)
            ·
              refine ⟨15206127352836973137901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20274836470449297517201 15206127352836973137901)
              ·
                refine ⟨5702297757313864926713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15206127352836973137901 5702297757313864926713)
                ·
                  refine ⟨4276723317985398695035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5702297757313864926713 4276723317985398695035)
                  ·
                    rfl

theorem cell20_9370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_9370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9370 prefixEnd_9370 := by exact prefixLift 9370
  have htrace : WordTrace (prefixWord ++ tailWord_9370) baseStart_9370 baseEnd_9370 := by
    simpa [prefixWord, tailWord_9370, baseEnd_9370] using wordTrace_append hprefix tailTrace_9370
  have hstable : (prefixWord ++ tailWord_9370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9370).length < 2 ^ (prefixWord ++ tailWord_9370).sum := by decide
  have hdescent : baseEnd_9370 < baseStart_9370 := by decide
  rcases family_descends (prefixWord ++ tailWord_9370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9388 : List Nat := [2, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_9388 : Nat := 118140960795 + 9388 * 2 ^ 59
def prefixEnd_9388 : Nat := 4983230072969 + 3 ^ 40 * 9388 * 2
def baseEnd_9388 : Nat := 4284939008457336094961

theorem tailTrace_9388 : CollatzResearch.WordTrace tailWord_9388 prefixEnd_9388 4284939008457336094961 := by
  unfold tailWord_9388
  simp only [CollatzResearch.WordTrace]
  refine ⟨171204244998177093930409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 228272326664236125240545 171204244998177093930409)
  ·
    refine ⟨128403183748632820447807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171204244998177093930409 128403183748632820447807)
    ·
      refine ⟨192604775622949230671711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128403183748632820447807 192604775622949230671711)
      ·
        refine ⟨288907163434423846007567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192604775622949230671711 288907163434423846007567)
        ·
          refine ⟨433360745151635769011351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 288907163434423846007567 433360745151635769011351)
          ·
            refine ⟨650041117727453653517027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433360745151635769011351 650041117727453653517027)
            ·
              refine ⟨975061676591180480275541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650041117727453653517027 975061676591180480275541)
              ·
                refine ⟨11426504022552896253229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 975061676591180480275541 11426504022552896253229)
                ·
                  refine ⟨4284939008457336094961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11426504022552896253229 4284939008457336094961)
                  ·
                    rfl

theorem cell20_9388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_9388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9388 prefixEnd_9388 := by exact prefixLift 9388
  have htrace : WordTrace (prefixWord ++ tailWord_9388) baseStart_9388 baseEnd_9388 := by
    simpa [prefixWord, tailWord_9388, baseEnd_9388] using wordTrace_append hprefix tailTrace_9388
  have hstable : (prefixWord ++ tailWord_9388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9388).length < 2 ^ (prefixWord ++ tailWord_9388).sum := by decide
  have hdescent : baseEnd_9388 < baseStart_9388 := by decide
  rcases family_descends (prefixWord ++ tailWord_9388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9395 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 4]
def baseStart_9395 : Nat := 118140960795 + 9395 * 2 ^ 59
def prefixEnd_9395 : Nat := 4983230072969 + 3 ^ 40 * 9395 * 2
def baseEnd_9395 : Nat := 4288133999196422861599

theorem tailTrace_9395 : CollatzResearch.WordTrace tailWord_9395 prefixEnd_9395 4288133999196422861599 := by
  unfold tailWord_9395
  simp only [CollatzResearch.WordTrace]
  refine ⟨342663800970994383365639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 228442533980662922243759 342663800970994383365639)
  ·
    refine ⟨513995701456491575048459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342663800970994383365639 513995701456491575048459)
    ·
      refine ⟨770993552184737362572689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513995701456491575048459 770993552184737362572689)
      ·
        refine ⟨578245164138553021929517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 770993552184737362572689 578245164138553021929517)
        ·
          refine ⟨216841936551957383223569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578245164138553021929517 216841936551957383223569)
          ·
            refine ⟨162631452413968037417677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 216841936551957383223569 162631452413968037417677)
            ·
              refine ⟨60986794655238014031629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162631452413968037417677 60986794655238014031629)
              ·
                refine ⟨22870047995714255261861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60986794655238014031629 22870047995714255261861)
                ·
                  refine ⟨4288133999196422861599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22870047995714255261861 4288133999196422861599)
                  ·
                    rfl

theorem cell20_9395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_9395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9395 prefixEnd_9395 := by exact prefixLift 9395
  have htrace : WordTrace (prefixWord ++ tailWord_9395) baseStart_9395 baseEnd_9395 := by
    simpa [prefixWord, tailWord_9395, baseEnd_9395] using wordTrace_append hprefix tailTrace_9395
  have hstable : (prefixWord ++ tailWord_9395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9395).length < 2 ^ (prefixWord ++ tailWord_9395).sum := by decide
  have hdescent : baseEnd_9395 < baseStart_9395 := by decide
  rcases family_descends (prefixWord ++ tailWord_9395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9402 : List Nat := [3, 1, 1, 1, 2, 2, 1, 9]
def baseStart_9402 : Nat := 118140960795 + 9402 * 2 ^ 59
def prefixEnd_9402 : Nat := 4983230072969 + 3 ^ 40 * 9402 * 2
def baseEnd_9402 : Nat := 1430442996645169876079

theorem tailTrace_9402 : CollatzResearch.WordTrace tailWord_9402 prefixEnd_9402 1430442996645169876079 := by
  unfold tailWord_9402
  simp only [CollatzResearch.WordTrace]
  refine ⟨85729777986408644717615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 228612741297089719246973 85729777986408644717615)
  ·
    refine ⟨128594666979612967076423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85729777986408644717615 128594666979612967076423)
    ·
      refine ⟨192892000469419450614635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128594666979612967076423 192892000469419450614635)
      ·
        refine ⟨289338000704129175921953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192892000469419450614635 289338000704129175921953)
        ·
          refine ⟨217003500528096881941465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289338000704129175921953 217003500528096881941465)
          ·
            refine ⟨162752625396072661456099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217003500528096881941465 162752625396072661456099)
            ·
              refine ⟨244128938094108992184149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162752625396072661456099 244128938094108992184149)
              ·
                refine ⟨1430442996645169876079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 244128938094108992184149 1430442996645169876079)
                ·
                  rfl

theorem cell20_9402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_9402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9402 prefixEnd_9402 := by exact prefixLift 9402
  have htrace : WordTrace (prefixWord ++ tailWord_9402) baseStart_9402 baseEnd_9402 := by
    simpa [prefixWord, tailWord_9402, baseEnd_9402] using wordTrace_append hprefix tailTrace_9402
  have hstable : (prefixWord ++ tailWord_9402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9402).length < 2 ^ (prefixWord ++ tailWord_9402).sum := by decide
  have hdescent : baseEnd_9402 < baseStart_9402 := by decide
  rcases family_descends (prefixWord ++ tailWord_9402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9421 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 2]
def baseStart_9421 : Nat := 118140960795 + 9421 * 2 ^ 59
def prefixEnd_9421 : Nat := 4983230072969 + 3 ^ 40 * 9421 * 2
def baseEnd_9421 : Nat := 4300001107655887994827

theorem tailTrace_9421 : CollatzResearch.WordTrace tailWord_9421 prefixEnd_9421 4300001107655887994827 := by
  unfold tailWord_9421
  simp only [CollatzResearch.WordTrace]
  refine ⟨343612098876800823812117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 229074732584533882541411 343612098876800823812117)
  ·
    refine ⟨16106817134850038616193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 343612098876800823812117 16106817134850038616193)
    ·
      refine ⟨12080112851137528962145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16106817134850038616193 12080112851137528962145)
      ·
        refine ⟨9060084638353146721609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12080112851137528962145 9060084638353146721609)
        ·
          refine ⟨6795063478764860041207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9060084638353146721609 6795063478764860041207)
          ·
            refine ⟨10192595218147290061811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795063478764860041207 10192595218147290061811)
            ·
              refine ⟨15288892827220935092717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10192595218147290061811 15288892827220935092717)
              ·
                refine ⟨5733334810207850659769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15288892827220935092717 5733334810207850659769)
                ·
                  refine ⟨4300001107655887994827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5733334810207850659769 4300001107655887994827)
                  ·
                    rfl

theorem cell20_9421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_9421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9421 prefixEnd_9421 := by exact prefixLift 9421
  have htrace : WordTrace (prefixWord ++ tailWord_9421) baseStart_9421 baseEnd_9421 := by
    simpa [prefixWord, tailWord_9421, baseEnd_9421] using wordTrace_append hprefix tailTrace_9421
  have hstable : (prefixWord ++ tailWord_9421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9421).length < 2 ^ (prefixWord ++ tailWord_9421).sum := by decide
  have hdescent : baseEnd_9421 < baseStart_9421 := by decide
  rcases family_descends (prefixWord ++ tailWord_9421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9426 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_9426 : Nat := 118140960795 + 9426 * 2 ^ 59
def prefixEnd_9426 : Nat := 4983230072969 + 3 ^ 40 * 9426 * 2
def baseEnd_9426 : Nat := 4302283243898092828139

theorem tailTrace_9426 : CollatzResearch.WordTrace tailWord_9426 prefixEnd_9426 4302283243898092828139 := by
  unfold tailWord_9426
  simp only [CollatzResearch.WordTrace]
  refine ⟨85948615964671669436033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 229196309239124451829421 85948615964671669436033)
  ·
    refine ⟨64461461973503752077025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85948615964671669436033 64461461973503752077025)
    ·
      refine ⟨48346096480127814057769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64461461973503752077025 48346096480127814057769)
      ·
        refine ⟨36259572360095860543327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48346096480127814057769 36259572360095860543327)
        ·
          refine ⟨54389358540143790814991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36259572360095860543327 54389358540143790814991)
          ·
            refine ⟨81584037810215686222487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54389358540143790814991 81584037810215686222487)
            ·
              refine ⟨122376056715323529333731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81584037810215686222487 122376056715323529333731)
              ·
                refine ⟨183564085072985294000597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122376056715323529333731 183564085072985294000597)
                ·
                  refine ⟨4302283243898092828139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 183564085072985294000597 4302283243898092828139)
                  ·
                    rfl

theorem cell20_9426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_9426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9426 prefixEnd_9426 := by exact prefixLift 9426
  have htrace : WordTrace (prefixWord ++ tailWord_9426) baseStart_9426 baseEnd_9426 := by
    simpa [prefixWord, tailWord_9426, baseEnd_9426] using wordTrace_append hprefix tailTrace_9426
  have hstable : (prefixWord ++ tailWord_9426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9426).length < 2 ^ (prefixWord ++ tailWord_9426).sum := by decide
  have hdescent : baseEnd_9426 < baseStart_9426 := by decide
  rcases family_descends (prefixWord ++ tailWord_9426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9440 : List Nat := [2, 1, 1, 3, 1, 4, 8]
def baseStart_9440 : Nat := 118140960795 + 9440 * 2 ^ 59
def prefixEnd_9440 : Nat := 4983230072969 + 3 ^ 40 * 9440 * 2
def baseEnd_9440 : Nat := 478741469486251817935

theorem tailTrace_9440 : CollatzResearch.WordTrace tailWord_9440 prefixEnd_9440 478741469486251817935 := by
  unfold tailWord_9440
  simp only [CollatzResearch.WordTrace]
  refine ⟨172152542903983534376887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 229536723871978045835849 172152542903983534376887)
  ·
    refine ⟨258228814355975301565331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 172152542903983534376887 258228814355975301565331)
    ·
      refine ⟨387343221533962952347997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258228814355975301565331 387343221533962952347997)
      ·
        refine ⟨145253708075236107130499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 387343221533962952347997 145253708075236107130499)
        ·
          refine ⟨217880562112854160695749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145253708075236107130499 217880562112854160695749)
          ·
            refine ⟨40852605396160155130453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217880562112854160695749 40852605396160155130453)
            ·
              refine ⟨478741469486251817935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 40852605396160155130453 478741469486251817935)
              ·
                rfl

theorem cell20_9440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_9440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9440 prefixEnd_9440 := by exact prefixLift 9440
  have htrace : WordTrace (prefixWord ++ tailWord_9440) baseStart_9440 baseEnd_9440 := by
    simpa [prefixWord, tailWord_9440, baseEnd_9440] using wordTrace_append hprefix tailTrace_9440
  have hstable : (prefixWord ++ tailWord_9440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9440).length < 2 ^ (prefixWord ++ tailWord_9440).sum := by decide
  have hdescent : baseEnd_9440 < baseStart_9440 := by decide
  rcases family_descends (prefixWord ++ tailWord_9440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9450 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_9450 : Nat := 118140960795 + 9450 * 2 ^ 59
def prefixEnd_9450 : Nat := 4983230072969 + 3 ^ 40 * 9450 * 2
def baseEnd_9450 : Nat := 4313237497860676028041

theorem tailTrace_9450 : CollatzResearch.WordTrace tailWord_9450 prefixEnd_9450 4313237497860676028041 := by
  unfold tailWord_9450
  simp only [CollatzResearch.WordTrace]
  refine ⟨86167453942934694154451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 229779877181159184411869 86167453942934694154451)
  ·
    refine ⟨129251180914402041231677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86167453942934694154451 129251180914402041231677)
    ·
      refine ⟨48469192842900765461879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129251180914402041231677 48469192842900765461879)
      ·
        refine ⟨72703789264351148192819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48469192842900765461879 72703789264351148192819)
        ·
          refine ⟨109055683896526722289229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72703789264351148192819 109055683896526722289229)
          ·
            refine ⟨40895881461197520858461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109055683896526722289229 40895881461197520858461)
            ·
              refine ⟨15335955547949070321923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40895881461197520858461 15335955547949070321923)
              ·
                refine ⟨23003933321923605482885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15335955547949070321923 23003933321923605482885)
                ·
                  refine ⟨4313237497860676028041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23003933321923605482885 4313237497860676028041)
                  ·
                    rfl

theorem cell20_9450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_9450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9450 prefixEnd_9450 := by exact prefixLift 9450
  have htrace : WordTrace (prefixWord ++ tailWord_9450) baseStart_9450 baseEnd_9450 := by
    simpa [prefixWord, tailWord_9450, baseEnd_9450] using wordTrace_append hprefix tailTrace_9450
  have hstable : (prefixWord ++ tailWord_9450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9450).length < 2 ^ (prefixWord ++ tailWord_9450).sum := by decide
  have hdescent : baseEnd_9450 < baseStart_9450 := by decide
  rcases family_descends (prefixWord ++ tailWord_9450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9501 : List Nat := [1, 4, 2, 3, 1, 3, 2, 2, 2]
def baseStart_9501 : Nat := 118140960795 + 9501 * 2 ^ 59
def prefixEnd_9501 : Nat := 4983230072969 + 3 ^ 40 * 9501 * 2
def baseEnd_9501 : Nat := 4336515287531165327833

theorem tailTrace_9501 : CollatzResearch.WordTrace tailWord_9501 prefixEnd_9501 4336515287531165327833 := by
  unfold tailWord_9501
  simp only [CollatzResearch.WordTrace]
  refine ⟨346529938586974486724357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 231019959057982991149571 346529938586974486724357)
  ·
    refine ⟨64974363485057716260817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 346529938586974486724357 64974363485057716260817)
    ·
      refine ⟨48730772613793287195613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64974363485057716260817 48730772613793287195613)
      ·
        refine ⟨18274039730172482698355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48730772613793287195613 18274039730172482698355)
        ·
          refine ⟨27411059595258724047533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18274039730172482698355 27411059595258724047533)
          ·
            refine ⟨10279147348222021517825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27411059595258724047533 10279147348222021517825)
            ·
              refine ⟨7709360511166516138369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10279147348222021517825 7709360511166516138369)
              ·
                refine ⟨5782020383374887103777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7709360511166516138369 5782020383374887103777)
                ·
                  refine ⟨4336515287531165327833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5782020383374887103777 4336515287531165327833)
                  ·
                    rfl

theorem cell20_9501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_9501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9501 prefixEnd_9501 := by exact prefixLift 9501
  have htrace : WordTrace (prefixWord ++ tailWord_9501) baseStart_9501 baseEnd_9501 := by
    simpa [prefixWord, tailWord_9501, baseEnd_9501] using wordTrace_append hprefix tailTrace_9501
  have hstable : (prefixWord ++ tailWord_9501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9501).length < 2 ^ (prefixWord ++ tailWord_9501).sum := by decide
  have hdescent : baseEnd_9501 < baseStart_9501 := by decide
  rcases family_descends (prefixWord ++ tailWord_9501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9512 : List Nat := [2, 1, 5, 1, 2, 3, 1, 5]
def baseStart_9512 : Nat := 118140960795 + 9512 * 2 ^ 59
def prefixEnd_9512 : Nat := 4983230072969 + 3 ^ 40 * 9512 * 2
def baseEnd_9512 : Nat := 1447178662421338653707

theorem tailTrace_9512 : CollatzResearch.WordTrace tailWord_9512 prefixEnd_9512 1447178662421338653707 := by
  unfold tailWord_9512
  simp only [CollatzResearch.WordTrace]
  refine ⟨173465570773561682687395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 231287427698082243583193 173465570773561682687395)
  ·
    refine ⟨260198356160342524031093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173465570773561682687395 260198356160342524031093)
    ·
      refine ⟨24393595890032111627915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 260198356160342524031093 24393595890032111627915)
      ·
        refine ⟨36590393835048167441873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24393595890032111627915 36590393835048167441873)
        ·
          refine ⟨27442795376286125581405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36590393835048167441873 27442795376286125581405)
          ·
            refine ⟨10291048266107297093027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27442795376286125581405 10291048266107297093027)
            ·
              refine ⟨15436572399160945639541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10291048266107297093027 15436572399160945639541)
              ·
                refine ⟨1447178662421338653707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15436572399160945639541 1447178662421338653707)
                ·
                  rfl

theorem cell20_9512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_9512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9512 prefixEnd_9512 := by exact prefixLift 9512
  have htrace : WordTrace (prefixWord ++ tailWord_9512) baseStart_9512 baseEnd_9512 := by
    simpa [prefixWord, tailWord_9512, baseEnd_9512] using wordTrace_append hprefix tailTrace_9512
  have hstable : (prefixWord ++ tailWord_9512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9512).length < 2 ^ (prefixWord ++ tailWord_9512).sum := by decide
  have hdescent : baseEnd_9512 < baseStart_9512 := by decide
  rcases family_descends (prefixWord ++ tailWord_9512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9543 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 2]
def baseStart_9543 : Nat := 118140960795 + 9543 * 2 ^ 59
def prefixEnd_9543 : Nat := 4983230072969 + 3 ^ 40 * 9543 * 2
def baseEnd_9543 : Nat := 4355685231965685927661

theorem tailTrace_9543 : CollatzResearch.WordTrace tailWord_9543 prefixEnd_9543 4355685231965685927661 := by
  unfold tailWord_9543
  simp only [CollatzResearch.WordTrace]
  refine ⟨348061804434815659753283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 232041202956543773168855 348061804434815659753283)
  ·
    refine ⟨522092706652223489629925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 348061804434815659753283 522092706652223489629925)
    ·
      refine ⟨97892382497291904305611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 522092706652223489629925 97892382497291904305611)
      ·
        refine ⟨146838573745937856458417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97892382497291904305611 146838573745937856458417)
        ·
          refine ⟨110128930309453392343813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146838573745937856458417 110128930309453392343813)
          ·
            refine ⟨20649174433022511064465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110128930309453392343813 20649174433022511064465)
            ·
              refine ⟨15486880824766883298349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20649174433022511064465 15486880824766883298349)
              ·
                refine ⟨5807580309287581236881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15486880824766883298349 5807580309287581236881)
                ·
                  refine ⟨4355685231965685927661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5807580309287581236881 4355685231965685927661)
                  ·
                    rfl

theorem cell20_9543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 2].length) (baseStart_9543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9543 prefixEnd_9543 := by exact prefixLift 9543
  have htrace : WordTrace (prefixWord ++ tailWord_9543) baseStart_9543 baseEnd_9543 := by
    simpa [prefixWord, tailWord_9543, baseEnd_9543] using wordTrace_append hprefix tailTrace_9543
  have hstable : (prefixWord ++ tailWord_9543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9543).length < 2 ^ (prefixWord ++ tailWord_9543).sum := by decide
  have hdescent : baseEnd_9543 < baseStart_9543 := by decide
  rcases family_descends (prefixWord ++ tailWord_9543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9557 : List Nat := [1, 3, 2, 2, 3, 1, 3, 2, 3]
def baseStart_9557 : Nat := 118140960795 + 9557 * 2 ^ 59
def prefixEnd_9557 : Nat := 4983230072969 + 3 ^ 40 * 9557 * 2
def baseEnd_9557 : Nat := 4362075213443859460937

theorem tailTrace_9557 : CollatzResearch.WordTrace tailWord_9557 prefixEnd_9557 4362075213443859460937 := by
  unfold tailWord_9557
  simp only [CollatzResearch.WordTrace]
  refine ⟨348572426384096050762925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 232381617589397367175283 348572426384096050762925)
  ·
    refine ⟨130714659894036019036097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 348572426384096050762925 130714659894036019036097)
    ·
      refine ⟨98035994920527014277073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130714659894036019036097 98035994920527014277073)
      ·
        refine ⟨73526996190395260707805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98035994920527014277073 73526996190395260707805)
        ·
          refine ⟨27572623571398222765427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73526996190395260707805 27572623571398222765427)
          ·
            refine ⟨41358935357097334148141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572623571398222765427 41358935357097334148141)
            ·
              refine ⟨15509600758911500305553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41358935357097334148141 15509600758911500305553)
              ·
                refine ⟨11632200569183625229165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15509600758911500305553 11632200569183625229165)
                ·
                  refine ⟨4362075213443859460937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11632200569183625229165 4362075213443859460937)
                  ·
                    rfl

theorem cell20_9557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_9557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9557 prefixEnd_9557 := by exact prefixLift 9557
  have htrace : WordTrace (prefixWord ++ tailWord_9557) baseStart_9557 baseEnd_9557 := by
    simpa [prefixWord, tailWord_9557, baseEnd_9557] using wordTrace_append hprefix tailTrace_9557
  have hstable : (prefixWord ++ tailWord_9557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9557).length < 2 ^ (prefixWord ++ tailWord_9557).sum := by decide
  have hdescent : baseEnd_9557 < baseStart_9557 := by decide
  rcases family_descends (prefixWord ++ tailWord_9557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9585 : List Nat := [1, 2, 2, 2, 1, 2, 4, 2, 4]
def baseStart_9585 : Nat := 118140960795 + 9585 * 2 ^ 59
def prefixEnd_9585 : Nat := 4983230072969 + 3 ^ 40 * 9585 * 2
def baseEnd_9585 : Nat := 4374855176400206527489

theorem tailTrace_9585 : CollatzResearch.WordTrace tailWord_9585 prefixEnd_9585 4374855176400206527489 := by
  unfold tailWord_9585
  simp only [CollatzResearch.WordTrace]
  refine ⟨349593670282656832782209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 233062446855104555188139 349593670282656832782209)
  ·
    refine ⟨262195252711992624586657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 349593670282656832782209 262195252711992624586657)
    ·
      refine ⟨196646439533994468439993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262195252711992624586657 196646439533994468439993)
      ·
        refine ⟨147484829650495851329995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196646439533994468439993 147484829650495851329995)
        ·
          refine ⟨221227244475743776994993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147484829650495851329995 221227244475743776994993)
          ·
            refine ⟨165920433356807832746245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221227244475743776994993 165920433356807832746245)
            ·
              refine ⟨31110081254401468639921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 165920433356807832746245 31110081254401468639921)
              ·
                refine ⟨23332560940801101479941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31110081254401468639921 23332560940801101479941)
                ·
                  refine ⟨4374855176400206527489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23332560940801101479941 4374855176400206527489)
                  ·
                    rfl

theorem cell20_9585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_9585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9585 prefixEnd_9585 := by exact prefixLift 9585
  have htrace : WordTrace (prefixWord ++ tailWord_9585) baseStart_9585 baseEnd_9585 := by
    simpa [prefixWord, tailWord_9585, baseEnd_9585] using wordTrace_append hprefix tailTrace_9585
  have hstable : (prefixWord ++ tailWord_9585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9585).length < 2 ^ (prefixWord ++ tailWord_9585).sum := by decide
  have hdescent : baseEnd_9585 < baseStart_9585 := by decide
  rcases family_descends (prefixWord ++ tailWord_9585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9609 : List Nat := [1, 2, 1, 1, 7, 2, 6]
def baseStart_9609 : Nat := 118140960795 + 9609 * 2 ^ 59
def prefixEnd_9609 : Nat := 4983230072969 + 3 ^ 40 * 9609 * 2
def baseEnd_9609 : Nat := 487312158929198858599

theorem tailTrace_9609 : CollatzResearch.WordTrace tailWord_9609 prefixEnd_9609 487312158929198858599 := by
  unfold tailWord_9609
  simp only [CollatzResearch.WordTrace]
  refine ⟨350469022195708931655881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 233646014797139287770587 350469022195708931655881)
  ·
    refine ⟨262851766646781698741911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 350469022195708931655881 262851766646781698741911)
    ·
      refine ⟨394277649970172548112867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262851766646781698741911 394277649970172548112867)
      ·
        refine ⟨591416474955258822169301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394277649970172548112867 591416474955258822169301)
        ·
          refine ⟨13861323631763878644593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 591416474955258822169301 13861323631763878644593)
          ·
            refine ⟨10395992723822908983445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13861323631763878644593 10395992723822908983445)
            ·
              refine ⟨487312158929198858599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10395992723822908983445 487312158929198858599)
              ·
                rfl

theorem cell20_9609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 6].length) (baseStart_9609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9609 prefixEnd_9609 := by exact prefixLift 9609
  have htrace : WordTrace (prefixWord ++ tailWord_9609) baseStart_9609 baseEnd_9609 := by
    simpa [prefixWord, tailWord_9609, baseEnd_9609] using wordTrace_append hprefix tailTrace_9609
  have hstable : (prefixWord ++ tailWord_9609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9609).length < 2 ^ (prefixWord ++ tailWord_9609).sum := by decide
  have hdescent : baseEnd_9609 < baseStart_9609 := by decide
  rcases family_descends (prefixWord ++ tailWord_9609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9637 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 7]
def baseStart_9637 : Nat := 118140960795 + 9637 * 2 ^ 59
def prefixEnd_9637 : Nat := 4983230072969 + 3 ^ 40 * 9637 * 2
def baseEnd_9637 : Nat := 4398589393319136793943

theorem tailTrace_9637 : CollatzResearch.WordTrace tailWord_9637 prefixEnd_9637 4398589393319136793943 := by
  unfold tailWord_9637
  simp only [CollatzResearch.WordTrace]
  refine ⟨351490266094269713675165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 234326844062846475783443 351490266094269713675165)
  ·
    refine ⟨131808849785351142628187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 351490266094269713675165 131808849785351142628187)
    ·
      refine ⟨197713274678026713942281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131808849785351142628187 197713274678026713942281)
      ·
        refine ⟨148284956008520035456711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197713274678026713942281 148284956008520035456711)
        ·
          refine ⟨222427434012780053185067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148284956008520035456711 222427434012780053185067)
          ·
            refine ⟨333641151019170079777601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222427434012780053185067 333641151019170079777601)
            ·
              refine ⟨250230863264377559833201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333641151019170079777601 250230863264377559833201)
              ·
                refine ⟨187673147448283169874901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250230863264377559833201 187673147448283169874901)
                ·
                  refine ⟨4398589393319136793943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 187673147448283169874901 4398589393319136793943)
                  ·
                    rfl

theorem cell20_9637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_9637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9637 prefixEnd_9637 := by exact prefixLift 9637
  have htrace : WordTrace (prefixWord ++ tailWord_9637) baseStart_9637 baseEnd_9637 := by
    simpa [prefixWord, tailWord_9637, baseEnd_9637] using wordTrace_append hprefix tailTrace_9637
  have hstable : (prefixWord ++ tailWord_9637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9637).length < 2 ^ (prefixWord ++ tailWord_9637).sum := by decide
  have hdescent : baseEnd_9637 < baseStart_9637 := by decide
  rcases family_descends (prefixWord ++ tailWord_9637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9666 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_9666 : Nat := 118140960795 + 9666 * 2 ^ 59
def prefixEnd_9666 : Nat := 4983230072969 + 3 ^ 40 * 9666 * 2
def baseEnd_9666 : Nat := 4411825783523924827159

theorem tailTrace_9666 : CollatzResearch.WordTrace tailWord_9666 prefixEnd_9666 4411825783523924827159 := by
  unfold tailWord_9666
  simp only [CollatzResearch.WordTrace]
  refine ⟨88136995747301916620213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 235031988659471777653901 88136995747301916620213)
  ·
    refine ⟨8262843351309554683145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88136995747301916620213 8262843351309554683145)
    ·
      refine ⟨6197132513482166012359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8262843351309554683145 6197132513482166012359)
      ·
        refine ⟨9295698770223249018539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6197132513482166012359 9295698770223249018539)
        ·
          refine ⟨13943548155334873527809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9295698770223249018539 13943548155334873527809)
          ·
            refine ⟨10457661116501155145857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13943548155334873527809 10457661116501155145857)
            ·
              refine ⟨7843245837375866359393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10457661116501155145857 7843245837375866359393)
              ·
                refine ⟨5882434378031899769545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7843245837375866359393 5882434378031899769545)
                ·
                  refine ⟨4411825783523924827159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5882434378031899769545 4411825783523924827159)
                  ·
                    rfl

theorem cell20_9666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_9666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9666 prefixEnd_9666 := by exact prefixLift 9666
  have htrace : WordTrace (prefixWord ++ tailWord_9666) baseStart_9666 baseEnd_9666 := by
    simpa [prefixWord, tailWord_9666, baseEnd_9666] using wordTrace_append hprefix tailTrace_9666
  have hstable : (prefixWord ++ tailWord_9666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9666).length < 2 ^ (prefixWord ++ tailWord_9666).sum := by decide
  have hdescent : baseEnd_9666 < baseStart_9666 := by decide
  rcases family_descends (prefixWord ++ tailWord_9666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9674 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_9674 : Nat := 118140960795 + 9674 * 2 ^ 59
def prefixEnd_9674 : Nat := 4983230072969 + 3 ^ 40 * 9674 * 2
def baseEnd_9674 : Nat := 4415477201511452560459

theorem tailTrace_9674 : CollatzResearch.WordTrace tailWord_9674 prefixEnd_9674 4415477201511452560459 := by
  unfold tailWord_9674
  simp only [CollatzResearch.WordTrace]
  refine ⟨88209941740056258193019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 235226511306816688514717 88209941740056258193019)
  ·
    refine ⟨132314912610084387289529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88209941740056258193019 132314912610084387289529)
    ·
      refine ⟨99236184457563290467147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132314912610084387289529 99236184457563290467147)
      ·
        refine ⟨148854276686344935700721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99236184457563290467147 148854276686344935700721)
        ·
          refine ⟨111640707514758701775541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148854276686344935700721 111640707514758701775541)
          ·
            refine ⟨10466316329508628291457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111640707514758701775541 10466316329508628291457)
            ·
              refine ⟨7849737247131471218593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10466316329508628291457 7849737247131471218593)
              ·
                refine ⟨5887302935348603413945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7849737247131471218593 5887302935348603413945)
                ·
                  refine ⟨4415477201511452560459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887302935348603413945 4415477201511452560459)
                  ·
                    rfl

theorem cell20_9674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_9674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9674 prefixEnd_9674 := by exact prefixLift 9674
  have htrace : WordTrace (prefixWord ++ tailWord_9674) baseStart_9674 baseEnd_9674 := by
    simpa [prefixWord, tailWord_9674, baseEnd_9674] using wordTrace_append hprefix tailTrace_9674
  have hstable : (prefixWord ++ tailWord_9674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9674).length < 2 ^ (prefixWord ++ tailWord_9674).sum := by decide
  have hdescent : baseEnd_9674 < baseStart_9674 := by decide
  rcases family_descends (prefixWord ++ tailWord_9674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9675 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 5]
def baseStart_9675 : Nat := 118140960795 + 9675 * 2 ^ 59
def prefixEnd_9675 : Nat := 4983230072969 + 3 ^ 40 * 9675 * 2
def baseEnd_9675 : Nat := 4415933628759893527121

theorem tailTrace_9675 : CollatzResearch.WordTrace tailWord_9675 prefixEnd_9675 4415933628759893527121 := by
  unfold tailWord_9675
  simp only [CollatzResearch.WordTrace]
  refine ⟨352876239956602203558479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 235250826637734802372319 352876239956602203558479)
  ·
    refine ⟨529314359934903305337719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 352876239956602203558479 529314359934903305337719)
    ·
      refine ⟨793971539902354958006579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529314359934903305337719 793971539902354958006579)
      ·
        refine ⟨1190957309853532437009869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793971539902354958006579 1190957309853532437009869)
        ·
          refine ⟨446608991195074663878701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1190957309853532437009869 446608991195074663878701)
          ·
            refine ⟨167478371698152998954513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446608991195074663878701 167478371698152998954513)
            ·
              refine ⟨125608778773614749215885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167478371698152998954513 125608778773614749215885)
              ·
                refine ⟨47103292040105530955957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125608778773614749215885 47103292040105530955957)
                ·
                  refine ⟨4415933628759893527121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47103292040105530955957 4415933628759893527121)
                  ·
                    rfl

theorem cell20_9675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_9675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9675 prefixEnd_9675 := by exact prefixLift 9675
  have htrace : WordTrace (prefixWord ++ tailWord_9675) baseStart_9675 baseEnd_9675 := by
    simpa [prefixWord, tailWord_9675, baseEnd_9675] using wordTrace_append hprefix tailTrace_9675
  have hstable : (prefixWord ++ tailWord_9675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9675).length < 2 ^ (prefixWord ++ tailWord_9675).sum := by decide
  have hdescent : baseEnd_9675 < baseStart_9675 := by decide
  rcases family_descends (prefixWord ++ tailWord_9675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9699 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 6]
def baseStart_9699 : Nat := 118140960795 + 9699 * 2 ^ 59
def prefixEnd_9699 : Nat := 4983230072969 + 3 ^ 40 * 9699 * 2
def baseEnd_9699 : Nat := 4426887882722476727023

theorem tailTrace_9699 : CollatzResearch.WordTrace tailWord_9699 prefixEnd_9699 4426887882722476727023 := by
  unfold tailWord_9699
  simp only [CollatzResearch.WordTrace]
  refine ⟨353751591869654302432151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 235834394579769534954767 353751591869654302432151)
  ·
    refine ⟨530627387804481453648227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353751591869654302432151 530627387804481453648227)
    ·
      refine ⟨795941081706722180472341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530627387804481453648227 795941081706722180472341)
      ·
        refine ⟨37309738205002602209641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 795941081706722180472341 37309738205002602209641)
        ·
          refine ⟨27982303653751951657231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37309738205002602209641 27982303653751951657231)
          ·
            refine ⟨41973455480627927485847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27982303653751951657231 41973455480627927485847)
            ·
              refine ⟨62960183220941891228771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41973455480627927485847 62960183220941891228771)
              ·
                refine ⟨94440274831412836843157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62960183220941891228771 94440274831412836843157)
                ·
                  refine ⟨4426887882722476727023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94440274831412836843157 4426887882722476727023)
                  ·
                    rfl

theorem cell20_9699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_9699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9699 prefixEnd_9699 := by exact prefixLift 9699
  have htrace : WordTrace (prefixWord ++ tailWord_9699) baseStart_9699 baseEnd_9699 := by
    simpa [prefixWord, tailWord_9699, baseEnd_9699] using wordTrace_append hprefix tailTrace_9699
  have hstable : (prefixWord ++ tailWord_9699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9699).length < 2 ^ (prefixWord ++ tailWord_9699).sum := by decide
  have hdescent : baseEnd_9699 < baseStart_9699 := by decide
  rcases family_descends (prefixWord ++ tailWord_9699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9726 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_9726 : Nat := 118140960795 + 9726 * 2 ^ 59
def prefixEnd_9726 : Nat := 4983230072969 + 3 ^ 40 * 9726 * 2
def baseEnd_9726 : Nat := 4439211418430382826913

theorem tailTrace_9726 : CollatzResearch.WordTrace tailWord_9726 prefixEnd_9726 4439211418430382826913 := by
  unfold tailWord_9726
  simp only [CollatzResearch.WordTrace]
  refine ⟨44342045346479739208129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 236490908514558609110021 44342045346479739208129)
  ·
    refine ⟨33256534009859804406097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44342045346479739208129 33256534009859804406097)
    ·
      refine ⟨24942400507394853304573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33256534009859804406097 24942400507394853304573)
      ·
        refine ⟨9353400190273069989215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24942400507394853304573 9353400190273069989215)
        ·
          refine ⟨14030100285409604983823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353400190273069989215 14030100285409604983823)
          ·
            refine ⟨21045150428114407475735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030100285409604983823 21045150428114407475735)
            ·
              refine ⟨31567725642171611213603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21045150428114407475735 31567725642171611213603)
              ·
                refine ⟨47351588463257416820405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31567725642171611213603 47351588463257416820405)
                ·
                  refine ⟨4439211418430382826913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47351588463257416820405 4439211418430382826913)
                  ·
                    rfl

theorem cell20_9726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_9726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9726 prefixEnd_9726 := by exact prefixLift 9726
  have htrace : WordTrace (prefixWord ++ tailWord_9726) baseStart_9726 baseEnd_9726 := by
    simpa [prefixWord, tailWord_9726, baseEnd_9726] using wordTrace_append hprefix tailTrace_9726
  have hstable : (prefixWord ++ tailWord_9726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9726).length < 2 ^ (prefixWord ++ tailWord_9726).sum := by decide
  have hdescent : baseEnd_9726 < baseStart_9726 := by decide
  rcases family_descends (prefixWord ++ tailWord_9726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9737 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 4]
def baseStart_9737 : Nat := 118140960795 + 9737 * 2 ^ 59
def prefixEnd_9737 : Nat := 4983230072969 + 3 ^ 40 * 9737 * 2
def baseEnd_9737 : Nat := 4444232118163233460201

theorem tailTrace_9737 : CollatzResearch.WordTrace tailWord_9737 prefixEnd_9737 4444232118163233460201 := by
  unfold tailWord_9737
  simp only [CollatzResearch.WordTrace]
  refine ⟨355137565731986792315465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 236758377154657861543643 355137565731986792315465)
  ·
    refine ⟨266353174298990094236599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 355137565731986792315465 266353174298990094236599)
    ·
      refine ⟨399529761448485141354899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266353174298990094236599 399529761448485141354899)
      ·
        refine ⟨599294642172727712032349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399529761448485141354899 599294642172727712032349)
        ·
          refine ⟨224735490814772892012131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 599294642172727712032349 224735490814772892012131)
          ·
            refine ⟨337103236222159338018197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224735490814772892012131 337103236222159338018197)
            ·
              refine ⟨15801714197913718969603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 337103236222159338018197 15801714197913718969603)
              ·
                refine ⟨23702571296870578454405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15801714197913718969603 23702571296870578454405)
                ·
                  refine ⟨4444232118163233460201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23702571296870578454405 4444232118163233460201)
                  ·
                    rfl

theorem cell20_9737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_9737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9737 prefixEnd_9737 := by exact prefixLift 9737
  have htrace : WordTrace (prefixWord ++ tailWord_9737) baseStart_9737 baseEnd_9737 := by
    simpa [prefixWord, tailWord_9737, baseEnd_9737] using wordTrace_append hprefix tailTrace_9737
  have hstable : (prefixWord ++ tailWord_9737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9737).length < 2 ^ (prefixWord ++ tailWord_9737).sum := by decide
  have hdescent : baseEnd_9737 < baseStart_9737 := by decide
  rcases family_descends (prefixWord ++ tailWord_9737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9747 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 3]
def baseStart_9747 : Nat := 118140960795 + 9747 * 2 ^ 59
def prefixEnd_9747 : Nat := 4983230072969 + 3 ^ 40 * 9747 * 2
def baseEnd_9747 : Nat := 4448796390647643126827

theorem tailTrace_9747 : CollatzResearch.WordTrace tailWord_9747 prefixEnd_9747 4448796390647643126827 := by
  unfold tailWord_9747
  simp only [CollatzResearch.WordTrace]
  refine ⟨355502295695758500179495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 237001530463839000119663 355502295695758500179495)
  ·
    refine ⟨533253443543637750269243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 355502295695758500179495 533253443543637750269243)
    ·
      refine ⟨799880165315456625403865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533253443543637750269243 799880165315456625403865)
      ·
        refine ⟨599910123986592469052899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 799880165315456625403865 599910123986592469052899)
        ·
          refine ⟨899865185979888703579349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599910123986592469052899 899865185979888703579349)
          ·
            refine ⟨21090590296403641490141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 899865185979888703579349 21090590296403641490141)
            ·
              refine ⟨7908971361151365558803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21090590296403641490141 7908971361151365558803)
              ·
                refine ⟨11863457041727048338205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7908971361151365558803 11863457041727048338205)
                ·
                  refine ⟨4448796390647643126827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11863457041727048338205 4448796390647643126827)
                  ·
                    rfl

theorem cell20_9747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 3].length) (baseStart_9747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9747 prefixEnd_9747 := by exact prefixLift 9747
  have htrace : WordTrace (prefixWord ++ tailWord_9747) baseStart_9747 baseEnd_9747 := by
    simpa [prefixWord, tailWord_9747, baseEnd_9747] using wordTrace_append hprefix tailTrace_9747
  have hstable : (prefixWord ++ tailWord_9747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9747).length < 2 ^ (prefixWord ++ tailWord_9747).sum := by decide
  have hdescent : baseEnd_9747 < baseStart_9747 := by decide
  rcases family_descends (prefixWord ++ tailWord_9747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9761 : List Nat := [1, 2, 3, 2, 2, 2, 4, 4]
def baseStart_9761 : Nat := 118140960795 + 9761 * 2 ^ 59
def prefixEnd_9761 : Nat := 4983230072969 + 3 ^ 40 * 9761 * 2
def baseEnd_9761 : Nat := 1485062124041938886701

theorem tailTrace_9761 : CollatzResearch.WordTrace tailWord_9761 prefixEnd_9761 1485062124041938886701 := by
  unfold tailWord_9761
  simp only [CollatzResearch.WordTrace]
  refine ⟨356012917645038891189137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 237341945096692594126091 356012917645038891189137)
  ·
    refine ⟨267009688233779168391853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 356012917645038891189137 267009688233779168391853)
    ·
      refine ⟨100128633087667188146945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267009688233779168391853 100128633087667188146945)
      ·
        refine ⟨75096474815750391110209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100128633087667188146945 75096474815750391110209)
        ·
          refine ⟨56322356111812793332657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75096474815750391110209 56322356111812793332657)
          ·
            refine ⟨42241767083859594999493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56322356111812793332657 42241767083859594999493)
            ·
              refine ⟨7920331328223674062405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42241767083859594999493 7920331328223674062405)
              ·
                refine ⟨1485062124041938886701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7920331328223674062405 1485062124041938886701)
                ·
                  rfl

theorem cell20_9761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_9761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9761 prefixEnd_9761 := by exact prefixLift 9761
  have htrace : WordTrace (prefixWord ++ tailWord_9761) baseStart_9761 baseEnd_9761 := by
    simpa [prefixWord, tailWord_9761, baseEnd_9761] using wordTrace_append hprefix tailTrace_9761
  have hstable : (prefixWord ++ tailWord_9761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9761).length < 2 ^ (prefixWord ++ tailWord_9761).sum := by decide
  have hdescent : baseEnd_9761 < baseStart_9761 := by decide
  rcases family_descends (prefixWord ++ tailWord_9761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9788 : List Nat := [2, 2, 2, 2, 4, 1, 3, 2, 2]
def baseStart_9788 : Nat := 118140960795 + 9788 * 2 ^ 59
def prefixEnd_9788 : Nat := 4983230072969 + 3 ^ 40 * 9788 * 2
def baseEnd_9788 : Nat := 4467509907833722759993

theorem tailTrace_9788 : CollatzResearch.WordTrace tailWord_9788 prefixEnd_9788 4467509907833722759993 := by
  unfold tailWord_9788
  simp only [CollatzResearch.WordTrace]
  refine ⟨178498844273611251211009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 237998459031481668281345 178498844273611251211009)
  ·
    refine ⟨133874133205208438408257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178498844273611251211009 133874133205208438408257)
    ·
      refine ⟨100405599903906328806193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133874133205208438408257 100405599903906328806193)
      ·
        refine ⟨75304199927929746604645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100405599903906328806193 75304199927929746604645)
        ·
          refine ⟨14119537486486827488371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75304199927929746604645 14119537486486827488371)
          ·
            refine ⟨21179306229730241232557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14119537486486827488371 21179306229730241232557)
            ·
              refine ⟨7942239836148840462209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21179306229730241232557 7942239836148840462209)
              ·
                refine ⟨5956679877111630346657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7942239836148840462209 5956679877111630346657)
                ·
                  refine ⟨4467509907833722759993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5956679877111630346657 4467509907833722759993)
                  ·
                    rfl

theorem cell20_9788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_9788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9788 prefixEnd_9788 := by exact prefixLift 9788
  have htrace : WordTrace (prefixWord ++ tailWord_9788) baseStart_9788 baseEnd_9788 := by
    simpa [prefixWord, tailWord_9788, baseEnd_9788] using wordTrace_append hprefix tailTrace_9788
  have hstable : (prefixWord ++ tailWord_9788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9788).length < 2 ^ (prefixWord ++ tailWord_9788).sum := by decide
  have hdescent : baseEnd_9788 < baseStart_9788 := by decide
  rcases family_descends (prefixWord ++ tailWord_9788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9798 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_9798 : Nat := 118140960795 + 9798 * 2 ^ 59
def prefixEnd_9798 : Nat := 4983230072969 + 3 ^ 40 * 9798 * 2
def baseEnd_9798 : Nat := 4472074180318132426619

theorem tailTrace_9798 : CollatzResearch.WordTrace tailWord_9798 prefixEnd_9798 4472074180318132426619 := by
  unfold tailWord_9798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167575578468569071439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 238241612340662806857365 11167575578468569071439)
  ·
    refine ⟨16751363367702853607159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11167575578468569071439 16751363367702853607159)
    ·
      refine ⟨25127045051554280410739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16751363367702853607159 25127045051554280410739)
      ·
        refine ⟨37690567577331420616109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25127045051554280410739 37690567577331420616109)
        ·
          refine ⟨14133962841499282731041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37690567577331420616109 14133962841499282731041)
          ·
            refine ⟨10600472131124462048281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14133962841499282731041 10600472131124462048281)
            ·
              refine ⟨7950354098343346536211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10600472131124462048281 7950354098343346536211)
              ·
                refine ⟨11925531147515019804317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950354098343346536211 11925531147515019804317)
                ·
                  refine ⟨4472074180318132426619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11925531147515019804317 4472074180318132426619)
                  ·
                    rfl

theorem cell20_9798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_9798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9798 prefixEnd_9798 := by exact prefixLift 9798
  have htrace : WordTrace (prefixWord ++ tailWord_9798) baseStart_9798 baseEnd_9798 := by
    simpa [prefixWord, tailWord_9798, baseEnd_9798] using wordTrace_append hprefix tailTrace_9798
  have hstable : (prefixWord ++ tailWord_9798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9798).length < 2 ^ (prefixWord ++ tailWord_9798).sum := by decide
  have hdescent : baseEnd_9798 < baseStart_9798 := by decide
  rcases family_descends (prefixWord ++ tailWord_9798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9799 : List Nat := [1, 1, 4, 1, 5, 1, 2, 5]
def baseStart_9799 : Nat := 118140960795 + 9799 * 2 ^ 59
def prefixEnd_9799 : Nat := 4983230072969 + 3 ^ 40 * 9799 * 2
def baseEnd_9799 : Nat := 1490843535855524464427

theorem tailTrace_9799 : CollatzResearch.WordTrace tailWord_9799 prefixEnd_9799 1490843535855524464427 := by
  unfold tailWord_9799
  simp only [CollatzResearch.WordTrace]
  refine ⟨357398891507371381072451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 238265927671580920714967 357398891507371381072451)
  ·
    refine ⟨536098337261057071608677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 357398891507371381072451 536098337261057071608677)
    ·
      refine ⟨100518438236448200926627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 536098337261057071608677 100518438236448200926627)
      ·
        refine ⟨150777657354672301389941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100518438236448200926627 150777657354672301389941)
        ·
          refine ⟨14135405377000528255307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150777657354672301389941 14135405377000528255307)
          ·
            refine ⟨21203108065500792382961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14135405377000528255307 21203108065500792382961)
            ·
              refine ⟨15902331049125594287221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21203108065500792382961 15902331049125594287221)
              ·
                refine ⟨1490843535855524464427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15902331049125594287221 1490843535855524464427)
                ·
                  rfl

theorem cell20_9799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 5].length) (baseStart_9799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9799 prefixEnd_9799 := by exact prefixLift 9799
  have htrace : WordTrace (prefixWord ++ tailWord_9799) baseStart_9799 baseEnd_9799 := by
    simpa [prefixWord, tailWord_9799, baseEnd_9799] using wordTrace_append hprefix tailTrace_9799
  have hstable : (prefixWord ++ tailWord_9799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9799).length < 2 ^ (prefixWord ++ tailWord_9799).sum := by decide
  have hdescent : baseEnd_9799 < baseStart_9799 := by decide
  rcases family_descends (prefixWord ++ tailWord_9799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9837 : List Nat := [1, 5, 1, 1, 5, 7]
def baseStart_9837 : Nat := 118140960795 + 9837 * 2 ^ 59
def prefixEnd_9837 : Nat := 4983230072969 + 3 ^ 40 * 9837 * 2
def baseEnd_9837 : Nat := 166291660852123338017

theorem tailTrace_9837 : CollatzResearch.WordTrace tailWord_9837 prefixEnd_9837 166291660852123338017 := by
  unfold tailWord_9837
  simp only [CollatzResearch.WordTrace]
  refine ⟨358784865369703870955765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 239189910246469247303843 358784865369703870955765)
  ·
    refine ⟨33636081128409737902103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 358784865369703870955765 33636081128409737902103)
    ·
      refine ⟨50454121692614606853155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33636081128409737902103 50454121692614606853155)
      ·
        refine ⟨75681182538921910279733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50454121692614606853155 75681182538921910279733)
        ·
          refine ⟨7095110863023929088725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75681182538921910279733 7095110863023929088725)
          ·
            refine ⟨166291660852123338017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7095110863023929088725 166291660852123338017)
            ·
              rfl

theorem cell20_9837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 7].length) (baseStart_9837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9837 prefixEnd_9837 := by exact prefixLift 9837
  have htrace : WordTrace (prefixWord ++ tailWord_9837) baseStart_9837 baseEnd_9837 := by
    simpa [prefixWord, tailWord_9837, baseEnd_9837] using wordTrace_append hprefix tailTrace_9837
  have hstable : (prefixWord ++ tailWord_9837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9837).length < 2 ^ (prefixWord ++ tailWord_9837).sum := by decide
  have hdescent : baseEnd_9837 < baseStart_9837 := by decide
  rcases family_descends (prefixWord ++ tailWord_9837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9903 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_9903 : Nat := 118140960795 + 9903 * 2 ^ 59
def prefixEnd_9903 : Nat := 4983230072969 + 3 ^ 40 * 9903 * 2
def baseEnd_9903 : Nat := 4519999041404433926189

theorem tailTrace_9903 : CollatzResearch.WordTrace tailWord_9903 prefixEnd_9903 4519999041404433926189 := by
  unfold tailWord_9903
  simp only [CollatzResearch.WordTrace]
  refine ⟨361192083130597142858363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 240794722087064761905575 361192083130597142858363)
  ·
    refine ⟨541788124695895714287545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361192083130597142858363 541788124695895714287545)
    ·
      refine ⟨406341093521921785715659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 541788124695895714287545 406341093521921785715659)
      ·
        refine ⟨609511640282882678573489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406341093521921785715659 609511640282882678573489)
        ·
          refine ⟨457133730212162008930117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609511640282882678573489 457133730212162008930117)
          ·
            refine ⟨85712574414780376674397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 457133730212162008930117 85712574414780376674397)
            ·
              refine ⟨32142215405542641252899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85712574414780376674397 32142215405542641252899)
              ·
                refine ⟨48213323108313961879349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32142215405542641252899 48213323108313961879349)
                ·
                  refine ⟨4519999041404433926189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48213323108313961879349 4519999041404433926189)
                  ·
                    rfl

theorem cell20_9903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_9903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9903 prefixEnd_9903 := by exact prefixLift 9903
  have htrace : WordTrace (prefixWord ++ tailWord_9903) baseStart_9903 baseEnd_9903 := by
    simpa [prefixWord, tailWord_9903, baseEnd_9903] using wordTrace_append hprefix tailTrace_9903
  have hstable : (prefixWord ++ tailWord_9903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9903).length < 2 ^ (prefixWord ++ tailWord_9903).sum := by decide
  have hdescent : baseEnd_9903 < baseStart_9903 := by decide
  rcases family_descends (prefixWord ++ tailWord_9903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9906 : List Nat := [3, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_9906 : Nat := 118140960795 + 9906 * 2 ^ 59
def prefixEnd_9906 : Nat := 4983230072969 + 3 ^ 40 * 9906 * 2
def baseEnd_9906 : Nat := 4521368323149756826177

theorem tailTrace_9906 : CollatzResearch.WordTrace tailWord_9906 prefixEnd_9906 4521368323149756826177 := by
  unfold tailWord_9906
  simp only [CollatzResearch.WordTrace]
  refine ⟨90325375529932163804393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 240867668079819103478381 90325375529932163804393)
  ·
    refine ⟨67744031647449122853295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90325375529932163804393 67744031647449122853295)
    ·
      refine ⟨101616047471173684279943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67744031647449122853295 101616047471173684279943)
      ·
        refine ⟨152424071206760526419915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101616047471173684279943 152424071206760526419915)
        ·
          refine ⟨228636106810140789629873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152424071206760526419915 228636106810140789629873)
          ·
            refine ⟨171477080107605592222405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228636106810140789629873 171477080107605592222405)
            ·
              refine ⟨32151952520176048541701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171477080107605592222405 32151952520176048541701)
              ·
                refine ⟨6028491097533009101569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32151952520176048541701 6028491097533009101569)
                ·
                  refine ⟨4521368323149756826177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6028491097533009101569 4521368323149756826177)
                  ·
                    rfl

theorem cell20_9906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_9906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9906 prefixEnd_9906 := by exact prefixLift 9906
  have htrace : WordTrace (prefixWord ++ tailWord_9906) baseStart_9906 baseEnd_9906 := by
    simpa [prefixWord, tailWord_9906, baseEnd_9906] using wordTrace_append hprefix tailTrace_9906
  have hstable : (prefixWord ++ tailWord_9906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9906).length < 2 ^ (prefixWord ++ tailWord_9906).sum := by decide
  have hdescent : baseEnd_9906 < baseStart_9906 := by decide
  rcases family_descends (prefixWord ++ tailWord_9906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9926 : List Nat := [6, 1, 2, 1, 1, 3, 2, 4]
def baseStart_9926 : Nat := 118140960795 + 9926 * 2 ^ 59
def prefixEnd_9926 : Nat := 4983230072969 + 3 ^ 40 * 9926 * 2
def baseEnd_9926 : Nat := 1510165622706192053143

theorem tailTrace_9926 : CollatzResearch.WordTrace tailWord_9926 prefixEnd_9926 1510165622706192053143 := by
  unfold tailWord_9926
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313467563977252217051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 241353974698181380630421 11313467563977252217051)
  ·
    refine ⟨16970201345965878325577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11313467563977252217051 16970201345965878325577)
    ·
      refine ⟨12727651009474408744183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16970201345965878325577 12727651009474408744183)
      ·
        refine ⟨19091476514211613116275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12727651009474408744183 19091476514211613116275)
        ·
          refine ⟨28637214771317419674413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19091476514211613116275 28637214771317419674413)
          ·
            refine ⟨10738955539244032377905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28637214771317419674413 10738955539244032377905)
            ·
              refine ⟨8054216654433024283429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10738955539244032377905 8054216654433024283429)
              ·
                refine ⟨1510165622706192053143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8054216654433024283429 1510165622706192053143)
                ·
                  rfl

theorem cell20_9926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_9926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9926 prefixEnd_9926 := by exact prefixLift 9926
  have htrace : WordTrace (prefixWord ++ tailWord_9926) baseStart_9926 baseEnd_9926 := by
    simpa [prefixWord, tailWord_9926, baseEnd_9926] using wordTrace_append hprefix tailTrace_9926
  have hstable : (prefixWord ++ tailWord_9926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9926).length < 2 ^ (prefixWord ++ tailWord_9926).sum := by decide
  have hdescent : baseEnd_9926 < baseStart_9926 := by decide
  rcases family_descends (prefixWord ++ tailWord_9926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9930 : List Nat := [3, 1, 2, 1, 5, 2, 2, 4]
def baseStart_9930 : Nat := 118140960795 + 9930 * 2 ^ 59
def prefixEnd_9930 : Nat := 4983230072969 + 3 ^ 40 * 9930 * 2
def baseEnd_9930 : Nat := 1510774192370780008693

theorem tailTrace_9930 : CollatzResearch.WordTrace tailWord_9930 prefixEnd_9930 1510774192370780008693 := by
  unfold tailWord_9930
  simp only [CollatzResearch.WordTrace]
  refine ⟨90544213508195188522811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 241451236021853836060829 90544213508195188522811)
  ·
    refine ⟨135816320262292782784217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90544213508195188522811 135816320262292782784217)
    ·
      refine ⟨101862240196719587088163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135816320262292782784217 101862240196719587088163)
      ·
        refine ⟨152793360295079380632245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101862240196719587088163 152793360295079380632245)
        ·
          refine ⟨14324377527663691934273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152793360295079380632245 14324377527663691934273)
          ·
            refine ⟨10743283145747768950705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14324377527663691934273 10743283145747768950705)
            ·
              refine ⟨8057462359310826713029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10743283145747768950705 8057462359310826713029)
              ·
                refine ⟨1510774192370780008693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8057462359310826713029 1510774192370780008693)
                ·
                  rfl

theorem cell20_9930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_9930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9930 prefixEnd_9930 := by exact prefixLift 9930
  have htrace : WordTrace (prefixWord ++ tailWord_9930) baseStart_9930 baseEnd_9930 := by
    simpa [prefixWord, tailWord_9930, baseEnd_9930] using wordTrace_append hprefix tailTrace_9930
  have hstable : (prefixWord ++ tailWord_9930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9930).length < 2 ^ (prefixWord ++ tailWord_9930).sum := by decide
  have hdescent : baseEnd_9930 < baseStart_9930 := by decide
  rcases family_descends (prefixWord ++ tailWord_9930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9934 : List Nat := [4, 1, 1, 1, 3, 1, 3, 6]
def baseStart_9934 : Nat := 118140960795 + 9934 * 2 ^ 59
def prefixEnd_9934 : Nat := 4983230072969 + 3 ^ 40 * 9934 * 2
def baseEnd_9934 : Nat := 1511382762035367964243

theorem tailTrace_9934 : CollatzResearch.WordTrace tailWord_9934 prefixEnd_9934 1511382762035367964243 := by
  unfold tailWord_9934
  simp only [CollatzResearch.WordTrace]
  refine ⟨45290343252286179654607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 241548497345526291491237 45290343252286179654607)
  ·
    refine ⟨67935514878429269481911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45290343252286179654607 67935514878429269481911)
    ·
      refine ⟨101903272317643904222867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67935514878429269481911 101903272317643904222867)
      ·
        refine ⟨152854908476465856334301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101903272317643904222867 152854908476465856334301)
        ·
          refine ⟨57320590678674696125363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152854908476465856334301 57320590678674696125363)
          ·
            refine ⟨85980886018012044188045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57320590678674696125363 85980886018012044188045)
            ·
              refine ⟨32242832256754516570517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85980886018012044188045 32242832256754516570517)
              ·
                refine ⟨1511382762035367964243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32242832256754516570517 1511382762035367964243)
                ·
                  rfl

theorem cell20_9934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_9934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9934 prefixEnd_9934 := by exact prefixLift 9934
  have htrace : WordTrace (prefixWord ++ tailWord_9934) baseStart_9934 baseEnd_9934 := by
    simpa [prefixWord, tailWord_9934, baseEnd_9934] using wordTrace_append hprefix tailTrace_9934
  have hstable : (prefixWord ++ tailWord_9934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9934).length < 2 ^ (prefixWord ++ tailWord_9934).sum := by decide
  have hdescent : baseEnd_9934 < baseStart_9934 := by decide
  rcases family_descends (prefixWord ++ tailWord_9934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9940 : List Nat := [2, 4, 1, 3, 1, 3, 1, 3, 2]
def baseStart_9940 : Nat := 118140960795 + 9940 * 2 ^ 59
def prefixEnd_9940 : Nat := 4983230072969 + 3 ^ 40 * 9940 * 2
def baseEnd_9940 : Nat := 4536886849596749692705

theorem tailTrace_9940 : CollatzResearch.WordTrace tailWord_9940 prefixEnd_9940 4536886849596749692705 := by
  unfold tailWord_9940
  simp only [CollatzResearch.WordTrace]
  refine ⟨181270791998276230977637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 241694389331034974636849 181270791998276230977637)
  ·
    refine ⟨33988273499676793308307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181270791998276230977637 33988273499676793308307)
    ·
      refine ⟨50982410249515189962461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33988273499676793308307 50982410249515189962461)
      ·
        refine ⟨19118403843568196235923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50982410249515189962461 19118403843568196235923)
        ·
          refine ⟨28677605765352294353885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19118403843568196235923 28677605765352294353885)
          ·
            refine ⟨10754102162007110382707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28677605765352294353885 10754102162007110382707)
            ·
              refine ⟨16131153243010665574061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754102162007110382707 16131153243010665574061)
              ·
                refine ⟨6049182466128999590273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16131153243010665574061 6049182466128999590273)
                ·
                  refine ⟨4536886849596749692705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6049182466128999590273 4536886849596749692705)
                  ·
                    rfl

theorem cell20_9940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_9940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_9940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_9940 prefixEnd_9940 := by exact prefixLift 9940
  have htrace : WordTrace (prefixWord ++ tailWord_9940) baseStart_9940 baseEnd_9940 := by
    simpa [prefixWord, tailWord_9940, baseEnd_9940] using wordTrace_append hprefix tailTrace_9940
  have hstable : (prefixWord ++ tailWord_9940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9940).length < 2 ^ (prefixWord ++ tailWord_9940).sum := by decide
  have hdescent : baseEnd_9940 < baseStart_9940 := by decide
  rcases family_descends (prefixWord ++ tailWord_9940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10034 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_10034 : Nat := 118140960795 + 10034 * 2 ^ 59
def prefixEnd_10034 : Nat := 4983230072969 + 3 ^ 40 * 10034 * 2
def baseEnd_10034 : Nat := 4579791010950200558987

theorem tailTrace_10034 : CollatzResearch.WordTrace tailWord_10034 prefixEnd_10034 4579791010950200558987 := by
  unfold tailWord_10034
  simp only [CollatzResearch.WordTrace]
  refine ⟨91492511414001628969289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 243980030437337677251437 91492511414001628969289)
  ·
    refine ⟨68619383560501221726967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91492511414001628969289 68619383560501221726967)
    ·
      refine ⟨102929075340751832590451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68619383560501221726967 102929075340751832590451)
      ·
        refine ⟨154393613011127748885677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102929075340751832590451 154393613011127748885677)
        ·
          refine ⟨57897604879172905832129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154393613011127748885677 57897604879172905832129)
          ·
            refine ⟨43423203659379679374097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57897604879172905832129 43423203659379679374097)
            ·
              refine ⟨32567402744534759530573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43423203659379679374097 32567402744534759530573)
              ·
                refine ⟨12212776029200534823965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32567402744534759530573 12212776029200534823965)
                ·
                  refine ⟨4579791010950200558987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12212776029200534823965 4579791010950200558987)
                  ·
                    rfl

theorem cell20_10034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_10034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10034 prefixEnd_10034 := by exact prefixLift 10034
  have htrace : WordTrace (prefixWord ++ tailWord_10034) baseStart_10034 baseEnd_10034 := by
    simpa [prefixWord, tailWord_10034, baseEnd_10034] using wordTrace_append hprefix tailTrace_10034
  have hstable : (prefixWord ++ tailWord_10034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10034).length < 2 ^ (prefixWord ++ tailWord_10034).sum := by decide
  have hdescent : baseEnd_10034 < baseStart_10034 := by decide
  rcases family_descends (prefixWord ++ tailWord_10034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10054 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_10054 : Nat := 118140960795 + 10054 * 2 ^ 59
def prefixEnd_10054 : Nat := 4983230072969 + 3 ^ 40 * 10054 * 2
def baseEnd_10054 : Nat := 4588919555919019892239

theorem tailTrace_10054 : CollatzResearch.WordTrace tailWord_10054 prefixEnd_10054 4588919555919019892239 := by
  unfold tailWord_10054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11459359549485935362663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 244466337055699954403477 11459359549485935362663)
  ·
    refine ⟨17189039324228903043995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11459359549485935362663 17189039324228903043995)
    ·
      refine ⟨25783558986343354565993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17189039324228903043995 25783558986343354565993)
      ·
        refine ⟨19337669239757515924495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25783558986343354565993 19337669239757515924495)
        ·
          refine ⟨29006503859636273886743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19337669239757515924495 29006503859636273886743)
          ·
            refine ⟨43509755789454410830115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29006503859636273886743 43509755789454410830115)
            ·
              refine ⟨65264633684181616245173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43509755789454410830115 65264633684181616245173)
              ·
                refine ⟨6118559407892026522985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65264633684181616245173 6118559407892026522985)
                ·
                  refine ⟨4588919555919019892239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6118559407892026522985 4588919555919019892239)
                  ·
                    rfl

theorem cell20_10054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_10054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10054 prefixEnd_10054 := by exact prefixLift 10054
  have htrace : WordTrace (prefixWord ++ tailWord_10054) baseStart_10054 baseEnd_10054 := by
    simpa [prefixWord, tailWord_10054, baseEnd_10054] using wordTrace_append hprefix tailTrace_10054
  have hstable : (prefixWord ++ tailWord_10054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10054).length < 2 ^ (prefixWord ++ tailWord_10054).sum := by decide
  have hdescent : baseEnd_10054 < baseStart_10054 := by decide
  rcases family_descends (prefixWord ++ tailWord_10054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10058 : List Nat := [3, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_10058 : Nat := 118140960795 + 10058 * 2 ^ 59
def prefixEnd_10058 : Nat := 4983230072969 + 3 ^ 40 * 10058 * 2
def baseEnd_10058 : Nat := 4590745264912783758889

theorem tailTrace_10058 : CollatzResearch.WordTrace tailWord_10058 prefixEnd_10058 4590745264912783758889 := by
  unfold tailWord_10058
  simp only [CollatzResearch.WordTrace]
  refine ⟨91711349392264653687707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 244563598379372409833885 91711349392264653687707)
  ·
    refine ⟨137567024088396980531561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91711349392264653687707 137567024088396980531561)
    ·
      refine ⟨103175268066297735398671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137567024088396980531561 103175268066297735398671)
      ·
        refine ⟨154762902099446603098007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103175268066297735398671 154762902099446603098007)
        ·
          refine ⟨232144353149169904647011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154762902099446603098007 232144353149169904647011)
          ·
            refine ⟨348216529723754856970517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232144353149169904647011 348216529723754856970517)
            ·
              refine ⟨16322649830801008920493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 348216529723754856970517 16322649830801008920493)
              ·
                refine ⟨6120993686550378345185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16322649830801008920493 6120993686550378345185)
                ·
                  refine ⟨4590745264912783758889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6120993686550378345185 4590745264912783758889)
                  ·
                    rfl

theorem cell20_10058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_10058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10058 prefixEnd_10058 := by exact prefixLift 10058
  have htrace : WordTrace (prefixWord ++ tailWord_10058) baseStart_10058 baseEnd_10058 := by
    simpa [prefixWord, tailWord_10058, baseEnd_10058] using wordTrace_append hprefix tailTrace_10058
  have hstable : (prefixWord ++ tailWord_10058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10058).length < 2 ^ (prefixWord ++ tailWord_10058).sum := by decide
  have hdescent : baseEnd_10058 < baseStart_10058 := by decide
  rcases family_descends (prefixWord ++ tailWord_10058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10079 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 4]
def baseStart_10079 : Nat := 118140960795 + 10079 * 2 ^ 59
def prefixEnd_10079 : Nat := 4983230072969 + 3 ^ 40 * 10079 * 2
def baseEnd_10079 : Nat := 4600330237130044058803

theorem tailTrace_10079 : CollatzResearch.WordTrace tailWord_10079 prefixEnd_10079 4600330237130044058803 := by
  unfold tailWord_10079
  simp only [CollatzResearch.WordTrace]
  refine ⟨367611330492979201265291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 245074220328652800843527 367611330492979201265291)
  ·
    refine ⟨551416995739468801897937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367611330492979201265291 551416995739468801897937)
    ·
      refine ⟨413562746804601601423453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 551416995739468801897937 413562746804601601423453)
      ·
        refine ⟨155086030051725600533795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 413562746804601601423453 155086030051725600533795)
        ·
          refine ⟨232629045077588400800693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155086030051725600533795 232629045077588400800693)
          ·
            refine ⟨21808972976023912575065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232629045077588400800693 21808972976023912575065)
            ·
              refine ⟨16356729732017934431299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21808972976023912575065 16356729732017934431299)
              ·
                refine ⟨24535094598026901646949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16356729732017934431299 24535094598026901646949)
                ·
                  refine ⟨4600330237130044058803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24535094598026901646949 4600330237130044058803)
                  ·
                    rfl

theorem cell20_10079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 4].length) (baseStart_10079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10079 prefixEnd_10079 := by exact prefixLift 10079
  have htrace : WordTrace (prefixWord ++ tailWord_10079) baseStart_10079 baseEnd_10079 := by
    simpa [prefixWord, tailWord_10079, baseEnd_10079] using wordTrace_append hprefix tailTrace_10079
  have hstable : (prefixWord ++ tailWord_10079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10079).length < 2 ^ (prefixWord ++ tailWord_10079).sum := by decide
  have hdescent : baseEnd_10079 < baseStart_10079 := by decide
  rcases family_descends (prefixWord ++ tailWord_10079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10130 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_10130 : Nat := 118140960795 + 10130 * 2 ^ 59
def prefixEnd_10130 : Nat := 4983230072969 + 3 ^ 40 * 10130 * 2
def baseEnd_10130 : Nat := 4623608026800533358595

theorem tailTrace_10130 : CollatzResearch.WordTrace tailWord_10130 prefixEnd_10130 4623608026800533358595 := by
  unfold tailWord_10130
  simp only [CollatzResearch.WordTrace]
  refine ⟨92367863327053727842961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 246314302205476607581229 92367863327053727842961)
  ·
    refine ⟨69275897495290295882221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92367863327053727842961 69275897495290295882221)
    ·
      refine ⟨25978461560733860955833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69275897495290295882221 25978461560733860955833)
      ·
        refine ⟨19483846170550395716875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25978461560733860955833 19483846170550395716875)
        ·
          refine ⟨29225769255825593575313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19483846170550395716875 29225769255825593575313)
          ·
            refine ⟨21919326941869195181485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29225769255825593575313 21919326941869195181485)
            ·
              refine ⟨8219747603200948193057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21919326941869195181485 8219747603200948193057)
              ·
                refine ⟨6164810702400711144793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8219747603200948193057 6164810702400711144793)
                ·
                  refine ⟨4623608026800533358595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6164810702400711144793 4623608026800533358595)
                  ·
                    rfl

theorem cell20_10130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_10130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10130 prefixEnd_10130 := by exact prefixLift 10130
  have htrace : WordTrace (prefixWord ++ tailWord_10130) baseStart_10130 baseEnd_10130 := by
    simpa [prefixWord, tailWord_10130, baseEnd_10130] using wordTrace_append hprefix tailTrace_10130
  have hstable : (prefixWord ++ tailWord_10130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10130).length < 2 ^ (prefixWord ++ tailWord_10130).sum := by decide
  have hdescent : baseEnd_10130 < baseStart_10130 := by decide
  rcases family_descends (prefixWord ++ tailWord_10130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10148 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_10148 : Nat := 118140960795 + 10148 * 2 ^ 59
def prefixEnd_10148 : Nat := 4983230072969 + 3 ^ 40 * 10148 * 2
def baseEnd_10148 : Nat := 4631823717272470758521

theorem tailTrace_10148 : CollatzResearch.WordTrace tailWord_10148 prefixEnd_10148 4631823717272470758521 := by
  unfold tailWord_10148
  simp only [CollatzResearch.WordTrace]
  refine ⟨185063983621501992763549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 246751978162002657018065 185063983621501992763549)
  ·
    refine ⟨69398993858063247286331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 185063983621501992763549 69398993858063247286331)
    ·
      refine ⟨104098490787094870929497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69398993858063247286331 104098490787094870929497)
      ·
        refine ⟨78073868090321153197123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104098490787094870929497 78073868090321153197123)
        ·
          refine ⟨117110802135481729795685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78073868090321153197123 117110802135481729795685)
          ·
            refine ⟨21958275400402824336691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117110802135481729795685 21958275400402824336691)
            ·
              refine ⟨32937413100604236505037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21958275400402824336691 32937413100604236505037)
              ·
                refine ⟨12351529912726588689389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32937413100604236505037 12351529912726588689389)
                ·
                  refine ⟨4631823717272470758521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12351529912726588689389 4631823717272470758521)
                  ·
                    rfl

theorem cell20_10148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_10148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10148 prefixEnd_10148 := by exact prefixLift 10148
  have htrace : WordTrace (prefixWord ++ tailWord_10148) baseStart_10148 baseEnd_10148 := by
    simpa [prefixWord, tailWord_10148, baseEnd_10148] using wordTrace_append hprefix tailTrace_10148
  have hstable : (prefixWord ++ tailWord_10148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10148).length < 2 ^ (prefixWord ++ tailWord_10148).sum := by decide
  have hdescent : baseEnd_10148 < baseStart_10148 := by decide
  rcases family_descends (prefixWord ++ tailWord_10148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10245 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_10245 : Nat := 118140960795 + 10245 * 2 ^ 59
def prefixEnd_10245 : Nat := 4983230072969 + 3 ^ 40 * 10245 * 2
def baseEnd_10245 : Nat := 4676097160371244524791

theorem tailTrace_10245 : CollatzResearch.WordTrace tailWord_10245 prefixEnd_10245 4676097160371244524791 := by
  unfold tailWord_10245
  simp only [CollatzResearch.WordTrace]
  refine ⟨373665847891589551808189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 249110565261059701205459 373665847891589551808189)
  ·
    refine ⟨140124692959346081928071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 373665847891589551808189 140124692959346081928071)
    ·
      refine ⟨210187039439019122892107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140124692959346081928071 210187039439019122892107)
      ·
        refine ⟨315280559158528684338161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210187039439019122892107 315280559158528684338161)
        ·
          refine ⟨236460419368896513253621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315280559158528684338161 236460419368896513253621)
          ·
            refine ⟨22168164315834048117527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 236460419368896513253621 22168164315834048117527)
            ·
              refine ⟨33252246473751072176291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22168164315834048117527 33252246473751072176291)
              ·
                refine ⟨49878369710626608264437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33252246473751072176291 49878369710626608264437)
                ·
                  refine ⟨4676097160371244524791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49878369710626608264437 4676097160371244524791)
                  ·
                    rfl

theorem cell20_10245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_10245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10245 prefixEnd_10245 := by exact prefixLift 10245
  have htrace : WordTrace (prefixWord ++ tailWord_10245) baseStart_10245 baseEnd_10245 := by
    simpa [prefixWord, tailWord_10245, baseEnd_10245] using wordTrace_append hprefix tailTrace_10245
  have hstable : (prefixWord ++ tailWord_10245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10245).length < 2 ^ (prefixWord ++ tailWord_10245).sum := by decide
  have hdescent : baseEnd_10245 < baseStart_10245 := by decide
  rcases family_descends (prefixWord ++ tailWord_10245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10269 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 4]
def baseStart_10269 : Nat := 118140960795 + 10269 * 2 ^ 59
def prefixEnd_10269 : Nat := 4983230072969 + 3 ^ 40 * 10269 * 2
def baseEnd_10269 : Nat := 4687051414333827724693

theorem tailTrace_10269 : CollatzResearch.WordTrace tailWord_10269 prefixEnd_10269 4687051414333827724693 := by
  unfold tailWord_10269
  simp only [CollatzResearch.WordTrace]
  refine ⟨374541199804641650681861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 249694133203094433787907 374541199804641650681861)
  ·
    refine ⟨70226474963370309502849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 374541199804641650681861 70226474963370309502849)
    ·
      refine ⟨52669856222527732127137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70226474963370309502849 52669856222527732127137)
      ·
        refine ⟨39502392166895799095353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52669856222527732127137 39502392166895799095353)
        ·
          refine ⟨29626794125171849321515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39502392166895799095353 29626794125171849321515)
          ·
            refine ⟨44440191187757773982273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29626794125171849321515 44440191187757773982273)
            ·
              refine ⟨33330143390818330486705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44440191187757773982273 33330143390818330486705)
              ·
                refine ⟨24997607543113747865029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33330143390818330486705 24997607543113747865029)
                ·
                  refine ⟨4687051414333827724693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24997607543113747865029 4687051414333827724693)
                  ·
                    rfl

theorem cell20_10269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_10269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10269 prefixEnd_10269 := by exact prefixLift 10269
  have htrace : WordTrace (prefixWord ++ tailWord_10269) baseStart_10269 baseEnd_10269 := by
    simpa [prefixWord, tailWord_10269, baseEnd_10269] using wordTrace_append hprefix tailTrace_10269
  have hstable : (prefixWord ++ tailWord_10269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10269).length < 2 ^ (prefixWord ++ tailWord_10269).sum := by decide
  have hdescent : baseEnd_10269 < baseStart_10269 := by decide
  rcases family_descends (prefixWord ++ tailWord_10269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10345 : List Nat := [1, 2, 1, 1, 1, 5, 2, 5, 2]
def baseStart_10345 : Nat := 118140960795 + 10345 * 2 ^ 59
def prefixEnd_10345 : Nat := 4983230072969 + 3 ^ 40 * 10345 * 2
def baseEnd_10345 : Nat := 4721739885215341191049

theorem tailTrace_10345 : CollatzResearch.WordTrace tailWord_10345 prefixEnd_10345 4721739885215341191049 := by
  unfold tailWord_10345
  simp only [CollatzResearch.WordTrace]
  refine ⟨377313147529306630448489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 251542098352871086965659 377313147529306630448489)
  ·
    refine ⟨282984860646979972836367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 377313147529306630448489 282984860646979972836367)
    ·
      refine ⟨424477290970469959254551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282984860646979972836367 424477290970469959254551)
      ·
        refine ⟨636715936455704938881827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424477290970469959254551 636715936455704938881827)
        ·
          refine ⟨955073904683557408322741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636715936455704938881827 955073904683557408322741)
          ·
            refine ⟨89538178564083507030257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 955073904683557408322741 89538178564083507030257)
            ·
              refine ⟨67153633923062630272693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89538178564083507030257 67153633923062630272693)
              ·
                refine ⟨6295653180287121588065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67153633923062630272693 6295653180287121588065)
                ·
                  refine ⟨4721739885215341191049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6295653180287121588065 4721739885215341191049)
                  ·
                    rfl

theorem cell20_10345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_10345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10345 prefixEnd_10345 := by exact prefixLift 10345
  have htrace : WordTrace (prefixWord ++ tailWord_10345) baseStart_10345 baseEnd_10345 := by
    simpa [prefixWord, tailWord_10345, baseEnd_10345] using wordTrace_append hprefix tailTrace_10345
  have hstable : (prefixWord ++ tailWord_10345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10345).length < 2 ^ (prefixWord ++ tailWord_10345).sum := by decide
  have hdescent : baseEnd_10345 < baseStart_10345 := by decide
  rcases family_descends (prefixWord ++ tailWord_10345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10358 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_10358 : Nat := 118140960795 + 10358 * 2 ^ 59
def prefixEnd_10358 : Nat := 4983230072969 + 3 ^ 40 * 10358 * 2
def baseEnd_10358 : Nat := 4727673439445073757663

theorem tailTrace_10358 : CollatzResearch.WordTrace tailWord_10358 prefixEnd_10358 4727673439445073757663 := by
  unfold tailWord_10358
  simp only [CollatzResearch.WordTrace]
  refine ⟨23611706030138115666983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 251858197654806567114485 23611706030138115666983)
  ·
    refine ⟨35417559045207173500475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23611706030138115666983 35417559045207173500475)
    ·
      refine ⟨53126338567810760250713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35417559045207173500475 53126338567810760250713)
      ·
        refine ⟨39844753925858070188035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53126338567810760250713 39844753925858070188035)
        ·
          refine ⟨59767130888787105282053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39844753925858070188035 59767130888787105282053)
          ·
            refine ⟨11206337041647582240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59767130888787105282053 11206337041647582240385)
            ·
              refine ⟨8404752781235686680289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11206337041647582240385 8404752781235686680289)
              ·
                refine ⟨6303564585926765010217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8404752781235686680289 6303564585926765010217)
                ·
                  refine ⟨4727673439445073757663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303564585926765010217 4727673439445073757663)
                  ·
                    rfl

theorem cell20_10358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_10358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10358 prefixEnd_10358 := by exact prefixLift 10358
  have htrace : WordTrace (prefixWord ++ tailWord_10358) baseStart_10358 baseEnd_10358 := by
    simpa [prefixWord, tailWord_10358, baseEnd_10358] using wordTrace_append hprefix tailTrace_10358
  have hstable : (prefixWord ++ tailWord_10358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10358).length < 2 ^ (prefixWord ++ tailWord_10358).sum := by decide
  have hdescent : baseEnd_10358 < baseStart_10358 := by decide
  rcases family_descends (prefixWord ++ tailWord_10358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10359 : List Nat := [1, 1, 3, 1, 1, 5, 1, 4, 3]
def baseStart_10359 : Nat := 118140960795 + 10359 * 2 ^ 59
def prefixEnd_10359 : Nat := 4983230072969 + 3 ^ 40 * 10359 * 2
def baseEnd_10359 : Nat := 4728129866693514724325

theorem tailTrace_10359 : CollatzResearch.WordTrace tailWord_10359 prefixEnd_10359 4728129866693514724325 := by
  unfold tailWord_10359
  simp only [CollatzResearch.WordTrace]
  refine ⟨377823769478587021458131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 251882512985724680972087 377823769478587021458131)
  ·
    refine ⟨566735654217880532187197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 377823769478587021458131 566735654217880532187197)
    ·
      refine ⟨212525870331705199570199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 566735654217880532187197 212525870331705199570199)
      ·
        refine ⟨318788805497557799355299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212525870331705199570199 318788805497557799355299)
        ·
          refine ⟨478183208246336699032949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318788805497557799355299 478183208246336699032949)
          ·
            refine ⟨44829675773094065534339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 478183208246336699032949 44829675773094065534339)
            ·
              refine ⟨67244513659641098301509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44829675773094065534339 67244513659641098301509)
              ·
                refine ⟨12608346311182705931533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67244513659641098301509 12608346311182705931533)
                ·
                  refine ⟨4728129866693514724325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12608346311182705931533 4728129866693514724325)
                  ·
                    rfl

theorem cell20_10359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 3].length) (baseStart_10359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10359 prefixEnd_10359 := by exact prefixLift 10359
  have htrace : WordTrace (prefixWord ++ tailWord_10359) baseStart_10359 baseEnd_10359 := by
    simpa [prefixWord, tailWord_10359, baseEnd_10359] using wordTrace_append hprefix tailTrace_10359
  have hstable : (prefixWord ++ tailWord_10359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10359).length < 2 ^ (prefixWord ++ tailWord_10359).sum := by decide
  have hdescent : baseEnd_10359 < baseStart_10359 := by decide
  rcases family_descends (prefixWord ++ tailWord_10359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10369 : List Nat := [1, 2, 4, 2, 3, 2, 1, 5]
def baseStart_10369 : Nat := 118140960795 + 10369 * 2 ^ 59
def prefixEnd_10369 : Nat := 4983230072969 + 3 ^ 40 * 10369 * 2
def baseEnd_10369 : Nat := 1577564713059308130317

theorem tailTrace_10369 : CollatzResearch.WordTrace tailWord_10369 prefixEnd_10369 1577564713059308130317 := by
  unfold tailWord_10369
  simp only [CollatzResearch.WordTrace]
  refine ⟨378188499442358729322161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 252125666294905819548107 378188499442358729322161)
  ·
    refine ⟨283641374581769046991621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 378188499442358729322161 283641374581769046991621)
    ·
      refine ⟨53182757734081696310929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283641374581769046991621 53182757734081696310929)
      ·
        refine ⟨39887068300561272233197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53182757734081696310929 39887068300561272233197)
        ·
          refine ⟨14957650612710477087449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39887068300561272233197 14957650612710477087449)
          ·
            refine ⟨11218237959532857815587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14957650612710477087449 11218237959532857815587)
            ·
              refine ⟨16827356939299286723381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11218237959532857815587 16827356939299286723381)
              ·
                refine ⟨1577564713059308130317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16827356939299286723381 1577564713059308130317)
                ·
                  rfl

theorem cell20_10369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_10369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10369 prefixEnd_10369 := by exact prefixLift 10369
  have htrace : WordTrace (prefixWord ++ tailWord_10369) baseStart_10369 baseEnd_10369 := by
    simpa [prefixWord, tailWord_10369, baseEnd_10369] using wordTrace_append hprefix tailTrace_10369
  have hstable : (prefixWord ++ tailWord_10369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10369).length < 2 ^ (prefixWord ++ tailWord_10369).sum := by decide
  have hdescent : baseEnd_10369 < baseStart_10369 := by decide
  rcases family_descends (prefixWord ++ tailWord_10369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10376 : List Nat := [2, 1, 3, 4, 1, 1, 2, 3, 3]
def baseStart_10376 : Nat := 118140960795 + 10376 * 2 ^ 59
def prefixEnd_10376 : Nat := 4983230072969 + 3 ^ 40 * 10376 * 2
def baseEnd_10376 : Nat := 4735889129917011157589

theorem tailTrace_10376 : CollatzResearch.WordTrace tailWord_10376 prefixEnd_10376 4735889129917011157589 := by
  unfold tailWord_10376
  simp only [CollatzResearch.WordTrace]
  refine ⟨189221905208499462413491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 252295873611332616551321 189221905208499462413491)
  ·
    refine ⟨283832857812749193620237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189221905208499462413491 283832857812749193620237)
    ·
      refine ⟨106437321679780947607589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283832857812749193620237 106437321679780947607589)
      ·
        refine ⟨19956997814958927676423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106437321679780947607589 19956997814958927676423)
        ·
          refine ⟨29935496722438391514635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19956997814958927676423 29935496722438391514635)
          ·
            refine ⟨44903245083657587271953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29935496722438391514635 44903245083657587271953)
            ·
              refine ⟨33677433812743190453965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44903245083657587271953 33677433812743190453965)
              ·
                refine ⟨12629037679778696420237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33677433812743190453965 12629037679778696420237)
                ·
                  refine ⟨4735889129917011157589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12629037679778696420237 4735889129917011157589)
                  ·
                    rfl

theorem cell20_10376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_10376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10376 prefixEnd_10376 := by exact prefixLift 10376
  have htrace : WordTrace (prefixWord ++ tailWord_10376) baseStart_10376 baseEnd_10376 := by
    simpa [prefixWord, tailWord_10376, baseEnd_10376] using wordTrace_append hprefix tailTrace_10376
  have hstable : (prefixWord ++ tailWord_10376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10376).length < 2 ^ (prefixWord ++ tailWord_10376).sum := by decide
  have hdescent : baseEnd_10376 < baseStart_10376 := by decide
  rcases family_descends (prefixWord ++ tailWord_10376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10380 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_10380 : Nat := 118140960795 + 10380 * 2 ^ 59
def prefixEnd_10380 : Nat := 4983230072969 + 3 ^ 40 * 10380 * 2
def baseEnd_10380 : Nat := 4737714838910775024239

theorem tailTrace_10380 : CollatzResearch.WordTrace tailWord_10380 prefixEnd_10380 4737714838910775024239 := by
  unfold tailWord_10380
  simp only [CollatzResearch.WordTrace]
  refine ⟨189294851201253803986297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 252393134935005071981729 189294851201253803986297)
  ·
    refine ⟨141971138400940352989723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 189294851201253803986297 141971138400940352989723)
    ·
      refine ⟨212956707601410529484585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141971138400940352989723 212956707601410529484585)
      ·
        refine ⟨159717530701057897113439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212956707601410529484585 159717530701057897113439)
        ·
          refine ⟨239576296051586845670159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159717530701057897113439 239576296051586845670159)
          ·
            refine ⟨359364444077380268505239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239576296051586845670159 359364444077380268505239)
            ·
              refine ⟨539046666116070402757859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359364444077380268505239 539046666116070402757859)
              ·
                refine ⟨808569999174105604136789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 539046666116070402757859 808569999174105604136789)
                ·
                  refine ⟨4737714838910775024239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 808569999174105604136789 4737714838910775024239)
                  ·
                    rfl

theorem cell20_10380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_10380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10380 prefixEnd_10380 := by exact prefixLift 10380
  have htrace : WordTrace (prefixWord ++ tailWord_10380) baseStart_10380 baseEnd_10380 := by
    simpa [prefixWord, tailWord_10380, baseEnd_10380] using wordTrace_append hprefix tailTrace_10380
  have hstable : (prefixWord ++ tailWord_10380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10380).length < 2 ^ (prefixWord ++ tailWord_10380).sum := by decide
  have hdescent : baseEnd_10380 < baseStart_10380 := by decide
  rcases family_descends (prefixWord ++ tailWord_10380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10400 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 2]
def baseStart_10400 : Nat := 118140960795 + 10400 * 2 ^ 59
def prefixEnd_10400 : Nat := 4983230072969 + 3 ^ 40 * 10400 * 2
def baseEnd_10400 : Nat := 4746843383879594357491

theorem tailTrace_10400 : CollatzResearch.WordTrace tailWord_10400 prefixEnd_10400 4746843383879594357491 := by
  unfold tailWord_10400
  simp only [CollatzResearch.WordTrace]
  refine ⟨189659581165025511850327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 252879441553367349133769 189659581165025511850327)
  ·
    refine ⟨284489371747538267775491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189659581165025511850327 284489371747538267775491)
    ·
      refine ⟨426734057621307401663237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284489371747538267775491 426734057621307401663237)
      ·
        refine ⟨80012635803995137811857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 426734057621307401663237 80012635803995137811857)
        ·
          refine ⟨60009476852996353358893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80012635803995137811857 60009476852996353358893)
          ·
            refine ⟨22503553819873632509585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60009476852996353358893 22503553819873632509585)
            ·
              refine ⟨16877665364905224382189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22503553819873632509585 16877665364905224382189)
              ·
                refine ⟨6329124511839459143321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16877665364905224382189 6329124511839459143321)
                ·
                  refine ⟨4746843383879594357491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6329124511839459143321 4746843383879594357491)
                  ·
                    rfl

theorem cell20_10400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_10400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10400 prefixEnd_10400 := by exact prefixLift 10400
  have htrace : WordTrace (prefixWord ++ tailWord_10400) baseStart_10400 baseEnd_10400 := by
    simpa [prefixWord, tailWord_10400, baseEnd_10400] using wordTrace_append hprefix tailTrace_10400
  have hstable : (prefixWord ++ tailWord_10400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10400).length < 2 ^ (prefixWord ++ tailWord_10400).sum := by decide
  have hdescent : baseEnd_10400 < baseStart_10400 := by decide
  rcases family_descends (prefixWord ++ tailWord_10400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10410 : List Nat := [3, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_10410 : Nat := 118140960795 + 10410 * 2 ^ 59
def prefixEnd_10410 : Nat := 4983230072969 + 3 ^ 40 * 10410 * 2
def baseEnd_10410 : Nat := 4751407656364004024117

theorem tailTrace_10410 : CollatzResearch.WordTrace tailWord_10410 prefixEnd_10410 4751407656364004024117 := by
  unfold tailWord_10410
  simp only [CollatzResearch.WordTrace]
  refine ⟨94920973073455682891171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 253122594862548487709789 94920973073455682891171)
  ·
    refine ⟨142381459610183524336757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94920973073455682891171 142381459610183524336757)
    ·
      refine ⟨13348261838454705406571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142381459610183524336757 13348261838454705406571)
      ·
        refine ⟨20022392757682058109857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13348261838454705406571 20022392757682058109857)
        ·
          refine ⟨15016794568261543582393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20022392757682058109857 15016794568261543582393)
          ·
            refine ⟨11262595926196157686795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15016794568261543582393 11262595926196157686795)
            ·
              refine ⟨16893893889294236530193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11262595926196157686795 16893893889294236530193)
              ·
                refine ⟨12670420416970677397645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16893893889294236530193 12670420416970677397645)
                ·
                  refine ⟨4751407656364004024117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12670420416970677397645 4751407656364004024117)
                  ·
                    rfl

theorem cell20_10410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_10410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10410 prefixEnd_10410 := by exact prefixLift 10410
  have htrace : WordTrace (prefixWord ++ tailWord_10410) baseStart_10410 baseEnd_10410 := by
    simpa [prefixWord, tailWord_10410, baseEnd_10410] using wordTrace_append hprefix tailTrace_10410
  have hstable : (prefixWord ++ tailWord_10410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10410).length < 2 ^ (prefixWord ++ tailWord_10410).sum := by decide
  have hdescent : baseEnd_10410 < baseStart_10410 := by decide
  rcases family_descends (prefixWord ++ tailWord_10410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10442 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_10442 : Nat := 118140960795 + 10442 * 2 ^ 59
def prefixEnd_10442 : Nat := 4983230072969 + 3 ^ 40 * 10442 * 2
def baseEnd_10442 : Nat := 4766013328314114957319

theorem tailTrace_10442 : CollatzResearch.WordTrace tailWord_10442 prefixEnd_10442 4766013328314114957319 := by
  unfold tailWord_10442
  simp only [CollatzResearch.WordTrace]
  refine ⟨95212757044473049182395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 253900685451928131153053 95212757044473049182395)
  ·
    refine ⟨142819135566709573773593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95212757044473049182395 142819135566709573773593)
    ·
      refine ⟨107114351675032180330195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142819135566709573773593 107114351675032180330195)
      ·
        refine ⟨160671527512548270495293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107114351675032180330195 160671527512548270495293)
        ·
          refine ⟨60251822817205601435735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160671527512548270495293 60251822817205601435735)
          ·
            refine ⟨90377734225808402153603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60251822817205601435735 90377734225808402153603)
            ·
              refine ⟨135566601338712603230405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90377734225808402153603 135566601338712603230405)
              ·
                refine ⟨25418737751008613105701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135566601338712603230405 25418737751008613105701)
                ·
                  refine ⟨4766013328314114957319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25418737751008613105701 4766013328314114957319)
                  ·
                    rfl

theorem cell20_10442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_10442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10442 prefixEnd_10442 := by exact prefixLift 10442
  have htrace : WordTrace (prefixWord ++ tailWord_10442) baseStart_10442 baseEnd_10442 := by
    simpa [prefixWord, tailWord_10442, baseEnd_10442] using wordTrace_append hprefix tailTrace_10442
  have hstable : (prefixWord ++ tailWord_10442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10442).length < 2 ^ (prefixWord ++ tailWord_10442).sum := by decide
  have hdescent : baseEnd_10442 < baseStart_10442 := by decide
  rcases family_descends (prefixWord ++ tailWord_10442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10476 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 2]
def baseStart_10476 : Nat := 118140960795 + 10476 * 2 ^ 59
def prefixEnd_10476 : Nat := 4983230072969 + 3 ^ 40 * 10476 * 2
def baseEnd_10476 : Nat := 4781531854761107823847

theorem tailTrace_10476 : CollatzResearch.WordTrace tailWord_10476 prefixEnd_10476 4781531854761107823847 := by
  unfold tailWord_10476
  simp only [CollatzResearch.WordTrace]
  refine ⟨191045555027358001733641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 254727406703144002311521 191045555027358001733641)
  ·
    refine ⟨143284166270518501300231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 191045555027358001733641 143284166270518501300231)
    ·
      refine ⟨214926249405777751950347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143284166270518501300231 214926249405777751950347)
      ·
        refine ⟨322389374108666627925521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214926249405777751950347 322389374108666627925521)
        ·
          refine ⟨241792030581499970944141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322389374108666627925521 241792030581499970944141)
          ·
            refine ⟨90672011468062489104053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241792030581499970944141 90672011468062489104053)
            ·
              refine ⟨8500501075130858353505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90672011468062489104053 8500501075130858353505)
              ·
                refine ⟨6375375806348143765129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8500501075130858353505 6375375806348143765129)
                ·
                  refine ⟨4781531854761107823847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6375375806348143765129 4781531854761107823847)
                  ·
                    rfl

theorem cell20_10476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_10476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10476 prefixEnd_10476 := by exact prefixLift 10476
  have htrace : WordTrace (prefixWord ++ tailWord_10476) baseStart_10476 baseEnd_10476 := by
    simpa [prefixWord, tailWord_10476, baseEnd_10476] using wordTrace_append hprefix tailTrace_10476
  have hstable : (prefixWord ++ tailWord_10476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10476).length < 2 ^ (prefixWord ++ tailWord_10476).sum := by decide
  have hdescent : baseEnd_10476 < baseStart_10476 := by decide
  rcases family_descends (prefixWord ++ tailWord_10476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10490 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_10490 : Nat := 118140960795 + 10490 * 2 ^ 59
def prefixEnd_10490 : Nat := 4983230072969 + 3 ^ 40 * 10490 * 2
def baseEnd_10490 : Nat := 4787921836239281357123

theorem tailTrace_10490 : CollatzResearch.WordTrace tailWord_10490 prefixEnd_10490 4787921836239281357123 := by
  unfold tailWord_10490
  simp only [CollatzResearch.WordTrace]
  refine ⟨95650433000999098619231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 255067821335997596317949 95650433000999098619231)
  ·
    refine ⟨143475649501498647928847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95650433000999098619231 143475649501498647928847)
    ·
      refine ⟨215213474252247971893271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143475649501498647928847 215213474252247971893271)
      ·
        refine ⟨322820211378371957839907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215213474252247971893271 322820211378371957839907)
        ·
          refine ⟨484230317067557936759861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322820211378371957839907 484230317067557936759861)
          ·
            refine ⟨45396592225083556571237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 484230317067557936759861 45396592225083556571237)
            ·
              refine ⟨8511861042203166857107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45396592225083556571237 8511861042203166857107)
              ·
                refine ⟨12767791563304750285661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8511861042203166857107 12767791563304750285661)
                ·
                  refine ⟨4787921836239281357123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12767791563304750285661 4787921836239281357123)
                  ·
                    rfl

theorem cell20_10490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_10490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10490 prefixEnd_10490 := by exact prefixLift 10490
  have htrace : WordTrace (prefixWord ++ tailWord_10490) baseStart_10490 baseEnd_10490 := by
    simpa [prefixWord, tailWord_10490, baseEnd_10490] using wordTrace_append hprefix tailTrace_10490
  have hstable : (prefixWord ++ tailWord_10490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10490).length < 2 ^ (prefixWord ++ tailWord_10490).sum := by decide
  have hdescent : baseEnd_10490 < baseStart_10490 := by decide
  rcases family_descends (prefixWord ++ tailWord_10490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10525 : List Nat := [1, 4, 2, 3, 10]
def baseStart_10525 : Nat := 118140960795 + 10525 * 2 ^ 59
def prefixEnd_10525 : Nat := 4983230072969 + 3 ^ 40 * 10525 * 2
def baseEnd_10525 : Nat := 59307367776971792473

theorem tailTrace_10525 : CollatzResearch.WordTrace tailWord_10525 prefixEnd_10525 59307367776971792473 := by
  unfold tailWord_10525
  simp only [CollatzResearch.WordTrace]
  refine ⟨383878286877197372001029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 255918857918131581334019 383878286877197372001029)
  ·
    refine ⟨71977178789474507250193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 383878286877197372001029 71977178789474507250193)
    ·
      refine ⟨53982884092105880437645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71977178789474507250193 53982884092105880437645)
      ·
        refine ⟨20243581534539705164117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53982884092105880437645 20243581534539705164117)
        ·
          refine ⟨59307367776971792473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 20243581534539705164117 59307367776971792473)
          ·
            rfl

theorem cell20_10525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 10].length) (baseStart_10525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10525 prefixEnd_10525 := by exact prefixLift 10525
  have htrace : WordTrace (prefixWord ++ tailWord_10525) baseStart_10525 baseEnd_10525 := by
    simpa [prefixWord, tailWord_10525, baseEnd_10525] using wordTrace_append hprefix tailTrace_10525
  have hstable : (prefixWord ++ tailWord_10525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10525).length < 2 ^ (prefixWord ++ tailWord_10525).sum := by decide
  have hdescent : baseEnd_10525 < baseStart_10525 := by decide
  rcases family_descends (prefixWord ++ tailWord_10525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10528 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_10528 : Nat := 118140960795 + 10528 * 2 ^ 59
def prefixEnd_10528 : Nat := 4983230072969 + 3 ^ 40 * 10528 * 2
def baseEnd_10528 : Nat := 4805266071680038090301

theorem tailTrace_10528 : CollatzResearch.WordTrace tailWord_10528 prefixEnd_10528 4805266071680038090301 := by
  unfold tailWord_10528
  simp only [CollatzResearch.WordTrace]
  refine ⟨191993852933164442180119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 255991803910885922906825 191993852933164442180119)
  ·
    refine ⟨287990779399746663270179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191993852933164442180119 287990779399746663270179)
    ·
      refine ⟨431986169099619994905269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287990779399746663270179 431986169099619994905269)
      ·
        refine ⟨40498703353089374522369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 431986169099619994905269 40498703353089374522369)
        ·
          refine ⟨30374027514817030891777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40498703353089374522369 30374027514817030891777)
          ·
            refine ⟨22780520636112773168833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30374027514817030891777 22780520636112773168833)
            ·
              refine ⟨17085390477084579876625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22780520636112773168833 17085390477084579876625)
              ·
                refine ⟨12814042857813434907469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17085390477084579876625 12814042857813434907469)
                ·
                  refine ⟨4805266071680038090301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12814042857813434907469 4805266071680038090301)
                  ·
                    rfl

theorem cell20_10528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_10528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10528 prefixEnd_10528 := by exact prefixLift 10528
  have htrace : WordTrace (prefixWord ++ tailWord_10528) baseStart_10528 baseEnd_10528 := by
    simpa [prefixWord, tailWord_10528, baseEnd_10528] using wordTrace_append hprefix tailTrace_10528
  have hstable : (prefixWord ++ tailWord_10528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10528).length < 2 ^ (prefixWord ++ tailWord_10528).sum := by decide
  have hdescent : baseEnd_10528 < baseStart_10528 := by decide
  rcases family_descends (prefixWord ++ tailWord_10528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10538 : List Nat := [3, 1, 4, 2, 3, 1, 1, 5]
def baseStart_10538 : Nat := 118140960795 + 10538 * 2 ^ 59
def prefixEnd_10538 : Nat := 4983230072969 + 3 ^ 40 * 10538 * 2
def baseEnd_10538 : Nat := 1603276781388149252309

theorem tailTrace_10538 : CollatzResearch.WordTrace tailWord_10538 prefixEnd_10538 1603276781388149252309 := by
  unfold tailWord_10538
  simp only [CollatzResearch.WordTrace]
  refine ⟨96088108957525148056067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 256234957220067061482845 96088108957525148056067)
  ·
    refine ⟨144132163436287722084101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96088108957525148056067 144132163436287722084101)
    ·
      refine ⟨27024780644303947890769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 144132163436287722084101 27024780644303947890769)
      ·
        refine ⟨20268585483227960918077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27024780644303947890769 20268585483227960918077)
        ·
          refine ⟨7600719556210485344279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20268585483227960918077 7600719556210485344279)
          ·
            refine ⟨11401079334315728016419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600719556210485344279 11401079334315728016419)
            ·
              refine ⟨17101619001473592024629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11401079334315728016419 17101619001473592024629)
              ·
                refine ⟨1603276781388149252309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17101619001473592024629 1603276781388149252309)
                ·
                  rfl

theorem cell20_10538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_10538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10538 prefixEnd_10538 := by exact prefixLift 10538
  have htrace : WordTrace (prefixWord ++ tailWord_10538) baseStart_10538 baseEnd_10538 := by
    simpa [prefixWord, tailWord_10538, baseEnd_10538] using wordTrace_append hprefix tailTrace_10538
  have hstable : (prefixWord ++ tailWord_10538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10538).length < 2 ^ (prefixWord ++ tailWord_10538).sum := by decide
  have hdescent : baseEnd_10538 < baseStart_10538 := by decide
  rcases family_descends (prefixWord ++ tailWord_10538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10549 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_10549 : Nat := 118140960795 + 10549 * 2 ^ 59
def prefixEnd_10549 : Nat := 4983230072969 + 3 ^ 40 * 10549 * 2
def baseEnd_10549 : Nat := 4814851043897298390215

theorem tailTrace_10549 : CollatzResearch.WordTrace tailWord_10549 prefixEnd_10549 4814851043897298390215 := by
  unfold tailWord_10549
  simp only [CollatzResearch.WordTrace]
  refine ⟨384753638790249470874701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 256502425860166313916467 384753638790249470874701)
  ·
    refine ⟨144282614546343551578013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 384753638790249470874701 144282614546343551578013)
    ·
      refine ⟨54105980454878831841755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 144282614546343551578013 54105980454878831841755)
      ·
        refine ⟨81158970682318247762633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54105980454878831841755 81158970682318247762633)
        ·
          refine ⟨60869228011738685821975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81158970682318247762633 60869228011738685821975)
          ·
            refine ⟨91303842017608028732963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60869228011738685821975 91303842017608028732963)
            ·
              refine ⟨136955763026412043099445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91303842017608028732963 136955763026412043099445)
              ·
                refine ⟨12839602783726129040573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136955763026412043099445 12839602783726129040573)
                ·
                  refine ⟨4814851043897298390215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12839602783726129040573 4814851043897298390215)
                  ·
                    rfl

theorem cell20_10549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_10549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10549 prefixEnd_10549 := by exact prefixLift 10549
  have htrace : WordTrace (prefixWord ++ tailWord_10549) baseStart_10549 baseEnd_10549 := by
    simpa [prefixWord, tailWord_10549, baseEnd_10549] using wordTrace_append hprefix tailTrace_10549
  have hstable : (prefixWord ++ tailWord_10549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10549).length < 2 ^ (prefixWord ++ tailWord_10549).sum := by decide
  have hdescent : baseEnd_10549 < baseStart_10549 := by decide
  rcases family_descends (prefixWord ++ tailWord_10549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10556 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 4]
def baseStart_10556 : Nat := 118140960795 + 10556 * 2 ^ 59
def prefixEnd_10556 : Nat := 4983230072969 + 3 ^ 40 * 10556 * 2
def baseEnd_10556 : Nat := 4818046034636385156853

theorem tailTrace_10556 : CollatzResearch.WordTrace tailWord_10556 prefixEnd_10556 4818046034636385156853 := by
  unfold tailWord_10556
  simp only [CollatzResearch.WordTrace]
  refine ⟨192504474882444833189761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 256672633176593110919681 192504474882444833189761)
  ·
    refine ⟨144378356161833624892321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 192504474882444833189761 144378356161833624892321)
    ·
      refine ⟨108283767121375218669241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144378356161833624892321 108283767121375218669241)
      ·
        refine ⟨81212825341031414001931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108283767121375218669241 81212825341031414001931)
        ·
          refine ⟨121819238011547121002897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81212825341031414001931 121819238011547121002897)
          ·
            refine ⟨91364428508660340752173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121819238011547121002897 91364428508660340752173)
            ·
              refine ⟨34261660690747627782065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91364428508660340752173 34261660690747627782065)
              ·
                refine ⟨25696245518060720836549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34261660690747627782065 25696245518060720836549)
                ·
                  refine ⟨4818046034636385156853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25696245518060720836549 4818046034636385156853)
                  ·
                    rfl

theorem cell20_10556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_10556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10556 prefixEnd_10556 := by exact prefixLift 10556
  have htrace : WordTrace (prefixWord ++ tailWord_10556) baseStart_10556 baseEnd_10556 := by
    simpa [prefixWord, tailWord_10556, baseEnd_10556] using wordTrace_append hprefix tailTrace_10556
  have hstable : (prefixWord ++ tailWord_10556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10556).length < 2 ^ (prefixWord ++ tailWord_10556).sum := by decide
  have hdescent : baseEnd_10556 < baseStart_10556 := by decide
  rcases family_descends (prefixWord ++ tailWord_10556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10615 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 6]
def baseStart_10615 : Nat := 118140960795 + 10615 * 2 ^ 59
def prefixEnd_10615 : Nat := 4983230072969 + 3 ^ 40 * 10615 * 2
def baseEnd_10615 : Nat := 4844975242294402189945

theorem tailTrace_10615 : CollatzResearch.WordTrace tailWord_10615 prefixEnd_10615 4844975242294402189945 := by
  unfold tailWord_10615
  simp only [CollatzResearch.WordTrace]
  refine ⟨387160856551142742777299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 258107237700761828518199 387160856551142742777299)
  ·
    refine ⟨580741284826714114165949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 387160856551142742777299 580741284826714114165949)
    ·
      refine ⟨217777981810017792812231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 580741284826714114165949 217777981810017792812231)
      ·
        refine ⟨326666972715026689218347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217777981810017792812231 326666972715026689218347)
        ·
          refine ⟨490000459072540033827521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326666972715026689218347 490000459072540033827521)
          ·
            refine ⟨367500344304405025370641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490000459072540033827521 367500344304405025370641)
            ·
              refine ⟨275625258228303769027981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367500344304405025370641 275625258228303769027981)
              ·
                refine ⟨103359471835613913385493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275625258228303769027981 103359471835613913385493)
                ·
                  refine ⟨4844975242294402189945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103359471835613913385493 4844975242294402189945)
                  ·
                    rfl

theorem cell20_10615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_10615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10615 prefixEnd_10615 := by exact prefixLift 10615
  have htrace : WordTrace (prefixWord ++ tailWord_10615) baseStart_10615 baseEnd_10615 := by
    simpa [prefixWord, tailWord_10615, baseEnd_10615] using wordTrace_append hprefix tailTrace_10615
  have hstable : (prefixWord ++ tailWord_10615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10615).length < 2 ^ (prefixWord ++ tailWord_10615).sum := by decide
  have hdescent : baseEnd_10615 < baseStart_10615 := by decide
  rcases family_descends (prefixWord ++ tailWord_10615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10625 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_10625 : Nat := 118140960795 + 10625 * 2 ^ 59
def prefixEnd_10625 : Nat := 4983230072969 + 3 ^ 40 * 10625 * 2
def baseEnd_10625 : Nat := 4849539514778811856571

theorem tailTrace_10625 : CollatzResearch.WordTrace tailWord_10625 prefixEnd_10625 4849539514778811856571 := by
  unfold tailWord_10625
  simp only [CollatzResearch.WordTrace]
  refine ⟨387525586514914450641329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 258350391009942967094219 387525586514914450641329)
  ·
    refine ⟨290644189886185837980997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 387525586514914450641329 290644189886185837980997)
    ·
      refine ⟨54495785603659844621437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290644189886185837980997 54495785603659844621437)
      ·
        refine ⟨20435919601372441733039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54495785603659844621437 20435919601372441733039)
        ·
          refine ⟨30653879402058662599559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20435919601372441733039 30653879402058662599559)
          ·
            refine ⟨45980819103087993899339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30653879402058662599559 45980819103087993899339)
            ·
              refine ⟨68971228654631990849009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45980819103087993899339 68971228654631990849009)
              ·
                refine ⟨51728421490973993136757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68971228654631990849009 51728421490973993136757)
                ·
                  refine ⟨4849539514778811856571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51728421490973993136757 4849539514778811856571)
                  ·
                    rfl

theorem cell20_10625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_10625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10625 prefixEnd_10625 := by exact prefixLift 10625
  have htrace : WordTrace (prefixWord ++ tailWord_10625) baseStart_10625 baseEnd_10625 := by
    simpa [prefixWord, tailWord_10625, baseEnd_10625] using wordTrace_append hprefix tailTrace_10625
  have hstable : (prefixWord ++ tailWord_10625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10625).length < 2 ^ (prefixWord ++ tailWord_10625).sum := by decide
  have hdescent : baseEnd_10625 < baseStart_10625 := by decide
  rcases family_descends (prefixWord ++ tailWord_10625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10700 : List Nat := [2, 2, 1, 4, 4, 1, 2, 2, 2]
def baseStart_10700 : Nat := 118140960795 + 10700 * 2 ^ 59
def prefixEnd_10700 : Nat := 4983230072969 + 3 ^ 40 * 10700 * 2
def baseEnd_10700 : Nat := 4883771558411884356265

theorem tailTrace_10700 : CollatzResearch.WordTrace tailWord_10700 prefixEnd_10700 4883771558411884356265 := by
  unfold tailWord_10700
  simp only [CollatzResearch.WordTrace]
  refine ⟨195130530621601129810777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 260174040828801506414369 195130530621601129810777)
  ·
    refine ⟨146347897966200847358083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195130530621601129810777 146347897966200847358083)
    ·
      refine ⟨219521846949301271037125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146347897966200847358083 219521846949301271037125)
      ·
        refine ⟨41160346302993988319461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219521846949301271037125 41160346302993988319461)
        ·
          refine ⟨7717564931811372809899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41160346302993988319461 7717564931811372809899)
          ·
            refine ⟨11576347397717059214849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7717564931811372809899 11576347397717059214849)
            ·
              refine ⟨8682260548287794411137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11576347397717059214849 8682260548287794411137)
              ·
                refine ⟨6511695411215845808353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8682260548287794411137 6511695411215845808353)
                ·
                  refine ⟨4883771558411884356265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511695411215845808353 4883771558411884356265)
                  ·
                    rfl

theorem cell20_10700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_10700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10700 prefixEnd_10700 := by exact prefixLift 10700
  have htrace : WordTrace (prefixWord ++ tailWord_10700) baseStart_10700 baseEnd_10700 := by
    simpa [prefixWord, tailWord_10700, baseEnd_10700] using wordTrace_append hprefix tailTrace_10700
  have hstable : (prefixWord ++ tailWord_10700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10700).length < 2 ^ (prefixWord ++ tailWord_10700).sum := by decide
  have hdescent : baseEnd_10700 < baseStart_10700 := by decide
  rcases family_descends (prefixWord ++ tailWord_10700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10725 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 4]
def baseStart_10725 : Nat := 118140960795 + 10725 * 2 ^ 59
def prefixEnd_10725 : Nat := 4983230072969 + 3 ^ 40 * 10725 * 2
def baseEnd_10725 : Nat := 4895182239622908522829

theorem tailTrace_10725 : CollatzResearch.WordTrace tailWord_10725 prefixEnd_10725 4895182239622908522829 := by
  unfold tailWord_10725
  simp only [CollatzResearch.WordTrace]
  refine ⟨391172886152631529281629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 260781924101754352854419 391172886152631529281629)
  ·
    refine ⟨146689832307236823480611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 391172886152631529281629 146689832307236823480611)
    ·
      refine ⟨220034748460855235220917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146689832307236823480611 220034748460855235220917)
      ·
        refine ⟨20628257668205178301961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220034748460855235220917 20628257668205178301961)
        ·
          refine ⟨15471193251153883726471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20628257668205178301961 15471193251153883726471)
          ·
            refine ⟨23206789876730825589707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15471193251153883726471 23206789876730825589707)
            ·
              refine ⟨34810184815096238384561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23206789876730825589707 34810184815096238384561)
              ·
                refine ⟨26107638611322178788421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34810184815096238384561 26107638611322178788421)
                ·
                  refine ⟨4895182239622908522829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26107638611322178788421 4895182239622908522829)
                  ·
                    rfl

theorem cell20_10725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_10725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10725 prefixEnd_10725 := by exact prefixLift 10725
  have htrace : WordTrace (prefixWord ++ tailWord_10725) baseStart_10725 baseEnd_10725 := by
    simpa [prefixWord, tailWord_10725, baseEnd_10725] using wordTrace_append hprefix tailTrace_10725
  have hstable : (prefixWord ++ tailWord_10725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10725).length < 2 ^ (prefixWord ++ tailWord_10725).sum := by decide
  have hdescent : baseEnd_10725 < baseStart_10725 := by decide
  rcases family_descends (prefixWord ++ tailWord_10725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10742 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_10742 : Nat := 118140960795 + 10742 * 2 ^ 59
def prefixEnd_10742 : Nat := 4983230072969 + 3 ^ 40 * 10742 * 2
def baseEnd_10742 : Nat := 4902941502846404956093

theorem tailTrace_10742 : CollatzResearch.WordTrace tailWord_10742 prefixEnd_10742 4902941502846404956093 := by
  unfold tailWord_10742
  simp only [CollatzResearch.WordTrace]
  refine ⟨24487057943190214540655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 261195284727362288433653 24487057943190214540655)
  ·
    refine ⟨36730586914785321810983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24487057943190214540655 36730586914785321810983)
    ·
      refine ⟨55095880372177982716475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36730586914785321810983 55095880372177982716475)
      ·
        refine ⟨82643820558266974074713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55095880372177982716475 82643820558266974074713)
        ·
          refine ⟨61982865418700230556035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82643820558266974074713 61982865418700230556035)
          ·
            refine ⟨92974298128050345834053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61982865418700230556035 92974298128050345834053)
            ·
              refine ⟨17432680899009439843885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92974298128050345834053 17432680899009439843885)
              ·
                refine ⟨6537255337128539941457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17432680899009439843885 6537255337128539941457)
                ·
                  refine ⟨4902941502846404956093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6537255337128539941457 4902941502846404956093)
                  ·
                    rfl

theorem cell20_10742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_10742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10742 prefixEnd_10742 := by exact prefixLift 10742
  have htrace : WordTrace (prefixWord ++ tailWord_10742) baseStart_10742 baseEnd_10742 := by
    simpa [prefixWord, tailWord_10742, baseEnd_10742] using wordTrace_append hprefix tailTrace_10742
  have hstable : (prefixWord ++ tailWord_10742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10742).length < 2 ^ (prefixWord ++ tailWord_10742).sum := by decide
  have hdescent : baseEnd_10742 < baseStart_10742 := by decide
  rcases family_descends (prefixWord ++ tailWord_10742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10753 : List Nat := [1, 2, 4, 1, 3, 2, 7]
def baseStart_10753 : Nat := 118140960795 + 10753 * 2 ^ 59
def prefixEnd_10753 : Nat := 4983230072969 + 3 ^ 40 * 10753 * 2
def baseEnd_10753 : Nat := 545329133619917287709

theorem tailTrace_10753 : CollatzResearch.WordTrace tailWord_10753 prefixEnd_10753 545329133619917287709 := by
  unfold tailWord_10753
  simp only [CollatzResearch.WordTrace]
  refine ⟨392194130051192311300913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261462753367461540867275 392194130051192311300913)
  ·
    refine ⟨294145597538394233475685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 392194130051192311300913 294145597538394233475685)
    ·
      refine ⟨55152299538448918776691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 294145597538394233475685 55152299538448918776691)
      ·
        refine ⟨82728449307673378165037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55152299538448918776691 82728449307673378165037)
        ·
          refine ⟨31023168490377516811889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82728449307673378165037 31023168490377516811889)
          ·
            refine ⟨23267376367783137608917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31023168490377516811889 23267376367783137608917)
            ·
              refine ⟨545329133619917287709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23267376367783137608917 545329133619917287709)
              ·
                rfl

theorem cell20_10753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_10753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10753 prefixEnd_10753 := by exact prefixLift 10753
  have htrace : WordTrace (prefixWord ++ tailWord_10753) baseStart_10753 baseEnd_10753 := by
    simpa [prefixWord, tailWord_10753, baseEnd_10753] using wordTrace_append hprefix tailTrace_10753
  have hstable : (prefixWord ++ tailWord_10753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10753).length < 2 ^ (prefixWord ++ tailWord_10753).sum := by decide
  have hdescent : baseEnd_10753 < baseStart_10753 := by decide
  rcases family_descends (prefixWord ++ tailWord_10753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10756 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_10756 : Nat := 118140960795 + 10756 * 2 ^ 59
def prefixEnd_10756 : Nat := 4983230072969 + 3 ^ 40 * 10756 * 2
def baseEnd_10756 : Nat := 4909331484324578489369

theorem tailTrace_10756 : CollatzResearch.WordTrace tailWord_10756 prefixEnd_10756 4909331484324578489369 := by
  unfold tailWord_10756
  simp only [CollatzResearch.WordTrace]
  refine ⟨196151774520161911830061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 261535699360215882440081 196151774520161911830061)
  ·
    refine ⟨73556915445060716936273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196151774520161911830061 73556915445060716936273)
    ·
      refine ⟨55167686583795537702205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73556915445060716936273 55167686583795537702205)
      ·
        refine ⟨20687882468923326638327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55167686583795537702205 20687882468923326638327)
        ·
          refine ⟨31031823703384989957491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20687882468923326638327 31031823703384989957491)
          ·
            refine ⟨46547735555077484936237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31031823703384989957491 46547735555077484936237)
            ·
              refine ⟨17455400833154056851089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46547735555077484936237 17455400833154056851089)
              ·
                refine ⟨13091550624865542638317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17455400833154056851089 13091550624865542638317)
                ·
                  refine ⟨4909331484324578489369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13091550624865542638317 4909331484324578489369)
                  ·
                    rfl

theorem cell20_10756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_10756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10756 prefixEnd_10756 := by exact prefixLift 10756
  have htrace : WordTrace (prefixWord ++ tailWord_10756) baseStart_10756 baseEnd_10756 := by
    simpa [prefixWord, tailWord_10756, baseEnd_10756] using wordTrace_append hprefix tailTrace_10756
  have hstable : (prefixWord ++ tailWord_10756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10756).length < 2 ^ (prefixWord ++ tailWord_10756).sum := by decide
  have hdescent : baseEnd_10756 < baseStart_10756 := by decide
  rcases family_descends (prefixWord ++ tailWord_10756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10763 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 2]
def baseStart_10763 : Nat := 118140960795 + 10763 * 2 ^ 59
def prefixEnd_10763 : Nat := 4983230072969 + 3 ^ 40 * 10763 * 2
def baseEnd_10763 : Nat := 4912526475063665256007

theorem tailTrace_10763 : CollatzResearch.WordTrace tailWord_10763 prefixEnd_10763 4912526475063665256007 := by
  unfold tailWord_10763
  simp only [CollatzResearch.WordTrace]
  refine ⟨392558860014964019164943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261705906676642679443295 392558860014964019164943)
  ·
    refine ⟨588838290022446028747415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392558860014964019164943 588838290022446028747415)
    ·
      refine ⟨883257435033669043121123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588838290022446028747415 883257435033669043121123)
      ·
        refine ⟨1324886152550503564681685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883257435033669043121123 1324886152550503564681685)
        ·
          refine ⟨31052019200402427297227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1324886152550503564681685 31052019200402427297227)
          ·
            refine ⟨46578028800603640945841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31052019200402427297227 46578028800603640945841)
            ·
              refine ⟨34933521600452730709381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46578028800603640945841 34933521600452730709381)
              ·
                refine ⟨6550035300084887008009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34933521600452730709381 6550035300084887008009)
                ·
                  refine ⟨4912526475063665256007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6550035300084887008009 4912526475063665256007)
                  ·
                    rfl

theorem cell20_10763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 2].length) (baseStart_10763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10763 prefixEnd_10763 := by exact prefixLift 10763
  have htrace : WordTrace (prefixWord ++ tailWord_10763) baseStart_10763 baseEnd_10763 := by
    simpa [prefixWord, tailWord_10763, baseEnd_10763] using wordTrace_append hprefix tailTrace_10763
  have hstable : (prefixWord ++ tailWord_10763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10763).length < 2 ^ (prefixWord ++ tailWord_10763).sum := by decide
  have hdescent : baseEnd_10763 < baseStart_10763 := by decide
  rcases family_descends (prefixWord ++ tailWord_10763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10767 : List Nat := [1, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_10767 : Nat := 118140960795 + 10767 * 2 ^ 59
def prefixEnd_10767 : Nat := 4983230072969 + 3 ^ 40 * 10767 * 2
def baseEnd_10767 : Nat := 4914352184057429122657

theorem tailTrace_10767 : CollatzResearch.WordTrace tailWord_10767 prefixEnd_10767 4914352184057429122657 := by
  unfold tailWord_10767
  simp only [CollatzResearch.WordTrace]
  refine ⟨392704752000472702310555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261803168000315134873703 392704752000472702310555)
  ·
    refine ⟨589057128000709053465833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392704752000472702310555 589057128000709053465833)
    ·
      refine ⟨441792846000531790099375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 589057128000709053465833 441792846000531790099375)
      ·
        refine ⟨662689269000797685149063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441792846000531790099375 662689269000797685149063)
        ·
          refine ⟨994033903501196527723595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662689269000797685149063 994033903501196527723595)
          ·
            refine ⟨1491050855251794791585393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994033903501196527723595 1491050855251794791585393)
            ·
              refine ⟨1118288141438846093689045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491050855251794791585393 1118288141438846093689045)
              ·
                refine ⟨26209878314972955320837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1118288141438846093689045 26209878314972955320837)
                ·
                  refine ⟨4914352184057429122657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26209878314972955320837 4914352184057429122657)
                  ·
                    rfl

theorem cell20_10767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_10767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10767 prefixEnd_10767 := by exact prefixLift 10767
  have htrace : WordTrace (prefixWord ++ tailWord_10767) baseStart_10767 baseEnd_10767 := by
    simpa [prefixWord, tailWord_10767, baseEnd_10767] using wordTrace_append hprefix tailTrace_10767
  have hstable : (prefixWord ++ tailWord_10767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10767).length < 2 ^ (prefixWord ++ tailWord_10767).sum := by decide
  have hdescent : baseEnd_10767 < baseStart_10767 := by decide
  rcases family_descends (prefixWord ++ tailWord_10767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10801 : List Nat := [1, 2, 2, 3, 1, 1, 5, 3, 2]
def baseStart_10801 : Nat := 118140960795 + 10801 * 2 ^ 59
def prefixEnd_10801 : Nat := 4983230072969 + 3 ^ 40 * 10801 * 2
def baseEnd_10801 : Nat := 4929870710504421989185

theorem tailTrace_10801 : CollatzResearch.WordTrace tailWord_10801 prefixEnd_10801 4929870710504421989185 := by
  unfold tailWord_10801
  simp only [CollatzResearch.WordTrace]
  refine ⟨393944833877296509048257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 262629889251531006032171 393944833877296509048257)
  ·
    refine ⟨295458625407972381786193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 393944833877296509048257 295458625407972381786193)
    ·
      refine ⟨221593969055979286339645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295458625407972381786193 221593969055979286339645)
      ·
        refine ⟨83097738395992232377367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221593969055979286339645 83097738395992232377367)
        ·
          refine ⟨124646607593988348566051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83097738395992232377367 124646607593988348566051)
          ·
            refine ⟨186969911390982522849077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124646607593988348566051 186969911390982522849077)
            ·
              refine ⟨17528429192904611517101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 186969911390982522849077 17528429192904611517101)
              ·
                refine ⟨6573160947339229318913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17528429192904611517101 6573160947339229318913)
                ·
                  refine ⟨4929870710504421989185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6573160947339229318913 4929870710504421989185)
                  ·
                    rfl

theorem cell20_10801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_10801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10801 prefixEnd_10801 := by exact prefixLift 10801
  have htrace : WordTrace (prefixWord ++ tailWord_10801) baseStart_10801 baseEnd_10801 := by
    simpa [prefixWord, tailWord_10801, baseEnd_10801] using wordTrace_append hprefix tailTrace_10801
  have hstable : (prefixWord ++ tailWord_10801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10801).length < 2 ^ (prefixWord ++ tailWord_10801).sum := by decide
  have hdescent : baseEnd_10801 < baseStart_10801 := by decide
  rcases family_descends (prefixWord ++ tailWord_10801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10804 : List Nat := [2, 5, 1, 3, 2, 1, 6]
def baseStart_10804 : Nat := 118140960795 + 10804 * 2 ^ 59
def prefixEnd_10804 : Nat := 4983230072969 + 3 ^ 40 * 10804 * 2
def baseEnd_10804 : Nat := 547915554694416098797

theorem tailTrace_10804 : CollatzResearch.WordTrace tailWord_10804 prefixEnd_10804 547915554694416098797 := by
  unfold tailWord_10804
  simp only [CollatzResearch.WordTrace]
  refine ⟨197027126433214010703733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 262702835244285347604977 197027126433214010703733)
  ·
    refine ⟨18471293103113813503475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197027126433214010703733 18471293103113813503475)
    ·
      refine ⟨27706939654670720255213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18471293103113813503475 27706939654670720255213)
      ·
        refine ⟨10390102370501520095705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27706939654670720255213 10390102370501520095705)
        ·
          refine ⟨7792576777876140071779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10390102370501520095705 7792576777876140071779)
          ·
            refine ⟨11688865166814210107669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7792576777876140071779 11688865166814210107669)
            ·
              refine ⟨547915554694416098797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11688865166814210107669 547915554694416098797)
              ·
                rfl

theorem cell20_10804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 6].length) (baseStart_10804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10804 prefixEnd_10804 := by exact prefixLift 10804
  have htrace : WordTrace (prefixWord ++ tailWord_10804) baseStart_10804 baseEnd_10804 := by
    simpa [prefixWord, tailWord_10804, baseEnd_10804] using wordTrace_append hprefix tailTrace_10804
  have hstable : (prefixWord ++ tailWord_10804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10804).length < 2 ^ (prefixWord ++ tailWord_10804).sum := by decide
  have hdescent : baseEnd_10804 < baseStart_10804 := by decide
  rcases family_descends (prefixWord ++ tailWord_10804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10814 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_10814 : Nat := 118140960795 + 10814 * 2 ^ 59
def prefixEnd_10814 : Nat := 4983230072969 + 3 ^ 40 * 10814 * 2
def baseEnd_10814 : Nat := 4935804264734154555799

theorem tailTrace_10814 : CollatzResearch.WordTrace tailWord_10814 prefixEnd_10814 4935804264734154555799 := by
  unfold tailWord_10814
  simp only [CollatzResearch.WordTrace]
  refine ⟨49302372853774966158937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 262945988553466486180997 49302372853774966158937)
  ·
    refine ⟨36976779640331224619203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49302372853774966158937 36976779640331224619203)
    ·
      refine ⟨55465169460496836928805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36976779640331224619203 55465169460496836928805)
      ·
        refine ⟨10399719273843156924151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55465169460496836928805 10399719273843156924151)
        ·
          refine ⟨15599578910764735386227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399719273843156924151 15599578910764735386227)
          ·
            refine ⟨23399368366147103079341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15599578910764735386227 23399368366147103079341)
            ·
              refine ⟨8774763137305163654753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23399368366147103079341 8774763137305163654753)
              ·
                refine ⟨6581072352978872741065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8774763137305163654753 6581072352978872741065)
                ·
                  refine ⟨4935804264734154555799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581072352978872741065 4935804264734154555799)
                  ·
                    rfl

theorem cell20_10814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_10814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10814 prefixEnd_10814 := by exact prefixLift 10814
  have htrace : WordTrace (prefixWord ++ tailWord_10814) baseStart_10814 baseEnd_10814 := by
    simpa [prefixWord, tailWord_10814, baseEnd_10814] using wordTrace_append hprefix tailTrace_10814
  have hstable : (prefixWord ++ tailWord_10814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10814).length < 2 ^ (prefixWord ++ tailWord_10814).sum := by decide
  have hdescent : baseEnd_10814 < baseStart_10814 := by decide
  rcases family_descends (prefixWord ++ tailWord_10814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10884 : List Nat := [2, 3, 2, 1, 3, 3, 1, 5]
def baseStart_10884 : Nat := 118140960795 + 10884 * 2 ^ 59
def prefixEnd_10884 : Nat := 4983230072969 + 3 ^ 40 * 10884 * 2
def baseEnd_10884 : Nat := 1655918057375007407393

theorem tailTrace_10884 : CollatzResearch.WordTrace tailWord_10884 prefixEnd_10884 1655918057375007407393 := by
  unfold tailWord_10884
  simp only [CollatzResearch.WordTrace]
  refine ⟨198486046288300842159853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 264648061717734456213137 198486046288300842159853)
  ·
    refine ⟨74432267358112815809945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198486046288300842159853 74432267358112815809945)
    ·
      refine ⟨55824200518584611857459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74432267358112815809945 55824200518584611857459)
      ·
        refine ⟨83736300777876917786189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55824200518584611857459 83736300777876917786189)
        ·
          refine ⟨31401112791703844169821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83736300777876917786189 31401112791703844169821)
          ·
            refine ⟨11775417296888941563683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31401112791703844169821 11775417296888941563683)
            ·
              refine ⟨17663125945333412345525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11775417296888941563683 17663125945333412345525)
              ·
                refine ⟨1655918057375007407393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17663125945333412345525 1655918057375007407393)
                ·
                  rfl

theorem cell20_10884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_10884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10884 prefixEnd_10884 := by exact prefixLift 10884
  have htrace : WordTrace (prefixWord ++ tailWord_10884) baseStart_10884 baseEnd_10884 := by
    simpa [prefixWord, tailWord_10884, baseEnd_10884] using wordTrace_append hprefix tailTrace_10884
  have hstable : (prefixWord ++ tailWord_10884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10884).length < 2 ^ (prefixWord ++ tailWord_10884).sum := by decide
  have hdescent : baseEnd_10884 < baseStart_10884 := by decide
  rcases family_descends (prefixWord ++ tailWord_10884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10898 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_10898 : Nat := 118140960795 + 10898 * 2 ^ 59
def prefixEnd_10898 : Nat := 4983230072969 + 3 ^ 40 * 10898 * 2
def baseEnd_10898 : Nat := 4974144153603195755455

theorem tailTrace_10898 : CollatzResearch.WordTrace tailWord_10898 prefixEnd_10898 4974144153603195755455 := by
  unfold tailWord_10898
  simp only [CollatzResearch.WordTrace]
  refine ⟨99370678631470518832337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 264988476350588050219565 99370678631470518832337)
  ·
    refine ⟨74528008973602889124253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99370678631470518832337 74528008973602889124253)
    ·
      refine ⟨27948003365101083421595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74528008973602889124253 27948003365101083421595)
      ·
        refine ⟨41922005047651625132393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27948003365101083421595 41922005047651625132393)
        ·
          refine ⟨31441503785738718849295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41922005047651625132393 31441503785738718849295)
          ·
            refine ⟨47162255678608078273943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31441503785738718849295 47162255678608078273943)
            ·
              refine ⟨70743383517912117410915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47162255678608078273943 70743383517912117410915)
              ·
                refine ⟨106115075276868176116373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70743383517912117410915 106115075276868176116373)
                ·
                  refine ⟨4974144153603195755455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106115075276868176116373 4974144153603195755455)
                  ·
                    rfl

theorem cell20_10898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_10898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10898 prefixEnd_10898 := by exact prefixLift 10898
  have htrace : WordTrace (prefixWord ++ tailWord_10898) baseStart_10898 baseEnd_10898 := by
    simpa [prefixWord, tailWord_10898, baseEnd_10898] using wordTrace_append hprefix tailTrace_10898
  have hstable : (prefixWord ++ tailWord_10898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10898).length < 2 ^ (prefixWord ++ tailWord_10898).sum := by decide
  have hdescent : baseEnd_10898 < baseStart_10898 := by decide
  rcases family_descends (prefixWord ++ tailWord_10898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10905 : List Nat := [1, 2, 1, 2, 1, 2, 7, 4]
def baseStart_10905 : Nat := 118140960795 + 10905 * 2 ^ 59
def prefixEnd_10905 : Nat := 4983230072969 + 3 ^ 40 * 10905 * 2
def baseEnd_10905 : Nat := 1659113048114094174031

theorem tailTrace_10905 : CollatzResearch.WordTrace tailWord_10905 prefixEnd_10905 1659113048114094174031 := by
  unfold tailWord_10905
  simp only [CollatzResearch.WordTrace]
  refine ⟨397738025500522270834169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 265158683667014847222779 397738025500522270834169)
  ·
    refine ⟨298303519125391703125627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 397738025500522270834169 298303519125391703125627)
    ·
      refine ⟨447455278688087554688441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298303519125391703125627 447455278688087554688441)
      ·
        refine ⟨335591459016065666016331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447455278688087554688441 335591459016065666016331)
        ·
          refine ⟨503387188524098499024497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335591459016065666016331 503387188524098499024497)
          ·
            refine ⟨377540391393073874268373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503387188524098499024497 377540391393073874268373)
            ·
              refine ⟨8848602923275168928165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 377540391393073874268373 8848602923275168928165)
              ·
                refine ⟨1659113048114094174031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8848602923275168928165 1659113048114094174031)
                ·
                  rfl

theorem cell20_10905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 4].length) (baseStart_10905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10905 prefixEnd_10905 := by exact prefixLift 10905
  have htrace : WordTrace (prefixWord ++ tailWord_10905) baseStart_10905 baseEnd_10905 := by
    simpa [prefixWord, tailWord_10905, baseEnd_10905] using wordTrace_append hprefix tailTrace_10905
  have hstable : (prefixWord ++ tailWord_10905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10905).length < 2 ^ (prefixWord ++ tailWord_10905).sum := by decide
  have hdescent : baseEnd_10905 < baseStart_10905 := by decide
  rcases family_descends (prefixWord ++ tailWord_10905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10981 : List Nat := [1, 3, 1, 4, 1, 4, 6]
def baseStart_10981 : Nat := 118140960795 + 10981 * 2 ^ 59
def prefixEnd_10981 : Nat := 4983230072969 + 3 ^ 40 * 10981 * 2
def baseEnd_10981 : Nat := 556891957247088443161

theorem tailTrace_10981 : CollatzResearch.WordTrace tailWord_10981 prefixEnd_10981 556891957247088443161 := by
  unfold tailWord_10981
  simp only [CollatzResearch.WordTrace]
  refine ⟨400509973225187250600797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 267006648816791500400531 400509973225187250600797)
  ·
    refine ⟨150191239959445218975299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 400509973225187250600797 150191239959445218975299)
    ·
      refine ⟨225286859939167828462949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150191239959445218975299 225286859939167828462949)
      ·
        refine ⟨42241286238593967836803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 225286859939167828462949 42241286238593967836803)
        ·
          refine ⟨63361929357890951755205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42241286238593967836803 63361929357890951755205)
          ·
            refine ⟨11880361754604553454101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63361929357890951755205 11880361754604553454101)
            ·
              refine ⟨556891957247088443161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11880361754604553454101 556891957247088443161)
              ·
                rfl

theorem cell20_10981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 6].length) (baseStart_10981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10981 prefixEnd_10981 := by exact prefixLift 10981
  have htrace : WordTrace (prefixWord ++ tailWord_10981) baseStart_10981 baseEnd_10981 := by
    simpa [prefixWord, tailWord_10981, baseEnd_10981] using wordTrace_append hprefix tailTrace_10981
  have hstable : (prefixWord ++ tailWord_10981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10981).length < 2 ^ (prefixWord ++ tailWord_10981).sum := by decide
  have hdescent : baseEnd_10981 < baseStart_10981 := by decide
  rcases family_descends (prefixWord ++ tailWord_10981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10988 : List Nat := [2, 2, 1, 1, 2, 2, 1, 6, 3]
def baseStart_10988 : Nat := 118140960795 + 10988 * 2 ^ 59
def prefixEnd_10988 : Nat := 4983230072969 + 3 ^ 40 * 10988 * 2
def baseEnd_10988 : Nat := 5015222605962882755087

theorem tailTrace_10988 : CollatzResearch.WordTrace tailWord_10988 prefixEnd_10988 5015222605962882755087 := by
  unfold tailWord_10988
  simp only [CollatzResearch.WordTrace]
  refine ⟨200382642099913723052809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 267176856133218297403745 200382642099913723052809)
  ·
    refine ⟨150286981574935292289607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200382642099913723052809 150286981574935292289607)
    ·
      refine ⟨225430472362402938434411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150286981574935292289607 225430472362402938434411)
      ·
        refine ⟨338145708543604407651617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225430472362402938434411 338145708543604407651617)
        ·
          refine ⟨253609281407703305738713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338145708543604407651617 253609281407703305738713)
          ·
            refine ⟨190206961055777479304035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253609281407703305738713 190206961055777479304035)
            ·
              refine ⟨285310441583666218956053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190206961055777479304035 285310441583666218956053)
              ·
                refine ⟨13373926949234354013565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 285310441583666218956053 13373926949234354013565)
                ·
                  refine ⟨5015222605962882755087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13373926949234354013565 5015222605962882755087)
                  ·
                    rfl

theorem cell20_10988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_10988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10988 prefixEnd_10988 := by exact prefixLift 10988
  have htrace : WordTrace (prefixWord ++ tailWord_10988) baseStart_10988 baseEnd_10988 := by
    simpa [prefixWord, tailWord_10988, baseEnd_10988] using wordTrace_append hprefix tailTrace_10988
  have hstable : (prefixWord ++ tailWord_10988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10988).length < 2 ^ (prefixWord ++ tailWord_10988).sum := by decide
  have hdescent : baseEnd_10988 < baseStart_10988 := by decide
  rcases family_descends (prefixWord ++ tailWord_10988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10997 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 3]
def baseStart_10997 : Nat := 118140960795 + 10997 * 2 ^ 59
def prefixEnd_10997 : Nat := 4983230072969 + 3 ^ 40 * 10997 * 2
def baseEnd_10997 : Nat := 5019330451198851455051

theorem tailTrace_10997 : CollatzResearch.WordTrace tailWord_10997 prefixEnd_10997 5019330451198851455051 := by
  unfold tailWord_10997
  simp only [CollatzResearch.WordTrace]
  refine ⟨401093541167221983183245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 267395694111481322122163 401093541167221983183245)
  ·
    refine ⟨150410077937708243693717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 401093541167221983183245 150410077937708243693717)
    ·
      refine ⟨7050472403330073923143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 150410077937708243693717 7050472403330073923143)
      ·
        refine ⟨10575708604995110884715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050472403330073923143 10575708604995110884715)
        ·
          refine ⟨15863562907492666327073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10575708604995110884715 15863562907492666327073)
          ·
            refine ⟨11897672180619499745305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15863562907492666327073 11897672180619499745305)
            ·
              refine ⟨8923254135464624808979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11897672180619499745305 8923254135464624808979)
              ·
                refine ⟨13384881203196937213469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8923254135464624808979 13384881203196937213469)
                ·
                  refine ⟨5019330451198851455051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13384881203196937213469 5019330451198851455051)
                  ·
                    rfl

theorem cell20_10997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_10997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_10997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_10997 prefixEnd_10997 := by exact prefixLift 10997
  have htrace : WordTrace (prefixWord ++ tailWord_10997) baseStart_10997 baseEnd_10997 := by
    simpa [prefixWord, tailWord_10997, baseEnd_10997] using wordTrace_append hprefix tailTrace_10997
  have hstable : (prefixWord ++ tailWord_10997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10997).length < 2 ^ (prefixWord ++ tailWord_10997).sum := by decide
  have hdescent : baseEnd_10997 < baseStart_10997 := by decide
  rcases family_descends (prefixWord ++ tailWord_10997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11002 : List Nat := [3, 1, 1, 1, 1, 3, 3, 7]
def baseStart_11002 : Nat := 118140960795 + 11002 * 2 ^ 59
def prefixEnd_11002 : Nat := 4983230072969 + 3 ^ 40 * 11002 * 2
def baseEnd_11002 : Nat := 1673870862480352096121

theorem tailTrace_11002 : CollatzResearch.WordTrace tailWord_11002 prefixEnd_11002 1673870862480352096121 := by
  unfold tailWord_11002
  simp only [CollatzResearch.WordTrace]
  refine ⟨100318976537276959278815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 267517270766071891410173 100318976537276959278815)
  ·
    refine ⟨150478464805915438918223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100318976537276959278815 150478464805915438918223)
    ·
      refine ⟨225717697208873158377335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150478464805915438918223 225717697208873158377335)
      ·
        refine ⟨338576545813309737566003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225717697208873158377335 338576545813309737566003)
        ·
          refine ⟨507864818719964606349005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338576545813309737566003 507864818719964606349005)
          ·
            refine ⟨190449307019986727380877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507864818719964606349005 190449307019986727380877)
            ·
              refine ⟨71418490132495022767829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190449307019986727380877 71418490132495022767829)
              ·
                refine ⟨1673870862480352096121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71418490132495022767829 1673870862480352096121)
                ·
                  rfl

theorem cell20_11002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_11002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11002 prefixEnd_11002 := by exact prefixLift 11002
  have htrace : WordTrace (prefixWord ++ tailWord_11002) baseStart_11002 baseEnd_11002 := by
    simpa [prefixWord, tailWord_11002, baseEnd_11002] using wordTrace_append hprefix tailTrace_11002
  have hstable : (prefixWord ++ tailWord_11002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11002).length < 2 ^ (prefixWord ++ tailWord_11002).sum := by decide
  have hdescent : baseEnd_11002 < baseStart_11002 := by decide
  rcases family_descends (prefixWord ++ tailWord_11002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11040 : List Nat := [2, 1, 1, 5, 1, 10]
def baseStart_11040 : Nat := 118140960795 + 11040 * 2 ^ 59
def prefixEnd_11040 : Nat := 4983230072969 + 3 ^ 40 * 11040 * 2
def baseEnd_11040 : Nat := 186628030477104185983

theorem tailTrace_11040 : CollatzResearch.WordTrace tailWord_11040 prefixEnd_11040 186628030477104185983 := by
  unfold tailWord_11040
  simp only [CollatzResearch.WordTrace]
  refine ⟨201330940005720163499287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 268441253340960217999049 201330940005720163499287)
  ·
    refine ⟨301996410008580245248931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201330940005720163499287 301996410008580245248931)
    ·
      refine ⟨452994615012870367873397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301996410008580245248931 452994615012870367873397)
      ·
        refine ⟨42468245157456596988131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 452994615012870367873397 42468245157456596988131)
        ·
          refine ⟨63702367736184895482197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42468245157456596988131 63702367736184895482197)
          ·
            refine ⟨186628030477104185983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 63702367736184895482197 186628030477104185983)
            ·
              rfl

theorem cell20_11040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 10].length) (baseStart_11040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11040 prefixEnd_11040 := by exact prefixLift 11040
  have htrace : WordTrace (prefixWord ++ tailWord_11040) baseStart_11040 baseEnd_11040 := by
    simpa [prefixWord, tailWord_11040, baseEnd_11040] using wordTrace_append hprefix tailTrace_11040
  have hstable : (prefixWord ++ tailWord_11040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11040).length < 2 ^ (prefixWord ++ tailWord_11040).sum := by decide
  have hdescent : baseEnd_11040 < baseStart_11040 := by decide
  rcases family_descends (prefixWord ++ tailWord_11040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11064 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_11064 : Nat := 118140960795 + 11064 * 2 ^ 59
def prefixEnd_11064 : Nat := 4983230072969 + 3 ^ 40 * 11064 * 2
def baseEnd_11064 : Nat := 5049911076844396221443

theorem tailTrace_11064 : CollatzResearch.WordTrace tailWord_11064 prefixEnd_11064 5049911076844396221443 := by
  unfold tailWord_11064
  simp only [CollatzResearch.WordTrace]
  refine ⟨201768615962246212936123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 269024821282994950581497 201768615962246212936123)
  ·
    refine ⟨302652923943369319404185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201768615962246212936123 302652923943369319404185)
    ·
      refine ⟨226989692957526989553139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302652923943369319404185 226989692957526989553139)
      ·
        refine ⟨340484539436290484329709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226989692957526989553139 340484539436290484329709)
        ·
          refine ⟨127681702288608931623641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 340484539436290484329709 127681702288608931623641)
          ·
            refine ⟨95761276716456698717731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127681702288608931623641 95761276716456698717731)
            ·
              refine ⟨143641915074685048076597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95761276716456698717731 143641915074685048076597)
              ·
                refine ⟨13466429538251723257181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143641915074685048076597 13466429538251723257181)
                ·
                  refine ⟨5049911076844396221443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13466429538251723257181 5049911076844396221443)
                  ·
                    rfl

theorem cell20_11064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_11064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11064 prefixEnd_11064 := by exact prefixLift 11064
  have htrace : WordTrace (prefixWord ++ tailWord_11064) baseStart_11064 baseEnd_11064 := by
    simpa [prefixWord, tailWord_11064, baseEnd_11064] using wordTrace_append hprefix tailTrace_11064
  have hstable : (prefixWord ++ tailWord_11064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11064).length < 2 ^ (prefixWord ++ tailWord_11064).sum := by decide
  have hdescent : baseEnd_11064 < baseStart_11064 := by decide
  rcases family_descends (prefixWord ++ tailWord_11064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11071 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_11071 : Nat := 118140960795 + 11071 * 2 ^ 59
def prefixEnd_11071 : Nat := 4983230072969 + 3 ^ 40 * 11071 * 2
def baseEnd_11071 : Nat := 5053106067583482988081

theorem tailTrace_11071 : CollatzResearch.WordTrace tailWord_11071 prefixEnd_11071 5053106067583482988081 := by
  unfold tailWord_11071
  simp only [CollatzResearch.WordTrace]
  refine ⟨403792542899132621377067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 269195028599421747584711 403792542899132621377067)
  ·
    refine ⟨605688814348698932065601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 403792542899132621377067 605688814348698932065601)
    ·
      refine ⟨454266610761524199049201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 605688814348698932065601 454266610761524199049201)
      ·
        refine ⟨340699958071143149286901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454266610761524199049201 340699958071143149286901)
        ·
          refine ⟨31940621069169670245647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 340699958071143149286901 31940621069169670245647)
          ·
            refine ⟨47910931603754505368471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31940621069169670245647 47910931603754505368471)
            ·
              refine ⟨71866397405631758052707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47910931603754505368471 71866397405631758052707)
              ·
                refine ⟨107799596108447637079061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71866397405631758052707 107799596108447637079061)
                ·
                  refine ⟨5053106067583482988081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107799596108447637079061 5053106067583482988081)
                  ·
                    rfl

theorem cell20_11071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_11071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11071 prefixEnd_11071 := by exact prefixLift 11071
  have htrace : WordTrace (prefixWord ++ tailWord_11071) baseStart_11071 baseEnd_11071 := by
    simpa [prefixWord, tailWord_11071, baseEnd_11071] using wordTrace_append hprefix tailTrace_11071
  have hstable : (prefixWord ++ tailWord_11071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11071).length < 2 ^ (prefixWord ++ tailWord_11071).sum := by decide
  have hdescent : baseEnd_11071 < baseStart_11071 := by decide
  rcases family_descends (prefixWord ++ tailWord_11071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11088 : List Nat := [2, 1, 1, 1, 1, 4, 3, 5, 2]
def baseStart_11088 : Nat := 118140960795 + 11088 * 2 ^ 59
def prefixEnd_11088 : Nat := 4983230072969 + 3 ^ 40 * 11088 * 2
def baseEnd_11088 : Nat := 5060865330806979421345

theorem tailTrace_11088 : CollatzResearch.WordTrace tailWord_11088 prefixEnd_11088 5060865330806979421345 := by
  unfold tailWord_11088
  simp only [CollatzResearch.WordTrace]
  refine ⟨202206291918772262372959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 269608389225029683163945 202206291918772262372959)
  ·
    refine ⟨303309437878158393559439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202206291918772262372959 303309437878158393559439)
    ·
      refine ⟨454964156817237590339159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303309437878158393559439 454964156817237590339159)
      ·
        refine ⟨682446235225856385508739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454964156817237590339159 682446235225856385508739)
        ·
          refine ⟨1023669352838784578263109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682446235225856385508739 1023669352838784578263109)
          ·
            refine ⟨191938003657272108424333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1023669352838784578263109 191938003657272108424333)
            ·
              refine ⟨71976751371477040659125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191938003657272108424333 71976751371477040659125)
              ·
                refine ⟨6747820441075972561793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71976751371477040659125 6747820441075972561793)
                ·
                  refine ⟨5060865330806979421345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6747820441075972561793 5060865330806979421345)
                  ·
                    rfl

theorem cell20_11088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_11088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11088 prefixEnd_11088 := by exact prefixLift 11088
  have htrace : WordTrace (prefixWord ++ tailWord_11088) baseStart_11088 baseEnd_11088 := by
    simpa [prefixWord, tailWord_11088, baseEnd_11088] using wordTrace_append hprefix tailTrace_11088
  have hstable : (prefixWord ++ tailWord_11088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11088).length < 2 ^ (prefixWord ++ tailWord_11088).sum := by decide
  have hdescent : baseEnd_11088 < baseStart_11088 := by decide
  rcases family_descends (prefixWord ++ tailWord_11088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11109 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_11109 : Nat := 118140960795 + 11109 * 2 ^ 59
def prefixEnd_11109 : Nat := 4983230072969 + 3 ^ 40 * 11109 * 2
def baseEnd_11109 : Nat := 5070450303024239721259

theorem tailTrace_11109 : CollatzResearch.WordTrace tailWord_11109 prefixEnd_11109 5070450303024239721259 := by
  unfold tailWord_11109
  simp only [CollatzResearch.WordTrace]
  refine ⟨405178516761465111260381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 270119011174310074173587 405178516761465111260381)
  ·
    refine ⟨151941943785549416722643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 405178516761465111260381 151941943785549416722643)
    ·
      refine ⟨227912915678324125083965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151941943785549416722643 227912915678324125083965)
      ·
        refine ⟨85467343379371546906487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227912915678324125083965 85467343379371546906487)
        ·
          refine ⟨128201015069057320359731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85467343379371546906487 128201015069057320359731)
          ·
            refine ⟨192301522603585980539597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128201015069057320359731 192301522603585980539597)
            ·
              refine ⟨72113070976344742702349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192301522603585980539597 72113070976344742702349)
              ·
                refine ⟨27042401616129278513381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72113070976344742702349 27042401616129278513381)
                ·
                  refine ⟨5070450303024239721259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27042401616129278513381 5070450303024239721259)
                  ·
                    rfl

theorem cell20_11109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_11109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11109 prefixEnd_11109 := by exact prefixLift 11109
  have htrace : WordTrace (prefixWord ++ tailWord_11109) baseStart_11109 baseEnd_11109 := by
    simpa [prefixWord, tailWord_11109, baseEnd_11109] using wordTrace_append hprefix tailTrace_11109
  have hstable : (prefixWord ++ tailWord_11109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11109).length < 2 ^ (prefixWord ++ tailWord_11109).sum := by decide
  have hdescent : baseEnd_11109 < baseStart_11109 := by decide
  rcases family_descends (prefixWord ++ tailWord_11109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11116 : List Nat := [2, 2, 1, 1, 4, 1, 2, 7]
def baseStart_11116 : Nat := 118140960795 + 11116 * 2 ^ 59
def prefixEnd_11116 : Nat := 4983230072969 + 3 ^ 40 * 11116 * 2
def baseEnd_11116 : Nat := 1691215097921108829299

theorem tailTrace_11116 : CollatzResearch.WordTrace tailWord_11116 prefixEnd_11116 1691215097921108829299 := by
  unfold tailWord_11116
  simp only [CollatzResearch.WordTrace]
  refine ⟨202716913868052653382601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 270289218490736871176801 202716913868052653382601)
  ·
    refine ⟨152037685401039490036951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 202716913868052653382601 152037685401039490036951)
    ·
      refine ⟨228056528101559235055427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152037685401039490036951 228056528101559235055427)
      ·
        refine ⟨342084792152338852583141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228056528101559235055427 342084792152338852583141)
        ·
          refine ⟨64140898528563534859339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 342084792152338852583141 64140898528563534859339)
          ·
            refine ⟨96211347792845302289009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64140898528563534859339 96211347792845302289009)
            ·
              refine ⟨72158510844633976716757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96211347792845302289009 72158510844633976716757)
              ·
                refine ⟨1691215097921108829299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72158510844633976716757 1691215097921108829299)
                ·
                  rfl

theorem cell20_11116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_11116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11116 prefixEnd_11116 := by exact prefixLift 11116
  have htrace : WordTrace (prefixWord ++ tailWord_11116) baseStart_11116 baseEnd_11116 := by
    simpa [prefixWord, tailWord_11116, baseEnd_11116] using wordTrace_append hprefix tailTrace_11116
  have hstable : (prefixWord ++ tailWord_11116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11116).length < 2 ^ (prefixWord ++ tailWord_11116).sum := by decide
  have hdescent : baseEnd_11116 < baseStart_11116 := by decide
  rcases family_descends (prefixWord ++ tailWord_11116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11133 : List Nat := [1, 4, 1, 1, 2, 1, 6, 4]
def baseStart_11133 : Nat := 118140960795 + 11133 * 2 ^ 59
def prefixEnd_11133 : Nat := 4983230072969 + 3 ^ 40 * 11133 * 2
def baseEnd_11133 : Nat := 1693801518995607640387

theorem tailTrace_11133 : CollatzResearch.WordTrace tailWord_11133 prefixEnd_11133 1693801518995607640387 := by
  unfold tailWord_11133
  simp only [CollatzResearch.WordTrace]
  refine ⟨406053868674517210134053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 270702579116344806756035 406053868674517210134053)
  ·
    refine ⟨76135100376471976900135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 406053868674517210134053 76135100376471976900135)
    ·
      refine ⟨114202650564707965350203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76135100376471976900135 114202650564707965350203)
      ·
        refine ⟨171303975847061948025305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114202650564707965350203 171303975847061948025305)
        ·
          refine ⟨128477981885296461018979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171303975847061948025305 128477981885296461018979)
          ·
            refine ⟨192716972827944691528469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128477981885296461018979 192716972827944691528469)
            ·
              refine ⟨9033608101309907415397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 192716972827944691528469 9033608101309907415397)
              ·
                refine ⟨1693801518995607640387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9033608101309907415397 1693801518995607640387)
                ·
                  rfl

theorem cell20_11133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 4].length) (baseStart_11133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11133 prefixEnd_11133 := by exact prefixLift 11133
  have htrace : WordTrace (prefixWord ++ tailWord_11133) baseStart_11133 baseEnd_11133 := by
    simpa [prefixWord, tailWord_11133, baseEnd_11133] using wordTrace_append hprefix tailTrace_11133
  have hstable : (prefixWord ++ tailWord_11133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11133).length < 2 ^ (prefixWord ++ tailWord_11133).sum := by decide
  have hdescent : baseEnd_11133 < baseStart_11133 := by decide
  rcases family_descends (prefixWord ++ tailWord_11133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11143 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 2]
def baseStart_11143 : Nat := 118140960795 + 11143 * 2 ^ 59
def prefixEnd_11143 : Nat := 4983230072969 + 3 ^ 40 * 11143 * 2
def baseEnd_11143 : Nat := 5085968829471232587787

theorem tailTrace_11143 : CollatzResearch.WordTrace tailWord_11143 prefixEnd_11143 5085968829471232587787 := by
  unfold tailWord_11143
  simp only [CollatzResearch.WordTrace]
  refine ⟨406418598638288917998083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 270945732425525945332055 406418598638288917998083)
  ·
    refine ⟨609627897957433376997125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 406418598638288917998083 609627897957433376997125)
    ·
      refine ⟨114305230867018758186961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 609627897957433376997125 114305230867018758186961)
      ·
        refine ⟨85728923150264068640221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114305230867018758186961 85728923150264068640221)
        ·
          refine ⟨32148346181349025740083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85728923150264068640221 32148346181349025740083)
          ·
            refine ⟨48222519272023538610125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32148346181349025740083 48222519272023538610125)
            ·
              refine ⟨18083444727008826978797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48222519272023538610125 18083444727008826978797)
              ·
                refine ⟨6781291772628310117049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18083444727008826978797 6781291772628310117049)
                ·
                  refine ⟨5085968829471232587787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6781291772628310117049 5085968829471232587787)
                  ·
                    rfl

theorem cell20_11143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 2].length) (baseStart_11143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11143 prefixEnd_11143 := by exact prefixLift 11143
  have htrace : WordTrace (prefixWord ++ tailWord_11143) baseStart_11143 baseEnd_11143 := by
    simpa [prefixWord, tailWord_11143, baseEnd_11143] using wordTrace_append hprefix tailTrace_11143
  have hstable : (prefixWord ++ tailWord_11143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11143).length < 2 ^ (prefixWord ++ tailWord_11143).sum := by decide
  have hdescent : baseEnd_11143 < baseStart_11143 := by decide
  rcases family_descends (prefixWord ++ tailWord_11143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11188 : List Nat := [2, 5, 2, 1, 1, 1, 2, 6]
def baseStart_11188 : Nat := 118140960795 + 11188 * 2 ^ 59
def prefixEnd_11188 : Nat := 4983230072969 + 3 ^ 40 * 11188 * 2
def baseEnd_11188 : Nat := 1702169351883692029201

theorem tailTrace_11188 : CollatzResearch.WordTrace tailWord_11188 prefixEnd_11188 1702169351883692029201 := by
  unfold tailWord_11188
  simp only [CollatzResearch.WordTrace]
  refine ⟨204029941737630801693109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 272039922316841068924145 204029941737630801693109)
  ·
    refine ⟨19127807037902887658729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204029941737630801693109 19127807037902887658729)
    ·
      refine ⟨14345855278427165744047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19127807037902887658729 14345855278427165744047)
      ·
        refine ⟨21518782917640748616071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14345855278427165744047 21518782917640748616071)
        ·
          refine ⟨32278174376461122924107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21518782917640748616071 32278174376461122924107)
          ·
            refine ⟨48417261564691684386161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32278174376461122924107 48417261564691684386161)
            ·
              refine ⟨36312946173518763289621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48417261564691684386161 36312946173518763289621)
              ·
                refine ⟨1702169351883692029201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36312946173518763289621 1702169351883692029201)
                ·
                  rfl

theorem cell20_11188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_11188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11188 prefixEnd_11188 := by exact prefixLift 11188
  have htrace : WordTrace (prefixWord ++ tailWord_11188) baseStart_11188 baseEnd_11188 := by
    simpa [prefixWord, tailWord_11188, baseEnd_11188] using wordTrace_append hprefix tailTrace_11188
  have hstable : (prefixWord ++ tailWord_11188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11188).length < 2 ^ (prefixWord ++ tailWord_11188).sum := by decide
  have hdescent : baseEnd_11188 < baseStart_11188 := by decide
  rcases family_descends (prefixWord ++ tailWord_11188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11192 : List Nat := [2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_11192 : Nat := 118140960795 + 11192 * 2 ^ 59
def prefixEnd_11192 : Nat := 4983230072969 + 3 ^ 40 * 11192 * 2
def baseEnd_11192 : Nat := 1702777921548279984751

theorem tailTrace_11192 : CollatzResearch.WordTrace tailWord_11192 prefixEnd_11192 1702777921548279984751 := by
  unfold tailWord_11192
  simp only [CollatzResearch.WordTrace]
  refine ⟨204102887730385143265915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 272137183640513524354553 204102887730385143265915)
  ·
    refine ⟨306154331595577714898873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204102887730385143265915 306154331595577714898873)
    ·
      refine ⟨229615748696683286174155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306154331595577714898873 229615748696683286174155)
      ·
        refine ⟨344423623045024929261233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229615748696683286174155 344423623045024929261233)
        ·
          refine ⟨258317717283768696945925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344423623045024929261233 258317717283768696945925)
          ·
            refine ⟨48434571990706630677361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258317717283768696945925 48434571990706630677361)
            ·
              refine ⟨36325928993029973008021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48434571990706630677361 36325928993029973008021)
              ·
                refine ⟨1702777921548279984751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36325928993029973008021 1702777921548279984751)
                ·
                  rfl

theorem cell20_11192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_11192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11192 prefixEnd_11192 := by exact prefixLift 11192
  have htrace : WordTrace (prefixWord ++ tailWord_11192) baseStart_11192 baseEnd_11192 := by
    simpa [prefixWord, tailWord_11192, baseEnd_11192] using wordTrace_append hprefix tailTrace_11192
  have hstable : (prefixWord ++ tailWord_11192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11192).length < 2 ^ (prefixWord ++ tailWord_11192).sum := by decide
  have hdescent : baseEnd_11192 < baseStart_11192 := by decide
  rcases family_descends (prefixWord ++ tailWord_11192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11199 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_11199 : Nat := 118140960795 + 11199 * 2 ^ 59
def prefixEnd_11199 : Nat := 4983230072969 + 3 ^ 40 * 11199 * 2
def baseEnd_11199 : Nat := 5111528755383926720891

theorem tailTrace_11199 : CollatzResearch.WordTrace tailWord_11199 prefixEnd_11199 5111528755383926720891 := by
  unfold tailWord_11199
  simp only [CollatzResearch.WordTrace]
  refine ⟨408461086435410482036651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 272307390956940321357767 408461086435410482036651)
  ·
    refine ⟨612691629653115723054977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 408461086435410482036651 612691629653115723054977)
    ·
      refine ⟨459518722239836792291233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612691629653115723054977 459518722239836792291233)
      ·
        refine ⟨344639041679877594218425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459518722239836792291233 344639041679877594218425)
        ·
          refine ⟨258479281259908195663819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344639041679877594218425 258479281259908195663819)
          ·
            refine ⟨387718921889862293495729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258479281259908195663819 387718921889862293495729)
            ·
              refine ⟨290789191417396720121797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387718921889862293495729 290789191417396720121797)
              ·
                refine ⟨54522973390761885022837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 290789191417396720121797 54522973390761885022837)
                ·
                  refine ⟨5111528755383926720891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54522973390761885022837 5111528755383926720891)
                  ·
                    rfl

theorem cell20_11199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_11199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11199 prefixEnd_11199 := by exact prefixLift 11199
  have htrace : WordTrace (prefixWord ++ tailWord_11199) baseStart_11199 baseEnd_11199 := by
    simpa [prefixWord, tailWord_11199, baseEnd_11199] using wordTrace_append hprefix tailTrace_11199
  have hstable : (prefixWord ++ tailWord_11199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11199).length < 2 ^ (prefixWord ++ tailWord_11199).sum := by decide
  have hdescent : baseEnd_11199 < baseStart_11199 := by decide
  rcases family_descends (prefixWord ++ tailWord_11199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11247 : List Nat := [1, 1, 2, 1, 4, 4, 3, 4]
def baseStart_11247 : Nat := 118140960795 + 11247 * 2 ^ 59
def prefixEnd_11247 : Nat := 4983230072969 + 3 ^ 40 * 11247 * 2
def baseEnd_11247 : Nat := 1711145754436364373565

theorem tailTrace_11247 : CollatzResearch.WordTrace tailWord_11247 prefixEnd_11247 1711145754436364373565 := by
  unfold tailWord_11247
  simp only [CollatzResearch.WordTrace]
  refine ⟨410211790261514679783995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 273474526841009786522663 410211790261514679783995)
  ·
    refine ⟨615317685392272019675993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410211790261514679783995 615317685392272019675993)
    ·
      refine ⟨461488264044204014756995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615317685392272019675993 461488264044204014756995)
      ·
        refine ⟨692232396066306022135493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461488264044204014756995 692232396066306022135493)
        ·
          refine ⟨129793574262432379150405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 692232396066306022135493 129793574262432379150405)
          ·
            refine ⟨24336295174206071090701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129793574262432379150405 24336295174206071090701)
            ·
              refine ⟨9126110690327276659013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24336295174206071090701 9126110690327276659013)
              ·
                refine ⟨1711145754436364373565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9126110690327276659013 1711145754436364373565)
                ·
                  rfl

theorem cell20_11247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 4].length) (baseStart_11247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11247 prefixEnd_11247 := by exact prefixLift 11247
  have htrace : WordTrace (prefixWord ++ tailWord_11247) baseStart_11247 baseEnd_11247 := by
    simpa [prefixWord, tailWord_11247, baseEnd_11247] using wordTrace_append hprefix tailTrace_11247
  have hstable : (prefixWord ++ tailWord_11247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11247).length < 2 ^ (prefixWord ++ tailWord_11247).sum := by decide
  have hdescent : baseEnd_11247 < baseStart_11247 := by decide
  rcases family_descends (prefixWord ++ tailWord_11247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11253 : List Nat := [1, 3, 5, 2, 1, 1, 2, 3, 2]
def baseStart_11253 : Nat := 118140960795 + 11253 * 2 ^ 59
def prefixEnd_11253 : Nat := 4983230072969 + 3 ^ 40 * 11253 * 2
def baseEnd_11253 : Nat := 5136175826799738920671

theorem tailTrace_11253 : CollatzResearch.WordTrace tailWord_11253 prefixEnd_11253 5136175826799738920671 := by
  unfold tailWord_11253
  simp only [CollatzResearch.WordTrace]
  refine ⟨410430628239777704502413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 273620418826518469668275 410430628239777704502413)
  ·
    refine ⟨153911485589916639188405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 410430628239777704502413 153911485589916639188405)
    ·
      refine ⟨14429201774054684923913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153911485589916639188405 14429201774054684923913)
      ·
        refine ⟨10821901330541013692935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14429201774054684923913 10821901330541013692935)
        ·
          refine ⟨16232851995811520539403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10821901330541013692935 16232851995811520539403)
          ·
            refine ⟨24349277993717280809105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16232851995811520539403 24349277993717280809105)
            ·
              refine ⟨18261958495287960606829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24349277993717280809105 18261958495287960606829)
              ·
                refine ⟨6848234435732985227561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18261958495287960606829 6848234435732985227561)
                ·
                  refine ⟨5136175826799738920671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6848234435732985227561 5136175826799738920671)
                  ·
                    rfl

theorem cell20_11253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_11253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_11253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_11253 prefixEnd_11253 := by exact prefixLift 11253
  have htrace : WordTrace (prefixWord ++ tailWord_11253) baseStart_11253 baseEnd_11253 := by
    simpa [prefixWord, tailWord_11253, baseEnd_11253] using wordTrace_append hprefix tailTrace_11253
  have hstable : (prefixWord ++ tailWord_11253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11253).length < 2 ^ (prefixWord ++ tailWord_11253).sum := by decide
  have hdescent : baseEnd_11253 < baseStart_11253 := by decide
  rcases family_descends (prefixWord ++ tailWord_11253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
