import V185TrunkScan23Chunk0459

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2721484 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_2721484 : Nat := 118140960795 + 2721484 * 2 ^ 59
def prefixEnd_2721484 : Nat := 4983230072969 + 3 ^ 40 * 2721484 * 2
def baseEnd_2721484 : Nat := 465809795173578471678043

theorem tailTrace_2721484 : CollatzResearch.WordTrace tailWord_2721484 prefixEnd_2721484 465809795173578471678043 := by
  unfold tailWord_2721484
  simp only [CollatzResearch.WordTrace]
  refine ⟨49630338036267867654145753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66173784048357156872194337 49630338036267867654145753)
  ·
    refine ⟨37222753527200900740609315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49630338036267867654145753 37222753527200900740609315)
    ·
      refine ⟨55834130290801351110913973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37222753527200900740609315 55834130290801351110913973)
      ·
        refine ⟨5234449714762626666648185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55834130290801351110913973 5234449714762626666648185)
        ·
          refine ⟨3925837286071969999986139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5234449714762626666648185 3925837286071969999986139)
          ·
            refine ⟨5888755929107954999979209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925837286071969999986139 5888755929107954999979209)
            ·
              refine ⟨4416566946830966249984407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888755929107954999979209 4416566946830966249984407)
              ·
                refine ⟨6624850420246449374976611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416566946830966249984407 6624850420246449374976611)
                ·
                  refine ⟨9937275630369674062464917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6624850420246449374976611 9937275630369674062464917)
                  ·
                    refine ⟨465809795173578471678043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9937275630369674062464917 465809795173578471678043)
                    ·
                      rfl

theorem cell23_2721484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_2721484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721484 prefixEnd_2721484 := by exact prefixLift 2721484
  have htrace : WordTrace (prefixWord ++ tailWord_2721484) baseStart_2721484 baseEnd_2721484 := by
    simpa [prefixWord, tailWord_2721484, baseEnd_2721484] using wordTrace_append hprefix tailTrace_2721484
  have hstable : (prefixWord ++ tailWord_2721484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721484).length < 2 ^ (prefixWord ++ tailWord_2721484).sum := by decide
  have hdescent : baseEnd_2721484 < baseStart_2721484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721497 : List Nat := [1, 2, 1, 2, 3, 4, 3, 7]
def baseStart_2721497 : Nat := 118140960795 + 2721497 * 2 ^ 59
def prefixEnd_2721497 : Nat := 4983230072969 + 3 ^ 40 * 2721497 * 2
def baseEnd_2721497 : Nat := 51756891139601624598947

theorem tailTrace_2721497 : CollatzResearch.WordTrace tailWord_2721497 prefixEnd_2721497 51756891139601624598947 := by
  unfold tailWord_2721497
  simp only [CollatzResearch.WordTrace]
  refine ⟨99261150221488638528514745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66174100147659092352343163 99261150221488638528514745)
  ·
    refine ⟨74445862666116478896386059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99261150221488638528514745 74445862666116478896386059)
    ·
      refine ⟨111668793999174718344579089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74445862666116478896386059 111668793999174718344579089)
      ·
        refine ⟨83751595499381038758434317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111668793999174718344579089 83751595499381038758434317)
        ·
          refine ⟨31406848312267889534412869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83751595499381038758434317 31406848312267889534412869)
          ·
            refine ⟨5888784058550229287702413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31406848312267889534412869 5888784058550229287702413)
            ·
              refine ⟨2208294021956335982888405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5888784058550229287702413 2208294021956335982888405)
              ·
                refine ⟨51756891139601624598947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2208294021956335982888405 51756891139601624598947)
                ·
                  rfl

theorem cell23_2721497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 7].length) (baseStart_2721497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721497 prefixEnd_2721497 := by exact prefixLift 2721497
  have htrace : WordTrace (prefixWord ++ tailWord_2721497) baseStart_2721497 baseEnd_2721497 := by
    simpa [prefixWord, tailWord_2721497, baseEnd_2721497] using wordTrace_append hprefix tailTrace_2721497
  have hstable : (prefixWord ++ tailWord_2721497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721497).length < 2 ^ (prefixWord ++ tailWord_2721497).sum := by decide
  have hdescent : baseEnd_2721497 < baseStart_2721497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721508 : List Nat := [2, 3, 1, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_2721508 : Nat := 118140960795 + 2721508 * 2 ^ 59
def prefixEnd_2721508 : Nat := 4983230072969 + 3 ^ 40 * 2721508 * 2
def baseEnd_2721508 : Nat := 1397441709056443321134019

theorem tailTrace_2721508 : CollatzResearch.WordTrace tailWord_2721508 prefixEnd_2721508 1397441709056443321134019 := by
  unfold tailWord_2721508
  simp only [CollatzResearch.WordTrace]
  refine ⟨49630775712224393703582589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66174367616299191604776785 49630775712224393703582589)
  ·
    refine ⟨18611540892084147638843471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49630775712224393703582589 18611540892084147638843471)
    ·
      refine ⟨27917311338126221458265207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18611540892084147638843471 27917311338126221458265207)
      ·
        refine ⟨41875967007189332187397811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27917311338126221458265207 41875967007189332187397811)
        ·
          refine ⟨62813950510783998281096717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41875967007189332187397811 62813950510783998281096717)
          ·
            refine ⟨23555231441543999355411269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62813950510783998281096717 23555231441543999355411269)
            ·
              refine ⟨4416605895289499879139613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23555231441543999355411269 4416605895289499879139613)
              ·
                refine ⟨1656227210733562454677355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4416605895289499879139613 1656227210733562454677355)
                ·
                  refine ⟨2484340816100343682016033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656227210733562454677355 2484340816100343682016033)
                  ·
                    refine ⟨1863255612075257761512025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2484340816100343682016033 1863255612075257761512025)
                    ·
                      refine ⟨1397441709056443321134019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863255612075257761512025 1397441709056443321134019)
                      ·
                        rfl

theorem cell23_2721508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_2721508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721508 prefixEnd_2721508 := by exact prefixLift 2721508
  have htrace : WordTrace (prefixWord ++ tailWord_2721508) baseStart_2721508 baseEnd_2721508 := by
    simpa [prefixWord, tailWord_2721508, baseEnd_2721508] using wordTrace_append hprefix tailTrace_2721508
  have hstable : (prefixWord ++ tailWord_2721508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721508).length < 2 ^ (prefixWord ++ tailWord_2721508).sum := by decide
  have hdescent : baseEnd_2721508 < baseStart_2721508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721520 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_2721520 : Nat := 118140960795 + 2721520 * 2 ^ 59
def prefixEnd_2721520 : Nat := 4983230072969 + 3 ^ 40 * 2721520 * 2
def baseEnd_2721520 : Nat := 1397447870824297274183963

theorem tailTrace_2721520 : CollatzResearch.WordTrace tailWord_2721520 prefixEnd_2721520 1397447870824297274183963 := by
  unfold tailWord_2721520
  simp only [CollatzResearch.WordTrace]
  refine ⟨49630994550202656728301007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66174659400270208971068009 49630994550202656728301007)
  ·
    refine ⟨74446491825303985092451511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49630994550202656728301007 74446491825303985092451511)
    ·
      refine ⟨111669737737955977638677267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74446491825303985092451511 111669737737955977638677267)
      ·
        refine ⟨167504606606933966458015901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111669737737955977638677267 167504606606933966458015901)
        ·
          refine ⟨62814227477600237421755963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167504606606933966458015901 62814227477600237421755963)
          ·
            refine ⟨94221341216400356132633945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62814227477600237421755963 94221341216400356132633945)
            ·
              refine ⟨70666005912300267099475459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94221341216400356132633945 70666005912300267099475459)
              ·
                refine ⟨105999008868450400649213189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70666005912300267099475459 105999008868450400649213189)
                ·
                  refine ⟨19874814162834450121727473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105999008868450400649213189 19874814162834450121727473)
                  ·
                    refine ⟨14906110622125837591295605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19874814162834450121727473 14906110622125837591295605)
                    ·
                      refine ⟨1397447870824297274183963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14906110622125837591295605 1397447870824297274183963)
                      ·
                        rfl

theorem cell23_2721520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_2721520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721520 prefixEnd_2721520 := by exact prefixLift 2721520
  have htrace : WordTrace (prefixWord ++ tailWord_2721520) baseStart_2721520 baseEnd_2721520 := by
    simpa [prefixWord, tailWord_2721520, baseEnd_2721520] using wordTrace_append hprefix tailTrace_2721520
  have hstable : (prefixWord ++ tailWord_2721520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721520).length < 2 ^ (prefixWord ++ tailWord_2721520).sum := by decide
  have hdescent : baseEnd_2721520 < baseStart_2721520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721554 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2721554 : Nat := 118140960795 + 2721554 * 2 ^ 59
def prefixEnd_2721554 : Nat := 4983230072969 + 3 ^ 40 * 2721554 * 2
def baseEnd_2721554 : Nat := 1397465329166550141158807

theorem tailTrace_2721554 : CollatzResearch.WordTrace tailWord_2721554 prefixEnd_2721554 1397465329166550141158807 := by
  unfold tailWord_2721554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24815807295570534315834929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66175486121521424842226477 24815807295570534315834929)
  ·
    refine ⟨18611855471677900736876197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24815807295570534315834929 18611855471677900736876197)
    ·
      refine ⟨3489722900939606388164287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18611855471677900736876197 3489722900939606388164287)
      ·
        refine ⟨5234584351409409582246431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489722900939606388164287 5234584351409409582246431)
        ·
          refine ⟨7851876527114114373369647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234584351409409582246431 7851876527114114373369647)
          ·
            refine ⟨11777814790671171560054471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7851876527114114373369647 11777814790671171560054471)
            ·
              refine ⟨17666722186006757340081707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11777814790671171560054471 17666722186006757340081707)
              ·
                refine ⟨26500083279010136010122561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17666722186006757340081707 26500083279010136010122561)
                ·
                  refine ⟨19875062459257602007591921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26500083279010136010122561 19875062459257602007591921)
                  ·
                    refine ⟨14906296844443201505693941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19875062459257602007591921 14906296844443201505693941)
                    ·
                      refine ⟨1397465329166550141158807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14906296844443201505693941 1397465329166550141158807)
                      ·
                        rfl

theorem cell23_2721554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2721554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721554 prefixEnd_2721554 := by exact prefixLift 2721554
  have htrace : WordTrace (prefixWord ++ tailWord_2721554) baseStart_2721554 baseEnd_2721554 := by
    simpa [prefixWord, tailWord_2721554, baseEnd_2721554] using wordTrace_append hprefix tailTrace_2721554
  have hstable : (prefixWord ++ tailWord_2721554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721554).length < 2 ^ (prefixWord ++ tailWord_2721554).sum := by decide
  have hdescent : baseEnd_2721554 < baseStart_2721554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721564 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_2721564 : Nat := 118140960795 + 2721564 * 2 ^ 59
def prefixEnd_2721564 : Nat := 4983230072969 + 3 ^ 40 * 2721564 * 2
def baseEnd_2721564 : Nat := 1397470463973095102033761

theorem tailTrace_2721564 : CollatzResearch.WordTrace tailWord_2721564 prefixEnd_2721564 1397470463973095102033761 := by
  unfold tailWord_2721564
  simp only [CollatzResearch.WordTrace]
  refine ⟨49631796956122954485601873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66175729274830605980802497 49631796956122954485601873)
  ·
    refine ⟨37223847717092215864201405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49631796956122954485601873 37223847717092215864201405)
    ·
      refine ⟨13958942893909580949075527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37223847717092215864201405 13958942893909580949075527)
      ·
        refine ⟨20938414340864371423613291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13958942893909580949075527 20938414340864371423613291)
        ·
          refine ⟨31407621511296557135419937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20938414340864371423613291 31407621511296557135419937)
          ·
            refine ⟨23555716133472417851564953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31407621511296557135419937 23555716133472417851564953)
            ·
              refine ⟨17666787100104313388673715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23555716133472417851564953 17666787100104313388673715)
              ·
                refine ⟨26500180650156470083010573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17666787100104313388673715 26500180650156470083010573)
                ·
                  refine ⟨9937567743808676281128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26500180650156470083010573 9937567743808676281128965)
                  ·
                    refine ⟨1863293951964126802711681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9937567743808676281128965 1863293951964126802711681)
                    ·
                      refine ⟨1397470463973095102033761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863293951964126802711681 1397470463973095102033761)
                      ·
                        rfl

theorem cell23_2721564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_2721564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721564 prefixEnd_2721564 := by exact prefixLift 2721564
  have htrace : WordTrace (prefixWord ++ tailWord_2721564) baseStart_2721564 baseEnd_2721564 := by
    simpa [prefixWord, tailWord_2721564, baseEnd_2721564] using wordTrace_append hprefix tailTrace_2721564
  have hstable : (prefixWord ++ tailWord_2721564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721564).length < 2 ^ (prefixWord ++ tailWord_2721564).sum := by decide
  have hdescent : baseEnd_2721564 < baseStart_2721564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721567 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_2721567 : Nat := 118140960795 + 2721567 * 2 ^ 59
def prefixEnd_2721567 : Nat := 4983230072969 + 3 ^ 40 * 2721567 * 2
def baseEnd_2721567 : Nat := 1397472004415058590296247

theorem tailTrace_2721567 : CollatzResearch.WordTrace tailWord_2721567 prefixEnd_2721567 1397472004415058590296247 := by
  unfold tailWord_2721567
  simp only [CollatzResearch.WordTrace]
  refine ⟨99263703331235040483562955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66175802220823360322375303 99263703331235040483562955)
  ·
    refine ⟨148895554996852560725344433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99263703331235040483562955 148895554996852560725344433)
    ·
      refine ⟨111671666247639420544008325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148895554996852560725344433 111671666247639420544008325)
      ·
        refine ⟨20938437421432391352001561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111671666247639420544008325 20938437421432391352001561)
        ·
          refine ⟨15703828066074293514001171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20938437421432391352001561 15703828066074293514001171)
          ·
            refine ⟨23555742099111440271001757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15703828066074293514001171 23555742099111440271001757)
            ·
              refine ⟨8833403287166790101625659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23555742099111440271001757 8833403287166790101625659)
              ·
                refine ⟨13250104930750185152438489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8833403287166790101625659 13250104930750185152438489)
                ·
                  refine ⟨9937578698062638864328867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13250104930750185152438489 9937578698062638864328867)
                  ·
                    refine ⟨14906368047093958296493301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9937578698062638864328867 14906368047093958296493301)
                    ·
                      refine ⟨1397472004415058590296247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14906368047093958296493301 1397472004415058590296247)
                      ·
                        rfl

theorem cell23_2721567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_2721567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721567 prefixEnd_2721567 := by exact prefixLift 2721567
  have htrace : WordTrace (prefixWord ++ tailWord_2721567) baseStart_2721567 baseEnd_2721567 := by
    simpa [prefixWord, tailWord_2721567, baseEnd_2721567] using wordTrace_append hprefix tailTrace_2721567
  have hstable : (prefixWord ++ tailWord_2721567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721567).length < 2 ^ (prefixWord ++ tailWord_2721567).sum := by decide
  have hdescent : baseEnd_2721567 < baseStart_2721567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721637 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2721637 : Nat := 118140960795 + 2721637 * 2 ^ 59
def prefixEnd_2721637 : Nat := 4983230072969 + 3 ^ 40 * 2721637 * 2
def baseEnd_2721637 : Nat := 1397507948060873316420925

theorem tailTrace_2721637 : CollatzResearch.WordTrace tailWord_2721637 prefixEnd_2721637 1397507948060873316420925 := by
  unfold tailWord_2721637
  simp only [CollatzResearch.WordTrace]
  refine ⟨99266256440981442438611165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66177504293987628292407443 99266256440981442438611165)
  ·
    refine ⟨37224846165368040914479187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99266256440981442438611165 37224846165368040914479187)
    ·
      refine ⟨55837269248052061371718781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37224846165368040914479187 55837269248052061371718781)
      ·
        refine ⟨20938975968019523014394543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55837269248052061371718781 20938975968019523014394543)
        ·
          refine ⟨31408463952029284521591815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20938975968019523014394543 31408463952029284521591815)
          ·
            refine ⟨47112695928043926782387723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31408463952029284521591815 47112695928043926782387723)
            ·
              refine ⟨70669043892065890173581585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47112695928043926782387723 70669043892065890173581585)
              ·
                refine ⟨53001782919049417630186189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70669043892065890173581585 53001782919049417630186189)
                ·
                  refine ⟨19875668594643531611319821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53001782919049417630186189 19875668594643531611319821)
                  ·
                    refine ⟨7453375722991324354244933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19875668594643531611319821 7453375722991324354244933)
                    ·
                      refine ⟨1397507948060873316420925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7453375722991324354244933 1397507948060873316420925)
                      ·
                        rfl

theorem cell23_2721637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2721637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721637 prefixEnd_2721637 := by exact prefixLift 2721637
  have htrace : WordTrace (prefixWord ++ tailWord_2721637) baseStart_2721637 baseEnd_2721637 := by
    simpa [prefixWord, tailWord_2721637, baseEnd_2721637] using wordTrace_append hprefix tailTrace_2721637
  have hstable : (prefixWord ++ tailWord_2721637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721637).length < 2 ^ (prefixWord ++ tailWord_2721637).sum := by decide
  have hdescent : baseEnd_2721637 < baseStart_2721637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721664 : List Nat := [2, 1, 1, 2, 1, 2, 5, 2, 3, 4]
def baseStart_2721664 : Nat := 118140960795 + 2721664 * 2 ^ 59
def prefixEnd_2721664 : Nat := 4983230072969 + 3 ^ 40 * 2721664 * 2
def baseEnd_2721664 : Nat := 465840604012848236927767

theorem tailTrace_2721664 : CollatzResearch.WordTrace tailWord_2721664 prefixEnd_2721664 465840604012848236927767 := by
  unfold tailWord_2721664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49633620605941813024922023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66178160807922417366562697 49633620605941813024922023)
  ·
    refine ⟨74450430908912719537383035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49633620605941813024922023 74450430908912719537383035)
    ·
      refine ⟨111675646363369079306074553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74450430908912719537383035 111675646363369079306074553)
      ·
        refine ⟨83756734772526809479555915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111675646363369079306074553 83756734772526809479555915)
        ·
          refine ⟨125635102158790214219333873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83756734772526809479555915 125635102158790214219333873)
          ·
            refine ⟨94226326619092660664500405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125635102158790214219333873 94226326619092660664500405)
            ·
              refine ⟨8833718120539936937296913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94226326619092660664500405 8833718120539936937296913)
              ·
                refine ⟨6625288590404952702972685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8833718120539936937296913 6625288590404952702972685)
                ·
                  refine ⟨2484483221401857263614757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6625288590404952702972685 2484483221401857263614757)
                  ·
                    refine ⟨465840604012848236927767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484483221401857263614757 465840604012848236927767)
                    ·
                      rfl

theorem cell23_2721664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_2721664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721664 prefixEnd_2721664 := by exact prefixLift 2721664
  have htrace : WordTrace (prefixWord ++ tailWord_2721664) baseStart_2721664 baseEnd_2721664 := by
    simpa [prefixWord, tailWord_2721664, baseEnd_2721664] using wordTrace_append hprefix tailTrace_2721664
  have hstable : (prefixWord ++ tailWord_2721664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721664).length < 2 ^ (prefixWord ++ tailWord_2721664).sum := by decide
  have hdescent : baseEnd_2721664 < baseStart_2721664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721681 : List Nat := [1, 2, 2, 1, 1, 1, 5, 5, 1, 4]
def baseStart_2721681 : Nat := 118140960795 + 2721681 * 2 ^ 59
def prefixEnd_2721681 : Nat := 4983230072969 + 3 ^ 40 * 2721681 * 2
def baseEnd_2721681 : Nat := 465843513736557048090241

theorem tailTrace_2721681 : CollatzResearch.WordTrace tailWord_2721681 prefixEnd_2721681 465843513736557048090241 := by
  unfold tailWord_2721681
  simp only [CollatzResearch.WordTrace]
  refine ⟨99267861252822037953212897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66178574168548025302141931 99267861252822037953212897)
  ·
    refine ⟨74450895939616528464909673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99267861252822037953212897 74450895939616528464909673)
    ·
      refine ⟨55838171954712396348682255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74450895939616528464909673 55838171954712396348682255)
      ·
        refine ⟨83757257932068594523023383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55838171954712396348682255 83757257932068594523023383)
        ·
          refine ⟨125635886898102891784535075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83757257932068594523023383 125635886898102891784535075)
          ·
            refine ⟨188453830347154337676802613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125635886898102891784535075 188453830347154337676802613)
            ·
              refine ⟨17667546595045719157200245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188453830347154337676802613 17667546595045719157200245)
              ·
                refine ⟨1656332493285536170987523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17667546595045719157200245 1656332493285536170987523)
                ·
                  refine ⟨2484498739928304256481285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656332493285536170987523 2484498739928304256481285)
                  ·
                    refine ⟨465843513736557048090241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484498739928304256481285 465843513736557048090241)
                    ·
                      rfl

theorem cell23_2721681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_2721681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721681 prefixEnd_2721681 := by exact prefixLift 2721681
  have htrace : WordTrace (prefixWord ++ tailWord_2721681) baseStart_2721681 baseEnd_2721681 := by
    simpa [prefixWord, tailWord_2721681, baseEnd_2721681] using wordTrace_append hprefix tailTrace_2721681
  have hstable : (prefixWord ++ tailWord_2721681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721681).length < 2 ^ (prefixWord ++ tailWord_2721681).sum := by decide
  have hdescent : baseEnd_2721681 < baseStart_2721681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721684 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2721684 : Nat := 118140960795 + 2721684 * 2 ^ 59
def prefixEnd_2721684 : Nat := 4983230072969 + 3 ^ 40 * 2721684 * 2
def baseEnd_2721684 : Nat := 1397532081651634632533209

theorem tailTrace_2721684 : CollatzResearch.WordTrace tailWord_2721684 prefixEnd_2721684 1397532081651634632533209 := by
  unfold tailWord_2721684
  simp only [CollatzResearch.WordTrace]
  refine ⟨49633985335905584732786053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66178647114540779643714737 49633985335905584732786053)
  ·
    refine ⟨9306372250482297137397385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49633985335905584732786053 9306372250482297137397385)
    ·
      refine ⟨6979779187861722853048039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9306372250482297137397385 6979779187861722853048039)
      ·
        refine ⟨10469668781792584279572059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6979779187861722853048039 10469668781792584279572059)
        ·
          refine ⟨15704503172688876419358089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10469668781792584279572059 15704503172688876419358089)
          ·
            refine ⟨11778377379516657314518567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15704503172688876419358089 11778377379516657314518567)
            ·
              refine ⟨17667566069274985971777851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11778377379516657314518567 17667566069274985971777851)
              ·
                refine ⟨26501349103912478957666777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17667566069274985971777851 26501349103912478957666777)
                ·
                  refine ⟨19876011827934359218250083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26501349103912478957666777 19876011827934359218250083)
                  ·
                    refine ⟨29814017741901538827375125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19876011827934359218250083 29814017741901538827375125)
                    ·
                      refine ⟨1397532081651634632533209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29814017741901538827375125 1397532081651634632533209)
                      ·
                        rfl

theorem cell23_2721684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2721684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721684 prefixEnd_2721684 := by exact prefixLift 2721684
  have htrace : WordTrace (prefixWord ++ tailWord_2721684) baseStart_2721684 baseEnd_2721684 := by
    simpa [prefixWord, tailWord_2721684, baseEnd_2721684] using wordTrace_append hprefix tailTrace_2721684
  have hstable : (prefixWord ++ tailWord_2721684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721684).length < 2 ^ (prefixWord ++ tailWord_2721684).sum := by decide
  have hdescent : baseEnd_2721684 < baseStart_2721684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721698 : List Nat := [3, 3, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2721698 : Nat := 118140960795 + 2721698 * 2 ^ 59
def prefixEnd_2721698 : Nat := 4983230072969 + 3 ^ 40 * 2721698 * 2
def baseEnd_2721698 : Nat := 465846423460265859252715

theorem tailTrace_2721698 : CollatzResearch.WordTrace tailWord_2721698 prefixEnd_2721698 465846423460265859252715 := by
  unfold tailWord_2721698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817120323440112464145437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66178987529173633237721165 24817120323440112464145437)
  ·
    refine ⟨9306420121290042174054539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24817120323440112464145437 9306420121290042174054539)
    ·
      refine ⟨13959630181935063261081809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9306420121290042174054539 13959630181935063261081809)
      ·
        refine ⟨10469722636451297445811357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13959630181935063261081809 10469722636451297445811357)
        ·
          refine ⟨3926145988669236542179259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10469722636451297445811357 3926145988669236542179259)
          ·
            refine ⟨5889218983003854813268889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926145988669236542179259 5889218983003854813268889)
            ·
              refine ⟨4416914237252891109951667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5889218983003854813268889 4416914237252891109951667)
              ·
                refine ⟨6625371355879336664927501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416914237252891109951667 6625371355879336664927501)
                ·
                  refine ⟨2484514258454751249347813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6625371355879336664927501 2484514258454751249347813)
                  ·
                    refine ⟨465846423460265859252715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484514258454751249347813 465846423460265859252715)
                    ·
                      rfl

theorem cell23_2721698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2721698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721698 prefixEnd_2721698 := by exact prefixLift 2721698
  have htrace : WordTrace (prefixWord ++ tailWord_2721698) baseStart_2721698 baseEnd_2721698 := by
    simpa [prefixWord, tailWord_2721698, baseEnd_2721698] using wordTrace_append hprefix tailTrace_2721698
  have hstable : (prefixWord ++ tailWord_2721698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721698).length < 2 ^ (prefixWord ++ tailWord_2721698).sum := by decide
  have hdescent : baseEnd_2721698 < baseStart_2721698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721721 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2721721 : Nat := 118140960795 + 2721721 * 2 ^ 59
def prefixEnd_2721721 : Nat := 4983230072969 + 3 ^ 40 * 2721721 * 2
def baseEnd_2721721 : Nat := 1397551080435850987770539

theorem tailTrace_2721721 : CollatzResearch.WordTrace tailWord_2721721 prefixEnd_2721721 1397551080435850987770539 := by
  unfold tailWord_2721721
  simp only [CollatzResearch.WordTrace]
  refine ⟨99269320172677124784669017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66179546781784749856446011 99269320172677124784669017)
  ·
    refine ⟨74451990129507843588501763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99269320172677124784669017 74451990129507843588501763)
    ·
      refine ⟨111677985194261765382752645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74451990129507843588501763 111677985194261765382752645)
      ·
        refine ⟨20939622223924081009266121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111677985194261765382752645 20939622223924081009266121)
        ·
          refine ⟨15704716667943060756949591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20939622223924081009266121 15704716667943060756949591)
          ·
            refine ⟨23557075001914591135424387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15704716667943060756949591 23557075001914591135424387)
            ·
              refine ⟨35335612502871886703136581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23557075001914591135424387 35335612502871886703136581)
              ·
                refine ⟨6625427344288478756838109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35335612502871886703136581 6625427344288478756838109)
                ·
                  refine ⟨2484535254108179533814291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6625427344288478756838109 2484535254108179533814291)
                  ·
                    refine ⟨3726802881162269300721437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484535254108179533814291 3726802881162269300721437)
                    ·
                      refine ⟨1397551080435850987770539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3726802881162269300721437 1397551080435850987770539)
                      ·
                        rfl

theorem cell23_2721721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2721721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721721 prefixEnd_2721721 := by exact prefixLift 2721721
  have htrace : WordTrace (prefixWord ++ tailWord_2721721) baseStart_2721721 baseEnd_2721721 := by
    simpa [prefixWord, tailWord_2721721, baseEnd_2721721] using wordTrace_append hprefix tailTrace_2721721
  have hstable : (prefixWord ++ tailWord_2721721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721721).length < 2 ^ (prefixWord ++ tailWord_2721721).sum := by decide
  have hdescent : baseEnd_2721721 < baseStart_2721721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721748 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_2721748 : Nat := 118140960795 + 2721748 * 2 ^ 59
def prefixEnd_2721748 : Nat := 4983230072969 + 3 ^ 40 * 2721748 * 2
def baseEnd_2721748 : Nat := 1397564944413522382132915

theorem tailTrace_2721748 : CollatzResearch.WordTrace tailWord_2721748 prefixEnd_2721748 1397564944413522382132915 := by
  unfold tailWord_2721748
  simp only [CollatzResearch.WordTrace]
  refine ⟨49635152471789654197950949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66180203295719538930601265 49635152471789654197950949)
  ·
    refine ⟨9306591088460560162115803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49635152471789654197950949 9306591088460560162115803)
    ·
      refine ⟨13959886632690840243173705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9306591088460560162115803 13959886632690840243173705)
      ·
        refine ⟨10469914974518130182380279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13959886632690840243173705 10469914974518130182380279)
        ·
          refine ⟨15704872461777195273570419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10469914974518130182380279 15704872461777195273570419)
          ·
            refine ⟨23557308692665792910355629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15704872461777195273570419 23557308692665792910355629)
            ·
              refine ⟨8833990759749672341383361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23557308692665792910355629 8833990759749672341383361)
              ·
                refine ⟨6625493069812254256037521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8833990759749672341383361 6625493069812254256037521)
                ·
                  refine ⟨4969119802359190692028141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6625493069812254256037521 4969119802359190692028141)
                  ·
                    refine ⟨1863419925884696509510553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4969119802359190692028141 1863419925884696509510553)
                    ·
                      refine ⟨1397564944413522382132915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863419925884696509510553 1397564944413522382132915)
                      ·
                        rfl

theorem cell23_2721748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_2721748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721748 prefixEnd_2721748 := by exact prefixLift 2721748
  have htrace : WordTrace (prefixWord ++ tailWord_2721748) baseStart_2721748 baseEnd_2721748 := by
    simpa [prefixWord, tailWord_2721748, baseEnd_2721748] using wordTrace_append hprefix tailTrace_2721748
  have hstable : (prefixWord ++ tailWord_2721748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721748).length < 2 ^ (prefixWord ++ tailWord_2721748).sum := by decide
  have hdescent : baseEnd_2721748 < baseStart_2721748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721762 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_2721762 : Nat := 118140960795 + 2721762 * 2 ^ 59
def prefixEnd_2721762 : Nat := 4983230072969 + 3 ^ 40 * 2721762 * 2
def baseEnd_2721762 : Nat := 155285792571409480817539

theorem tailTrace_2721762 : CollatzResearch.WordTrace tailWord_2721762 prefixEnd_2721762 155285792571409480817539 := by
  unfold tailWord_2721762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24817703891382147196727885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66180543710352392524607693 24817703891382147196727885)
  ·
    refine ⟨9306638959268305198772957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24817703891382147196727885 9306638959268305198772957)
    ·
      refine ⟨3489989609725614449539859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9306638959268305198772957 3489989609725614449539859)
      ·
        refine ⟨5234984414588421674309789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489989609725614449539859 5234984414588421674309789)
        ·
          refine ⟨1963119155470658127866171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5234984414588421674309789 1963119155470658127866171)
          ·
            refine ⟨2944678733205987191799257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963119155470658127866171 2944678733205987191799257)
            ·
              refine ⟨2208509049904490393849443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2944678733205987191799257 2208509049904490393849443)
              ·
                refine ⟨3312763574856735590774165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208509049904490393849443 3312763574856735590774165)
                ·
                  refine ⟨155285792571409480817539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3312763574856735590774165 155285792571409480817539)
                  ·
                    rfl

theorem cell23_2721762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_2721762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721762 prefixEnd_2721762 := by exact prefixLift 2721762
  have htrace : WordTrace (prefixWord ++ tailWord_2721762) baseStart_2721762 baseEnd_2721762 := by
    simpa [prefixWord, tailWord_2721762, baseEnd_2721762] using wordTrace_append hprefix tailTrace_2721762
  have hstable : (prefixWord ++ tailWord_2721762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721762).length < 2 ^ (prefixWord ++ tailWord_2721762).sum := by decide
  have hdescent : baseEnd_2721762 < baseStart_2721762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721764 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_2721764 : Nat := 118140960795 + 2721764 * 2 ^ 59
def prefixEnd_2721764 : Nat := 4983230072969 + 3 ^ 40 * 2721764 * 2
def baseEnd_2721764 : Nat := 1397573160103994319532841

theorem tailTrace_2721764 : CollatzResearch.WordTrace tailWord_2721764 prefixEnd_2721764 1397573160103994319532841 := by
  unfold tailWord_2721764
  simp only [CollatzResearch.WordTrace]
  refine ⟨49635444255760671564242173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66180592341014228752322897 49635444255760671564242173)
  ·
    refine ⟨18613291595910251836590815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49635444255760671564242173 18613291595910251836590815)
    ·
      refine ⟨27919937393865377754886223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18613291595910251836590815 27919937393865377754886223)
      ·
        refine ⟨41879906090798066632329335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27919937393865377754886223 41879906090798066632329335)
        ·
          refine ⟨62819859136197099948494003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41879906090798066632329335 62819859136197099948494003)
          ·
            refine ⟨94229788704295649922741005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62819859136197099948494003 94229788704295649922741005)
            ·
              refine ⟨35336170764110868721027877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94229788704295649922741005 35336170764110868721027877)
              ·
                refine ⟨6625532018270787885192727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35336170764110868721027877 6625532018270787885192727)
                ·
                  refine ⟨9938298027406181827789091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6625532018270787885192727 9938298027406181827789091)
                  ·
                    refine ⟨14907447041109272741683637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9938298027406181827789091 14907447041109272741683637)
                    ·
                      refine ⟨1397573160103994319532841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14907447041109272741683637 1397573160103994319532841)
                      ·
                        rfl

theorem cell23_2721764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_2721764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721764 prefixEnd_2721764 := by exact prefixLift 2721764
  have htrace : WordTrace (prefixWord ++ tailWord_2721764) baseStart_2721764 baseEnd_2721764 := by
    simpa [prefixWord, tailWord_2721764, baseEnd_2721764] using wordTrace_append hprefix tailTrace_2721764
  have hstable : (prefixWord ++ tailWord_2721764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721764).length < 2 ^ (prefixWord ++ tailWord_2721764).sum := by decide
  have hdescent : baseEnd_2721764 < baseStart_2721764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721811 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 3]
def baseStart_2721811 : Nat := 118140960795 + 2721811 * 2 ^ 59
def prefixEnd_2721811 : Nat := 4983230072969 + 3 ^ 40 * 2721811 * 2
def baseEnd_2721811 : Nat := 1397597293694755635645125

theorem tailTrace_2721811 : CollatzResearch.WordTrace tailWord_2721811 prefixEnd_2721811 1397597293694755635645125 := by
  unfold tailWord_2721811
  simp only [CollatzResearch.WordTrace]
  refine ⟨99272602742351070155445287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66181735161567380103630191 99272602742351070155445287)
  ·
    refine ⟨148908904113526605233167931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99272602742351070155445287 148908904113526605233167931)
    ·
      refine ⟨223363356170289907849751897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148908904113526605233167931 223363356170289907849751897)
      ·
        refine ⟨167522517127717430887313923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223363356170289907849751897 167522517127717430887313923)
        ·
          refine ⟨251283775691576146330970885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167522517127717430887313923 251283775691576146330970885)
          ·
            refine ⟨47115707942170527437057041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251283775691576146330970885 47115707942170527437057041)
            ·
              refine ⟨35336780956627895577792781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47115707942170527437057041 35336780956627895577792781)
              ·
                refine ⟨13251292858735460841672293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35336780956627895577792781 13251292858735460841672293)
                ·
                  refine ⟨2484617411012898907813555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13251292858735460841672293 2484617411012898907813555)
                  ·
                    refine ⟨3726926116519348361720333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484617411012898907813555 3726926116519348361720333)
                    ·
                      refine ⟨1397597293694755635645125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3726926116519348361720333 1397597293694755635645125)
                      ·
                        rfl

theorem cell23_2721811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_2721811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721811 prefixEnd_2721811 := by exact prefixLift 2721811
  have htrace : WordTrace (prefixWord ++ tailWord_2721811) baseStart_2721811 baseEnd_2721811 := by
    simpa [prefixWord, tailWord_2721811, baseEnd_2721811] using wordTrace_append hprefix tailTrace_2721811
  have hstable : (prefixWord ++ tailWord_2721811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721811).length < 2 ^ (prefixWord ++ tailWord_2721811).sum := by decide
  have hdescent : baseEnd_2721811 < baseStart_2721811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721855 : List Nat := [1, 1, 2, 2, 3, 1, 6, 1, 1, 3, 2]
def baseStart_2721855 : Nat := 118140960795 + 2721855 * 2 ^ 59
def prefixEnd_2721855 : Nat := 4983230072969 + 3 ^ 40 * 2721855 * 2
def baseEnd_2721855 : Nat := 1397619886843553463494923

theorem tailTrace_2721855 : CollatzResearch.WordTrace tailWord_2721855 prefixEnd_2721855 1397619886843553463494923 := by
  unfold tailWord_2721855
  simp only [CollatzResearch.WordTrace]
  refine ⟨99274207554191665670047019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66182805036127777113364679 99274207554191665670047019)
  ·
    refine ⟨148911311331287498505070529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99274207554191665670047019 148911311331287498505070529)
    ·
      refine ⟨111683483498465623878802897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148911311331287498505070529 111683483498465623878802897)
      ·
        refine ⟨83762612623849217909102173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111683483498465623878802897 83762612623849217909102173)
        ·
          refine ⟨31410979733943456715913315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83762612623849217909102173 31410979733943456715913315)
          ·
            refine ⟨47116469600915185073869973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31410979733943456715913315 47116469600915185073869973)
            ·
              refine ⟨2208584512542899300337655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47116469600915185073869973 2208584512542899300337655)
              ·
                refine ⟨3312876768814348950506483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2208584512542899300337655 3312876768814348950506483)
                ·
                  refine ⟨4969315153221523425759725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3312876768814348950506483 4969315153221523425759725)
                  ·
                    refine ⟨1863493182458071284659897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4969315153221523425759725 1863493182458071284659897)
                    ·
                      refine ⟨1397619886843553463494923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863493182458071284659897 1397619886843553463494923)
                      ·
                        rfl

theorem cell23_2721855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_2721855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721855 prefixEnd_2721855 := by exact prefixLift 2721855
  have htrace : WordTrace (prefixWord ++ tailWord_2721855) baseStart_2721855 baseEnd_2721855 := by
    simpa [prefixWord, tailWord_2721855, baseEnd_2721855] using wordTrace_append hprefix tailTrace_2721855
  have hstable : (prefixWord ++ tailWord_2721855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721855).length < 2 ^ (prefixWord ++ tailWord_2721855).sum := by decide
  have hdescent : baseEnd_2721855 < baseStart_2721855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721914 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2721914 : Nat := 118140960795 + 2721914 * 2 ^ 59
def prefixEnd_2721914 : Nat := 4983230072969 + 3 ^ 40 * 2721914 * 2
def baseEnd_2721914 : Nat := 1397650182202168732657151

theorem tailTrace_2721914 : CollatzResearch.WordTrace tailWord_2721914 prefixEnd_2721914 1397650182202168732657151 := by
  unfold tailWord_2721914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24819089865244479686611199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66184239640651945830963197 24819089865244479686611199)
  ·
    refine ⟨37228634797866719529916799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24819089865244479686611199 37228634797866719529916799)
    ·
      refine ⟨55842952196800079294875199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37228634797866719529916799 55842952196800079294875199)
      ·
        refine ⟨83764428295200118942312799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55842952196800079294875199 83764428295200118942312799)
        ·
          refine ⟨125646642442800178413469199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83764428295200118942312799 125646642442800178413469199)
          ·
            refine ⟨188469963664200267620203799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125646642442800178413469199 188469963664200267620203799)
            ·
              refine ⟨282704945496300401430305699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188469963664200267620203799 282704945496300401430305699)
              ·
                refine ⟨424057418244450602145458549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282704945496300401430305699 424057418244450602145458549)
                ·
                  refine ⟨39755382960417243951136739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 424057418244450602145458549 39755382960417243951136739)
                  ·
                    refine ⟨59633074440625865926705109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39755382960417243951136739 59633074440625865926705109)
                    ·
                      refine ⟨1397650182202168732657151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59633074440625865926705109 1397650182202168732657151)
                      ·
                        rfl

theorem cell23_2721914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2721914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721914 prefixEnd_2721914 := by exact prefixLift 2721914
  have htrace : WordTrace (prefixWord ++ tailWord_2721914) baseStart_2721914 baseEnd_2721914 := by
    simpa [prefixWord, tailWord_2721914, baseEnd_2721914] using wordTrace_append hprefix tailTrace_2721914
  have hstable : (prefixWord ++ tailWord_2721914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721914).length < 2 ^ (prefixWord ++ tailWord_2721914).sum := by decide
  have hdescent : baseEnd_2721914 < baseStart_2721914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721925 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 5]
def baseStart_2721925 : Nat := 118140960795 + 2721925 * 2 ^ 59
def prefixEnd_2721925 : Nat := 4983230072969 + 3 ^ 40 * 2721925 * 2
def baseEnd_2721925 : Nat := 155295092276596465513289

theorem tailTrace_2721925 : CollatzResearch.WordTrace tailWord_2721925 prefixEnd_2721925 155295092276596465513289 := by
  unfold tailWord_2721925
  simp only [CollatzResearch.WordTrace]
  refine ⟨99276760663938067625095229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66184507109292045083396819 99276760663938067625095229)
  ·
    refine ⟨37228785248976775359410711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99276760663938067625095229 37228785248976775359410711)
    ·
      refine ⟨55843177873465163039116067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37228785248976775359410711 55843177873465163039116067)
      ·
        refine ⟨83764766810197744558674101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55843177873465163039116067 83764766810197744558674101)
        ·
          refine ⟨7852946888456038552375697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83764766810197744558674101 7852946888456038552375697)
          ·
            refine ⟨5889710166342028914281773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7852946888456038552375697 5889710166342028914281773)
            ·
              refine ⟨2208641312378260842855665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5889710166342028914281773 2208641312378260842855665)
              ·
                refine ⟨1656480984283695632141749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208641312378260842855665 1656480984283695632141749)
                ·
                  refine ⟨155295092276596465513289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1656480984283695632141749 155295092276596465513289)
                  ·
                    rfl

theorem cell23_2721925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_2721925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721925 prefixEnd_2721925 := by exact prefixLift 2721925
  have htrace : WordTrace (prefixWord ++ tailWord_2721925) baseStart_2721925 baseEnd_2721925 := by
    simpa [prefixWord, tailWord_2721925, baseEnd_2721925] using wordTrace_append hprefix tailTrace_2721925
  have hstable : (prefixWord ++ tailWord_2721925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721925).length < 2 ^ (prefixWord ++ tailWord_2721925).sum := by decide
  have hdescent : baseEnd_2721925 < baseStart_2721925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721941 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2721941 : Nat := 118140960795 + 2721941 * 2 ^ 59
def prefixEnd_2721941 : Nat := 4983230072969 + 3 ^ 40 * 2721941 * 2
def baseEnd_2721941 : Nat := 1397664046179840127019527

theorem tailTrace_2721941 : CollatzResearch.WordTrace tailWord_2721941 prefixEnd_2721941 1397664046179840127019527 := by
  unfold tailWord_2721941
  simp only [CollatzResearch.WordTrace]
  refine ⟨99277344231880102357677677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66184896154586734905118451 99277344231880102357677677)
  ·
    refine ⟨37229004086955038384129129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99277344231880102357677677 37229004086955038384129129)
    ·
      refine ⟨27921753065216278788096847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37229004086955038384129129 27921753065216278788096847)
      ·
        refine ⟨41882629597824418182145271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27921753065216278788096847 41882629597824418182145271)
        ·
          refine ⟨62823944396736627273217907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41882629597824418182145271 62823944396736627273217907)
          ·
            refine ⟨94235916595104940909826861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62823944396736627273217907 94235916595104940909826861)
            ·
              refine ⟨35338468723164352841185073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94235916595104940909826861 35338468723164352841185073)
              ·
                refine ⟨26503851542373264630888805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35338468723164352841185073 26503851542373264630888805)
                ·
                  refine ⟨4969472164194987118291651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26503851542373264630888805 4969472164194987118291651)
                  ·
                    refine ⟨7454208246292480677437477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4969472164194987118291651 7454208246292480677437477)
                    ·
                      refine ⟨1397664046179840127019527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7454208246292480677437477 1397664046179840127019527)
                      ·
                        rfl

theorem cell23_2721941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2721941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721941 prefixEnd_2721941 := by exact prefixLift 2721941
  have htrace : WordTrace (prefixWord ++ tailWord_2721941) baseStart_2721941 baseEnd_2721941 := by
    simpa [prefixWord, tailWord_2721941, baseEnd_2721941] using wordTrace_append hprefix tailTrace_2721941
  have hstable : (prefixWord ++ tailWord_2721941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721941).length < 2 ^ (prefixWord ++ tailWord_2721941).sum := by decide
  have hdescent : baseEnd_2721941 < baseStart_2721941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721978 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_2721978 : Nat := 118140960795 + 2721978 * 2 ^ 59
def prefixEnd_2721978 : Nat := 4983230072969 + 3 ^ 40 * 2721978 * 2
def baseEnd_2721978 : Nat := 1397683044964056482256857

theorem tailTrace_2721978 : CollatzResearch.WordTrace tailWord_2721978 prefixEnd_2721978 1397683044964056482256857 := by
  unfold tailWord_2721978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24819673433186514419193647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66185795821830705117849725 24819673433186514419193647)
  ·
    refine ⟨37229510149779771628790471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24819673433186514419193647 37229510149779771628790471)
    ·
      refine ⟨55844265224669657443185707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37229510149779771628790471 55844265224669657443185707)
      ·
        refine ⟨83766397837004486164778561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55844265224669657443185707 83766397837004486164778561)
        ·
          refine ⟨62824798377753364623583921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83766397837004486164778561 62824798377753364623583921)
          ·
            refine ⟨47118598783315023467687941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62824798377753364623583921 47118598783315023467687941)
            ·
              refine ⟨8834737271871566900191489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47118598783315023467687941 8834737271871566900191489)
              ·
                refine ⟨6626052953903675175143617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8834737271871566900191489 6626052953903675175143617)
                ·
                  refine ⟨4969539715427756381357713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6626052953903675175143617 4969539715427756381357713)
                  ·
                    refine ⟨3727154786570817286018285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4969539715427756381357713 3727154786570817286018285)
                    ·
                      refine ⟨1397683044964056482256857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3727154786570817286018285 1397683044964056482256857)
                      ·
                        rfl

theorem cell23_2721978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_2721978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721978 prefixEnd_2721978 := by exact prefixLift 2721978
  have htrace : WordTrace (prefixWord ++ tailWord_2721978) baseStart_2721978 baseEnd_2721978 := by
    simpa [prefixWord, tailWord_2721978, baseEnd_2721978] using wordTrace_append hprefix tailTrace_2721978
  have hstable : (prefixWord ++ tailWord_2721978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721978).length < 2 ^ (prefixWord ++ tailWord_2721978).sum := by decide
  have hdescent : baseEnd_2721978 < baseStart_2721978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721991 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_2721991 : Nat := 118140960795 + 2721991 * 2 ^ 59
def prefixEnd_2721991 : Nat := 4983230072969 + 3 ^ 40 * 2721991 * 2
def baseEnd_2721991 : Nat := 1397689720212564931394297

theorem tailTrace_2721991 : CollatzResearch.WordTrace tailWord_2721991 prefixEnd_2721991 1397689720212564931394297 := by
  unfold tailWord_2721991
  simp only [CollatzResearch.WordTrace]
  refine ⟨99279167881698960896997827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66186111921132640597998551 99279167881698960896997827)
  ·
    refine ⟨148918751822548441345496741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99279167881698960896997827 148918751822548441345496741)
    ·
      refine ⟨27922265966727832752280639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148918751822548441345496741 27922265966727832752280639)
      ·
        refine ⟨41883398950091749128420959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27922265966727832752280639 41883398950091749128420959)
        ·
          refine ⟨62825098425137623692631439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41883398950091749128420959 62825098425137623692631439)
          ·
            refine ⟨94237647637706435538947159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62825098425137623692631439 94237647637706435538947159)
            ·
              refine ⟨141356471456559653308420739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94237647637706435538947159 141356471456559653308420739)
              ·
                refine ⟨212034707184839479962631109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141356471456559653308420739 212034707184839479962631109)
                ·
                  refine ⟨39756507597157402492993333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212034707184839479962631109 39756507597157402492993333)
                  ·
                    refine ⟨3727172587233506483718125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39756507597157402492993333 3727172587233506483718125)
                    ·
                      refine ⟨1397689720212564931394297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3727172587233506483718125 1397689720212564931394297)
                      ·
                        rfl

theorem cell23_2721991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_2721991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721991 prefixEnd_2721991 := by exact prefixLift 2721991
  have htrace : WordTrace (prefixWord ++ tailWord_2721991) baseStart_2721991 baseEnd_2721991 := by
    simpa [prefixWord, tailWord_2721991, baseEnd_2721991] using wordTrace_append hprefix tailTrace_2721991
  have hstable : (prefixWord ++ tailWord_2721991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721991).length < 2 ^ (prefixWord ++ tailWord_2721991).sum := by decide
  have hdescent : baseEnd_2721991 < baseStart_2721991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2721998 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_2721998 : Nat := 118140960795 + 2721998 * 2 ^ 59
def prefixEnd_2721998 : Nat := 4983230072969 + 3 ^ 40 * 2721998 * 2
def baseEnd_2721998 : Nat := 155299257175238489334085

theorem tailTrace_2721998 : CollatzResearch.WordTrace tailWord_2721998 prefixEnd_2721998 155299257175238489334085 := by
  unfold tailWord_2721998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12409927899084200136562831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66186282128449067395001765 12409927899084200136562831)
  ·
    refine ⟨18614891848626300204844247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12409927899084200136562831 18614891848626300204844247)
    ·
      refine ⟨27922337772939450307266371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18614891848626300204844247 27922337772939450307266371)
      ·
        refine ⟨41883506659409175460899557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27922337772939450307266371 41883506659409175460899557)
        ·
          refine ⟨7853157498639220398918667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41883506659409175460899557 7853157498639220398918667)
          ·
            refine ⟨11779736247958830598378001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853157498639220398918667 11779736247958830598378001)
            ·
              refine ⟨8834802185969122948783501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11779736247958830598378001 8834802185969122948783501)
              ·
                refine ⟨3313050819738421105793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8834802185969122948783501 3313050819738421105793813)
                ·
                  refine ⟨155299257175238489334085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3313050819738421105793813 155299257175238489334085)
                  ·
                    rfl

theorem cell23_2721998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_2721998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2721998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2721998 prefixEnd_2721998 := by exact prefixLift 2721998
  have htrace : WordTrace (prefixWord ++ tailWord_2721998) baseStart_2721998 baseEnd_2721998 := by
    simpa [prefixWord, tailWord_2721998, baseEnd_2721998] using wordTrace_append hprefix tailTrace_2721998
  have hstable : (prefixWord ++ tailWord_2721998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2721998).length < 2 ^ (prefixWord ++ tailWord_2721998).sum := by decide
  have hdescent : baseEnd_2721998 < baseStart_2721998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2721998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722012 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2722012 : Nat := 118140960795 + 2722012 * 2 ^ 59
def prefixEnd_2722012 : Nat := 4983230072969 + 3 ^ 40 * 2722012 * 2
def baseEnd_2722012 : Nat := 1397700503306309349231701

theorem tailTrace_2722012 : CollatzResearch.WordTrace tailWord_2722012 prefixEnd_2722012 1397700503306309349231701 := by
  unfold tailWord_2722012
  simp only [CollatzResearch.WordTrace]
  refine ⟨49639966907311440741756145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66186622543081920989008193 49639966907311440741756145)
  ·
    refine ⟨37229975180483580556317109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49639966907311440741756145 37229975180483580556317109)
    ·
      refine ⟨3490310173170335677154729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37229975180483580556317109 3490310173170335677154729)
      ·
        refine ⟨2617732629877751757866047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3490310173170335677154729 2617732629877751757866047)
        ·
          refine ⟨3926598944816627636799071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617732629877751757866047 3926598944816627636799071)
          ·
            refine ⟨5889898417224941455198607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926598944816627636799071 5889898417224941455198607)
            ·
              refine ⟨8834847625837412182797911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5889898417224941455198607 8834847625837412182797911)
              ·
                refine ⟨13252271438756118274196867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8834847625837412182797911 13252271438756118274196867)
                ·
                  refine ⟨19878407158134177411295301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13252271438756118274196867 19878407158134177411295301)
                  ·
                    refine ⟨3727201342150158264617869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19878407158134177411295301 3727201342150158264617869)
                    ·
                      refine ⟨1397700503306309349231701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3727201342150158264617869 1397700503306309349231701)
                      ·
                        rfl

theorem cell23_2722012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2722012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722012 prefixEnd_2722012 := by exact prefixLift 2722012
  have htrace : WordTrace (prefixWord ++ tailWord_2722012) baseStart_2722012 baseEnd_2722012 := by
    simpa [prefixWord, tailWord_2722012, baseEnd_2722012] using wordTrace_append hprefix tailTrace_2722012
  have hstable : (prefixWord ++ tailWord_2722012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722012).length < 2 ^ (prefixWord ++ tailWord_2722012).sum := by decide
  have hdescent : baseEnd_2722012 < baseStart_2722012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722019 : List Nat := [1, 1, 1, 8, 1, 1, 2, 3, 1, 4]
def baseStart_2722019 : Nat := 118140960795 + 2722019 * 2 ^ 59
def prefixEnd_2722019 : Nat := 4983230072969 + 3 ^ 40 * 2722019 * 2
def baseEnd_2722019 : Nat := 465901365890296940614723

theorem tailTrace_2722019 : CollatzResearch.WordTrace tailWord_2722019 prefixEnd_2722019 465901365890296940614723 := by
  unfold tailWord_2722019
  simp only [CollatzResearch.WordTrace]
  refine ⟨99280189125597521679017111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66186792750398347786011407 99280189125597521679017111)
  ·
    refine ⟨148920283688396282518525667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99280189125597521679017111 148920283688396282518525667)
    ·
      refine ⟨223380425532594423777788501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148920283688396282518525667 223380425532594423777788501)
      ·
        refine ⟨2617739361710090903645959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 223380425532594423777788501 2617739361710090903645959)
        ·
          refine ⟨3926609042565136355468939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617739361710090903645959 3926609042565136355468939)
          ·
            refine ⟨5889913563847704533203409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926609042565136355468939 5889913563847704533203409)
            ·
              refine ⟨4417435172885778399902557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5889913563847704533203409 4417435172885778399902557)
              ·
                refine ⟨1656538189832166899963459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4417435172885778399902557 1656538189832166899963459)
                ·
                  refine ⟨2484807284748250349945189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656538189832166899963459 2484807284748250349945189)
                  ·
                    refine ⟨465901365890296940614723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2484807284748250349945189 465901365890296940614723)
                    ·
                      rfl

theorem cell23_2722019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 1, 4].length) (baseStart_2722019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722019 prefixEnd_2722019 := by exact prefixLift 2722019
  have htrace : WordTrace (prefixWord ++ tailWord_2722019) baseStart_2722019 baseEnd_2722019 := by
    simpa [prefixWord, tailWord_2722019, baseEnd_2722019] using wordTrace_append hprefix tailTrace_2722019
  have hstable : (prefixWord ++ tailWord_2722019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722019).length < 2 ^ (prefixWord ++ tailWord_2722019).sum := by decide
  have hdescent : baseEnd_2722019 < baseStart_2722019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722028 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_2722028 : Nat := 118140960795 + 2722028 * 2 ^ 59
def prefixEnd_2722028 : Nat := 4983230072969 + 3 ^ 40 * 2722028 * 2
def baseEnd_2722028 : Nat := 465902906332260428877209

theorem tailTrace_2722028 : CollatzResearch.WordTrace tailWord_2722028 prefixEnd_2722028 465902906332260428877209 := by
  unfold tailWord_2722028
  simp only [CollatzResearch.WordTrace]
  refine ⟨49640258691282458108047369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66187011588376610810729825 49640258691282458108047369)
  ·
    refine ⟨37230194018461843581035527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49640258691282458108047369 37230194018461843581035527)
    ·
      refine ⟨55845291027692765371553291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37230194018461843581035527 55845291027692765371553291)
      ·
        refine ⟨83767936541539148057329937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55845291027692765371553291 83767936541539148057329937)
        ·
          refine ⟨62825952406154361042997453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83767936541539148057329937 62825952406154361042997453)
          ·
            refine ⟨23559732152307885391124045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62825952406154361042997453 23559732152307885391124045)
            ·
              refine ⟨8834899557115457021671517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23559732152307885391124045 8834899557115457021671517)
              ·
                refine ⟨3313087333918296383126819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8834899557115457021671517 3313087333918296383126819)
                ·
                  refine ⟨4969631000877444574690229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313087333918296383126819 4969631000877444574690229)
                  ·
                    refine ⟨465902906332260428877209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4969631000877444574690229 465902906332260428877209)
                    ·
                      rfl

theorem cell23_2722028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_2722028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722028 prefixEnd_2722028 := by exact prefixLift 2722028
  have htrace : WordTrace (prefixWord ++ tailWord_2722028) baseStart_2722028 baseEnd_2722028 := by
    simpa [prefixWord, tailWord_2722028, baseEnd_2722028] using wordTrace_append hprefix tailTrace_2722028
  have hstable : (prefixWord ++ tailWord_2722028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722028).length < 2 ^ (prefixWord ++ tailWord_2722028).sum := by decide
  have hdescent : baseEnd_2722028 < baseStart_2722028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722042 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3]
def baseStart_2722042 : Nat := 118140960795 + 2722042 * 2 ^ 59
def prefixEnd_2722042 : Nat := 4983230072969 + 3 ^ 40 * 2722042 * 2
def baseEnd_2722042 : Nat := 1397715907725944231856563

theorem tailTrace_2722042 : CollatzResearch.WordTrace tailWord_2722042 prefixEnd_2722042 1397715907725944231856563 := by
  unfold tailWord_2722042
  simp only [CollatzResearch.WordTrace]
  refine ⟨24820257001128549151776095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66187352003009464404736253 24820257001128549151776095)
  ·
    refine ⟨37230385501692823727664143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24820257001128549151776095 37230385501692823727664143)
    ·
      refine ⟨55845578252539235591496215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37230385501692823727664143 55845578252539235591496215)
      ·
        refine ⟨83768367378808853387244323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55845578252539235591496215 83768367378808853387244323)
        ·
          refine ⟨125652551068213280080866485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83768367378808853387244323 125652551068213280080866485)
          ·
            refine ⟨11779926662644995007581233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125652551068213280080866485 11779926662644995007581233)
            ·
              refine ⟨8834944996983746255685925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11779926662644995007581233 8834944996983746255685925)
              ·
                refine ⟨1656552186934452422941111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8834944996983746255685925 1656552186934452422941111)
                ·
                  refine ⟨2484828280401678634411667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656552186934452422941111 2484828280401678634411667)
                  ·
                    refine ⟨3727242420602517951617501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484828280401678634411667 3727242420602517951617501)
                    ·
                      refine ⟨1397715907725944231856563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3727242420602517951617501 1397715907725944231856563)
                      ·
                        rfl

theorem cell23_2722042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_2722042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722042 prefixEnd_2722042 := by exact prefixLift 2722042
  have htrace : WordTrace (prefixWord ++ tailWord_2722042) baseStart_2722042 baseEnd_2722042 := by
    simpa [prefixWord, tailWord_2722042, baseEnd_2722042] using wordTrace_append hprefix tailTrace_2722042
  have hstable : (prefixWord ++ tailWord_2722042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722042).length < 2 ^ (prefixWord ++ tailWord_2722042).sum := by decide
  have hdescent : baseEnd_2722042 < baseStart_2722042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722058 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_2722058 : Nat := 118140960795 + 2722058 * 2 ^ 59
def prefixEnd_2722058 : Nat := 4983230072969 + 3 ^ 40 * 2722058 * 2
def baseEnd_2722058 : Nat := 465908041138805389752163

theorem tailTrace_2722058 : CollatzResearch.WordTrace tailWord_2722058 prefixEnd_2722058 465908041138805389752163 := by
  unfold tailWord_2722058
  simp only [CollatzResearch.WordTrace]
  refine ⟨24820402893114057834921707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66187741048304154226457885 24820402893114057834921707)
  ·
    refine ⟨37230604339671086752382561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24820402893114057834921707 37230604339671086752382561)
    ·
      refine ⟨27922953254753315064286921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37230604339671086752382561 27922953254753315064286921)
      ·
        refine ⟨20942214941064986298215191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27922953254753315064286921 20942214941064986298215191)
        ·
          refine ⟨31413322411597479447322787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20942214941064986298215191 31413322411597479447322787)
          ·
            refine ⟨47119983617396219170984181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31413322411597479447322787 47119983617396219170984181)
            ·
              refine ⟨4417498464130895547279767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47119983617396219170984181 4417498464130895547279767)
              ·
                refine ⟨6626247696196343320919651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417498464130895547279767 6626247696196343320919651)
                ·
                  refine ⟨9939371544294514981379477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6626247696196343320919651 9939371544294514981379477)
                  ·
                    refine ⟨465908041138805389752163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9939371544294514981379477 465908041138805389752163)
                    ·
                      rfl

theorem cell23_2722058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_2722058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722058 prefixEnd_2722058 := by exact prefixLift 2722058
  have htrace : WordTrace (prefixWord ++ tailWord_2722058) baseStart_2722058 baseEnd_2722058 := by
    simpa [prefixWord, tailWord_2722058, baseEnd_2722058] using wordTrace_append hprefix tailTrace_2722058
  have hstable : (prefixWord ++ tailWord_2722058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722058).length < 2 ^ (prefixWord ++ tailWord_2722058).sum := by decide
  have hdescent : baseEnd_2722058 < baseStart_2722058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722065 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_2722065 : Nat := 118140960795 + 2722065 * 2 ^ 59
def prefixEnd_2722065 : Nat := 4983230072969 + 3 ^ 40 * 2722065 * 2
def baseEnd_2722065 : Nat := 1397727717780997641868957

theorem tailTrace_2722065 : CollatzResearch.WordTrace tailWord_2722065 prefixEnd_2722065 1397727717780997641868957 := by
  unfold tailWord_2722065
  simp only [CollatzResearch.WordTrace]
  refine ⟨99281866883430871535191649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66187911255620581023461099 99281866883430871535191649)
  ·
    refine ⟨74461400162573153651393737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99281866883430871535191649 74461400162573153651393737)
    ·
      refine ⟨55846050121929865238545303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74461400162573153651393737 55846050121929865238545303)
      ·
        refine ⟨83769075182894797857817955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55846050121929865238545303 83769075182894797857817955)
        ·
          refine ⟨125653612774342196786726933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83769075182894797857817955 125653612774342196786726933)
          ·
            refine ⟨5890013098797290474377825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125653612774342196786726933 5890013098797290474377825)
            ·
              refine ⟨4417509824097967855783369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5890013098797290474377825 4417509824097967855783369)
              ·
                refine ⟨3313132368073475891837527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417509824097967855783369 3313132368073475891837527)
                ·
                  refine ⟨4969698552110213837756291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313132368073475891837527 4969698552110213837756291)
                  ·
                    refine ⟨7454547828165320756634437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4969698552110213837756291 7454547828165320756634437)
                    ·
                      refine ⟨1397727717780997641868957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7454547828165320756634437 1397727717780997641868957)
                      ·
                        rfl

theorem cell23_2722065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_2722065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722065 prefixEnd_2722065 := by exact prefixLift 2722065
  have htrace : WordTrace (prefixWord ++ tailWord_2722065) baseStart_2722065 baseEnd_2722065 := by
    simpa [prefixWord, tailWord_2722065, baseEnd_2722065] using wordTrace_append hprefix tailTrace_2722065
  have hstable : (prefixWord ++ tailWord_2722065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722065).length < 2 ^ (prefixWord ++ tailWord_2722065).sum := by decide
  have hdescent : baseEnd_2722065 < baseStart_2722065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722085 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_2722085 : Nat := 118140960795 + 2722085 * 2 ^ 59
def prefixEnd_2722085 : Nat := 4983230072969 + 3 ^ 40 * 2722085 * 2
def baseEnd_2722085 : Nat := 1397737987394087563618865

theorem tailTrace_2722085 : CollatzResearch.WordTrace tailWord_2722085 prefixEnd_2722085 1397737987394087563618865 := by
  unfold tailWord_2722085
  simp only [CollatzResearch.WordTrace]
  refine ⟨99282596343358414950919709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66188397562238943300613139 99282596343358414950919709)
  ·
    refine ⟨37230973628759405606594891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99282596343358414950919709 37230973628759405606594891)
    ·
      refine ⟨55846460443139108409892337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37230973628759405606594891 55846460443139108409892337)
      ·
        refine ⟨41884845332354331307419253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55846460443139108409892337 41884845332354331307419253)
        ·
          refine ⟨3926704249908218560070555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41884845332354331307419253 3926704249908218560070555)
          ·
            refine ⟨5890056374862327840105833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926704249908218560070555 5890056374862327840105833)
            ·
              refine ⟨4417542281146745880079375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5890056374862327840105833 4417542281146745880079375)
              ·
                refine ⟨6626313421720118820119063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4417542281146745880079375 6626313421720118820119063)
                ·
                  refine ⟨9939470132580178230178595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6626313421720118820119063 9939470132580178230178595)
                  ·
                    refine ⟨14909205198870267345267893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9939470132580178230178595 14909205198870267345267893)
                    ·
                      refine ⟨1397737987394087563618865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14909205198870267345267893 1397737987394087563618865)
                      ·
                        rfl

theorem cell23_2722085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_2722085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722085 prefixEnd_2722085 := by exact prefixLift 2722085
  have htrace : WordTrace (prefixWord ++ tailWord_2722085) baseStart_2722085 baseEnd_2722085 := by
    simpa [prefixWord, tailWord_2722085, baseEnd_2722085] using wordTrace_append hprefix tailTrace_2722085
  have hstable : (prefixWord ++ tailWord_2722085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722085).length < 2 ^ (prefixWord ++ tailWord_2722085).sum := by decide
  have hdescent : baseEnd_2722085 < baseStart_2722085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722093 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2722093 : Nat := 118140960795 + 2722093 * 2 ^ 59
def prefixEnd_2722093 : Nat := 4983230072969 + 3 ^ 40 * 2722093 * 2
def baseEnd_2722093 : Nat := 1397742095239323532318829

theorem tailTrace_2722093 : CollatzResearch.WordTrace tailWord_2722093 prefixEnd_2722093 1397742095239323532318829 := by
  unfold tailWord_2722093
  simp only [CollatzResearch.WordTrace]
  refine ⟨99282888127329432317210933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66188592084886288211473955 99282888127329432317210933)
  ·
    refine ⟨9307770761937134279738525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99282888127329432317210933 9307770761937134279738525)
    ·
      refine ⟨3490414035726425354901947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9307770761937134279738525 3490414035726425354901947)
      ·
        refine ⟨5235621053589638032352921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490414035726425354901947 5235621053589638032352921)
        ·
          refine ⟨3926715790192228524264691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5235621053589638032352921 3926715790192228524264691)
          ·
            refine ⟨5890073685288342786397037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926715790192228524264691 5890073685288342786397037)
            ·
              refine ⟨2208777631983128544898889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5890073685288342786397037 2208777631983128544898889)
              ·
                refine ⟨1656583223987346408674167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208777631983128544898889 1656583223987346408674167)
                ·
                  refine ⟨2484874835981019613011251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656583223987346408674167 2484874835981019613011251)
                  ·
                    refine ⟨3727312253971529419516877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2484874835981019613011251 3727312253971529419516877)
                    ·
                      refine ⟨1397742095239323532318829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3727312253971529419516877 1397742095239323532318829)
                      ·
                        rfl

theorem cell23_2722093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2722093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722093 prefixEnd_2722093 := by exact prefixLift 2722093
  have htrace : WordTrace (prefixWord ++ tailWord_2722093) baseStart_2722093 baseEnd_2722093 := by
    simpa [prefixWord, tailWord_2722093, baseEnd_2722093] using wordTrace_append hprefix tailTrace_2722093
  have hstable : (prefixWord ++ tailWord_2722093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722093).length < 2 ^ (prefixWord ++ tailWord_2722093).sum := by decide
  have hdescent : baseEnd_2722093 < baseStart_2722093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722116 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2722116 : Nat := 118140960795 + 2722116 * 2 ^ 59
def prefixEnd_2722116 : Nat := 4983230072969 + 3 ^ 40 * 2722116 * 2
def baseEnd_2722116 : Nat := 1397753905294376942331223

theorem tailTrace_2722116 : CollatzResearch.WordTrace tailWord_2722116 prefixEnd_2722116 1397753905294376942331223 := by
  unfold tailWord_2722116
  simp only [CollatzResearch.WordTrace]
  refine ⟨49641863503123053622649101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66189151337497404830198801 49641863503123053622649101)
  ·
    refine ⟨18615698813671145108493413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49641863503123053622649101 18615698813671145108493413)
    ·
      refine ⟨3490443527563339707842515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18615698813671145108493413 3490443527563339707842515)
      ·
        refine ⟨5235665291345009561763773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490443527563339707842515 5235665291345009561763773)
        ·
          refine ⟨1963374484254378585661415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5235665291345009561763773 1963374484254378585661415)
          ·
            refine ⟨2945061726381567878492123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963374484254378585661415 2945061726381567878492123)
            ·
              refine ⟨4417592589572351817738185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945061726381567878492123 4417592589572351817738185)
              ·
                refine ⟨3313194442179263863303639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4417592589572351817738185 3313194442179263863303639)
                ·
                  refine ⟨4969791663268895794955459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313194442179263863303639 4969791663268895794955459)
                  ·
                    refine ⟨7454687494903343692433189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4969791663268895794955459 7454687494903343692433189)
                    ·
                      refine ⟨1397753905294376942331223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7454687494903343692433189 1397753905294376942331223)
                      ·
                        rfl

theorem cell23_2722116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2722116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722116 prefixEnd_2722116 := by exact prefixLift 2722116
  have htrace : WordTrace (prefixWord ++ tailWord_2722116) baseStart_2722116 baseEnd_2722116 := by
    simpa [prefixWord, tailWord_2722116, baseEnd_2722116] using wordTrace_append hprefix tailTrace_2722116
  have hstable : (prefixWord ++ tailWord_2722116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722116).length < 2 ^ (prefixWord ++ tailWord_2722116).sum := by decide
  have hdescent : baseEnd_2722116 < baseStart_2722116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722121 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_2722121 : Nat := 118140960795 + 2722121 * 2 ^ 59
def prefixEnd_2722121 : Nat := 4983230072969 + 3 ^ 40 * 2722121 * 2
def baseEnd_2722121 : Nat := 1397756472697649422768699

theorem tailTrace_2722121 : CollatzResearch.WordTrace tailWord_2722121 prefixEnd_2722121 1397756472697649422768699 := by
  unfold tailWord_2722121
  simp only [CollatzResearch.WordTrace]
  refine ⟨99283909371227993099230217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66189272914151995399486811 99283909371227993099230217)
  ·
    refine ⟨74462932028420994824422663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99283909371227993099230217 74462932028420994824422663)
    ·
      refine ⟨111694398042631492236633995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74462932028420994824422663 111694398042631492236633995)
      ·
        refine ⟨167541597063947238354950993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111694398042631492236633995 167541597063947238354950993)
        ·
          refine ⟨125656197797960428766213245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167541597063947238354950993 125656197797960428766213245)
          ·
            refine ⟨47121074174235160787329967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125656197797960428766213245 47121074174235160787329967)
            ·
              refine ⟨70681611261352741180994951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47121074174235160787329967 70681611261352741180994951)
              ·
                refine ⟨106022416892029111771492427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70681611261352741180994951 106022416892029111771492427)
                ·
                  refine ⟨159033625338043667657238641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106022416892029111771492427 159033625338043667657238641)
                  ·
                    refine ⟨119275219003532750742928981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159033625338043667657238641 119275219003532750742928981)
                    ·
                      refine ⟨1397756472697649422768699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 119275219003532750742928981 1397756472697649422768699)
                      ·
                        rfl

theorem cell23_2722121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_2722121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722121 prefixEnd_2722121 := by exact prefixLift 2722121
  have htrace : WordTrace (prefixWord ++ tailWord_2722121) baseStart_2722121 baseEnd_2722121 := by
    simpa [prefixWord, tailWord_2722121, baseEnd_2722121] using wordTrace_append hprefix tailTrace_2722121
  have hstable : (prefixWord ++ tailWord_2722121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722121).length < 2 ^ (prefixWord ++ tailWord_2722121).sum := by decide
  have hdescent : baseEnd_2722121 < baseStart_2722121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722131 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 8]
def baseStart_2722131 : Nat := 118140960795 + 2722131 * 2 ^ 59
def prefixEnd_2722131 : Nat := 4983230072969 + 3 ^ 40 * 2722131 * 2
def baseEnd_2722131 : Nat := 465920535834731461214551

theorem tailTrace_2722131 : CollatzResearch.WordTrace tailWord_2722131 prefixEnd_2722131 465920535834731461214551 := by
  unfold tailWord_2722131
  simp only [CollatzResearch.WordTrace]
  refine ⟨99284274101191764807094247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66189516067461176538062831 99284274101191764807094247)
  ·
    refine ⟨148926411151787647210641371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99284274101191764807094247 148926411151787647210641371)
    ·
      refine ⟨223389616727681470815962057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148926411151787647210641371 223389616727681470815962057)
      ·
        refine ⟨167542212545761103111971543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223389616727681470815962057 167542212545761103111971543)
        ·
          refine ⟨251313318818641654667957315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167542212545761103111971543 251313318818641654667957315)
          ·
            refine ⟨376969978227962482001935973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251313318818641654667957315 376969978227962482001935973)
            ·
              refine ⟨70681870917742965375362995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 376969978227962482001935973 70681870917742965375362995)
              ·
                refine ⟨106022806376614448063044493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70681870917742965375362995 106022806376614448063044493)
                ·
                  refine ⟨39758552391230418023641685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106022806376614448063044493 39758552391230418023641685)
                  ·
                    refine ⟨465920535834731461214551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39758552391230418023641685 465920535834731461214551)
                    ·
                      rfl

theorem cell23_2722131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_2722131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722131 prefixEnd_2722131 := by exact prefixLift 2722131
  have htrace : WordTrace (prefixWord ++ tailWord_2722131) baseStart_2722131 baseEnd_2722131 := by
    simpa [prefixWord, tailWord_2722131, baseEnd_2722131] using wordTrace_append hprefix tailTrace_2722131
  have hstable : (prefixWord ++ tailWord_2722131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722131).length < 2 ^ (prefixWord ++ tailWord_2722131).sum := by decide
  have hdescent : baseEnd_2722131 < baseStart_2722131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722148 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_2722148 : Nat := 118140960795 + 2722148 * 2 ^ 59
def prefixEnd_2722148 : Nat := 4983230072969 + 3 ^ 40 * 2722148 * 2
def baseEnd_2722148 : Nat := 465923445558440272377025

theorem tailTrace_2722148 : CollatzResearch.WordTrace tailWord_2722148 prefixEnd_2722148 465923445558440272377025 := by
  unfold tailWord_2722148
  simp only [CollatzResearch.WordTrace]
  refine ⟨49642447071065088355231549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66189929428086784473642065 49642447071065088355231549)
  ·
    refine ⟨18615917651649408133211831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49642447071065088355231549 18615917651649408133211831)
    ·
      refine ⟨27923876477474112199817747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18615917651649408133211831 27923876477474112199817747)
      ·
        refine ⟨41885814716211168299726621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27923876477474112199817747 41885814716211168299726621)
        ·
          refine ⟨15707180518579188112397483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41885814716211168299726621 15707180518579188112397483)
          ·
            refine ⟨23560770777868782168596225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15707180518579188112397483 23560770777868782168596225)
            ·
              refine ⟨17670578083401586626447169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23560770777868782168596225 17670578083401586626447169)
              ·
                refine ⟨13252933562551189969835377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17670578083401586626447169 13252933562551189969835377)
                ·
                  refine ⟨9939700171913392477376533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13252933562551189969835377 9939700171913392477376533)
                  ·
                    refine ⟨465923445558440272377025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9939700171913392477376533 465923445558440272377025)
                    ·
                      rfl

theorem cell23_2722148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_2722148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722148 prefixEnd_2722148 := by exact prefixLift 2722148
  have htrace : WordTrace (prefixWord ++ tailWord_2722148) baseStart_2722148 baseEnd_2722148 := by
    simpa [prefixWord, tailWord_2722148, baseEnd_2722148] using wordTrace_append hprefix tailTrace_2722148
  have hstable : (prefixWord ++ tailWord_2722148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722148).length < 2 ^ (prefixWord ++ tailWord_2722148).sum := by decide
  have hdescent : baseEnd_2722148 < baseStart_2722148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722165 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2722165 : Nat := 118140960795 + 2722165 * 2 ^ 59
def prefixEnd_2722165 : Nat := 4983230072969 + 3 ^ 40 * 2722165 * 2
def baseEnd_2722165 : Nat := 465926355282149083539499

theorem tailTrace_2722165 : CollatzResearch.WordTrace tailWord_2722165 prefixEnd_2722165 465926355282149083539499 := by
  unfold tailWord_2722165
  simp only [CollatzResearch.WordTrace]
  refine ⟨99285514183068588613831949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66190342788712392409221299 99285514183068588613831949)
  ·
    refine ⟨37232067818650720730186981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99285514183068588613831949 37232067818650720730186981)
    ·
      refine ⟨6981012715997010136910059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37232067818650720730186981 6981012715997010136910059)
      ·
        refine ⟨10471519073995515205365089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6981012715997010136910059 10471519073995515205365089)
        ·
          refine ⟨7853639305496636404023817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10471519073995515205365089 7853639305496636404023817)
          ·
            refine ⟨5890229479122477303017863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7853639305496636404023817 5890229479122477303017863)
            ·
              refine ⟨8835344218683715954526795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890229479122477303017863 8835344218683715954526795)
              ·
                refine ⟨13253016328025573931790193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8835344218683715954526795 13253016328025573931790193)
                ·
                  refine ⟨9939762246019180448842645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13253016328025573931790193 9939762246019180448842645)
                  ·
                    refine ⟨465926355282149083539499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9939762246019180448842645 465926355282149083539499)
                    ·
                      rfl

theorem cell23_2722165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2722165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722165 prefixEnd_2722165 := by exact prefixLift 2722165
  have htrace : WordTrace (prefixWord ++ tailWord_2722165) baseStart_2722165 baseEnd_2722165 := by
    simpa [prefixWord, tailWord_2722165, baseEnd_2722165] using wordTrace_append hprefix tailTrace_2722165
  have hstable : (prefixWord ++ tailWord_2722165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722165).length < 2 ^ (prefixWord ++ tailWord_2722165).sum := by decide
  have hdescent : baseEnd_2722165 < baseStart_2722165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722206 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2722206 : Nat := 118140960795 + 2722206 * 2 ^ 59
def prefixEnd_2722206 : Nat := 4983230072969 + 3 ^ 40 * 2722206 * 2
def baseEnd_2722206 : Nat := 1397800118553281590205809

theorem tailTrace_2722206 : CollatzResearch.WordTrace tailWord_2722206 prefixEnd_2722206 1397800118553281590205809 := by
  unfold tailWord_2722206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410876196990006577009309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66191339717280035077382981 12410876196990006577009309)
  ·
    refine ⟨4654078573871252466378491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12410876196990006577009309 4654078573871252466378491)
    ·
      refine ⟨6981117860806878699567737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654078573871252466378491 6981117860806878699567737)
      ·
        refine ⟨5235838395605159024675803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6981117860806878699567737 5235838395605159024675803)
        ·
          refine ⟨7853757593407738537013705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5235838395605159024675803 7853757593407738537013705)
          ·
            refine ⟨5890318195055803902760279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7853757593407738537013705 5890318195055803902760279)
            ·
              refine ⟨8835477292583705854140419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890318195055803902760279 8835477292583705854140419)
              ·
                refine ⟨13253215938875558781210629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8835477292583705854140419 13253215938875558781210629)
                ·
                  refine ⟨2484977988539167271476993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13253215938875558781210629 2484977988539167271476993)
                  ·
                    refine ⟨1863733491404375453607745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2484977988539167271476993 1863733491404375453607745)
                    ·
                      refine ⟨1397800118553281590205809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863733491404375453607745 1397800118553281590205809)
                      ·
                        rfl

theorem cell23_2722206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2722206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722206 prefixEnd_2722206 := by exact prefixLift 2722206
  have htrace : WordTrace (prefixWord ++ tailWord_2722206) baseStart_2722206 baseEnd_2722206 := by
    simpa [prefixWord, tailWord_2722206, baseEnd_2722206] using wordTrace_append hprefix tailTrace_2722206
  have hstable : (prefixWord ++ tailWord_2722206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722206).length < 2 ^ (prefixWord ++ tailWord_2722206).sum := by decide
  have hdescent : baseEnd_2722206 < baseStart_2722206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722329 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 1, 1, 3]
def baseStart_2722329 : Nat := 118140960795 + 2722329 * 2 ^ 59
def prefixEnd_2722329 : Nat := 4983230072969 + 3 ^ 40 * 2722329 * 2
def baseEnd_2722329 : Nat := 1397863276673784608967743

theorem tailTrace_2722329 : CollatzResearch.WordTrace tailWord_2722329 prefixEnd_2722329 1397863276673784608967743 := by
  unfold tailWord_2722329
  simp only [CollatzResearch.WordTrace]
  refine ⟨99291495754474444622802041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66194330502982963081868027 99291495754474444622802041)
  ·
    refine ⟨74468621815855833467101531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99291495754474444622802041 74468621815855833467101531)
    ·
      refine ⟨111702932723783750200652297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74468621815855833467101531 111702932723783750200652297)
      ·
        refine ⟨83777199542837812650489223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111702932723783750200652297 83777199542837812650489223)
        ·
          refine ⟨125665799314256718975733835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83777199542837812650489223 125665799314256718975733835)
          ·
            refine ⟨188498698971385078463600753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125665799314256718975733835 188498698971385078463600753)
            ·
              refine ⟨141374024228538808847700565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188498698971385078463600753 141374024228538808847700565)
              ·
                refine ⟨1656726846428189166183991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 141374024228538808847700565 1656726846428189166183991)
                ·
                  refine ⟨2485090269642283749275987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1656726846428189166183991 2485090269642283749275987)
                  ·
                    refine ⟨3727635404463425623913981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2485090269642283749275987 3727635404463425623913981)
                    ·
                      refine ⟨1397863276673784608967743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3727635404463425623913981 1397863276673784608967743)
                      ·
                        rfl

theorem cell23_2722329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_2722329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722329 prefixEnd_2722329 := by exact prefixLift 2722329
  have htrace : WordTrace (prefixWord ++ tailWord_2722329) baseStart_2722329 baseEnd_2722329 := by
    simpa [prefixWord, tailWord_2722329, baseEnd_2722329] using wordTrace_append hprefix tailTrace_2722329
  have hstable : (prefixWord ++ tailWord_2722329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722329).length < 2 ^ (prefixWord ++ tailWord_2722329).sum := by decide
  have hdescent : baseEnd_2722329 < baseStart_2722329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722366 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2722366 : Nat := 118140960795 + 2722366 * 2 ^ 59
def prefixEnd_2722366 : Nat := 4983230072969 + 3 ^ 40 * 2722366 * 2
def baseEnd_2722366 : Nat := 465960758486000321401691

theorem tailTrace_2722366 : CollatzResearch.WordTrace tailWord_2722366 prefixEnd_2722366 465960758486000321401691 := by
  unfold tailWord_2722366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12411605656917549992737369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66195230170226933294599301 12411605656917549992737369)
  ·
    refine ⟨9308704242688162494553027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12411605656917549992737369 9308704242688162494553027)
    ·
      refine ⟨13963056364032243741829541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9308704242688162494553027 13963056364032243741829541)
      ·
        refine ⟨2618073068256045701593039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13963056364032243741829541 2618073068256045701593039)
        ·
          refine ⟨3927109602384068552389559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618073068256045701593039 3927109602384068552389559)
          ·
            refine ⟨5890664403576102828584339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927109602384068552389559 5890664403576102828584339)
            ·
              refine ⟨8835996605364154242876509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890664403576102828584339 8835996605364154242876509)
              ·
                refine ⟨3313498727011557841078691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8835996605364154242876509 3313498727011557841078691)
                ·
                  refine ⟨4970248090517336761618037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313498727011557841078691 4970248090517336761618037)
                  ·
                    refine ⟨465960758486000321401691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4970248090517336761618037 465960758486000321401691)
                    ·
                      rfl

theorem cell23_2722366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2722366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722366 prefixEnd_2722366 := by exact prefixLift 2722366
  have htrace : WordTrace (prefixWord ++ tailWord_2722366) baseStart_2722366 baseEnd_2722366 := by
    simpa [prefixWord, tailWord_2722366, baseEnd_2722366] using wordTrace_append hprefix tailTrace_2722366
  have hstable : (prefixWord ++ tailWord_2722366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722366).length < 2 ^ (prefixWord ++ tailWord_2722366).sum := by decide
  have hdescent : baseEnd_2722366 < baseStart_2722366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722369 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2722369 : Nat := 118140960795 + 2722369 * 2 ^ 59
def prefixEnd_2722369 : Nat := 4983230072969 + 3 ^ 40 * 2722369 * 2
def baseEnd_2722369 : Nat := 1397883815899964452467559

theorem tailTrace_2722369 : CollatzResearch.WordTrace tailWord_2722369 prefixEnd_2722369 1397883815899964452467559 := by
  unfold tailWord_2722369
  simp only [CollatzResearch.WordTrace]
  refine ⟨99292954674329531454258161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66195303116219687636172107 99292954674329531454258161)
  ·
    refine ⟨74469716005747148590693621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99292954674329531454258161 74469716005747148590693621)
    ·
      refine ⟨6981535875538795180377527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74469716005747148590693621 6981535875538795180377527)
      ·
        refine ⟨10472303813308192770566291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6981535875538795180377527 10472303813308192770566291)
        ·
          refine ⟨15708455719962289155849437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10472303813308192770566291 15708455719962289155849437)
          ·
            refine ⟨5890670894985858433443539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15708455719962289155849437 5890670894985858433443539)
            ·
              refine ⟨8836006342478787650165309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890670894985858433443539 8836006342478787650165309)
              ·
                refine ⟨3313502378429545368811991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8836006342478787650165309 3313502378429545368811991)
                ·
                  refine ⟨4970253567644318053217987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313502378429545368811991 4970253567644318053217987)
                  ·
                    refine ⟨7455380351466477079826981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4970253567644318053217987 7455380351466477079826981)
                    ·
                      refine ⟨1397883815899964452467559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7455380351466477079826981 1397883815899964452467559)
                      ·
                        rfl

theorem cell23_2722369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2722369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722369 prefixEnd_2722369 := by exact prefixLift 2722369
  have htrace : WordTrace (prefixWord ++ tailWord_2722369) baseStart_2722369 baseEnd_2722369 := by
    simpa [prefixWord, tailWord_2722369, baseEnd_2722369] using wordTrace_append hprefix tailTrace_2722369
  have hstable : (prefixWord ++ tailWord_2722369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722369).length < 2 ^ (prefixWord ++ tailWord_2722369).sum := by decide
  have hdescent : baseEnd_2722369 < baseStart_2722369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722375 : List Nat := [1, 1, 4, 1, 4, 2, 10]
def baseStart_2722375 : Nat := 118140960795 + 2722375 * 2 ^ 59
def prefixEnd_2722375 : Nat := 4983230072969 + 3 ^ 40 * 2722375 * 2
def baseEnd_2722375 : Nat := 17257862923257918876451

theorem tailTrace_2722375 : CollatzResearch.WordTrace tailWord_2722375 prefixEnd_2722375 17257862923257918876451 := by
  unfold tailWord_2722375
  simp only [CollatzResearch.WordTrace]
  refine ⟨99293173512307794478976579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66195449008205196319317719 99293173512307794478976579)
  ·
    refine ⟨148939760268461691718464869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99293173512307794478976579 148939760268461691718464869)
    ·
      refine ⟨27926205050336567197212163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148939760268461691718464869 27926205050336567197212163)
      ·
        refine ⟨41889307575504850795818245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27926205050336567197212163 41889307575504850795818245)
        ·
          refine ⟨7854245170407159524215921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41889307575504850795818245 7854245170407159524215921)
          ·
            refine ⟨5890683877805369643161941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7854245170407159524215921 5890683877805369643161941)
            ·
              refine ⟨17257862923257918876451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5890683877805369643161941 17257862923257918876451)
              ·
                rfl

theorem cell23_2722375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 10].length) (baseStart_2722375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722375 prefixEnd_2722375 := by exact prefixLift 2722375
  have htrace : WordTrace (prefixWord ++ tailWord_2722375) baseStart_2722375 baseEnd_2722375 := by
    simpa [prefixWord, tailWord_2722375, baseEnd_2722375] using wordTrace_append hprefix tailTrace_2722375
  have hstable : (prefixWord ++ tailWord_2722375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722375).length < 2 ^ (prefixWord ++ tailWord_2722375).sum := by decide
  have hdescent : baseEnd_2722375 < baseStart_2722375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722386 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_2722386 : Nat := 118140960795 + 2722386 * 2 ^ 59
def prefixEnd_2722386 : Nat := 4983230072969 + 3 ^ 40 * 2722386 * 2
def baseEnd_2722386 : Nat := 1397892545071090885954981

theorem tailTrace_2722386 : CollatzResearch.WordTrace tailWord_2722386 prefixEnd_2722386 1397892545071090885954981 := by
  unfold tailWord_2722386
  simp only [CollatzResearch.WordTrace]
  refine ⟨24823393678816985839406753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66195716476845295571751341 24823393678816985839406753)
  ·
    refine ⟨18617545259112739379555065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24823393678816985839406753 18617545259112739379555065)
    ·
      refine ⟨13963158944334554534666299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18617545259112739379555065 13963158944334554534666299)
      ·
        refine ⟨20944738416501831801999449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13963158944334554534666299 20944738416501831801999449)
        ·
          refine ⟨15708553812376373851499587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20944738416501831801999449 15708553812376373851499587)
          ·
            refine ⟨23562830718564560777249381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15708553812376373851499587 23562830718564560777249381)
            ·
              refine ⟨4418030759730855145734259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23562830718564560777249381 4418030759730855145734259)
              ·
                refine ⟨6627046139596282718601389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418030759730855145734259 6627046139596282718601389)
                ·
                  refine ⟨2485142302348606019475521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6627046139596282718601389 2485142302348606019475521)
                  ·
                    refine ⟨1863856726761454514606641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2485142302348606019475521 1863856726761454514606641)
                    ·
                      refine ⟨1397892545071090885954981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863856726761454514606641 1397892545071090885954981)
                      ·
                        rfl

theorem cell23_2722386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_2722386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722386 prefixEnd_2722386 := by exact prefixLift 2722386
  have htrace : WordTrace (prefixWord ++ tailWord_2722386) baseStart_2722386 baseEnd_2722386 := by
    simpa [prefixWord, tailWord_2722386, baseEnd_2722386] using wordTrace_append hprefix tailTrace_2722386
  have hstable : (prefixWord ++ tailWord_2722386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722386).length < 2 ^ (prefixWord ++ tailWord_2722386).sum := by decide
  have hdescent : baseEnd_2722386 < baseStart_2722386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722396 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_2722396 : Nat := 118140960795 + 2722396 * 2 ^ 59
def prefixEnd_2722396 : Nat := 4983230072969 + 3 ^ 40 * 2722396 * 2
def baseEnd_2722396 : Nat := 465965893292545282276645

theorem tailTrace_2722396 : CollatzResearch.WordTrace tailWord_2722396 prefixEnd_2722396 465965893292545282276645 := by
  unfold tailWord_2722396
  simp only [CollatzResearch.WordTrace]
  refine ⟨49646969722615857532745521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66195959630154476710327361 49646969722615857532745521)
  ·
    refine ⟨37235227291961893149559141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49646969722615857532745521 37235227291961893149559141)
    ·
      refine ⟨6981605117242854965542339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37235227291961893149559141 6981605117242854965542339)
      ·
        refine ⟨10472407675864282448313509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6981605117242854965542339 10472407675864282448313509)
        ·
          refine ⟨1963576439224552959058783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10472407675864282448313509 1963576439224552959058783)
          ·
            refine ⟨2945364658836829438588175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963576439224552959058783 2945364658836829438588175)
            ·
              refine ⟨4418046988255244157882263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945364658836829438588175 4418046988255244157882263)
              ·
                refine ⟨6627070482382866236823395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418046988255244157882263 6627070482382866236823395)
                ·
                  refine ⟨9940605723574299355235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627070482382866236823395 9940605723574299355235093)
                  ·
                    refine ⟨465965893292545282276645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9940605723574299355235093 465965893292545282276645)
                    ·
                      rfl

theorem cell23_2722396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_2722396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722396 prefixEnd_2722396 := by exact prefixLift 2722396
  have htrace : WordTrace (prefixWord ++ tailWord_2722396) baseStart_2722396 baseEnd_2722396 := by
    simpa [prefixWord, tailWord_2722396, baseEnd_2722396] using wordTrace_append hprefix tailTrace_2722396
  have hstable : (prefixWord ++ tailWord_2722396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722396).length < 2 ^ (prefixWord ++ tailWord_2722396).sum := by decide
  have hdescent : baseEnd_2722396 < baseStart_2722396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722415 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_2722415 : Nat := 118140960795 + 2722415 * 2 ^ 59
def prefixEnd_2722415 : Nat := 4983230072969 + 3 ^ 40 * 2722415 * 2
def baseEnd_2722415 : Nat := 1397907436010071272492347

theorem tailTrace_2722415 : CollatzResearch.WordTrace tailWord_2722415 prefixEnd_2722415 1397907436010071272492347 := by
  unfold tailWord_2722415
  simp only [CollatzResearch.WordTrace]
  refine ⟨99294632432162881310432699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66196421621441920873621799 99294632432162881310432699)
  ·
    refine ⟨148941948648244321965649049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99294632432162881310432699 148941948648244321965649049)
    ·
      refine ⟨111706461486183241474236787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148941948648244321965649049 111706461486183241474236787)
      ·
        refine ⟨167559692229274862211355181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111706461486183241474236787 167559692229274862211355181)
        ·
          refine ⟨62834884585978073329258193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167559692229274862211355181 62834884585978073329258193)
          ·
            refine ⟨47126163439483554996943645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62834884585978073329258193 47126163439483554996943645)
            ·
              refine ⟨17672311289806333123853867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47126163439483554996943645 17672311289806333123853867)
              ·
                refine ⟨26508466934709499685780801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17672311289806333123853867 26508466934709499685780801)
                ·
                  refine ⟨19881350201032124764335601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26508466934709499685780801 19881350201032124764335601)
                  ·
                    refine ⟨14911012650774093573251701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19881350201032124764335601 14911012650774093573251701)
                    ·
                      refine ⟨1397907436010071272492347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14911012650774093573251701 1397907436010071272492347)
                      ·
                        rfl

theorem cell23_2722415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_2722415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722415 prefixEnd_2722415 := by exact prefixLift 2722415
  have htrace : WordTrace (prefixWord ++ tailWord_2722415) baseStart_2722415 baseEnd_2722415 := by
    simpa [prefixWord, tailWord_2722415, baseEnd_2722415] using wordTrace_append hprefix tailTrace_2722415
  have hstable : (prefixWord ++ tailWord_2722415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722415).length < 2 ^ (prefixWord ++ tailWord_2722415).sum := by decide
  have hdescent : baseEnd_2722415 < baseStart_2722415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722435 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 4, 6]
def baseStart_2722435 : Nat := 118140960795 + 2722435 * 2 ^ 59
def prefixEnd_2722435 : Nat := 4983230072969 + 3 ^ 40 * 2722435 * 2
def baseEnd_2722435 : Nat := 465972568541053731414085

theorem tailTrace_2722435 : CollatzResearch.WordTrace tailWord_2722435 prefixEnd_2722435 465972568541053731414085 := by
  unfold tailWord_2722435
  simp only [CollatzResearch.WordTrace]
  refine ⟨99295361892090424726160759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66196907928060283150773839 99295361892090424726160759)
  ·
    refine ⟨148943042838135637089241139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99295361892090424726160759 148943042838135637089241139)
    ·
      refine ⟨223414564257203455633861709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148943042838135637089241139 223414564257203455633861709)
      ·
        refine ⟨83780461596451295862698141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223414564257203455633861709 83780461596451295862698141)
        ·
          refine ⟨31417673098669235948511803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83780461596451295862698141 31417673098669235948511803)
          ·
            refine ⟨47126509648003853922767705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31417673098669235948511803 47126509648003853922767705)
            ·
              refine ⟨35344882236002890442075779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47126509648003853922767705 35344882236002890442075779)
              ·
                refine ⟨53017323354004335663113669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35344882236002890442075779 53017323354004335663113669)
                ·
                  refine ⟨9940748128875812936833813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53017323354004335663113669 9940748128875812936833813)
                  ·
                    refine ⟨465972568541053731414085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9940748128875812936833813 465972568541053731414085)
                    ·
                      rfl

theorem cell23_2722435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 6].length) (baseStart_2722435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722435 prefixEnd_2722435 := by exact prefixLift 2722435
  have htrace : WordTrace (prefixWord ++ tailWord_2722435) baseStart_2722435 baseEnd_2722435 := by
    simpa [prefixWord, tailWord_2722435, baseEnd_2722435] using wordTrace_append hprefix tailTrace_2722435
  have hstable : (prefixWord ++ tailWord_2722435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722435).length < 2 ^ (prefixWord ++ tailWord_2722435).sum := by decide
  have hdescent : baseEnd_2722435 < baseStart_2722435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722493 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 2, 2, 2]
def baseStart_2722493 : Nat := 118140960795 + 2722493 * 2 ^ 59
def prefixEnd_2722493 : Nat := 4983230072969 + 3 ^ 40 * 2722493 * 2
def baseEnd_2722493 : Nat := 1397947487501121967316989

theorem tailTrace_2722493 : CollatzResearch.WordTrace tailWord_2722493 prefixEnd_2722493 1397947487501121967316989 := by
  unfold tailWord_2722493
  simp only [CollatzResearch.WordTrace]
  refine ⟨99297477325880300631772133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66198318217253533754514755 99297477325880300631772133)
  ·
    refine ⟨18618276998602556368457275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99297477325880300631772133 18618276998602556368457275)
    ·
      refine ⟨27927415497903834552685913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18618276998602556368457275 27927415497903834552685913)
      ·
        refine ⟨20945561623427875914514435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27927415497903834552685913 20945561623427875914514435)
        ·
          refine ⟨31418342435141813871771653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20945561623427875914514435 31418342435141813871771653)
          ·
            refine ⟨5890939206589090100957185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31418342435141813871771653 5890939206589090100957185)
            ·
              refine ⟨4418204404941817575717889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5890939206589090100957185 4418204404941817575717889)
              ·
                refine ⟨3313653303706363181788417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418204404941817575717889 3313653303706363181788417)
                ·
                  refine ⟨2485239977779772386341313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3313653303706363181788417 2485239977779772386341313)
                  ·
                    refine ⟨1863929983334829289755985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2485239977779772386341313 1863929983334829289755985)
                    ·
                      refine ⟨1397947487501121967316989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1863929983334829289755985 1397947487501121967316989)
                      ·
                        rfl

theorem cell23_2722493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_2722493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722493 prefixEnd_2722493 := by exact prefixLift 2722493
  have htrace : WordTrace (prefixWord ++ tailWord_2722493) baseStart_2722493 baseEnd_2722493 := by
    simpa [prefixWord, tailWord_2722493, baseEnd_2722493] using wordTrace_append hprefix tailTrace_2722493
  have hstable : (prefixWord ++ tailWord_2722493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722493).length < 2 ^ (prefixWord ++ tailWord_2722493).sum := by decide
  have hdescent : baseEnd_2722493 < baseStart_2722493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722515 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_2722515 : Nat := 118140960795 + 2722515 * 2 ^ 59
def prefixEnd_2722515 : Nat := 4983230072969 + 3 ^ 40 * 2722515 * 2
def baseEnd_2722515 : Nat := 1397958784075520881241887

theorem tailTrace_2722515 : CollatzResearch.WordTrace tailWord_2722515 prefixEnd_2722515 1397958784075520881241887 := by
  unfold tailWord_2722515
  simp only [CollatzResearch.WordTrace]
  refine ⟨99298279731800598389072999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66198853154533732259381999 99298279731800598389072999)
  ·
    refine ⟨148947419597700897583609499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99298279731800598389072999 148947419597700897583609499)
    ·
      refine ⟨223421129396551346375414249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148947419597700897583609499 223421129396551346375414249)
      ·
        refine ⟨167565847047413509781560687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223421129396551346375414249 167565847047413509781560687)
        ·
          refine ⟨251348770571120264672341031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167565847047413509781560687 251348770571120264672341031)
          ·
            refine ⟨377023155856680397008511547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251348770571120264672341031 377023155856680397008511547)
            ·
              refine ⟨565534733785020595512767321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377023155856680397008511547 565534733785020595512767321)
              ·
                refine ⟨424151050338765446634575491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565534733785020595512767321 424151050338765446634575491)
                ·
                  refine ⟨636226575508148169951863237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 424151050338765446634575491 636226575508148169951863237)
                  ·
                    refine ⟨119292482907777781865974357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 636226575508148169951863237 119292482907777781865974357)
                    ·
                      refine ⟨1397958784075520881241887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 119292482907777781865974357 1397958784075520881241887)
                      ·
                        rfl

theorem cell23_2722515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_2722515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722515 prefixEnd_2722515 := by exact prefixLift 2722515
  have htrace : WordTrace (prefixWord ++ tailWord_2722515) baseStart_2722515 baseEnd_2722515 := by
    simpa [prefixWord, tailWord_2722515, baseEnd_2722515] using wordTrace_append hprefix tailTrace_2722515
  have hstable : (prefixWord ++ tailWord_2722515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722515).length < 2 ^ (prefixWord ++ tailWord_2722515).sum := by decide
  have hdescent : baseEnd_2722515 < baseStart_2722515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722529 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2722529 : Nat := 118140960795 + 2722529 * 2 ^ 59
def prefixEnd_2722529 : Nat := 4983230072969 + 3 ^ 40 * 2722529 * 2
def baseEnd_2722529 : Nat := 465988657601561275488941

theorem tailTrace_2722529 : CollatzResearch.WordTrace tailWord_2722529 prefixEnd_2722529 465988657601561275488941 := by
  unfold tailWord_2722529
  simp only [CollatzResearch.WordTrace]
  refine ⟨99298790353749878780082641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66199193569166585853388427 99298790353749878780082641)
  ·
    refine ⟨74474092765312409085061981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99298790353749878780082641 74474092765312409085061981)
    ·
      refine ⟨27927784786992153406898243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74474092765312409085061981 27927784786992153406898243)
      ·
        refine ⟨41891677180488230110347365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27927784786992153406898243 41891677180488230110347365)
        ·
          refine ⟨7854689471341543145690131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41891677180488230110347365 7854689471341543145690131)
          ·
            refine ⟨11782034207012314718535197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7854689471341543145690131 11782034207012314718535197)
            ·
              refine ⟨4418262827629618019450699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11782034207012314718535197 4418262827629618019450699)
              ·
                refine ⟨6627394241444427029176049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418262827629618019450699 6627394241444427029176049)
                ·
                  refine ⟨4970545681083320271882037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6627394241444427029176049 4970545681083320271882037)
                  ·
                    refine ⟨465988657601561275488941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4970545681083320271882037 465988657601561275488941)
                    ·
                      rfl

theorem cell23_2722529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2722529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722529 prefixEnd_2722529 := by exact prefixLift 2722529
  have htrace : WordTrace (prefixWord ++ tailWord_2722529) baseStart_2722529 baseEnd_2722529 := by
    simpa [prefixWord, tailWord_2722529, baseEnd_2722529] using wordTrace_append hprefix tailTrace_2722529
  have hstable : (prefixWord ++ tailWord_2722529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722529).length < 2 ^ (prefixWord ++ tailWord_2722529).sum := by decide
  have hdescent : baseEnd_2722529 < baseStart_2722529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722636 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_2722636 : Nat := 118140960795 + 2722636 * 2 ^ 59
def prefixEnd_2722636 : Nat := 4983230072969 + 3 ^ 40 * 2722636 * 2
def baseEnd_2722636 : Nat := 466006971744904969276277

theorem tailTrace_2722636 : CollatzResearch.WordTrace tailWord_2722636 prefixEnd_2722636 466006971744904969276277 := by
  unfold tailWord_2722636
  simp only [CollatzResearch.WordTrace]
  refine ⟨49651346482181118027113881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66201795309574824036151841 49651346482181118027113881)
  ·
    refine ⟨37238509861635838520335411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49651346482181118027113881 37238509861635838520335411)
    ·
      refine ⟨55857764792453757780503117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37238509861635838520335411 55857764792453757780503117)
      ·
        refine ⟨20946661797170159167688669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55857764792453757780503117 20946661797170159167688669)
        ·
          refine ⟨7854998173938809687883251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20946661797170159167688669 7854998173938809687883251)
          ·
            refine ⟨11782497260908214531824877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7854998173938809687883251 11782497260908214531824877)
            ·
              refine ⟨4418436472840580449434329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11782497260908214531824877 4418436472840580449434329)
              ·
                refine ⟨3313827354630435337075747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418436472840580449434329 3313827354630435337075747)
                ·
                  refine ⟨4970741031945653005613621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313827354630435337075747 4970741031945653005613621)
                  ·
                    refine ⟨466006971744904969276277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4970741031945653005613621 466006971744904969276277)
                    ·
                      rfl

theorem cell23_2722636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_2722636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722636 prefixEnd_2722636 := by exact prefixLift 2722636
  have htrace : WordTrace (prefixWord ++ tailWord_2722636) baseStart_2722636 baseEnd_2722636 := by
    simpa [prefixWord, tailWord_2722636, baseEnd_2722636] using wordTrace_append hprefix tailTrace_2722636
  have hstable : (prefixWord ++ tailWord_2722636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722636).length < 2 ^ (prefixWord ++ tailWord_2722636).sum := by decide
  have hdescent : baseEnd_2722636 < baseStart_2722636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722649 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 1, 6]
def baseStart_2722649 : Nat := 118140960795 + 2722649 * 2 ^ 59
def prefixEnd_2722649 : Nat := 4983230072969 + 3 ^ 40 * 2722649 * 2
def baseEnd_2722649 : Nat := 466009196827741118988757

theorem tailTrace_2722649 : CollatzResearch.WordTrace tailWord_2722649 prefixEnd_2722649 466009196827741118988757 := by
  unfold tailWord_2722649
  simp only [CollatzResearch.WordTrace]
  refine ⟨99303167113315139274451001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66202111408876759516300667 99303167113315139274451001)
  ·
    refine ⟨74477375334986354455838251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99303167113315139274451001 74477375334986354455838251)
    ·
      refine ⟨111716063002479531683757377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74477375334986354455838251 111716063002479531683757377)
      ·
        refine ⟨83787047251859648762818033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111716063002479531683757377 83787047251859648762818033)
        ·
          refine ⟨62840285438894736572113525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83787047251859648762818033 62840285438894736572113525)
          ·
            refine ⟨5891276759896381553635643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62840285438894736572113525 5891276759896381553635643)
            ·
              refine ⟨8836915139844572330453465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891276759896381553635643 8836915139844572330453465)
              ·
                refine ⟨6627686354883429247840099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8836915139844572330453465 6627686354883429247840099)
                ·
                  refine ⟨9941529532325143871760149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627686354883429247840099 9941529532325143871760149)
                  ·
                    refine ⟨466009196827741118988757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9941529532325143871760149 466009196827741118988757)
                    ·
                      rfl

theorem cell23_2722649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_2722649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722649 prefixEnd_2722649 := by exact prefixLift 2722649
  have htrace : WordTrace (prefixWord ++ tailWord_2722649) baseStart_2722649 baseEnd_2722649 := by
    simpa [prefixWord, tailWord_2722649, baseEnd_2722649] using wordTrace_append hprefix tailTrace_2722649
  have hstable : (prefixWord ++ tailWord_2722649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722649).length < 2 ^ (prefixWord ++ tailWord_2722649).sum := by decide
  have hdescent : baseEnd_2722649 < baseStart_2722649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722669 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2722669 : Nat := 118140960795 + 2722669 * 2 ^ 59
def prefixEnd_2722669 : Nat := 4983230072969 + 3 ^ 40 * 2722669 * 2
def baseEnd_2722669 : Nat := 1398037860096313278716179

theorem tailTrace_2722669 : CollatzResearch.WordTrace tailWord_2722669 prefixEnd_2722669 1398037860096313278716179 := by
  unfold tailWord_2722669
  simp only [CollatzResearch.WordTrace]
  refine ⟨99303896573242682690179061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66202597715495121793452707 99303896573242682690179061)
  ·
    refine ⟨9309740303741501502204287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99303896573242682690179061 9309740303741501502204287)
    ·
      refine ⟨13964610455612252253306431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9309740303741501502204287 13964610455612252253306431)
      ·
        refine ⟨20946915683418378379959647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13964610455612252253306431 20946915683418378379959647)
        ·
          refine ⟨31420373525127567569939471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20946915683418378379959647 31420373525127567569939471)
          ·
            refine ⟨47130560287691351354909207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31420373525127567569939471 47130560287691351354909207)
            ·
              refine ⟨70695840431537027032363811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47130560287691351354909207 70695840431537027032363811)
              ·
                refine ⟨106043760647305540548545717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70695840431537027032363811 106043760647305540548545717)
                ·
                  refine ⟨9941602560684894426426161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106043760647305540548545717 9941602560684894426426161)
                  ·
                    refine ⟨7456201920513670819819621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9941602560684894426426161 7456201920513670819819621)
                    ·
                      refine ⟨1398037860096313278716179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7456201920513670819819621 1398037860096313278716179)
                      ·
                        rfl

theorem cell23_2722669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2722669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722669 prefixEnd_2722669 := by exact prefixLift 2722669
  have htrace : WordTrace (prefixWord ++ tailWord_2722669) baseStart_2722669 baseEnd_2722669 := by
    simpa [prefixWord, tailWord_2722669, baseEnd_2722669] using wordTrace_append hprefix tailTrace_2722669
  have hstable : (prefixWord ++ tailWord_2722669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722669).length < 2 ^ (prefixWord ++ tailWord_2722669).sum := by decide
  have hdescent : baseEnd_2722669 < baseStart_2722669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722696 : List Nat := [2, 1, 3, 3, 2, 2, 3, 7]
def baseStart_2722696 : Nat := 118140960795 + 2722696 * 2 ^ 59
def prefixEnd_2722696 : Nat := 4983230072969 + 3 ^ 40 * 2722696 * 2
def baseEnd_2722696 : Nat := 51779693484221654558465

theorem tailTrace_2722696 : CollatzResearch.WordTrace tailWord_2722696 prefixEnd_2722696 51779693484221654558465 := by
  unfold tailWord_2722696
  simp only [CollatzResearch.WordTrace]
  refine ⟨49652440672072433150705971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66203254229429910867607961 49652440672072433150705971)
  ·
    refine ⟨74478661008108649726058957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49652440672072433150705971 74478661008108649726058957)
    ·
      refine ⟨27929497878040743647272109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74478661008108649726058957 27929497878040743647272109)
      ·
        refine ⟨10473561704265278867727041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27929497878040743647272109 10473561704265278867727041)
        ·
          refine ⟨7855171278198959150795281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10473561704265278867727041 7855171278198959150795281)
          ·
            refine ⟨5891378458649219363096461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855171278198959150795281 5891378458649219363096461)
            ·
              refine ⟨2209266921993457261161173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5891378458649219363096461 2209266921993457261161173)
              ·
                refine ⟨51779693484221654558465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2209266921993457261161173 51779693484221654558465)
                ·
                  rfl

theorem cell23_2722696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 7].length) (baseStart_2722696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722696 prefixEnd_2722696 := by exact prefixLift 2722696
  have htrace : WordTrace (prefixWord ++ tailWord_2722696) baseStart_2722696 baseEnd_2722696 := by
    simpa [prefixWord, tailWord_2722696, baseEnd_2722696] using wordTrace_append hprefix tailTrace_2722696
  have hstable : (prefixWord ++ tailWord_2722696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722696).length < 2 ^ (prefixWord ++ tailWord_2722696).sum := by decide
  have hdescent : baseEnd_2722696 < baseStart_2722696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722723 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 3]
def baseStart_2722723 : Nat := 118140960795 + 2722723 * 2 ^ 59
def prefixEnd_2722723 : Nat := 4983230072969 + 3 ^ 40 * 2722723 * 2
def baseEnd_2722723 : Nat := 1398065588051656067440931

theorem tailTrace_2722723 : CollatzResearch.WordTrace tailWord_2722723 prefixEnd_2722723 1398065588051656067440931 := by
  unfold tailWord_2722723
  simp only [CollatzResearch.WordTrace]
  refine ⟨99305866115047049912644823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66203910743364699941763215 99305866115047049912644823)
  ·
    refine ⟨148958799172570574868967235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99305866115047049912644823 148958799172570574868967235)
    ·
      refine ⟨223438198758855862303450853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148958799172570574868967235 223438198758855862303450853)
      ·
        refine ⟨41894662267285474181897035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223438198758855862303450853 41894662267285474181897035)
        ·
          refine ⟨62841993400928211272845553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41894662267285474181897035 62841993400928211272845553)
          ·
            refine ⟨47131495050696158454634165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62841993400928211272845553 47131495050696158454634165)
            ·
              refine ⟨4418577661002764855121953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47131495050696158454634165 4418577661002764855121953)
              ·
                refine ⟨3313933245752073641341465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418577661002764855121953 3313933245752073641341465)
                ·
                  refine ⟨2485449934314055231006099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3313933245752073641341465 2485449934314055231006099)
                  ·
                    refine ⟨3728174901471082846509149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2485449934314055231006099 3728174901471082846509149)
                    ·
                      refine ⟨1398065588051656067440931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728174901471082846509149 1398065588051656067440931)
                      ·
                        rfl

theorem cell23_2722723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_2722723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722723 prefixEnd_2722723 := by exact prefixLift 2722723
  have htrace : WordTrace (prefixWord ++ tailWord_2722723) baseStart_2722723 baseEnd_2722723 := by
    simpa [prefixWord, tailWord_2722723, baseEnd_2722723] using wordTrace_append hprefix tailTrace_2722723
  have hstable : (prefixWord ++ tailWord_2722723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722723).length < 2 ^ (prefixWord ++ tailWord_2722723).sum := by decide
  have hdescent : baseEnd_2722723 < baseStart_2722723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722740 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2722740 : Nat := 118140960795 + 2722740 * 2 ^ 59
def prefixEnd_2722740 : Nat := 4983230072969 + 3 ^ 40 * 2722740 * 2
def baseEnd_2722740 : Nat := 1398074317222782500928353

theorem tailTrace_2722740 : CollatzResearch.WordTrace tailWord_2722740 prefixEnd_2722740 1398074317222782500928353 := by
  unfold tailWord_2722740
  simp only [CollatzResearch.WordTrace]
  refine ⟨49653243077992730908006837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66204324103990307877342449 49653243077992730908006837)
  ·
    refine ⟨4654991538561818522625641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49653243077992730908006837 4654991538561818522625641)
    ·
      refine ⟨3491243653921363891969231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4654991538561818522625641 3491243653921363891969231)
      ·
        refine ⟨5236865480882045837953847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491243653921363891969231 5236865480882045837953847)
        ·
          refine ⟨7855298221323068756930771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5236865480882045837953847 7855298221323068756930771)
          ·
            refine ⟨11782947331984603135396157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7855298221323068756930771 11782947331984603135396157)
            ·
              refine ⟨4418605249494226175773559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11782947331984603135396157 4418605249494226175773559)
              ·
                refine ⟨6627907874241339263660339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418605249494226175773559 6627907874241339263660339)
                ·
                  refine ⟨9941861811362008895490509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6627907874241339263660339 9941861811362008895490509)
                  ·
                    refine ⟨3728198179260753335808941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9941861811362008895490509 3728198179260753335808941)
                    ·
                      refine ⟨1398074317222782500928353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728198179260753335808941 1398074317222782500928353)
                      ·
                        rfl

theorem cell23_2722740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2722740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722740 prefixEnd_2722740 := by exact prefixLift 2722740
  have htrace : WordTrace (prefixWord ++ tailWord_2722740) baseStart_2722740 baseEnd_2722740 := by
    simpa [prefixWord, tailWord_2722740, baseEnd_2722740] using wordTrace_append hprefix tailTrace_2722740
  have hstable : (prefixWord ++ tailWord_2722740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722740).length < 2 ^ (prefixWord ++ tailWord_2722740).sum := by decide
  have hdescent : baseEnd_2722740 < baseStart_2722740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722750 : List Nat := [4, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_2722750 : Nat := 118140960795 + 2722750 * 2 ^ 59
def prefixEnd_2722750 : Nat := 4983230072969 + 3 ^ 40 * 2722750 * 2
def baseEnd_2722750 : Nat := 1398079452029327461803307

theorem tailTrace_2722750 : CollatzResearch.WordTrace tailWord_2722750 prefixEnd_2722750 1398079452029327461803307 := by
  unfold tailWord_2722750
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413356360743654190484713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66204567257299489015918469 12413356360743654190484713)
  ·
    refine ⟨9310017270557740642863535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12413356360743654190484713 9310017270557740642863535)
    ·
      refine ⟨13965025905836610964295303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9310017270557740642863535 13965025905836610964295303)
      ·
        refine ⟨20947538858754916446442955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13965025905836610964295303 20947538858754916446442955)
        ·
          refine ⟨31421308288132374669664433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20947538858754916446442955 31421308288132374669664433)
          ·
            refine ⟨23565981216099281002248325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31421308288132374669664433 23565981216099281002248325)
            ·
              refine ⟨4418621478018615187921561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23565981216099281002248325 4418621478018615187921561)
              ·
                refine ⟨3313966108513961390941171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418621478018615187921561 3313966108513961390941171)
                ·
                  refine ⟨4970949162770942086411757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3313966108513961390941171 4970949162770942086411757)
                  ·
                    refine ⟨1864105936039103282404409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4970949162770942086411757 1864105936039103282404409)
                    ·
                      refine ⟨1398079452029327461803307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864105936039103282404409 1398079452029327461803307)
                      ·
                        rfl

theorem cell23_2722750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_2722750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722750 prefixEnd_2722750 := by exact prefixLift 2722750
  have htrace : WordTrace (prefixWord ++ tailWord_2722750) baseStart_2722750 baseEnd_2722750 := by
    simpa [prefixWord, tailWord_2722750, baseEnd_2722750] using wordTrace_append hprefix tailTrace_2722750
  have hstable : (prefixWord ++ tailWord_2722750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722750).length < 2 ^ (prefixWord ++ tailWord_2722750).sum := by decide
  have hdescent : baseEnd_2722750 < baseStart_2722750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722759 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2722759 : Nat := 118140960795 + 2722759 * 2 ^ 59
def prefixEnd_2722759 : Nat := 4983230072969 + 3 ^ 40 * 2722759 * 2
def baseEnd_2722759 : Nat := 1398084073355217926590765

theorem tailTrace_2722759 : CollatzResearch.WordTrace tailWord_2722759 prefixEnd_2722759 1398084073355217926590765 := by
  unfold tailWord_2722759
  simp only [CollatzResearch.WordTrace]
  refine ⟨99307179142916628060955331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66204786095277752040636887 99307179142916628060955331)
  ·
    refine ⟨148960768714374942091432997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99307179142916628060955331 148960768714374942091432997)
    ·
      refine ⟨27930144133945301642143687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148960768714374942091432997 27930144133945301642143687)
      ·
        refine ⟨41895216200917952463215531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27930144133945301642143687 41895216200917952463215531)
        ·
          refine ⟨62842824301376928694823297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41895216200917952463215531 62842824301376928694823297)
          ·
            refine ⟨47132118226032696521117473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62842824301376928694823297 47132118226032696521117473)
            ·
              refine ⟨35349088669524522390838105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47132118226032696521117473 35349088669524522390838105)
              ·
                refine ⟨26511816502143391793128579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35349088669524522390838105 26511816502143391793128579)
                ·
                  refine ⟨39767724753215087689692869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26511816502143391793128579 39767724753215087689692869)
                  ·
                    refine ⟨7456448391227828941817413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39767724753215087689692869 7456448391227828941817413)
                    ·
                      refine ⟨1398084073355217926590765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7456448391227828941817413 1398084073355217926590765)
                      ·
                        rfl

theorem cell23_2722759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2722759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722759 prefixEnd_2722759 := by exact prefixLift 2722759
  have htrace : WordTrace (prefixWord ++ tailWord_2722759) baseStart_2722759 baseEnd_2722759 := by
    simpa [prefixWord, tailWord_2722759, baseEnd_2722759] using wordTrace_append hprefix tailTrace_2722759
  have hstable : (prefixWord ++ tailWord_2722759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722759).length < 2 ^ (prefixWord ++ tailWord_2722759).sum := by decide
  have hdescent : baseEnd_2722759 < baseStart_2722759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722763 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 4, 2, 2]
def baseStart_2722763 : Nat := 118140960795 + 2722763 * 2 ^ 59
def prefixEnd_2722763 : Nat := 4983230072969 + 3 ^ 40 * 2722763 * 2
def baseEnd_2722763 : Nat := 1398086127277835910940747

theorem tailTrace_2722763 : CollatzResearch.WordTrace tailWord_2722763 prefixEnd_2722763 1398086127277835910940747 := by
  unfold tailWord_2722763
  simp only [CollatzResearch.WordTrace]
  refine ⟨99307325034902136744100943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66204883356601424496067295 99307325034902136744100943)
  ·
    refine ⟨148960987552353205116151415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99307325034902136744100943 148960987552353205116151415)
    ·
      refine ⟨223441481328529807674227123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148960987552353205116151415 223441481328529807674227123)
      ·
        refine ⟨335162221992794711511340685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223441481328529807674227123 335162221992794711511340685)
        ·
          refine ⟨125685833247298016816752757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335162221992794711511340685 125685833247298016816752757)
          ·
            refine ⟨11783046866934189076570571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125685833247298016816752757 11783046866934189076570571)
            ·
              refine ⟨17674570300401283614855857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11783046866934189076570571 17674570300401283614855857)
              ·
                refine ⟨13255927725300962711141893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17674570300401283614855857 13255927725300962711141893)
                ·
                  refine ⟨2485486448493930508339105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13255927725300962711141893 2485486448493930508339105)
                  ·
                    refine ⟨1864114836370447881254329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2485486448493930508339105 1864114836370447881254329)
                    ·
                      refine ⟨1398086127277835910940747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864114836370447881254329 1398086127277835910940747)
                      ·
                        rfl

theorem cell23_2722763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 2, 2].length) (baseStart_2722763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722763 prefixEnd_2722763 := by exact prefixLift 2722763
  have htrace : WordTrace (prefixWord ++ tailWord_2722763) baseStart_2722763 baseEnd_2722763 := by
    simpa [prefixWord, tailWord_2722763, baseEnd_2722763] using wordTrace_append hprefix tailTrace_2722763
  have hstable : (prefixWord ++ tailWord_2722763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722763).length < 2 ^ (prefixWord ++ tailWord_2722763).sum := by decide
  have hdescent : baseEnd_2722763 < baseStart_2722763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722766 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2722766 : Nat := 118140960795 + 2722766 * 2 ^ 59
def prefixEnd_2722766 : Nat := 4983230072969 + 3 ^ 40 * 2722766 * 2
def baseEnd_2722766 : Nat := 1398087667719799399203233

theorem tailTrace_2722766 : CollatzResearch.WordTrace tailWord_2722766 prefixEnd_2722766 1398087667719799399203233 := by
  unfold tailWord_2722766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12413429306736408532057519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66204956302594178837640101 12413429306736408532057519)
  ·
    refine ⟨18620143960104612798086279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12413429306736408532057519 18620143960104612798086279)
    ·
      refine ⟨27930215940156919197129419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18620143960104612798086279 27930215940156919197129419)
      ·
        refine ⟨41895323910235378795694129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27930215940156919197129419 41895323910235378795694129)
        ·
          refine ⟨31421492932676534096770597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41895323910235378795694129 31421492932676534096770597)
          ·
            refine ⟨5891529924876850143144487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31421492932676534096770597 5891529924876850143144487)
            ·
              refine ⟨8837294887315275214716731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891529924876850143144487 8837294887315275214716731)
              ·
                refine ⟨13255942330972912822075097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837294887315275214716731 13255942330972912822075097)
                ·
                  refine ⟨9941956748229684616556323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13255942330972912822075097 9941956748229684616556323)
                  ·
                    refine ⟨14912935122344526924834485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9941956748229684616556323 14912935122344526924834485)
                    ·
                      refine ⟨1398087667719799399203233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14912935122344526924834485 1398087667719799399203233)
                      ·
                        rfl

theorem cell23_2722766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2722766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722766 prefixEnd_2722766 := by exact prefixLift 2722766
  have htrace : WordTrace (prefixWord ++ tailWord_2722766) baseStart_2722766 baseEnd_2722766 := by
    simpa [prefixWord, tailWord_2722766, baseEnd_2722766] using wordTrace_append hprefix tailTrace_2722766
  have hstable : (prefixWord ++ tailWord_2722766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722766).length < 2 ^ (prefixWord ++ tailWord_2722766).sum := by decide
  have hdescent : baseEnd_2722766 < baseStart_2722766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722809 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2722809 : Nat := 118140960795 + 2722809 * 2 ^ 59
def prefixEnd_2722809 : Nat := 4983230072969 + 3 ^ 40 * 2722809 * 2
def baseEnd_2722809 : Nat := 1398109747387942730965535

theorem tailTrace_2722809 : CollatzResearch.WordTrace tailWord_2722809 prefixEnd_2722809 1398109747387942730965535 := by
  unfold tailWord_2722809
  simp only [CollatzResearch.WordTrace]
  refine ⟨99309002792735486600275481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66206001861823657733516987 99309002792735486600275481)
  ·
    refine ⟨74481752094551614950206611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99309002792735486600275481 74481752094551614950206611)
    ·
      refine ⟨111722628141827422425309917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74481752094551614950206611 111722628141827422425309917)
      ·
        refine ⟨41895985553185283409491219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111722628141827422425309917 41895985553185283409491219)
        ·
          refine ⟨62843978329777925114236829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41895985553185283409491219 62843978329777925114236829)
          ·
            refine ⟨23566491873666721917838811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62843978329777925114236829 23566491873666721917838811)
            ·
              refine ⟨35349737810500082876758217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23566491873666721917838811 35349737810500082876758217)
              ·
                refine ⟨26512303357875062157568663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35349737810500082876758217 26512303357875062157568663)
                ·
                  refine ⟨39768455036812593236352995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26512303357875062157568663 39768455036812593236352995)
                  ·
                    refine ⟨59652682555218889854529493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39768455036812593236352995 59652682555218889854529493)
                    ·
                      refine ⟨1398109747387942730965535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59652682555218889854529493 1398109747387942730965535)
                      ·
                        rfl

theorem cell23_2722809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2722809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722809 prefixEnd_2722809 := by exact prefixLift 2722809
  have htrace : WordTrace (prefixWord ++ tailWord_2722809) baseStart_2722809 baseEnd_2722809 := by
    simpa [prefixWord, tailWord_2722809, baseEnd_2722809] using wordTrace_append hprefix tailTrace_2722809
  have hstable : (prefixWord ++ tailWord_2722809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722809).length < 2 ^ (prefixWord ++ tailWord_2722809).sum := by decide
  have hdescent : baseEnd_2722809 < baseStart_2722809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722826 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2722826 : Nat := 118140960795 + 2722826 * 2 ^ 59
def prefixEnd_2722826 : Nat := 4983230072969 + 3 ^ 40 * 2722826 * 2
def baseEnd_2722826 : Nat := 1398118476559069164452957

theorem tailTrace_2722826 : CollatzResearch.WordTrace tailWord_2722826 prefixEnd_2722826 1398118476559069164452957 := by
  unfold tailWord_2722826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24827405708418474625911083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66206415222449265669096221 24827405708418474625911083)
  ·
    refine ⟨37241108562627711938866625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24827405708418474625911083 37241108562627711938866625)
    ·
      refine ⟨27930831421970783954149969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37241108562627711938866625 27930831421970783954149969)
      ·
        refine ⟨20948123566478087965612477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27930831421970783954149969 20948123566478087965612477)
        ·
          refine ⟨7855546337429282987104679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20948123566478087965612477 7855546337429282987104679)
          ·
            refine ⟨11783319506143924480657019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7855546337429282987104679 11783319506143924480657019)
            ·
              refine ⟨17674979259215886720985529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11783319506143924480657019 17674979259215886720985529)
              ·
                refine ⟨13256234444411915040739147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17674979259215886720985529 13256234444411915040739147)
                ·
                  refine ⟨19884351666617872561108721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13256234444411915040739147 19884351666617872561108721)
                  ·
                    refine ⟨14913263749963404420831541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19884351666617872561108721 14913263749963404420831541)
                    ·
                      refine ⟨1398118476559069164452957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14913263749963404420831541 1398118476559069164452957)
                      ·
                        rfl

theorem cell23_2722826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2722826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722826 prefixEnd_2722826 := by exact prefixLift 2722826
  have htrace : WordTrace (prefixWord ++ tailWord_2722826) baseStart_2722826 baseEnd_2722826 := by
    simpa [prefixWord, tailWord_2722826, baseEnd_2722826] using wordTrace_append hprefix tailTrace_2722826
  have hstable : (prefixWord ++ tailWord_2722826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722826).length < 2 ^ (prefixWord ++ tailWord_2722826).sum := by decide
  have hdescent : baseEnd_2722826 < baseStart_2722826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722853 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 2, 4, 2]
def baseStart_2722853 : Nat := 118140960795 + 2722853 * 2 ^ 59
def prefixEnd_2722853 : Nat := 4983230072969 + 3 ^ 40 * 2722853 * 2
def baseEnd_2722853 : Nat := 1398132340536740558815333

theorem tailTrace_2722853 : CollatzResearch.WordTrace tailWord_2722853 prefixEnd_2722853 1398132340536740558815333 := by
  unfold tailWord_2722853
  simp only [CollatzResearch.WordTrace]
  refine ⟨99310607604576082114877213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66207071736384054743251475 99310607604576082114877213)
  ·
    refine ⟨37241477851716030793078955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99310607604576082114877213 37241477851716030793078955)
    ·
      refine ⟨55862216777574046189618433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37241477851716030793078955 55862216777574046189618433)
      ·
        refine ⟨41896662583180534642213825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55862216777574046189618433 41896662583180534642213825)
        ·
          refine ⟨31422496937385400981660369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41896662583180534642213825 31422496937385400981660369)
          ·
            refine ⟨23566872703039050736245277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31422496937385400981660369 23566872703039050736245277)
            ·
              refine ⟨8837577263639644026091979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23566872703039050736245277 8837577263639644026091979)
              ·
                refine ⟨13256365895459466039137969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837577263639644026091979 13256365895459466039137969)
                ·
                  refine ⟨9942274421594599529353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13256365895459466039137969 9942274421594599529353477)
                  ·
                    refine ⟨1864176454048987411753777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9942274421594599529353477 1864176454048987411753777)
                    ·
                      refine ⟨1398132340536740558815333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864176454048987411753777 1398132340536740558815333)
                      ·
                        rfl

theorem cell23_2722853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_2722853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722853 prefixEnd_2722853 := by exact prefixLift 2722853
  have htrace : WordTrace (prefixWord ++ tailWord_2722853) baseStart_2722853 baseEnd_2722853 := by
    simpa [prefixWord, tailWord_2722853, baseEnd_2722853] using wordTrace_append hprefix tailTrace_2722853
  have hstable : (prefixWord ++ tailWord_2722853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722853).length < 2 ^ (prefixWord ++ tailWord_2722853).sum := by decide
  have hdescent : baseEnd_2722853 < baseStart_2722853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722870 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2722870 : Nat := 118140960795 + 2722870 * 2 ^ 59
def prefixEnd_2722870 : Nat := 4983230072969 + 3 ^ 40 * 2722870 * 2
def baseEnd_2722870 : Nat := 1398141069707866992302755

theorem tailTrace_2722870 : CollatzResearch.WordTrace tailWord_2722870 prefixEnd_2722870 1398141069707866992302755 := by
  unfold tailWord_2722870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206951727844655876140379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66207485097009662678830709 6206951727844655876140379)
  ·
    refine ⟨9310427591766983814210569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6206951727844655876140379 9310427591766983814210569)
    ·
      refine ⟨6982820693825237860657927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9310427591766983814210569 6982820693825237860657927)
      ·
        refine ⟨10474231040737856790986891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982820693825237860657927 10474231040737856790986891)
        ·
          refine ⟨15711346561106785186480337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10474231040737856790986891 15711346561106785186480337)
          ·
            refine ⟨11783509920830088889860253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15711346561106785186480337 11783509920830088889860253)
            ·
              refine ⟨4418816220311283333697595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11783509920830088889860253 4418816220311283333697595)
              ·
                refine ⟨6628224330466925000546393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4418816220311283333697595 6628224330466925000546393)
                ·
                  refine ⟨4971168247850193750409795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6628224330466925000546393 4971168247850193750409795)
                  ·
                    refine ⟨7456752371775290625614693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4971168247850193750409795 7456752371775290625614693)
                    ·
                      refine ⟨1398141069707866992302755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7456752371775290625614693 1398141069707866992302755)
                      ·
                        rfl

theorem cell23_2722870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2722870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722870 prefixEnd_2722870 := by exact prefixLift 2722870
  have htrace : WordTrace (prefixWord ++ tailWord_2722870) baseStart_2722870 baseEnd_2722870 := by
    simpa [prefixWord, tailWord_2722870, baseEnd_2722870] using wordTrace_append hprefix tailTrace_2722870
  have hstable : (prefixWord ++ tailWord_2722870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722870).length < 2 ^ (prefixWord ++ tailWord_2722870).sum := by decide
  have hdescent : baseEnd_2722870 < baseStart_2722870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722873 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2722873 : Nat := 118140960795 + 2722873 * 2 ^ 59
def prefixEnd_2722873 : Nat := 4983230072969 + 3 ^ 40 * 2722873 * 2
def baseEnd_2722873 : Nat := 1398142610149830480565241

theorem tailTrace_2722873 : CollatzResearch.WordTrace tailWord_2722873 prefixEnd_2722873 1398142610149830480565241 := by
  unfold tailWord_2722873
  simp only [CollatzResearch.WordTrace]
  refine ⟨99311337064503625530605273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66207558043002417020403515 99311337064503625530605273)
  ·
    refine ⟨74483502798377719147953955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99311337064503625530605273 74483502798377719147953955)
    ·
      refine ⟨111725254197566578721930933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74483502798377719147953955 111725254197566578721930933)
      ·
        refine ⟨10474242581021866755181025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111725254197566578721930933 10474242581021866755181025)
        ·
          refine ⟨7855681935766400066385769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10474242581021866755181025 7855681935766400066385769)
          ·
            refine ⟨5891761451824800049789327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855681935766400066385769 5891761451824800049789327)
            ·
              refine ⟨8837642177737200074683991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891761451824800049789327 8837642177737200074683991)
              ·
                refine ⟨13256463266605800112025987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837642177737200074683991 13256463266605800112025987)
                ·
                  refine ⟨19884694899908700168038981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13256463266605800112025987 19884694899908700168038981)
                  ·
                    refine ⟨3728380293732881281507309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19884694899908700168038981 3728380293732881281507309)
                    ·
                      refine ⟨1398142610149830480565241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728380293732881281507309 1398142610149830480565241)
                      ·
                        rfl

theorem cell23_2722873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2722873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722873 prefixEnd_2722873 := by exact prefixLift 2722873
  have htrace : WordTrace (prefixWord ++ tailWord_2722873) baseStart_2722873 baseEnd_2722873 := by
    simpa [prefixWord, tailWord_2722873, baseEnd_2722873] using wordTrace_append hprefix tailTrace_2722873
  have hstable : (prefixWord ++ tailWord_2722873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722873).length < 2 ^ (prefixWord ++ tailWord_2722873).sum := by decide
  have hdescent : baseEnd_2722873 < baseStart_2722873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722880 : List Nat := [2, 1, 1, 2, 2, 3, 4, 3, 1, 4]
def baseStart_2722880 : Nat := 118140960795 + 2722880 * 2 ^ 59
def prefixEnd_2722880 : Nat := 4983230072969 + 3 ^ 40 * 2722880 * 2
def baseEnd_2722880 : Nat := 466048734838137317725903

theorem tailTrace_2722880 : CollatzResearch.WordTrace tailWord_2722880 prefixEnd_2722880 466048734838137317725903 := by
  unfold tailWord_2722880
  simp only [CollatzResearch.WordTrace]
  refine ⟨49655796187739132863055047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66207728250318843817406729 49655796187739132863055047)
  ·
    refine ⟨74483694281608699294582571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49655796187739132863055047 74483694281608699294582571)
    ·
      refine ⟨111725541422413048941873857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74483694281608699294582571 111725541422413048941873857)
      ·
        refine ⟨83794156066809786706405393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111725541422413048941873857 83794156066809786706405393)
        ·
          refine ⟨62845617050107340029804045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83794156066809786706405393 62845617050107340029804045)
          ·
            refine ⟨23567106393790252511176517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62845617050107340029804045 23567106393790252511176517)
            ·
              refine ⟨4418832448835672345845597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23567106393790252511176517 4418832448835672345845597)
              ·
                refine ⟨1657062168313377129692099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4418832448835672345845597 1657062168313377129692099)
                ·
                  refine ⟨2485593252470065694538149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657062168313377129692099 2485593252470065694538149)
                  ·
                    refine ⟨466048734838137317725903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2485593252470065694538149 466048734838137317725903)
                    ·
                      rfl

theorem cell23_2722880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 3, 1, 4].length) (baseStart_2722880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722880 prefixEnd_2722880 := by exact prefixLift 2722880
  have htrace : WordTrace (prefixWord ++ tailWord_2722880) baseStart_2722880 baseEnd_2722880 := by
    simpa [prefixWord, tailWord_2722880, baseEnd_2722880] using wordTrace_append hprefix tailTrace_2722880
  have hstable : (prefixWord ++ tailWord_2722880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722880).length < 2 ^ (prefixWord ++ tailWord_2722880).sum := by decide
  have hdescent : baseEnd_2722880 < baseStart_2722880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722893 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2722893 : Nat := 118140960795 + 2722893 * 2 ^ 59
def prefixEnd_2722893 : Nat := 4983230072969 + 3 ^ 40 * 2722893 * 2
def baseEnd_2722893 : Nat := 155350319973657822479461

theorem tailTrace_2722893 : CollatzResearch.WordTrace tailWord_2722893 prefixEnd_2722893 155350319973657822479461 := by
  unfold tailWord_2722893
  simp only [CollatzResearch.WordTrace]
  refine ⟨99312066524431168946333333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66208044349620779297555555 99312066524431168946333333)
  ·
    refine ⟨4655253118332711044359375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99312066524431168946333333 4655253118332711044359375)
    ·
      refine ⟨6982879677499066566539063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4655253118332711044359375 6982879677499066566539063)
      ·
        refine ⟨10474319516248599849808595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6982879677499066566539063 10474319516248599849808595)
        ·
          refine ⟨15711479274372899774712893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10474319516248599849808595 15711479274372899774712893)
          ·
            refine ⟨5891804727889837415517335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15711479274372899774712893 5891804727889837415517335)
            ·
              refine ⟨8837707091834756123276003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891804727889837415517335 8837707091834756123276003)
              ·
                refine ⟨13256560637752134184914005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837707091834756123276003 13256560637752134184914005)
                ·
                  refine ⟨155350319973657822479461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13256560637752134184914005 155350319973657822479461)
                  ·
                    rfl

theorem cell23_2722893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2722893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722893 prefixEnd_2722893 := by exact prefixLift 2722893
  have htrace : WordTrace (prefixWord ++ tailWord_2722893) baseStart_2722893 baseEnd_2722893 := by
    simpa [prefixWord, tailWord_2722893, baseEnd_2722893] using wordTrace_append hprefix tailTrace_2722893
  have hstable : (prefixWord ++ tailWord_2722893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722893).length < 2 ^ (prefixWord ++ tailWord_2722893).sum := by decide
  have hdescent : baseEnd_2722893 < baseStart_2722893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722906 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_2722906 : Nat := 118140960795 + 2722906 * 2 ^ 59
def prefixEnd_2722906 : Nat := 4983230072969 + 3 ^ 40 * 2722906 * 2
def baseEnd_2722906 : Nat := 466053185003809617150863

theorem tailTrace_2722906 : CollatzResearch.WordTrace tailWord_2722906 prefixEnd_2722906 466053185003809617150863 := by
  unfold tailWord_2722906
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828135168346018041639143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66208360448922714777704381 24828135168346018041639143)
  ·
    refine ⟨37242202752519027062458715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24828135168346018041639143 37242202752519027062458715)
    ·
      refine ⟨55863304128778540593688073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37242202752519027062458715 55863304128778540593688073)
      ·
        refine ⟨41897478096583905445266055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55863304128778540593688073 41897478096583905445266055)
        ·
          refine ⟨62846217144875858167899083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41897478096583905445266055 62846217144875858167899083)
          ·
            refine ⟨94269325717313787251848625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62846217144875858167899083 94269325717313787251848625)
            ·
              refine ⟨70701994287985340438886469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94269325717313787251848625 70701994287985340438886469)
              ·
                refine ⟨13256623928997251332291213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70701994287985340438886469 13256623928997251332291213)
                ·
                  refine ⟨4971233973373969249609205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13256623928997251332291213 4971233973373969249609205)
                  ·
                    refine ⟨466053185003809617150863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4971233973373969249609205 466053185003809617150863)
                    ·
                      rfl

theorem cell23_2722906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_2722906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722906 prefixEnd_2722906 := by exact prefixLift 2722906
  have htrace : WordTrace (prefixWord ++ tailWord_2722906) baseStart_2722906 baseEnd_2722906 := by
    simpa [prefixWord, tailWord_2722906, baseEnd_2722906] using wordTrace_append hprefix tailTrace_2722906
  have hstable : (prefixWord ++ tailWord_2722906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722906).length < 2 ^ (prefixWord ++ tailWord_2722906).sum := by decide
  have hdescent : baseEnd_2722906 < baseStart_2722906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722913 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_2722913 : Nat := 118140960795 + 2722913 * 2 ^ 59
def prefixEnd_2722913 : Nat := 4983230072969 + 3 ^ 40 * 2722913 * 2
def baseEnd_2722913 : Nat := 1398163149376010324065057

theorem tailTrace_2722913 : CollatzResearch.WordTrace tailWord_2722913 prefixEnd_2722913 1398163149376010324065057 := by
  unfold tailWord_2722913
  simp only [CollatzResearch.WordTrace]
  refine ⟨99312795984358712362061393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66208530656239141574707595 99312795984358712362061393)
  ·
    refine ⟨74484596988269034271546045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99312795984358712362061393 74484596988269034271546045)
    ·
      refine ⟨27931723870600887851829767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74484596988269034271546045 27931723870600887851829767)
      ·
        refine ⟨41897585805901331777744651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27931723870600887851829767 41897585805901331777744651)
        ·
          refine ⟨62846378708851997666616977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41897585805901331777744651 62846378708851997666616977)
          ·
            refine ⟨47134784031638998249962733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62846378708851997666616977 47134784031638998249962733)
            ·
              refine ⟨17675544011864624343736025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47134784031638998249962733 17675544011864624343736025)
              ·
                refine ⟨13256658008898468257802019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17675544011864624343736025 13256658008898468257802019)
                ·
                  refine ⟨19884987013347702386703029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13256658008898468257802019 19884987013347702386703029)
                  ·
                    refine ⟨1864217532501347098753409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19884987013347702386703029 1864217532501347098753409)
                    ·
                      refine ⟨1398163149376010324065057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864217532501347098753409 1398163149376010324065057)
                      ·
                        rfl

theorem cell23_2722913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_2722913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722913 prefixEnd_2722913 := by exact prefixLift 2722913
  have htrace : WordTrace (prefixWord ++ tailWord_2722913) baseStart_2722913 baseEnd_2722913 := by
    simpa [prefixWord, tailWord_2722913, baseEnd_2722913] using wordTrace_append hprefix tailTrace_2722913
  have hstable : (prefixWord ++ tailWord_2722913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722913).length < 2 ^ (prefixWord ++ tailWord_2722913).sum := by decide
  have hdescent : baseEnd_2722913 < baseStart_2722913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722930 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_2722930 : Nat := 118140960795 + 2722930 * 2 ^ 59
def prefixEnd_2722930 : Nat := 4983230072969 + 3 ^ 40 * 2722930 * 2
def baseEnd_2722930 : Nat := 1398171878547136757552479

theorem tailTrace_2722930 : CollatzResearch.WordTrace tailWord_2722930 prefixEnd_2722930 1398171878547136757552479 := by
  unfold tailWord_2722930
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828354006324281066357561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66208944016864749510286829 24828354006324281066357561)
  ·
    refine ⟨18621265504743210799768171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24828354006324281066357561 18621265504743210799768171)
    ·
      refine ⟨27931898257114816199652257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18621265504743210799768171 27931898257114816199652257)
      ·
        refine ⟨20948923692836112149739193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27931898257114816199652257 20948923692836112149739193)
        ·
          refine ⟨15711692769627084112304395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20948923692836112149739193 15711692769627084112304395)
          ·
            refine ⟨23567539154440626168456593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15711692769627084112304395 23567539154440626168456593)
            ·
              refine ⟨17675654365830469626342445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23567539154440626168456593 17675654365830469626342445)
              ·
                refine ⟨6628370387186426109878417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17675654365830469626342445 6628370387186426109878417)
                ·
                  refine ⟨4971277790389819582408813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6628370387186426109878417 4971277790389819582408813)
                  ·
                    refine ⟨1864229171396182343403305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4971277790389819582408813 1864229171396182343403305)
                    ·
                      refine ⟨1398171878547136757552479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864229171396182343403305 1398171878547136757552479)
                      ·
                        rfl

theorem cell23_2722930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_2722930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722930 prefixEnd_2722930 := by exact prefixLift 2722930
  have htrace : WordTrace (prefixWord ++ tailWord_2722930) baseStart_2722930 baseEnd_2722930 := by
    simpa [prefixWord, tailWord_2722930, baseEnd_2722930] using wordTrace_append hprefix tailTrace_2722930
  have hstable : (prefixWord ++ tailWord_2722930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722930).length < 2 ^ (prefixWord ++ tailWord_2722930).sum := by decide
  have hdescent : baseEnd_2722930 < baseStart_2722930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722936 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_2722936 : Nat := 118140960795 + 2722936 * 2 ^ 59
def prefixEnd_2722936 : Nat := 4983230072969 + 3 ^ 40 * 2722936 * 2
def baseEnd_2722936 : Nat := 466058319810354578025817

theorem tailTrace_2722936 : CollatzResearch.WordTrace tailWord_2722936 prefixEnd_2722936 466058319810354578025817 := by
  unfold tailWord_2722936
  simp only [CollatzResearch.WordTrace]
  refine ⟨49656817431637693645074331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66209089908850258193432441 49656817431637693645074331)
  ·
    refine ⟨74485226147456540467611497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49656817431637693645074331 74485226147456540467611497)
    ·
      refine ⟨55863919610592405350708623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74485226147456540467611497 55863919610592405350708623)
      ·
        refine ⟨83795879415888608026062935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55863919610592405350708623 83795879415888608026062935)
        ·
          refine ⟨125693819123832912039094403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83795879415888608026062935 125693819123832912039094403)
          ·
            refine ⟨188540728685749368058641605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125693819123832912039094403 188540728685749368058641605)
            ·
              refine ⟨35351386628578006510995301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188540728685749368058641605 35351386628578006510995301)
              ·
                refine ⟨6628384992858376220811619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35351386628578006510995301 6628384992858376220811619)
                ·
                  refine ⟨9942577489287564331217429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628384992858376220811619 9942577489287564331217429)
                  ·
                    refine ⟨466058319810354578025817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9942577489287564331217429 466058319810354578025817)
                    ·
                      rfl

theorem cell23_2722936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_2722936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722936 prefixEnd_2722936 := by exact prefixLift 2722936
  have htrace : WordTrace (prefixWord ++ tailWord_2722936) baseStart_2722936 baseEnd_2722936 := by
    simpa [prefixWord, tailWord_2722936, baseEnd_2722936] using wordTrace_append hprefix tailTrace_2722936
  have hstable : (prefixWord ++ tailWord_2722936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722936).length < 2 ^ (prefixWord ++ tailWord_2722936).sum := by decide
  have hdescent : baseEnd_2722936 < baseStart_2722936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722953 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 4, 4]
def baseStart_2722953 : Nat := 118140960795 + 2722953 * 2 ^ 59
def prefixEnd_2722953 : Nat := 4983230072969 + 3 ^ 40 * 2722953 * 2
def baseEnd_2722953 : Nat := 466061229534063389188291

theorem tailTrace_2722953 : CollatzResearch.WordTrace tailWord_2722953 prefixEnd_2722953 466061229534063389188291 := by
  unfold tailWord_2722953
  simp only [CollatzResearch.WordTrace]
  refine ⟨99314254904213799193517513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66209503269475866129011675 99314254904213799193517513)
  ·
    refine ⟨74485691178160349395138135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99314254904213799193517513 74485691178160349395138135)
    ·
      refine ⟨111728536767240524092707203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74485691178160349395138135 111728536767240524092707203)
      ·
        refine ⟨167592805150860786139060805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111728536767240524092707203 167592805150860786139060805)
        ·
          refine ⟨31423650965786397401073901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167592805150860786139060805 31423650965786397401073901)
          ·
            refine ⟨11783869112169899025402713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31423650965786397401073901 11783869112169899025402713)
            ·
              refine ⟨8837901834127424269052035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11783869112169899025402713 8837901834127424269052035)
              ·
                refine ⟨13256852751191136403578053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837901834127424269052035 13256852751191136403578053)
                ·
                  refine ⟨2485659890848338075670885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13256852751191136403578053 2485659890848338075670885)
                  ·
                    refine ⟨466061229534063389188291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2485659890848338075670885 466061229534063389188291)
                    ·
                      rfl

theorem cell23_2722953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_2722953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722953 prefixEnd_2722953 := by exact prefixLift 2722953
  have htrace : WordTrace (prefixWord ++ tailWord_2722953) baseStart_2722953 baseEnd_2722953 := by
    simpa [prefixWord, tailWord_2722953, baseEnd_2722953] using wordTrace_append hprefix tailTrace_2722953
  have hstable : (prefixWord ++ tailWord_2722953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722953).length < 2 ^ (prefixWord ++ tailWord_2722953).sum := by decide
  have hdescent : baseEnd_2722953 < baseStart_2722953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722954 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_2722954 : Nat := 118140960795 + 2722954 * 2 ^ 59
def prefixEnd_2722954 : Nat := 4983230072969 + 3 ^ 40 * 2722954 * 2
def baseEnd_2722954 : Nat := 1398184202082844663652369

theorem tailTrace_2722954 : CollatzResearch.WordTrace tailWord_2722954 prefixEnd_2722954 1398184202082844663652369 := by
  unfold tailWord_2722954
  simp only [CollatzResearch.WordTrace]
  refine ⟨24828572844302544091075979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66209527584806784242869277 24828572844302544091075979)
  ·
    refine ⟨37242859266453816136613969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24828572844302544091075979 37242859266453816136613969)
    ·
      refine ⟨27932144449840362102460477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37242859266453816136613969 27932144449840362102460477)
      ·
        refine ⟨10474554168690135788422679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27932144449840362102460477 10474554168690135788422679)
        ·
          refine ⟨15711831253035203682634019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10474554168690135788422679 15711831253035203682634019)
          ·
            refine ⟨23567746879552805523951029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15711831253035203682634019 23567746879552805523951029)
            ·
              refine ⟨2209476269958075517870409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23567746879552805523951029 2209476269958075517870409)
              ·
                refine ⟨1657107202468556638402807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209476269958075517870409 1657107202468556638402807)
                ·
                  refine ⟨2485660803702834957604211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657107202468556638402807 2485660803702834957604211)
                  ·
                    refine ⟨3728491205554252436406317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2485660803702834957604211 3728491205554252436406317)
                    ·
                      refine ⟨1398184202082844663652369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728491205554252436406317 1398184202082844663652369)
                      ·
                        rfl

theorem cell23_2722954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_2722954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722954 prefixEnd_2722954 := by exact prefixLift 2722954
  have htrace : WordTrace (prefixWord ++ tailWord_2722954) baseStart_2722954 baseEnd_2722954 := by
    simpa [prefixWord, tailWord_2722954, baseEnd_2722954] using wordTrace_append hprefix tailTrace_2722954
  have hstable : (prefixWord ++ tailWord_2722954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722954).length < 2 ^ (prefixWord ++ tailWord_2722954).sum := by decide
  have hdescent : baseEnd_2722954 < baseStart_2722954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722960 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 3, 2, 2]
def baseStart_2722960 : Nat := 118140960795 + 2722960 * 2 ^ 59
def prefixEnd_2722960 : Nat := 4983230072969 + 3 ^ 40 * 2722960 * 2
def baseEnd_2722960 : Nat := 1398187282966771640177341

theorem tailTrace_2722960 : CollatzResearch.WordTrace tailWord_2722960 prefixEnd_2722960 1398187282966771640177341 := by
  unfold tailWord_2722960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49657255107594219694511167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66209673476792292926014889 49657255107594219694511167)
  ·
    refine ⟨74485882661391329541766751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49657255107594219694511167 74485882661391329541766751)
    ·
      refine ⟨111728823992086994312650127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74485882661391329541766751 111728823992086994312650127)
      ·
        refine ⟨167593235988130491468975191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111728823992086994312650127 167593235988130491468975191)
        ·
          refine ⟨251389853982195737203462787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167593235988130491468975191 251389853982195737203462787)
          ·
            refine ⟨377084780973293605805194181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251389853982195737203462787 377084780973293605805194181)
            ·
              refine ⟨70703396432492551088473909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377084780973293605805194181 70703396432492551088473909)
              ·
                refine ⟨6628443415546176664544429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70703396432492551088473909 6628443415546176664544429)
                ·
                  refine ⟨2485666280829816249204161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6628443415546176664544429 2485666280829816249204161)
                  ·
                    refine ⟨1864249710622362186903121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2485666280829816249204161 1864249710622362186903121)
                    ·
                      refine ⟨1398187282966771640177341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864249710622362186903121 1398187282966771640177341)
                      ·
                        rfl

theorem cell23_2722960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 3, 2, 2].length) (baseStart_2722960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722960 prefixEnd_2722960 := by exact prefixLift 2722960
  have htrace : WordTrace (prefixWord ++ tailWord_2722960) baseStart_2722960 baseEnd_2722960 := by
    simpa [prefixWord, tailWord_2722960, baseEnd_2722960] using wordTrace_append hprefix tailTrace_2722960
  have hstable : (prefixWord ++ tailWord_2722960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722960).length < 2 ^ (prefixWord ++ tailWord_2722960).sum := by decide
  have hdescent : baseEnd_2722960 < baseStart_2722960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722973 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2722973 : Nat := 118140960795 + 2722973 * 2 ^ 59
def prefixEnd_2722973 : Nat := 4983230072969 + 3 ^ 40 * 2722973 * 2
def baseEnd_2722973 : Nat := 1398193958215280089314781

theorem tailTrace_2722973 : CollatzResearch.WordTrace tailWord_2722973 prefixEnd_2722973 1398193958215280089314781 := by
  unfold tailWord_2722973
  simp only [CollatzResearch.WordTrace]
  refine ⟨99314984364141342609245573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66209989576094228406163715 99314984364141342609245573)
  ·
    refine ⟨18621559568276501739233545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99314984364141342609245573 18621559568276501739233545)
    ·
      refine ⟨13966169676207376304425159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18621559568276501739233545 13966169676207376304425159)
      ·
        refine ⟨20949254514311064456637739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13966169676207376304425159 20949254514311064456637739)
        ·
          refine ⟨31423881771466596684956609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20949254514311064456637739 31423881771466596684956609)
          ·
            refine ⟨23567911328599947513717457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31423881771466596684956609 23567911328599947513717457)
            ·
              refine ⟨17675933496449960635288093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23567911328599947513717457 17675933496449960635288093)
              ·
                refine ⟨6628475061168735238233035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17675933496449960635288093 6628475061168735238233035)
                ·
                  refine ⟨9942712591753102857349553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6628475061168735238233035 9942712591753102857349553)
                  ·
                    refine ⟨7457034443814827143012165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9942712591753102857349553 7457034443814827143012165)
                    ·
                      refine ⟨1398193958215280089314781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7457034443814827143012165 1398193958215280089314781)
                      ·
                        rfl

theorem cell23_2722973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2722973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722973 prefixEnd_2722973 := by exact prefixLift 2722973
  have htrace : WordTrace (prefixWord ++ tailWord_2722973) baseStart_2722973 baseEnd_2722973 := by
    simpa [prefixWord, tailWord_2722973, baseEnd_2722973] using wordTrace_append hprefix tailTrace_2722973
  have hstable : (prefixWord ++ tailWord_2722973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722973).length < 2 ^ (prefixWord ++ tailWord_2722973).sum := by decide
  have hdescent : baseEnd_2722973 < baseStart_2722973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722980 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_2722980 : Nat := 118140960795 + 2722980 * 2 ^ 59
def prefixEnd_2722980 : Nat := 4983230072969 + 3 ^ 40 * 2722980 * 2
def baseEnd_2722980 : Nat := 1398197552579861561927249

theorem tailTrace_2722980 : CollatzResearch.WordTrace tailWord_2722980 prefixEnd_2722980 1398197552579861561927249 := by
  unfold tailWord_2722980
  simp only [CollatzResearch.WordTrace]
  refine ⟨49657619837557991402375197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66210159783410655203166929 49657619837557991402375197)
  ·
    refine ⟨18621607439084246775890699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49657619837557991402375197 18621607439084246775890699)
    ·
      refine ⟨27932411158626370163836049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18621607439084246775890699 27932411158626370163836049)
      ·
        refine ⟨20949308368969777622877037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27932411158626370163836049 20949308368969777622877037)
        ·
          refine ⟨7855990638363666608578889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20949308368969777622877037 7855990638363666608578889)
          ·
            refine ⟨5891992978772749956434167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855990638363666608578889 5891992978772749956434167)
            ·
              refine ⟨8837989468159124934651251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891992978772749956434167 8837989468159124934651251)
              ·
                refine ⟨13256984202238687401976877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8837989468159124934651251 13256984202238687401976877)
                ·
                  refine ⟨4971369075839507775741329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13256984202238687401976877 4971369075839507775741329)
                  ·
                    refine ⟨3728526806879630831805997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4971369075839507775741329 3728526806879630831805997)
                    ·
                      refine ⟨1398197552579861561927249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728526806879630831805997 1398197552579861561927249)
                      ·
                        rfl

theorem cell23_2722980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_2722980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722980 prefixEnd_2722980 := by exact prefixLift 2722980
  have htrace : WordTrace (prefixWord ++ tailWord_2722980) baseStart_2722980 baseEnd_2722980 := by
    simpa [prefixWord, tailWord_2722980, baseEnd_2722980] using wordTrace_append hprefix tailTrace_2722980
  have hstable : (prefixWord ++ tailWord_2722980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722980).length < 2 ^ (prefixWord ++ tailWord_2722980).sum := by decide
  have hdescent : baseEnd_2722980 < baseStart_2722980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2722983 : List Nat := [1, 1, 6, 2, 1, 1, 2, 9]
def baseStart_2722983 : Nat := 118140960795 + 2722983 * 2 ^ 59
def prefixEnd_2722983 : Nat := 4983230072969 + 3 ^ 40 * 2722983 * 2
def baseEnd_2722983 : Nat := 51785151593400927784805

theorem tailTrace_2722983 : CollatzResearch.WordTrace tailWord_2722983 prefixEnd_2722983 51785151593400927784805 := by
  unfold tailWord_2722983
  simp only [CollatzResearch.WordTrace]
  refine ⟨99315349094105114317109603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66210232729403409544739735 99315349094105114317109603)
  ·
    refine ⟨148973023641157671475664405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99315349094105114317109603 148973023641157671475664405)
    ·
      refine ⟨6983110483179265850421769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148973023641157671475664405 6983110483179265850421769)
      ·
        refine ⟨5237332862384449387816327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6983110483179265850421769 5237332862384449387816327)
        ·
          refine ⟨7855999293576674081724491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5237332862384449387816327 7855999293576674081724491)
          ·
            refine ⟨11783998940365011122586737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7855999293576674081724491 11783998940365011122586737)
            ·
              refine ⟨8837999205273758341940053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11783998940365011122586737 8837999205273758341940053)
              ·
                refine ⟨51785151593400927784805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8837999205273758341940053 51785151593400927784805)
                ·
                  rfl

theorem cell23_2722983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 9].length) (baseStart_2722983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2722983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2722983 prefixEnd_2722983 := by exact prefixLift 2722983
  have htrace : WordTrace (prefixWord ++ tailWord_2722983) baseStart_2722983 baseEnd_2722983 := by
    simpa [prefixWord, tailWord_2722983, baseEnd_2722983] using wordTrace_append hprefix tailTrace_2722983
  have hstable : (prefixWord ++ tailWord_2722983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2722983).length < 2 ^ (prefixWord ++ tailWord_2722983).sum := by decide
  have hdescent : baseEnd_2722983 < baseStart_2722983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2722983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723054 : List Nat := [4, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_2723054 : Nat := 118140960795 + 2723054 * 2 ^ 59
def prefixEnd_2723054 : Nat := 4983230072969 + 3 ^ 40 * 2723054 * 2
def baseEnd_2723054 : Nat := 1398235550148294272401909

theorem tailTrace_2723054 : CollatzResearch.WordTrace tailWord_2723054 prefixEnd_2723054 1398235550148294272401909 := by
  unfold tailWord_2723054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12414742334605986680368027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66211959117898595628629477 12414742334605986680368027)
  ·
    refine ⟨18622113501908980020552041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12414742334605986680368027 18622113501908980020552041)
    ·
      refine ⟨13966585126431735015414031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18622113501908980020552041 13966585126431735015414031)
      ·
        refine ⟨20949877689647602523121047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13966585126431735015414031 20949877689647602523121047)
        ·
          refine ⟨31424816534471403784681571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20949877689647602523121047 31424816534471403784681571)
          ·
            refine ⟨47137224801707105677022357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31424816534471403784681571 47137224801707105677022357)
            ·
              refine ⟨2209557412580020578610423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47137224801707105677022357 2209557412580020578610423)
              ·
                refine ⟨3314336118870030867915635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2209557412580020578610423 3314336118870030867915635)
                ·
                  refine ⟨4971504178305046301873453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314336118870030867915635 4971504178305046301873453)
                  ·
                    refine ⟨1864314066864392363202545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4971504178305046301873453 1864314066864392363202545)
                    ·
                      refine ⟨1398235550148294272401909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864314066864392363202545 1398235550148294272401909)
                      ·
                        rfl

theorem cell23_2723054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_2723054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723054 prefixEnd_2723054 := by exact prefixLift 2723054
  have htrace : WordTrace (prefixWord ++ tailWord_2723054) baseStart_2723054 baseEnd_2723054 := by
    simpa [prefixWord, tailWord_2723054, baseEnd_2723054] using wordTrace_append hprefix tailTrace_2723054
  have hstable : (prefixWord ++ tailWord_2723054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723054).length < 2 ^ (prefixWord ++ tailWord_2723054).sum := by decide
  have hdescent : baseEnd_2723054 < baseStart_2723054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723073 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 7]
def baseStart_2723073 : Nat := 118140960795 + 2723073 * 2 ^ 59
def prefixEnd_2723073 : Nat := 4983230072969 + 3 ^ 40 * 2723073 * 2
def baseEnd_2723073 : Nat := 155360589586747744229369

theorem tailTrace_2723073 : CollatzResearch.WordTrace tailWord_2723073 prefixEnd_2723073 155360589586747744229369 := by
  unfold tailWord_2723073
  simp only [CollatzResearch.WordTrace]
  refine ⟨99318631663779059687885873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66212421109186039791923915 99318631663779059687885873)
  ·
    refine ⟨74488973747834294765914405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99318631663779059687885873 74488973747834294765914405)
    ·
      refine ⟨13966682577718930268608951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74488973747834294765914405 13966682577718930268608951)
      ·
        refine ⟨20950023866578395402913427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13966682577718930268608951 20950023866578395402913427)
        ·
          refine ⟨31425035799867593104370141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20950023866578395402913427 31425035799867593104370141)
          ·
            refine ⟨11784388424950347414138803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31425035799867593104370141 11784388424950347414138803)
            ·
              refine ⟨17676582637425521121208205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11784388424950347414138803 17676582637425521121208205)
              ·
                refine ⟨6628718489034570420453077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17676582637425521121208205 6628718489034570420453077)
                ·
                  refine ⟨155360589586747744229369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6628718489034570420453077 155360589586747744229369)
                  ·
                    rfl

theorem cell23_2723073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 7].length) (baseStart_2723073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723073 prefixEnd_2723073 := by exact prefixLift 2723073
  have htrace : WordTrace (prefixWord ++ tailWord_2723073) baseStart_2723073 baseEnd_2723073 := by
    simpa [prefixWord, tailWord_2723073, baseEnd_2723073] using wordTrace_append hprefix tailTrace_2723073
  have hstable : (prefixWord ++ tailWord_2723073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723073).length < 2 ^ (prefixWord ++ tailWord_2723073).sum := by decide
  have hdescent : baseEnd_2723073 < baseStart_2723073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723107 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 5]
def baseStart_2723107 : Nat := 118140960795 + 2723107 * 2 ^ 59
def prefixEnd_2723107 : Nat := 4983230072969 + 3 ^ 40 * 2723107 * 2
def baseEnd_2723107 : Nat := 155362529402553618337685

theorem tailTrace_2723107 : CollatzResearch.WordTrace tailWord_2723107 prefixEnd_2723107 155362529402553618337685 := by
  unfold tailWord_2723107
  simp only [CollatzResearch.WordTrace]
  refine ⟨99319871745655883494623575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66213247830437255663082383 99319871745655883494623575)
  ·
    refine ⟨148979807618483825241935363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99319871745655883494623575 148979807618483825241935363)
    ·
      refine ⟨223469711427725737862903045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148979807618483825241935363 223469711427725737862903045)
      ·
        refine ⟨41900570892698575849294321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223469711427725737862903045 41900570892698575849294321)
        ·
          refine ⟨31425428169523931886970741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41900570892698575849294321 31425428169523931886970741)
          ·
            refine ⟨2946133890892868614403507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31425428169523931886970741 2946133890892868614403507)
            ·
              refine ⟨4419200836339302921605261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946133890892868614403507 4419200836339302921605261)
              ·
                refine ⟨1657200313627238595601973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4419200836339302921605261 1657200313627238595601973)
                ·
                  refine ⟨155362529402553618337685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657200313627238595601973 155362529402553618337685)
                  ·
                    rfl

theorem cell23_2723107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 5].length) (baseStart_2723107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723107 prefixEnd_2723107 := by exact prefixLift 2723107
  have htrace : WordTrace (prefixWord ++ tailWord_2723107) baseStart_2723107 baseEnd_2723107 := by
    simpa [prefixWord, tailWord_2723107, baseEnd_2723107] using wordTrace_append hprefix tailTrace_2723107
  have hstable : (prefixWord ++ tailWord_2723107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723107).length < 2 ^ (prefixWord ++ tailWord_2723107).sum := by decide
  have hdescent : baseEnd_2723107 < baseStart_2723107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723124 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 5]
def baseStart_2723124 : Nat := 118140960795 + 2723124 * 2 ^ 59
def prefixEnd_2723124 : Nat := 4983230072969 + 3 ^ 40 * 2723124 * 2
def baseEnd_2723124 : Nat := 155363499310456555391843

theorem tailTrace_2723124 : CollatzResearch.WordTrace tailWord_2723124 prefixEnd_2723124 155363499310456555391843 := by
  unfold tailWord_2723124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49660245893297147698996213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66213661191062863598661617 49660245893297147698996213)
  ·
    refine ⟨4655648052496607596780895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49660245893297147698996213 4655648052496607596780895)
    ·
      refine ⟨6983472078744911395171343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4655648052496607596780895 6983472078744911395171343)
      ·
        refine ⟨10475208118117367092757015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6983472078744911395171343 10475208118117367092757015)
        ·
          refine ⟨15712812177176050639135523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10475208118117367092757015 15712812177176050639135523)
          ·
            refine ⟨23569218265764075958703285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15712812177176050639135523 23569218265764075958703285)
            ·
              refine ⟨2209614212415382121128433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23569218265764075958703285 2209614212415382121128433)
              ·
                refine ⟨1657210659311536590846325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2209614212415382121128433 1657210659311536590846325)
                ·
                  refine ⟨155363499310456555391843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657210659311536590846325 155363499310456555391843)
                  ·
                    rfl

theorem cell23_2723124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_2723124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723124 prefixEnd_2723124 := by exact prefixLift 2723124
  have htrace : WordTrace (prefixWord ++ tailWord_2723124) baseStart_2723124 baseEnd_2723124 := by
    simpa [prefixWord, tailWord_2723124, baseEnd_2723124] using wordTrace_append hprefix tailTrace_2723124
  have hstable : (prefixWord ++ tailWord_2723124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723124).length < 2 ^ (prefixWord ++ tailWord_2723124).sum := by decide
  have hdescent : baseEnd_2723124 < baseStart_2723124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723150 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_2723150 : Nat := 118140960795 + 2723150 * 2 ^ 59
def prefixEnd_2723150 : Nat := 4983230072969 + 3 ^ 40 * 2723150 * 2
def baseEnd_2723150 : Nat := 466094948097041965600489

theorem tailTrace_2723150 : CollatzResearch.WordTrace tailWord_2723150 prefixEnd_2723150 466094948097041965600489 := by
  unfold tailWord_2723150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12415180010562512729804863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66214293389666734558959269 12415180010562512729804863)
  ·
    refine ⟨18622770015843769094707295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12415180010562512729804863 18622770015843769094707295)
    ·
      refine ⟨27934155023765653642060943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18622770015843769094707295 27934155023765653642060943)
      ·
        refine ⟨41901232535648480463091415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27934155023765653642060943 41901232535648480463091415)
        ·
          refine ⟨62851848803472720694637123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41901232535648480463091415 62851848803472720694637123)
          ·
            refine ⟨94277773205209081041955685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62851848803472720694637123 94277773205209081041955685)
            ·
              refine ⟨17677082475976702695366691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94277773205209081041955685 17677082475976702695366691)
              ·
                refine ⟨26515623713965054043050037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17677082475976702695366691 26515623713965054043050037)
                ·
                  refine ⟨2485839723184223816535941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26515623713965054043050037 2485839723184223816535941)
                  ·
                    refine ⟨466094948097041965600489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2485839723184223816535941 466094948097041965600489)
                    ·
                      rfl

theorem cell23_2723150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_2723150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723150 prefixEnd_2723150 := by exact prefixLift 2723150
  have htrace : WordTrace (prefixWord ++ tailWord_2723150) baseStart_2723150 baseEnd_2723150 := by
    simpa [prefixWord, tailWord_2723150, baseEnd_2723150] using wordTrace_append hprefix tailTrace_2723150
  have hstable : (prefixWord ++ tailWord_2723150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723150).length < 2 ^ (prefixWord ++ tailWord_2723150).sum := by decide
  have hdescent : baseEnd_2723150 < baseStart_2723150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723157 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_2723157 : Nat := 118140960795 + 2723157 * 2 ^ 59
def prefixEnd_2723157 : Nat := 4983230072969 + 3 ^ 40 * 2723157 * 2
def baseEnd_2723157 : Nat := 1398288438655707369413935

theorem tailTrace_2723157 : CollatzResearch.WordTrace tailWord_2723157 prefixEnd_2723157 1398288438655707369413935 := by
  unfold tailWord_2723157
  simp only [CollatzResearch.WordTrace]
  refine ⟨99321695395474742033943725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66214463596983161355962483 99321695395474742033943725)
  ·
    refine ⟨37245635773303028262728897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99321695395474742033943725 37245635773303028262728897)
    ·
      refine ⟨27934226829977271197046673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37245635773303028262728897 27934226829977271197046673)
      ·
        refine ⟨20950670122482953397785005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27934226829977271197046673 20950670122482953397785005)
        ·
          refine ⟨7856501295931107524169377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20950670122482953397785005 7856501295931107524169377)
          ·
            refine ⟨5892375971948330643127033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7856501295931107524169377 5892375971948330643127033)
            ·
              refine ⟨4419281978961247982345275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5892375971948330643127033 4419281978961247982345275)
              ·
                refine ⟨6628922968441871973517913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419281978961247982345275 6628922968441871973517913)
                ·
                  refine ⟨4971692226331403980138435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6628922968441871973517913 4971692226331403980138435)
                  ·
                    refine ⟨7457538339497105970207653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4971692226331403980138435 7457538339497105970207653)
                    ·
                      refine ⟨1398288438655707369413935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7457538339497105970207653 1398288438655707369413935)
                      ·
                        rfl

theorem cell23_2723157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_2723157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723157 prefixEnd_2723157 := by exact prefixLift 2723157
  have htrace : WordTrace (prefixWord ++ tailWord_2723157) baseStart_2723157 baseEnd_2723157 := by
    simpa [prefixWord, tailWord_2723157, baseEnd_2723157] using wordTrace_append hprefix tailTrace_2723157
  have hstable : (prefixWord ++ tailWord_2723157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723157).length < 2 ^ (prefixWord ++ tailWord_2723157).sum := by decide
  have hdescent : baseEnd_2723157 < baseStart_2723157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723167 : List Nat := [1, 1, 2, 3, 1, 2, 1, 7, 1, 4]
def baseStart_2723167 : Nat := 118140960795 + 2723167 * 2 ^ 59
def prefixEnd_2723167 : Nat := 4983230072969 + 3 ^ 40 * 2723167 * 2
def baseEnd_2723167 : Nat := 466097857820750776762963

theorem tailTrace_2723167 : CollatzResearch.WordTrace tailWord_2723167 prefixEnd_2723167 466097857820750776762963 := by
  unfold tailWord_2723167
  simp only [CollatzResearch.WordTrace]
  refine ⟨99322060125438513741807755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66214706750292342494538503 99322060125438513741807755)
  ·
    refine ⟨148983090188157770612711633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99322060125438513741807755 148983090188157770612711633)
    ·
      refine ⟨111737317641118327959533725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148983090188157770612711633 111737317641118327959533725)
      ·
        refine ⟨41901494115419372984825147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111737317641118327959533725 41901494115419372984825147)
        ·
          refine ⟨62852241173129059477237721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41901494115419372984825147 62852241173129059477237721)
          ·
            refine ⟨47139180879846794607928291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62852241173129059477237721 47139180879846794607928291)
            ·
              refine ⟨70708771319770191911892437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47139180879846794607928291 70708771319770191911892437)
              ·
                refine ⟨1657236827807113872934979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70708771319770191911892437 1657236827807113872934979)
                ·
                  refine ⟨2485855241710670809402469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657236827807113872934979 2485855241710670809402469)
                  ·
                    refine ⟨466097857820750776762963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2485855241710670809402469 466097857820750776762963)
                    ·
                      rfl

theorem cell23_2723167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 7, 1, 4].length) (baseStart_2723167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723167 prefixEnd_2723167 := by exact prefixLift 2723167
  have htrace : WordTrace (prefixWord ++ tailWord_2723167) baseStart_2723167 baseEnd_2723167 := by
    simpa [prefixWord, tailWord_2723167, baseEnd_2723167] using wordTrace_append hprefix tailTrace_2723167
  have hstable : (prefixWord ++ tailWord_2723167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723167).length < 2 ^ (prefixWord ++ tailWord_2723167).sum := by decide
  have hdescent : baseEnd_2723167 < baseStart_2723167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723170 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2723170 : Nat := 118140960795 + 2723170 * 2 ^ 59
def prefixEnd_2723170 : Nat := 4983230072969 + 3 ^ 40 * 2723170 * 2
def baseEnd_2723170 : Nat := 1398295113904215818551375

theorem tailTrace_2723170 : CollatzResearch.WordTrace tailWord_2723170 prefixEnd_2723170 1398295113904215818551375 := by
  unfold tailWord_2723170
  simp only [CollatzResearch.WordTrace]
  refine ⟨24830542386106911313541741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66214779696285096836111309 24830542386106911313541741)
  ·
    refine ⟨9311453394790091742578153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24830542386106911313541741 9311453394790091742578153)
    ·
      refine ⟨6983590046092568806933615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9311453394790091742578153 6983590046092568806933615)
      ·
        refine ⟨10475385069138853210400423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6983590046092568806933615 10475385069138853210400423)
        ·
          refine ⟨15713077603708279815600635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10475385069138853210400423 15713077603708279815600635)
          ·
            refine ⟨23569616405562419723400953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15713077603708279815600635 23569616405562419723400953)
            ·
              refine ⟨17677212304171814792550715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23569616405562419723400953 17677212304171814792550715)
              ·
                refine ⟨26515818456257722188826073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17677212304171814792550715 26515818456257722188826073)
                ·
                  refine ⟨19886863842193291641619555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26515818456257722188826073 19886863842193291641619555)
                  ·
                    refine ⟨29830295763289937462429333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19886863842193291641619555 29830295763289937462429333)
                    ·
                      refine ⟨1398295113904215818551375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29830295763289937462429333 1398295113904215818551375)
                      ·
                        rfl

theorem cell23_2723170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2723170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723170 prefixEnd_2723170 := by exact prefixLift 2723170
  have htrace : WordTrace (prefixWord ++ tailWord_2723170) baseStart_2723170 baseEnd_2723170 := by
    simpa [prefixWord, tailWord_2723170, baseEnd_2723170] using wordTrace_append hprefix tailTrace_2723170
  have hstable : (prefixWord ++ tailWord_2723170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723170).length < 2 ^ (prefixWord ++ tailWord_2723170).sum := by decide
  have hdescent : baseEnd_2723170 < baseStart_2723170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723180 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 6]
def baseStart_2723180 : Nat := 118140960795 + 2723180 * 2 ^ 59
def prefixEnd_2723180 : Nat := 4983230072969 + 3 ^ 40 * 2723180 * 2
def baseEnd_2723180 : Nat := 155366694301195642158481

theorem tailTrace_2723180 : CollatzResearch.WordTrace tailWord_2723180 prefixEnd_2723180 155366694301195642158481 := by
  unfold tailWord_2723180
  simp only [CollatzResearch.WordTrace]
  refine ⟨49661267137195708481015497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66215022849594277974687329 49661267137195708481015497)
  ·
    refine ⟨37245950352896781360761623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49661267137195708481015497 37245950352896781360761623)
    ·
      refine ⟨55868925529345172041142435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37245950352896781360761623 55868925529345172041142435)
      ·
        refine ⟨83803388294017758061713653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55868925529345172041142435 83803388294017758061713653)
        ·
          refine ⟨7856567652564164818285655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83803388294017758061713653 7856567652564164818285655)
          ·
            refine ⟨11784851478846247227428483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7856567652564164818285655 11784851478846247227428483)
            ·
              refine ⟨17677277218269370841142725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11784851478846247227428483 17677277218269370841142725)
              ·
                refine ⟨3314489478425507032714261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17677277218269370841142725 3314489478425507032714261)
                ·
                  refine ⟨155366694301195642158481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3314489478425507032714261 155366694301195642158481)
                  ·
                    rfl

theorem cell23_2723180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_2723180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723180 prefixEnd_2723180 := by exact prefixLift 2723180
  have htrace : WordTrace (prefixWord ++ tailWord_2723180) baseStart_2723180 baseEnd_2723180 := by
    simpa [prefixWord, tailWord_2723180, baseEnd_2723180] using wordTrace_append hprefix tailTrace_2723180
  have hstable : (prefixWord ++ tailWord_2723180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723180).length < 2 ^ (prefixWord ++ tailWord_2723180).sum := by decide
  have hdescent : baseEnd_2723180 < baseStart_2723180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723183 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_2723183 : Nat := 118140960795 + 2723183 * 2 ^ 59
def prefixEnd_2723183 : Nat := 4983230072969 + 3 ^ 40 * 2723183 * 2
def baseEnd_2723183 : Nat := 1398301789152724267688815

theorem tailTrace_2723183 : CollatzResearch.WordTrace tailWord_2723183 prefixEnd_2723183 1398301789152724267688815 := by
  unfold tailWord_2723183
  simp only [CollatzResearch.WordTrace]
  refine ⟨99322643693380548474390203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66215095795587032316260135 99322643693380548474390203)
  ·
    refine ⟨148983965540070822711585305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99322643693380548474390203 148983965540070822711585305)
    ·
      refine ⟨111737974155053117033688979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148983965540070822711585305 111737974155053117033688979)
      ·
        refine ⟨167606961232579675550533469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111737974155053117033688979 167606961232579675550533469)
        ·
          refine ⟨62852610462217378331450051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167606961232579675550533469 62852610462217378331450051)
          ·
            refine ⟨94278915693326067497175077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62852610462217378331450051 94278915693326067497175077)
            ·
              refine ⟨17677296692498637655720327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94278915693326067497175077 17677296692498637655720327)
              ·
                refine ⟨26515945038747956483580491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17677296692498637655720327 26515945038747956483580491)
                ·
                  refine ⟨39773917558121934725370737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26515945038747956483580491 39773917558121934725370737)
                  ·
                    refine ⟨29830438168591451044028053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39773917558121934725370737 29830438168591451044028053)
                    ·
                      refine ⟨1398301789152724267688815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29830438168591451044028053 1398301789152724267688815)
                      ·
                        rfl

theorem cell23_2723183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_2723183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723183 prefixEnd_2723183 := by exact prefixLift 2723183
  have htrace : WordTrace (prefixWord ++ tailWord_2723183) baseStart_2723183 baseEnd_2723183 := by
    simpa [prefixWord, tailWord_2723183, baseEnd_2723183] using wordTrace_append hprefix tailTrace_2723183
  have hstable : (prefixWord ++ tailWord_2723183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723183).length < 2 ^ (prefixWord ++ tailWord_2723183).sum := by decide
  have hdescent : baseEnd_2723183 < baseStart_2723183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723207 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_2723207 : Nat := 118140960795 + 2723207 * 2 ^ 59
def prefixEnd_2723207 : Nat := 4983230072969 + 3 ^ 40 * 2723207 * 2
def baseEnd_2723207 : Nat := 1398314112688432173788705

theorem tailTrace_2723207 : CollatzResearch.WordTrace tailWord_2723207 prefixEnd_2723207 1398314112688432173788705 := by
  unfold tailWord_2723207
  simp only [CollatzResearch.WordTrace]
  refine ⟨99323519045293600573263875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66215679363529067048842583 99323519045293600573263875)
  ·
    refine ⟨148985278567940400859895813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99323519045293600573263875 148985278567940400859895813)
    ·
      refine ⟨27934739731488825161230465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148985278567940400859895813 27934739731488825161230465)
      ·
        refine ⟨20951054798616618870922849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27934739731488825161230465 20951054798616618870922849)
        ·
          refine ⟨15713291098962464153192137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20951054798616618870922849 15713291098962464153192137)
          ·
            refine ⟨11784968324221848114894103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15713291098962464153192137 11784968324221848114894103)
            ·
              refine ⟨17677452486332772172341155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11784968324221848114894103 17677452486332772172341155)
              ·
                refine ⟨26516178729499158258511733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17677452486332772172341155 26516178729499158258511733)
                ·
                  refine ⟨2485891755890546086735475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26516178729499158258511733 2485891755890546086735475)
                  ·
                    refine ⟨3728837633835819130103213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2485891755890546086735475 3728837633835819130103213)
                    ·
                      refine ⟨1398314112688432173788705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728837633835819130103213 1398314112688432173788705)
                      ·
                        rfl

theorem cell23_2723207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_2723207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723207 prefixEnd_2723207 := by exact prefixLift 2723207
  have htrace : WordTrace (prefixWord ++ tailWord_2723207) baseStart_2723207 baseEnd_2723207 := by
    simpa [prefixWord, tailWord_2723207, baseEnd_2723207] using wordTrace_append hprefix tailTrace_2723207
  have hstable : (prefixWord ++ tailWord_2723207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723207).length < 2 ^ (prefixWord ++ tailWord_2723207).sum := by decide
  have hdescent : baseEnd_2723207 < baseStart_2723207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723218 : List Nat := [3, 2, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_2723218 : Nat := 118140960795 + 2723218 * 2 ^ 59
def prefixEnd_2723218 : Nat := 4983230072969 + 3 ^ 40 * 2723218 * 2
def baseEnd_2723218 : Nat := 466106586991877210250385

theorem tailTrace_2723218 : CollatzResearch.WordTrace tailWord_2723218 prefixEnd_2723218 466106586991877210250385 := by
  unfold tailWord_2723218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24830980062063437362978577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66215946832169166301276205 24830980062063437362978577)
  ·
    refine ⟨18623235046547578022233933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24830980062063437362978577 18623235046547578022233933)
    ·
      refine ⟨6983713142455341758337725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18623235046547578022233933 6983713142455341758337725)
      ·
        refine ⟨2618892428420753159376647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6983713142455341758337725 2618892428420753159376647)
        ·
          refine ⟨3928338642631129739064971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618892428420753159376647 3928338642631129739064971)
          ·
            refine ⟨5892507963946694608597457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928338642631129739064971 5892507963946694608597457)
            ·
              refine ⟨4419380972960020956448093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5892507963946694608597457 4419380972960020956448093)
              ·
                refine ⟨1657267864860007858668035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4419380972960020956448093 1657267864860007858668035)
                ·
                  refine ⟨2485901797290011788002053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657267864860007858668035 2485901797290011788002053)
                  ·
                    refine ⟨466106586991877210250385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2485901797290011788002053 466106586991877210250385)
                    ·
                      rfl

theorem cell23_2723218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_2723218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723218 prefixEnd_2723218 := by exact prefixLift 2723218
  have htrace : WordTrace (prefixWord ++ tailWord_2723218) baseStart_2723218 baseEnd_2723218 := by
    simpa [prefixWord, tailWord_2723218, baseEnd_2723218] using wordTrace_append hprefix tailTrace_2723218
  have hstable : (prefixWord ++ tailWord_2723218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723218).length < 2 ^ (prefixWord ++ tailWord_2723218).sum := by decide
  have hdescent : baseEnd_2723218 < baseStart_2723218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723243 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6]
def baseStart_2723243 : Nat := 118140960795 + 2723243 * 2 ^ 59
def prefixEnd_2723243 : Nat := 4983230072969 + 3 ^ 40 * 2723243 * 2
def baseEnd_2723243 : Nat := 1398332597991994032938539

theorem tailTrace_2723243 : CollatzResearch.WordTrace tailWord_2723243 prefixEnd_2723243 1398332597991994032938539 := by
  unfold tailWord_2723243
  simp only [CollatzResearch.WordTrace]
  refine ⟨99324832073163178721574383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66216554715442119147716255 99324832073163178721574383)
  ·
    refine ⟨148987248109744768082361575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99324832073163178721574383 148987248109744768082361575)
    ·
      refine ⟨223480872164617152123542363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148987248109744768082361575 223480872164617152123542363)
      ·
        refine ⟨335221308246925728185313545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223480872164617152123542363 335221308246925728185313545)
        ·
          refine ⟨251415981185194296138985159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335221308246925728185313545 251415981185194296138985159)
          ·
            refine ⟨377123971777791444208477739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251415981185194296138985159 377123971777791444208477739)
            ·
              refine ⟨565685957666687166312716609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377123971777791444208477739 565685957666687166312716609)
              ·
                refine ⟨424264468250015374734537457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565685957666687166312716609 424264468250015374734537457)
                ·
                  refine ⟨318198351187511531050903093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424264468250015374734537457 318198351187511531050903093)
                  ·
                    refine ⟨29831095423829206036022165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 318198351187511531050903093 29831095423829206036022165)
                    ·
                      refine ⟨1398332597991994032938539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29831095423829206036022165 1398332597991994032938539)
                      ·
                        rfl

theorem cell23_2723243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_2723243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723243 prefixEnd_2723243 := by exact prefixLift 2723243
  have htrace : WordTrace (prefixWord ++ tailWord_2723243) baseStart_2723243 baseEnd_2723243 := by
    simpa [prefixWord, tailWord_2723243, baseEnd_2723243] using wordTrace_append hprefix tailTrace_2723243
  have hstable : (prefixWord ++ tailWord_2723243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723243).length < 2 ^ (prefixWord ++ tailWord_2723243).sum := by decide
  have hdescent : baseEnd_2723243 < baseStart_2723243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723250 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_2723250 : Nat := 118140960795 + 2723250 * 2 ^ 59
def prefixEnd_2723250 : Nat := 4983230072969 + 3 ^ 40 * 2723250 * 2
def baseEnd_2723250 : Nat := 1398336192356575505551007

theorem tailTrace_2723250 : CollatzResearch.WordTrace tailWord_2723250 prefixEnd_2723250 1398336192356575505551007 := by
  unfold tailWord_2723250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24831271846034454729269801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66216724922758545944719469 24831271846034454729269801)
  ·
    refine ⟨18623453884525841046952351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24831271846034454729269801 18623453884525841046952351)
    ·
      refine ⟨27935180826788761570428527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18623453884525841046952351 27935180826788761570428527)
      ·
        refine ⟨41902771240183142355642791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27935180826788761570428527 41902771240183142355642791)
        ·
          refine ⟨62854156860274713533464187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41902771240183142355642791 62854156860274713533464187)
          ·
            refine ⟨94281235290412070300196281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62854156860274713533464187 94281235290412070300196281)
            ·
              refine ⟨70710926467809052725147211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94281235290412070300196281 70710926467809052725147211)
              ·
                refine ⟨106066389701713579087720817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70710926467809052725147211 106066389701713579087720817)
                ·
                  refine ⟨79549792276285184315790613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106066389701713579087720817 79549792276285184315790613)
                  ·
                    refine ⟨3728896512950868014802685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79549792276285184315790613 3728896512950868014802685)
                    ·
                      refine ⟨1398336192356575505551007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728896512950868014802685 1398336192356575505551007)
                      ·
                        rfl

theorem cell23_2723250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_2723250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723250 prefixEnd_2723250 := by exact prefixLift 2723250
  have htrace : WordTrace (prefixWord ++ tailWord_2723250) baseStart_2723250 baseEnd_2723250 := by
    simpa [prefixWord, tailWord_2723250, baseEnd_2723250] using wordTrace_append hprefix tailTrace_2723250
  have hstable : (prefixWord ++ tailWord_2723250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723250).length < 2 ^ (prefixWord ++ tailWord_2723250).sum := by decide
  have hdescent : baseEnd_2723250 < baseStart_2723250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723264 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 3, 2, 2]
def baseStart_2723264 : Nat := 118140960795 + 2723264 * 2 ^ 59
def prefixEnd_2723264 : Nat := 4983230072969 + 3 ^ 40 * 2723264 * 2
def baseEnd_2723264 : Nat := 1398343381085738450775943

theorem tailTrace_2723264 : CollatzResearch.WordTrace tailWord_2723264 prefixEnd_2723264 1398343381085738450775943 := by
  unfold tailWord_2723264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49662799003043549654044423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66217065337391399538725897 49662799003043549654044423)
  ·
    refine ⟨74494198504565324481066635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49662799003043549654044423 74494198504565324481066635)
    ·
      refine ⟨111741297756847986721599953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74494198504565324481066635 111741297756847986721599953)
      ·
        refine ⟨83805973317635990041199965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111741297756847986721599953 83805973317635990041199965)
        ·
          refine ⟨31427239994113496265449987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83805973317635990041199965 31427239994113496265449987)
          ·
            refine ⟨47140859991170244398174981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31427239994113496265449987 47140859991170244398174981)
            ·
              refine ⟨8838911248344420824657809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47140859991170244398174981 8838911248344420824657809)
              ·
                refine ⟨6629183436258315618493357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8838911248344420824657809 6629183436258315618493357)
                ·
                  refine ⟨2485943788596868356935009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6629183436258315618493357 2485943788596868356935009)
                  ·
                    refine ⟨1864457841447651267701257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2485943788596868356935009 1864457841447651267701257)
                    ·
                      refine ⟨1398343381085738450775943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864457841447651267701257 1398343381085738450775943)
                      ·
                        rfl

theorem cell23_2723264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_2723264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723264 prefixEnd_2723264 := by exact prefixLift 2723264
  have htrace : WordTrace (prefixWord ++ tailWord_2723264) baseStart_2723264 baseEnd_2723264 := by
    simpa [prefixWord, tailWord_2723264, baseEnd_2723264] using wordTrace_append hprefix tailTrace_2723264
  have hstable : (prefixWord ++ tailWord_2723264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723264).length < 2 ^ (prefixWord ++ tailWord_2723264).sum := by decide
  have hdescent : baseEnd_2723264 < baseStart_2723264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723267 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 3]
def baseStart_2723267 : Nat := 118140960795 + 2723267 * 2 ^ 59
def prefixEnd_2723267 : Nat := 4983230072969 + 3 ^ 40 * 2723267 * 2
def baseEnd_2723267 : Nat := 1398344921527701939038429

theorem tailTrace_2723267 : CollatzResearch.WordTrace tailWord_2723267 prefixEnd_2723267 1398344921527701939038429 := by
  unfold tailWord_2723267
  simp only [CollatzResearch.WordTrace]
  refine ⟨99325707425076230820448055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66217138283384153880298703 99325707425076230820448055)
  ·
    refine ⟨148988561137614346230672083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99325707425076230820448055 148988561137614346230672083)
    ·
      refine ⟨223482841706421519346008125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148988561137614346230672083 223482841706421519346008125)
      ·
        refine ⟨83806065639908069754753047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223482841706421519346008125 83806065639908069754753047)
        ·
          refine ⟨125709098459862104632129571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83806065639908069754753047 125709098459862104632129571)
          ·
            refine ⟨188563647689793156948194357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125709098459862104632129571 188563647689793156948194357)
            ·
              refine ⟨17677841970918108463893221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188563647689793156948194357 17677841970918108463893221)
              ·
                refine ⟨3314595369547145336979979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17677841970918108463893221 3314595369547145336979979)
                ·
                  refine ⟨4971893054320718005469969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3314595369547145336979979 4971893054320718005469969)
                  ·
                    refine ⟨3728919790740538504102477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4971893054320718005469969 3728919790740538504102477)
                    ·
                      refine ⟨1398344921527701939038429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3728919790740538504102477 1398344921527701939038429)
                      ·
                        rfl

theorem cell23_2723267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_2723267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723267 prefixEnd_2723267 := by exact prefixLift 2723267
  have htrace : WordTrace (prefixWord ++ tailWord_2723267) baseStart_2723267 baseEnd_2723267 := by
    simpa [prefixWord, tailWord_2723267, baseEnd_2723267] using wordTrace_append hprefix tailTrace_2723267
  have hstable : (prefixWord ++ tailWord_2723267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723267).length < 2 ^ (prefixWord ++ tailWord_2723267).sum := by decide
  have hdescent : baseEnd_2723267 < baseStart_2723267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723284 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2723284 : Nat := 118140960795 + 2723284 * 2 ^ 59
def prefixEnd_2723284 : Nat := 4983230072969 + 3 ^ 40 * 2723284 * 2
def baseEnd_2723284 : Nat := 1398353650698828372525851

theorem tailTrace_2723284 : CollatzResearch.WordTrace tailWord_2723284 prefixEnd_2723284 1398353650698828372525851 := by
  unfold tailWord_2723284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49663163733007321361908453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66217551644009761815877937 49663163733007321361908453)
  ·
    refine ⟨9311843199938872755357835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49663163733007321361908453 9311843199938872755357835)
    ·
      refine ⟨13967764799908309133036753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9311843199938872755357835 13967764799908309133036753)
      ·
        refine ⟨10475823599931231849777565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13967764799908309133036753 10475823599931231849777565)
        ·
          refine ⟨3928433849974211943666587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10475823599931231849777565 3928433849974211943666587)
          ·
            refine ⟨5892650774961317915499881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928433849974211943666587 5892650774961317915499881)
            ·
              refine ⟨4419488081220988436624911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5892650774961317915499881 4419488081220988436624911)
              ·
                refine ⟨6629232121831482654937367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419488081220988436624911 6629232121831482654937367)
                ·
                  refine ⟨9943848182747223982406051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6629232121831482654937367 9943848182747223982406051)
                  ·
                    refine ⟨14915772274120835973609077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9943848182747223982406051 14915772274120835973609077)
                    ·
                      refine ⟨1398353650698828372525851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14915772274120835973609077 1398353650698828372525851)
                      ·
                        rfl

theorem cell23_2723284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2723284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723284 prefixEnd_2723284 := by exact prefixLift 2723284
  have htrace : WordTrace (prefixWord ++ tailWord_2723284) baseStart_2723284 baseEnd_2723284 := by
    simpa [prefixWord, tailWord_2723284, baseEnd_2723284] using wordTrace_append hprefix tailTrace_2723284
  have hstable : (prefixWord ++ tailWord_2723284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723284).length < 2 ^ (prefixWord ++ tailWord_2723284).sum := by decide
  have hdescent : baseEnd_2723284 < baseStart_2723284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723357 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 3]
def baseStart_2723357 : Nat := 118140960795 + 2723357 * 2 ^ 59
def prefixEnd_2723357 : Nat := 4983230072969 + 3 ^ 40 * 2723357 * 2
def baseEnd_2723357 : Nat := 1398391134786606586913015

theorem tailTrace_2723357 : CollatzResearch.WordTrace tailWord_2723357 prefixEnd_2723357 1398391134786606586913015 := by
  unfold tailWord_2723357
  simp only [CollatzResearch.WordTrace]
  refine ⟨99328989994750176191224325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66219326663166784127482883 99328989994750176191224325)
  ·
    refine ⟨18624185624015658035854561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99328989994750176191224325 18624185624015658035854561)
    ·
      refine ⟨13968139218011743526890921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18624185624015658035854561 13968139218011743526890921)
      ·
        refine ⟨10476104413508807645168191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13968139218011743526890921 10476104413508807645168191)
        ·
          refine ⟨15714156620263211467752287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10476104413508807645168191 15714156620263211467752287)
          ·
            refine ⟨23571234930394817201628431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15714156620263211467752287 23571234930394817201628431)
            ·
              refine ⟨35356852395592225802442647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23571234930394817201628431 35356852395592225802442647)
              ·
                refine ⟨53035278593388338703663971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35356852395592225802442647 53035278593388338703663971)
                ·
                  refine ⟨79552917890082508055495957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53035278593388338703663971 79552917890082508055495957)
                  ·
                    refine ⟨3729043026097617565101373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79552917890082508055495957 3729043026097617565101373)
                    ·
                      refine ⟨1398391134786606586913015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3729043026097617565101373 1398391134786606586913015)
                      ·
                        rfl

theorem cell23_2723357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_2723357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723357 prefixEnd_2723357 := by exact prefixLift 2723357
  have htrace : WordTrace (prefixWord ++ tailWord_2723357) baseStart_2723357 baseEnd_2723357 := by
    simpa [prefixWord, tailWord_2723357, baseEnd_2723357] using wordTrace_append hprefix tailTrace_2723357
  have hstable : (prefixWord ++ tailWord_2723357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723357).length < 2 ^ (prefixWord ++ tailWord_2723357).sum := by decide
  have hdescent : baseEnd_2723357 < baseStart_2723357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723427 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2723427 : Nat := 118140960795 + 2723427 * 2 ^ 59
def prefixEnd_2723427 : Nat := 4983230072969 + 3 ^ 40 * 2723427 * 2
def baseEnd_2723427 : Nat := 1398427078432421313037693

theorem tailTrace_2723427 : CollatzResearch.WordTrace tailWord_2723427 prefixEnd_2723427 1398427078432421313037693 := by
  unfold tailWord_2723427
  simp only [CollatzResearch.WordTrace]
  refine ⟨99331543104496578146272535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66221028736331052097515023 99331543104496578146272535)
  ·
    refine ⟨148997314656744867219408803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99331543104496578146272535 148997314656744867219408803)
    ·
      refine ⟨223495971985117300829113205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148997314656744867219408803 223495971985117300829113205)
      ·
        refine ⟨20952747373604746952729363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 223495971985117300829113205 20952747373604746952729363)
        ·
          refine ⟨31429121060407120429094045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20952747373604746952729363 31429121060407120429094045)
          ·
            refine ⟨11785920397652670160910267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31429121060407120429094045 11785920397652670160910267)
            ·
              refine ⟨17678880596479005241365401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11785920397652670160910267 17678880596479005241365401)
              ·
                refine ⟨13259160447359253931024051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17678880596479005241365401 13259160447359253931024051)
                ·
                  refine ⟨19888740671038880896536077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13259160447359253931024051 19888740671038880896536077)
                  ·
                    refine ⟨7458277751639580336201029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19888740671038880896536077 7458277751639580336201029)
                    ·
                      refine ⟨1398427078432421313037693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7458277751639580336201029 1398427078432421313037693)
                      ·
                        rfl

theorem cell23_2723427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2723427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723427 prefixEnd_2723427 := by exact prefixLift 2723427
  have htrace : WordTrace (prefixWord ++ tailWord_2723427) baseStart_2723427 baseEnd_2723427 := by
    simpa [prefixWord, tailWord_2723427, baseEnd_2723427] using wordTrace_append hprefix tailTrace_2723427
  have hstable : (prefixWord ++ tailWord_2723427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723427).length < 2 ^ (prefixWord ++ tailWord_2723427).sum := by decide
  have hdescent : baseEnd_2723427 < baseStart_2723427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723467 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 6]
def baseStart_2723467 : Nat := 118140960795 + 2723467 * 2 ^ 59
def prefixEnd_2723467 : Nat := 4983230072969 + 3 ^ 40 * 2723467 * 2
def baseEnd_2723467 : Nat := 155383068628733461837501

theorem tailTrace_2723467 : CollatzResearch.WordTrace tailWord_2723467 prefixEnd_2723467 155383068628733461837501 := by
  unfold tailWord_2723467
  simp only [CollatzResearch.WordTrace]
  refine ⟨99333002024351664977728655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66222001349567776651819103 99333002024351664977728655)
  ·
    refine ⟨148999503036527497466592983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99333002024351664977728655 148999503036527497466592983)
    ·
      refine ⟨223499254554791246199889475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148999503036527497466592983 223499254554791246199889475)
      ·
        refine ⟨335248881832186869299834213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223499254554791246199889475 335248881832186869299834213)
        ·
          refine ⟨62859165343535037993718915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335248881832186869299834213 62859165343535037993718915)
          ·
            refine ⟨94288748015302556990578373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62859165343535037993718915 94288748015302556990578373)
            ·
              refine ⟨17679140252869229435733445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94288748015302556990578373 17679140252869229435733445)
              ·
                refine ⟨3314838797412980519200021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17679140252869229435733445 3314838797412980519200021)
                ·
                  refine ⟨155383068628733461837501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3314838797412980519200021 155383068628733461837501)
                  ·
                    rfl

theorem cell23_2723467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 6].length) (baseStart_2723467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723467 prefixEnd_2723467 := by exact prefixLift 2723467
  have htrace : WordTrace (prefixWord ++ tailWord_2723467) baseStart_2723467 baseEnd_2723467 := by
    simpa [prefixWord, tailWord_2723467, baseEnd_2723467] using wordTrace_append hprefix tailTrace_2723467
  have hstable : (prefixWord ++ tailWord_2723467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723467).length < 2 ^ (prefixWord ++ tailWord_2723467).sum := by decide
  have hdescent : baseEnd_2723467 < baseStart_2723467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723504 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 1, 5, 2]
def baseStart_2723504 : Nat := 118140960795 + 2723504 * 2 ^ 59
def prefixEnd_2723504 : Nat := 4983230072969 + 3 ^ 40 * 2723504 * 2
def baseEnd_2723504 : Nat := 1398466616442817511774839

theorem tailTrace_2723504 : CollatzResearch.WordTrace tailWord_2723504 prefixEnd_2723504 1398466616442817511774839 := by
  unfold tailWord_2723504
  simp only [CollatzResearch.WordTrace]
  refine ⟨49667175762608810148412783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66222901016811746864550377 49667175762608810148412783)
  ·
    refine ⟨74500763643913215222619175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49667175762608810148412783 74500763643913215222619175)
    ·
      refine ⟨111751145465869822833928763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74500763643913215222619175 111751145465869822833928763)
      ·
        refine ⟨167626718198804734250893145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111751145465869822833928763 167626718198804734250893145)
        ·
          refine ⟨125720038649103550688169859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167626718198804734250893145 125720038649103550688169859)
          ·
            refine ⟨188580057973655326032254789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125720038649103550688169859 188580057973655326032254789)
            ·
              refine ⟨35358760870060373631047773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188580057973655326032254789 35358760870060373631047773)
              ·
                refine ⟨13259535326272640111642915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35358760870060373631047773 13259535326272640111642915)
                ·
                  refine ⟨19889302989408960167464373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13259535326272640111642915 19889302989408960167464373)
                  ·
                    refine ⟨1864622155257090015699785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19889302989408960167464373 1864622155257090015699785)
                    ·
                      refine ⟨1398466616442817511774839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864622155257090015699785 1398466616442817511774839)
                      ·
                        rfl

theorem cell23_2723504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 5, 2].length) (baseStart_2723504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723504 prefixEnd_2723504 := by exact prefixLift 2723504
  have htrace : WordTrace (prefixWord ++ tailWord_2723504) baseStart_2723504 baseEnd_2723504 := by
    simpa [prefixWord, tailWord_2723504, baseEnd_2723504] using wordTrace_append hprefix tailTrace_2723504
  have hstable : (prefixWord ++ tailWord_2723504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723504).length < 2 ^ (prefixWord ++ tailWord_2723504).sum := by decide
  have hdescent : baseEnd_2723504 < baseStart_2723504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723527 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 3, 6]
def baseStart_2723527 : Nat := 118140960795 + 2723527 * 2 ^ 59
def prefixEnd_2723527 : Nat := 4983230072969 + 3 ^ 40 * 2723527 * 2
def baseEnd_2723527 : Nat := 466159475499290307262411

theorem tailTrace_2723527 : CollatzResearch.WordTrace tailWord_2723527 prefixEnd_2723527 466159475499290307262411 := by
  unfold tailWord_2723527
  simp only [CollatzResearch.WordTrace]
  refine ⟨99335190404134295224912835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66223460269422863483275223 99335190404134295224912835)
  ·
    refine ⟨149002785606201442837369253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99335190404134295224912835 149002785606201442837369253)
    ·
      refine ⟨27938022301162770532006735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149002785606201442837369253 27938022301162770532006735)
      ·
        refine ⟨41907033451744155798010103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27938022301162770532006735 41907033451744155798010103)
        ·
          refine ⟨62860550177616233697015155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41907033451744155798010103 62860550177616233697015155)
          ·
            refine ⟨94290825266424350545522733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62860550177616233697015155 94290825266424350545522733)
            ·
              refine ⟨35359059474909131454571025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94290825266424350545522733 35359059474909131454571025)
              ·
                refine ⟨26519294606181848590928269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35359059474909131454571025 26519294606181848590928269)
                ·
                  refine ⟨9944735477318193221598101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26519294606181848590928269 9944735477318193221598101)
                  ·
                    refine ⟨466159475499290307262411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9944735477318193221598101 466159475499290307262411)
                    ·
                      rfl

theorem cell23_2723527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_2723527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723527 prefixEnd_2723527 := by exact prefixLift 2723527
  have htrace : WordTrace (prefixWord ++ tailWord_2723527) baseStart_2723527 baseEnd_2723527 := by
    simpa [prefixWord, tailWord_2723527, baseEnd_2723527] using wordTrace_append hprefix tailTrace_2723527
  have hstable : (prefixWord ++ tailWord_2723527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723527).length < 2 ^ (prefixWord ++ tailWord_2723527).sum := by decide
  have hdescent : baseEnd_2723527 < baseStart_2723527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723528 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_2723528 : Nat := 118140960795 + 2723528 * 2 ^ 59
def prefixEnd_2723528 : Nat := 4983230072969 + 3 ^ 40 * 2723528 * 2
def baseEnd_2723528 : Nat := 1398478939978525417874729

theorem tailTrace_2723528 : CollatzResearch.WordTrace tailWord_2723528 prefixEnd_2723528 1398478939978525417874729 := by
  unfold tailWord_2723528
  simp only [CollatzResearch.WordTrace]
  refine ⟨49667613438565336197849619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66223484584753781597132825 49667613438565336197849619)
  ·
    refine ⟨74501420157848004296774429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49667613438565336197849619 74501420157848004296774429)
    ·
      refine ⟨27938032559193001611290411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74501420157848004296774429 27938032559193001611290411)
      ·
        refine ⟨41907048838789502416935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27938032559193001611290411 41907048838789502416935617)
        ·
          refine ⟨31430286629092126812701713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41907048838789502416935617 31430286629092126812701713)
          ·
            refine ⟨23572714971819095109526285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31430286629092126812701713 23572714971819095109526285)
            ·
              refine ⟨8839768114432160666072357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23572714971819095109526285 8839768114432160666072357)
              ·
                refine ⟨1657456521456030124888567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8839768114432160666072357 1657456521456030124888567)
                ·
                  refine ⟨2486184782184045187332851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657456521456030124888567 2486184782184045187332851)
                  ·
                    refine ⟨3729277173276067780999277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2486184782184045187332851 3729277173276067780999277)
                    ·
                      refine ⟨1398478939978525417874729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3729277173276067780999277 1398478939978525417874729)
                      ·
                        rfl

theorem cell23_2723528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_2723528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723528 prefixEnd_2723528 := by exact prefixLift 2723528
  have htrace : WordTrace (prefixWord ++ tailWord_2723528) baseStart_2723528 baseEnd_2723528 := by
    simpa [prefixWord, tailWord_2723528, baseEnd_2723528] using wordTrace_append hprefix tailTrace_2723528
  have hstable : (prefixWord ++ tailWord_2723528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723528).length < 2 ^ (prefixWord ++ tailWord_2723528).sum := by decide
  have hdescent : baseEnd_2723528 < baseStart_2723528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723534 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2723534 : Nat := 118140960795 + 2723534 * 2 ^ 59
def prefixEnd_2723534 : Nat := 4983230072969 + 3 ^ 40 * 2723534 * 2
def baseEnd_2723534 : Nat := 1398482020862452394399701

theorem tailTrace_2723534 : CollatzResearch.WordTrace tailWord_2723534 prefixEnd_2723534 1398482020862452394399701 := by
  unfold tailWord_2723534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12416930714388616927552207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66223630476739290280278437 12416930714388616927552207)
  ·
    refine ⟨18625396071582925391328311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12416930714388616927552207 18625396071582925391328311)
    ·
      refine ⟨27938094107374388086992467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18625396071582925391328311 27938094107374388086992467)
      ·
        refine ⟨41907141161061582130488701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27938094107374388086992467 41907141161061582130488701)
        ·
          refine ⟨15715177935398093298933263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41907141161061582130488701 15715177935398093298933263)
          ·
            refine ⟨23572766903097139948399895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15715177935398093298933263 23572766903097139948399895)
            ·
              refine ⟨35359150354645709922599843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23572766903097139948399895 35359150354645709922599843)
              ·
                refine ⟨53038725531968564883899765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35359150354645709922599843 53038725531968564883899765)
                ·
                  refine ⟨4972380518622052957865603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53038725531968564883899765 4972380518622052957865603)
                  ·
                    refine ⟨7458570777933079436798405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4972380518622052957865603 7458570777933079436798405)
                    ·
                      refine ⟨1398482020862452394399701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7458570777933079436798405 1398482020862452394399701)
                      ·
                        rfl

theorem cell23_2723534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2723534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723534 prefixEnd_2723534 := by exact prefixLift 2723534
  have htrace : WordTrace (prefixWord ++ tailWord_2723534) baseStart_2723534 baseEnd_2723534 := by
    simpa [prefixWord, tailWord_2723534, baseEnd_2723534] using wordTrace_append hprefix tailTrace_2723534
  have hstable : (prefixWord ++ tailWord_2723534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723534).length < 2 ^ (prefixWord ++ tailWord_2723534).sum := by decide
  have hdescent : baseEnd_2723534 < baseStart_2723534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723544 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 1, 6]
def baseStart_2723544 : Nat := 118140960795 + 2723544 * 2 ^ 59
def prefixEnd_2723544 : Nat := 4983230072969 + 3 ^ 40 * 2723544 * 2
def baseEnd_2723544 : Nat := 466162385222999118424885

theorem tailTrace_2723544 : CollatzResearch.WordTrace tailWord_2723544 prefixEnd_2723544 466162385222999118424885 := by
  unfold tailWord_2723544
  simp only [CollatzResearch.WordTrace]
  refine ⟨49667905222536353564140843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66223873630048471418854457 49667905222536353564140843)
  ·
    refine ⟨74501857833804530346211265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49667905222536353564140843 74501857833804530346211265)
    ·
      refine ⟨55876393375353397759658449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74501857833804530346211265 55876393375353397759658449)
      ·
        refine ⟨41907295031515048319743837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55876393375353397759658449 41907295031515048319743837)
        ·
          refine ⟨15715235636818143119903939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41907295031515048319743837 15715235636818143119903939)
          ·
            refine ⟨23572853455227214679855909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15715235636818143119903939 23572853455227214679855909)
            ·
              refine ⟨4419910022855102752472983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23572853455227214679855909 4419910022855102752472983)
              ·
                refine ⟨6629865034282654128709475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419910022855102752472983 6629865034282654128709475)
                ·
                  refine ⟨9944797551423981193064213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6629865034282654128709475 9944797551423981193064213)
                  ·
                    refine ⟨466162385222999118424885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9944797551423981193064213 466162385222999118424885)
                    ·
                      rfl

theorem cell23_2723544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_2723544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723544 prefixEnd_2723544 := by exact prefixLift 2723544
  have htrace : WordTrace (prefixWord ++ tailWord_2723544) baseStart_2723544 baseEnd_2723544 := by
    simpa [prefixWord, tailWord_2723544, baseEnd_2723544] using wordTrace_append hprefix tailTrace_2723544
  have hstable : (prefixWord ++ tailWord_2723544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723544).length < 2 ^ (prefixWord ++ tailWord_2723544).sum := by decide
  have hdescent : baseEnd_2723544 < baseStart_2723544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723555 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2723555 : Nat := 118140960795 + 2723555 * 2 ^ 59
def prefixEnd_2723555 : Nat := 4983230072969 + 3 ^ 40 * 2723555 * 2
def baseEnd_2723555 : Nat := 1398492803956196812237105

theorem tailTrace_2723555 : CollatzResearch.WordTrace tailWord_2723555 prefixEnd_2723555 1398492803956196812237105 := by
  unfold tailWord_2723555
  simp only [CollatzResearch.WordTrace]
  refine ⟨99336211648032856006932119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66224141098688570671288079 99336211648032856006932119)
  ·
    refine ⟨149004317472049284010398179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99336211648032856006932119 149004317472049284010398179)
    ·
      refine ⟨223506476208073926015597269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149004317472049284010398179 223506476208073926015597269)
      ·
        refine ⟨5238433036126732640990561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 223506476208073926015597269 5238433036126732640990561)
        ·
          refine ⟨3928824777095049480742921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5238433036126732640990561 3928824777095049480742921)
          ·
            refine ⟨2946618582821287110557191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3928824777095049480742921 2946618582821287110557191)
            ·
              refine ⟨4419927874231930665835787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946618582821287110557191 4419927874231930665835787)
              ·
                refine ⟨6629891811347895998753681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4419927874231930665835787 6629891811347895998753681)
                ·
                  refine ⟨4972418858510921999065261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6629891811347895998753681 4972418858510921999065261)
                  ·
                    refine ⟨1864657071941595749649473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4972418858510921999065261 1864657071941595749649473)
                    ·
                      refine ⟨1398492803956196812237105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864657071941595749649473 1398492803956196812237105)
                      ·
                        rfl

theorem cell23_2723555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2723555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723555 prefixEnd_2723555 := by exact prefixLift 2723555
  have htrace : WordTrace (prefixWord ++ tailWord_2723555) baseStart_2723555 baseEnd_2723555 := by
    simpa [prefixWord, tailWord_2723555, baseEnd_2723555] using wordTrace_append hprefix tailTrace_2723555
  have hstable : (prefixWord ++ tailWord_2723555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723555).length < 2 ^ (prefixWord ++ tailWord_2723555).sum := by decide
  have hdescent : baseEnd_2723555 < baseStart_2723555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723564 : List Nat := [2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2723564 : Nat := 118140960795 + 2723564 * 2 ^ 59
def prefixEnd_2723564 : Nat := 4983230072969 + 3 ^ 40 * 2723564 * 2
def baseEnd_2723564 : Nat := 1398497425282087277024563

theorem tailTrace_2723564 : CollatzResearch.WordTrace tailWord_2723564 prefixEnd_2723564 1398497425282087277024563 := by
  unfold tailWord_2723564
  simp only [CollatzResearch.WordTrace]
  refine ⟨49668269952500125272004873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66224359936666833696006497 49668269952500125272004873)
  ·
    refine ⟨37251202464375093954003655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49668269952500125272004873 37251202464375093954003655)
    ·
      refine ⟨55876803696562640931005483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37251202464375093954003655 55876803696562640931005483)
      ·
        refine ⟨83815205544843961396508225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55876803696562640931005483 83815205544843961396508225)
        ·
          refine ⟨62861404158632971047381169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83815205544843961396508225 62861404158632971047381169)
          ·
            refine ⟨47146053118974728285535877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62861404158632971047381169 47146053118974728285535877)
            ·
              refine ⟨8839884959807761553537977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47146053118974728285535877 8839884959807761553537977)
              ·
                refine ⟨6629913719855821165153483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8839884959807761553537977 6629913719855821165153483)
                ·
                  refine ⟨9944870579783731747730225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6629913719855821165153483 9944870579783731747730225)
                  ·
                    refine ⟨7458652934837798810797669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9944870579783731747730225 7458652934837798810797669)
                    ·
                      refine ⟨1398497425282087277024563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7458652934837798810797669 1398497425282087277024563)
                      ·
                        rfl

theorem cell23_2723564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2723564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723564 prefixEnd_2723564 := by exact prefixLift 2723564
  have htrace : WordTrace (prefixWord ++ tailWord_2723564) baseStart_2723564 baseEnd_2723564 := by
    simpa [prefixWord, tailWord_2723564, baseEnd_2723564] using wordTrace_append hprefix tailTrace_2723564
  have hstable : (prefixWord ++ tailWord_2723564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723564).length < 2 ^ (prefixWord ++ tailWord_2723564).sum := by decide
  have hdescent : baseEnd_2723564 < baseStart_2723564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723574 : List Nat := [5, 1, 1, 1, 1, 4, 10]
def baseStart_2723574 : Nat := 118140960795 + 2723574 * 2 ^ 59
def prefixEnd_2723574 : Nat := 4983230072969 + 3 ^ 40 * 2723574 * 2
def baseEnd_2723574 : Nat := 17265463704797928862957

theorem tailTrace_2723574 : CollatzResearch.WordTrace tailWord_2723574 prefixEnd_2723574 17265463704797928862957 := by
  unfold tailWord_2723574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208556539685251390742111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66224603089976014834582517 6208556539685251390742111)
  ·
    refine ⟨9312834809527877086113167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6208556539685251390742111 9312834809527877086113167)
    ·
      refine ⟨13969252214291815629169751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9312834809527877086113167 13969252214291815629169751)
      ·
        refine ⟨20953878321437723443754627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13969252214291815629169751 20953878321437723443754627)
        ·
          refine ⟨31430817482156585165631941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20953878321437723443754627 31430817482156585165631941)
          ·
            refine ⟨5893278277904359718555989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31430817482156585165631941 5893278277904359718555989)
            ·
              refine ⟨17265463704797928862957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5893278277904359718555989 17265463704797928862957)
              ·
                rfl

theorem cell23_2723574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 10].length) (baseStart_2723574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723574 prefixEnd_2723574 := by exact prefixLift 2723574
  have htrace : WordTrace (prefixWord ++ tailWord_2723574) baseStart_2723574 baseEnd_2723574 := by
    simpa [prefixWord, tailWord_2723574, baseEnd_2723574] using wordTrace_append hprefix tailTrace_2723574
  have hstable : (prefixWord ++ tailWord_2723574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723574).length < 2 ^ (prefixWord ++ tailWord_2723574).sum := by decide
  have hdescent : baseEnd_2723574 < baseStart_2723574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723577 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2723577 : Nat := 118140960795 + 2723577 * 2 ^ 59
def prefixEnd_2723577 : Nat := 4983230072969 + 3 ^ 40 * 2723577 * 2
def baseEnd_2723577 : Nat := 1398504100530595726162003

theorem tailTrace_2723577 : CollatzResearch.WordTrace tailWord_2723577 prefixEnd_2723577 1398504100530595726162003 := by
  unfold tailWord_2723577
  simp only [CollatzResearch.WordTrace]
  refine ⟨99337014053953153764232985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66224676035968769176155323 99337014053953153764232985)
  ·
    refine ⟨74502760540464865323174739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99337014053953153764232985 74502760540464865323174739)
    ·
      refine ⟨111754140810697297984762109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74502760540464865323174739 111754140810697297984762109)
      ·
        refine ⟨41907802804011486744285791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111754140810697297984762109 41907802804011486744285791)
        ·
          refine ⟨62861704206017230116428687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41907802804011486744285791 62861704206017230116428687)
          ·
            refine ⟨94292556309025845174643031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62861704206017230116428687 94292556309025845174643031)
            ·
              refine ⟨141438834463538767761964547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94292556309025845174643031 141438834463538767761964547)
              ·
                refine ⟨212158251695308151642946821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141438834463538767761964547 212158251695308151642946821)
                ·
                  refine ⟨39779672192870278433052529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212158251695308151642946821 39779672192870278433052529)
                  ·
                    refine ⟨29834754144652708824789397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39779672192870278433052529 29834754144652708824789397)
                    ·
                      refine ⟨1398504100530595726162003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29834754144652708824789397 1398504100530595726162003)
                      ·
                        rfl

theorem cell23_2723577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2723577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723577 prefixEnd_2723577 := by exact prefixLift 2723577
  have htrace : WordTrace (prefixWord ++ tailWord_2723577) baseStart_2723577 baseEnd_2723577 := by
    simpa [prefixWord, tailWord_2723577, baseEnd_2723577] using wordTrace_append hprefix tailTrace_2723577
  have hstable : (prefixWord ++ tailWord_2723577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723577).length < 2 ^ (prefixWord ++ tailWord_2723577).sum := by decide
  have hdescent : baseEnd_2723577 < baseStart_2723577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723585 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_2723585 : Nat := 118140960795 + 2723585 * 2 ^ 59
def prefixEnd_2723585 : Nat := 4983230072969 + 3 ^ 40 * 2723585 * 2
def baseEnd_2723585 : Nat := 1398508208375831694861967

theorem tailTrace_2723585 : CollatzResearch.WordTrace tailWord_2723585 prefixEnd_2723585 1398508208375831694861967 := by
  unfold tailWord_2723585
  simp only [CollatzResearch.WordTrace]
  refine ⟨99337305837924171130524209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66224870558616114087016139 99337305837924171130524209)
  ·
    refine ⟨74502979378443128347893157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99337305837924171130524209 74502979378443128347893157)
    ·
      refine ⟨13969308633458086565229967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74502979378443128347893157 13969308633458086565229967)
      ·
        refine ⟨20953962950187129847844951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13969308633458086565229967 20953962950187129847844951)
        ·
          refine ⟨31430944425280694771767427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20953962950187129847844951 31430944425280694771767427)
          ·
            refine ⟨47146416637921042157651141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31430944425280694771767427 47146416637921042157651141)
            ·
              refine ⟨8839953119610195404559589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47146416637921042157651141 8839953119610195404559589)
              ·
                refine ⟨1657491209926911638354923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8839953119610195404559589 1657491209926911638354923)
                ·
                  refine ⟨2486236814890367457532385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657491209926911638354923 2486236814890367457532385)
                  ·
                    refine ⟨1864677611167775593149289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2486236814890367457532385 1864677611167775593149289)
                    ·
                      refine ⟨1398508208375831694861967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864677611167775593149289 1398508208375831694861967)
                      ·
                        rfl

theorem cell23_2723585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_2723585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723585 prefixEnd_2723585 := by exact prefixLift 2723585
  have htrace : WordTrace (prefixWord ++ tailWord_2723585) baseStart_2723585 baseEnd_2723585 := by
    simpa [prefixWord, tailWord_2723585, baseEnd_2723585] using wordTrace_append hprefix tailTrace_2723585
  have hstable : (prefixWord ++ tailWord_2723585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723585).length < 2 ^ (prefixWord ++ tailWord_2723585).sum := by decide
  have hdescent : baseEnd_2723585 < baseStart_2723585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723587 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 1, 9]
def baseStart_2723587 : Nat := 118140960795 + 2723587 * 2 ^ 59
def prefixEnd_2723587 : Nat := 4983230072969 + 3 ^ 40 * 2723587 * 2
def baseEnd_2723587 : Nat := 466169745112380229012319

theorem tailTrace_2723587 : CollatzResearch.WordTrace tailWord_2723587 prefixEnd_2723587 466169745112380229012319 := by
  unfold tailWord_2723587
  simp only [CollatzResearch.WordTrace]
  refine ⟨99337378783916925472097015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66224919189277950314731343 99337378783916925472097015)
  ·
    refine ⟨149006068175875388208145523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99337378783916925472097015 149006068175875388208145523)
    ·
      refine ⟨223509102263813082312218285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149006068175875388208145523 223509102263813082312218285)
      ·
        refine ⟨83815913348929905867081857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223509102263813082312218285 83815913348929905867081857)
        ·
          refine ⟨62861935011697429400311393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83815913348929905867081857 62861935011697429400311393)
          ·
            refine ⟨47146451258773072050233545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62861935011697429400311393 47146451258773072050233545)
            ·
              refine ⟨35359838444079804037675159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47146451258773072050233545 35359838444079804037675159)
              ·
                refine ⟨53039757666119706056512739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35359838444079804037675159 53039757666119706056512739)
                ·
                  refine ⟨79559636499179559084769109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53039757666119706056512739 79559636499179559084769109)
                  ·
                    refine ⟨466169745112380229012319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79559636499179559084769109 466169745112380229012319)
                    ·
                      rfl

theorem cell23_2723587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 9].length) (baseStart_2723587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723587 prefixEnd_2723587 := by exact prefixLift 2723587
  have htrace : WordTrace (prefixWord ++ tailWord_2723587) baseStart_2723587 baseEnd_2723587 := by
    simpa [prefixWord, tailWord_2723587, baseEnd_2723587] using wordTrace_append hprefix tailTrace_2723587
  have hstable : (prefixWord ++ tailWord_2723587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723587).length < 2 ^ (prefixWord ++ tailWord_2723587).sum := by decide
  have hdescent : baseEnd_2723587 < baseStart_2723587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723628 : List Nat := [2, 2, 1, 1, 1, 5, 2, 3, 1, 3, 2]
def baseStart_2723628 : Nat := 118140960795 + 2723628 * 2 ^ 59
def prefixEnd_2723628 : Nat := 4983230072969 + 3 ^ 40 * 2723628 * 2
def baseEnd_2723628 : Nat := 1398530288043975026624269

theorem tailTrace_2723628 : CollatzResearch.WordTrace tailWord_2723628 prefixEnd_2723628 1398530288043975026624269 := by
  unfold tailWord_2723628
  simp only [CollatzResearch.WordTrace]
  refine ⟨49669437088384194737169769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66225916117845592982893025 49669437088384194737169769)
  ·
    refine ⟨37252077816288146052877327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49669437088384194737169769 37252077816288146052877327)
    ·
      refine ⟨55878116724432219079315991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37252077816288146052877327 55878116724432219079315991)
      ·
        refine ⟨83817175086648328618973987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55878116724432219079315991 83817175086648328618973987)
        ·
          refine ⟨125725762629972492928460981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83817175086648328618973987 125725762629972492928460981)
          ·
            refine ⟨11786790246559921212043217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125725762629972492928460981 11786790246559921212043217)
            ·
              refine ⟨8840092684919940909032413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11786790246559921212043217 8840092684919940909032413)
              ·
                refine ⟨3315034756844977840887155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8840092684919940909032413 3315034756844977840887155)
                ·
                  refine ⟨4972552135267466761330733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315034756844977840887155 4972552135267466761330733)
                  ·
                    refine ⟨1864707050725300035499025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4972552135267466761330733 1864707050725300035499025)
                    ·
                      refine ⟨1398530288043975026624269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864707050725300035499025 1398530288043975026624269)
                      ·
                        rfl

theorem cell23_2723628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_2723628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723628 prefixEnd_2723628 := by exact prefixLift 2723628
  have htrace : WordTrace (prefixWord ++ tailWord_2723628) baseStart_2723628 baseEnd_2723628 := by
    simpa [prefixWord, tailWord_2723628, baseEnd_2723628] using wordTrace_append hprefix tailTrace_2723628
  have hstable : (prefixWord ++ tailWord_2723628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723628).length < 2 ^ (prefixWord ++ tailWord_2723628).sum := by decide
  have hdescent : baseEnd_2723628 < baseStart_2723628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723681 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 5]
def baseStart_2723681 : Nat := 118140960795 + 2723681 * 2 ^ 59
def prefixEnd_2723681 : Nat := 4983230072969 + 3 ^ 40 * 2723681 * 2
def baseEnd_2723681 : Nat := 155395278057629257695725

theorem tailTrace_2723681 : CollatzResearch.WordTrace tailWord_2723681 prefixEnd_2723681 155395278057629257695725 := by
  unfold tailWord_2723681
  simp only [CollatzResearch.WordTrace]
  refine ⟨99340807245576379526018897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66227204830384253017345931 99340807245576379526018897)
  ·
    refine ⟨74505605434182284644514173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99340807245576379526018897 74505605434182284644514173)
    ·
      refine ⟨27939602037818356741692815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74505605434182284644514173 27939602037818356741692815)
      ·
        refine ⟨41909403056727535112539223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27939602037818356741692815 41909403056727535112539223)
        ·
          refine ⟨62864104585091302668808835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41909403056727535112539223 62864104585091302668808835)
          ·
            refine ⟨94296156877636954003213253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62864104585091302668808835 94296156877636954003213253)
            ·
              refine ⟨17680529414556928875602485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94296156877636954003213253 17680529414556928875602485)
              ·
                refine ⟨1657549632614712082087733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17680529414556928875602485 1657549632614712082087733)
                ·
                  refine ⟨155395278057629257695725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1657549632614712082087733 155395278057629257695725)
                  ·
                    rfl

theorem cell23_2723681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 5].length) (baseStart_2723681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723681 prefixEnd_2723681 := by exact prefixLift 2723681
  have htrace : WordTrace (prefixWord ++ tailWord_2723681) baseStart_2723681 baseEnd_2723681 := by
    simpa [prefixWord, tailWord_2723681, baseEnd_2723681] using wordTrace_append hprefix tailTrace_2723681
  have hstable : (prefixWord ++ tailWord_2723681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723681).length < 2 ^ (prefixWord ++ tailWord_2723681).sum := by decide
  have hdescent : baseEnd_2723681 < baseStart_2723681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723748 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_2723748 : Nat := 118140960795 + 2723748 * 2 ^ 59
def prefixEnd_2723748 : Nat := 4983230072969 + 3 ^ 40 * 2723748 * 2
def baseEnd_2723748 : Nat := 1398591905722514557123717

theorem tailTrace_2723748 : CollatzResearch.WordTrace tailWord_2723748 prefixEnd_2723748 1398591905722514557123717 := by
  unfold tailWord_2723748
  simp only [CollatzResearch.WordTrace]
  refine ⟨49671625468166824984353949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66228833957555766645805265 49671625468166824984353949)
  ·
    refine ⟨18626859550562559369132731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49671625468166824984353949 18626859550562559369132731)
    ·
      refine ⟨27940289325843839053699097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18626859550562559369132731 27940289325843839053699097)
      ·
        refine ⟨20955216994382879290274323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27940289325843839053699097 20955216994382879290274323)
        ·
          refine ⟨31432825491574318935411485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20955216994382879290274323 31432825491574318935411485)
          ·
            refine ⟨11787309559340369600779307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31432825491574318935411485 11787309559340369600779307)
            ·
              refine ⟨17680964339010554401168961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11787309559340369600779307 17680964339010554401168961)
              ·
                refine ⟨13260723254257915800876721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17680964339010554401168961 13260723254257915800876721)
                ·
                  refine ⟨9945542440693436850657541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13260723254257915800876721 9945542440693436850657541)
                  ·
                    refine ⟨1864789207630019409498289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9945542440693436850657541 1864789207630019409498289)
                    ·
                      refine ⟨1398591905722514557123717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864789207630019409498289 1398591905722514557123717)
                      ·
                        rfl

theorem cell23_2723748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_2723748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723748 prefixEnd_2723748 := by exact prefixLift 2723748
  have htrace : WordTrace (prefixWord ++ tailWord_2723748) baseStart_2723748 baseEnd_2723748 := by
    simpa [prefixWord, tailWord_2723748, baseEnd_2723748] using wordTrace_append hprefix tailTrace_2723748
  have hstable : (prefixWord ++ tailWord_2723748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723748).length < 2 ^ (prefixWord ++ tailWord_2723748).sum := by decide
  have hdescent : baseEnd_2723748 < baseStart_2723748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723861 : List Nat := [1, 3, 2, 1, 5, 11]
def baseStart_2723861 : Nat := 118140960795 + 2723861 * 2 ^ 59
def prefixEnd_2723861 : Nat := 4983230072969 + 3 ^ 40 * 2723861 * 2
def baseEnd_2723861 : Nat := 5755761024841451090579

theorem tailTrace_2723861 : CollatzResearch.WordTrace tailWord_2723861 prefixEnd_2723861 5755761024841451090579 := by
  unfold tailWord_2723861
  simp only [CollatzResearch.WordTrace]
  refine ⟨99347372384924270267571437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66231581589949513511714291 99347372384924270267571437)
  ·
    refine ⟨37255264644346601350339289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99347372384924270267571437 37255264644346601350339289)
    ·
      refine ⟨27941448483259951012754467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37255264644346601350339289 27941448483259951012754467)
      ·
        refine ⟨41912172724889926519131701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27941448483259951012754467 41912172724889926519131701)
        ·
          refine ⟨3929266192958430611168597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41912172724889926519131701 3929266192958430611168597)
          ·
            refine ⟨5755761024841451090579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3929266192958430611168597 5755761024841451090579)
            ·
              rfl

theorem cell23_2723861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 11].length) (baseStart_2723861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723861 prefixEnd_2723861 := by exact prefixLift 2723861
  have htrace : WordTrace (prefixWord ++ tailWord_2723861) baseStart_2723861 baseEnd_2723861 := by
    simpa [prefixWord, tailWord_2723861, baseEnd_2723861] using wordTrace_append hprefix tailTrace_2723861
  have hstable : (prefixWord ++ tailWord_2723861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723861).length < 2 ^ (prefixWord ++ tailWord_2723861).sum := by decide
  have hdescent : baseEnd_2723861 < baseStart_2723861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723888 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_2723888 : Nat := 118140960795 + 2723888 * 2 ^ 59
def prefixEnd_2723888 : Nat := 4983230072969 + 3 ^ 40 * 2723888 * 2
def baseEnd_2723888 : Nat := 1398663793014144009373073

theorem tailTrace_2723888 : CollatzResearch.WordTrace tailWord_2723888 prefixEnd_2723888 1398663793014144009373073 := by
  unfold tailWord_2723888
  simp only [CollatzResearch.WordTrace]
  refine ⟨49674178577913226939402159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66232238103884302585869545 49674178577913226939402159)
  ·
    refine ⟨74511267866869840409103239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49674178577913226939402159 74511267866869840409103239)
    ·
      refine ⟨111766901800304760613654859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74511267866869840409103239 111766901800304760613654859)
      ·
        refine ⟨167650352700457140920482289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111766901800304760613654859 167650352700457140920482289)
        ·
          refine ⟨125737764525342855690361717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167650352700457140920482289 125737764525342855690361717)
          ·
            refine ⟨11787915424250892720971411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125737764525342855690361717 11787915424250892720971411)
            ·
              refine ⟨17681873136376339081457117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11787915424250892720971411 17681873136376339081457117)
              ·
                refine ⟨6630702426141127155546419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17681873136376339081457117 6630702426141127155546419)
                ·
                  refine ⟨9946053639211690733319629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630702426141127155546419 9946053639211690733319629)
                  ·
                    refine ⟨3729770114704384024994861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9946053639211690733319629 3729770114704384024994861)
                    ·
                      refine ⟨1398663793014144009373073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3729770114704384024994861 1398663793014144009373073)
                      ·
                        rfl

theorem cell23_2723888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_2723888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723888 prefixEnd_2723888 := by exact prefixLift 2723888
  have htrace : WordTrace (prefixWord ++ tailWord_2723888) baseStart_2723888 baseEnd_2723888 := by
    simpa [prefixWord, tailWord_2723888, baseEnd_2723888] using wordTrace_append hprefix tailTrace_2723888
  have hstable : (prefixWord ++ tailWord_2723888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723888).length < 2 ^ (prefixWord ++ tailWord_2723888).sum := by decide
  have hdescent : baseEnd_2723888 < baseStart_2723888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723905 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2723905 : Nat := 118140960795 + 2723905 * 2 ^ 59
def prefixEnd_2723905 : Nat := 4983230072969 + 3 ^ 40 * 2723905 * 2
def baseEnd_2723905 : Nat := 1398672522185270442860495

theorem tailTrace_2723905 : CollatzResearch.WordTrace tailWord_2723905 prefixEnd_2723905 1398672522185270442860495 := by
  unfold tailWord_2723905
  simp only [CollatzResearch.WordTrace]
  refine ⟨99348977196764865782173169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66232651464509910521448779 99348977196764865782173169)
  ·
    refine ⟨74511732897573649336629877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99348977196764865782173169 74511732897573649336629877)
    ·
      refine ⟨6985474959147529625309051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74511732897573649336629877 6985474959147529625309051)
      ·
        refine ⟨10478212438721294437963577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6985474959147529625309051 10478212438721294437963577)
        ·
          refine ⟨7858659329040970828472683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10478212438721294437963577 7858659329040970828472683)
          ·
            refine ⟨11787988993561456242709025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7858659329040970828472683 11787988993561456242709025)
            ·
              refine ⟨8840991745171092182031769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11787988993561456242709025 8840991745171092182031769)
              ·
                refine ⟨6630743808878319136523827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8840991745171092182031769 6630743808878319136523827)
                ·
                  refine ⟨9946115713317478704785741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6630743808878319136523827 9946115713317478704785741)
                  ·
                    refine ⟨3729793392494054514294653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9946115713317478704785741 3729793392494054514294653)
                    ·
                      refine ⟨1398672522185270442860495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3729793392494054514294653 1398672522185270442860495)
                      ·
                        rfl

theorem cell23_2723905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2723905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723905 prefixEnd_2723905 := by exact prefixLift 2723905
  have htrace : WordTrace (prefixWord ++ tailWord_2723905) baseStart_2723905 baseEnd_2723905 := by
    simpa [prefixWord, tailWord_2723905, baseEnd_2723905] using wordTrace_append hprefix tailTrace_2723905
  have hstable : (prefixWord ++ tailWord_2723905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723905).length < 2 ^ (prefixWord ++ tailWord_2723905).sum := by decide
  have hdescent : baseEnd_2723905 < baseStart_2723905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723915 : List Nat := [1, 1, 1, 1, 3, 1, 2, 7, 1, 3, 2]
def baseStart_2723915 : Nat := 118140960795 + 2723915 * 2 ^ 59
def prefixEnd_2723915 : Nat := 4983230072969 + 3 ^ 40 * 2723915 * 2
def baseEnd_2723915 : Nat := 1398677656991815403735449

theorem tailTrace_2723915 : CollatzResearch.WordTrace tailWord_2723915 prefixEnd_2723915 1398677656991815403735449 := by
  unfold tailWord_2723915
  simp only [CollatzResearch.WordTrace]
  refine ⟨99349341926728637490037199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66232894617819091660024799 99349341926728637490037199)
  ·
    refine ⟨149024012890092956235055799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99349341926728637490037199 149024012890092956235055799)
    ·
      refine ⟨223536019335139434352583699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149024012890092956235055799 223536019335139434352583699)
      ·
        refine ⟨335304029002709151528875549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223536019335139434352583699 335304029002709151528875549)
        ·
          refine ⟨125739010876015931823328331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335304029002709151528875549 125739010876015931823328331)
          ·
            refine ⟨188608516314023897734992497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125739010876015931823328331 188608516314023897734992497)
            ·
              refine ⟨141456387235517923301244373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188608516314023897734992497 141456387235517923301244373)
              ·
                refine ⟨3315384075832451327372915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 141456387235517923301244373 3315384075832451327372915)
                ·
                  refine ⟨4973076113748676991059373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315384075832451327372915 4973076113748676991059373)
                  ·
                    refine ⟨1864903542655753871647265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4973076113748676991059373 1864903542655753871647265)
                    ·
                      refine ⟨1398677656991815403735449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1864903542655753871647265 1398677656991815403735449)
                      ·
                        rfl

theorem cell23_2723915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 3, 2].length) (baseStart_2723915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723915 prefixEnd_2723915 := by exact prefixLift 2723915
  have htrace : WordTrace (prefixWord ++ tailWord_2723915) baseStart_2723915 baseEnd_2723915 := by
    simpa [prefixWord, tailWord_2723915, baseEnd_2723915] using wordTrace_append hprefix tailTrace_2723915
  have hstable : (prefixWord ++ tailWord_2723915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723915).length < 2 ^ (prefixWord ++ tailWord_2723915).sum := by decide
  have hdescent : baseEnd_2723915 < baseStart_2723915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723922 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_2723922 : Nat := 118140960795 + 2723922 * 2 ^ 59
def prefixEnd_2723922 : Nat := 4983230072969 + 3 ^ 40 * 2723922 * 2
def baseEnd_2723922 : Nat := 1398681251356396876347917

theorem tailTrace_2723922 : CollatzResearch.WordTrace tailWord_2723922 prefixEnd_2723922 1398681251356396876347917 := by
  unfold tailWord_2723922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24837399309425819421385505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66233064825135518457028013 24837399309425819421385505)
  ·
    refine ⟨18628049482069364566039129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24837399309425819421385505 18628049482069364566039129)
    ·
      refine ⟨13971037111552023424529347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18628049482069364566039129 13971037111552023424529347)
      ·
        refine ⟨20956555667328035136794021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13971037111552023424529347 20956555667328035136794021)
        ·
          refine ⟨3929354187624006588148879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20956555667328035136794021 3929354187624006588148879)
          ·
            refine ⟨5894031281436009882223319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929354187624006588148879 5894031281436009882223319)
            ·
              refine ⟨8841046922154014823334979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894031281436009882223319 8841046922154014823334979)
              ·
                refine ⟨13261570383231022235002469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8841046922154014823334979 13261570383231022235002469)
                ·
                  refine ⟨2486544446855816669062963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13261570383231022235002469 2486544446855816669062963)
                  ·
                    refine ⟨3729816670283725003594445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2486544446855816669062963 3729816670283725003594445)
                    ·
                      refine ⟨1398681251356396876347917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3729816670283725003594445 1398681251356396876347917)
                      ·
                        rfl

theorem cell23_2723922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_2723922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723922 prefixEnd_2723922 := by exact prefixLift 2723922
  have htrace : WordTrace (prefixWord ++ tailWord_2723922) baseStart_2723922 baseEnd_2723922 := by
    simpa [prefixWord, tailWord_2723922, baseEnd_2723922] using wordTrace_append hprefix tailTrace_2723922
  have hstable : (prefixWord ++ tailWord_2723922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723922).length < 2 ^ (prefixWord ++ tailWord_2723922).sum := by decide
  have hdescent : baseEnd_2723922 < baseStart_2723922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2723990 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2723990 : Nat := 118140960795 + 2723990 * 2 ^ 59
def prefixEnd_2723990 : Nat := 4983230072969 + 3 ^ 40 * 2723990 * 2
def baseEnd_2723990 : Nat := 1398716168040902610297605

theorem tailTrace_2723990 : CollatzResearch.WordTrace tailWord_2723990 prefixEnd_2723990 1398716168040902610297605 := by
  unfold tailWord_2723990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6209504837591057831188589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66234718267637950199344949 6209504837591057831188589)
  ·
    refine ⟨2328564314096646686695721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6209504837591057831188589 2328564314096646686695721)
    ·
      refine ⟨1746423235572485015021791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2328564314096646686695721 1746423235572485015021791)
      ·
        refine ⟨2619634853358727522532687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746423235572485015021791 2619634853358727522532687)
        ·
          refine ⟨3929452280038091283799031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619634853358727522532687 3929452280038091283799031)
          ·
            refine ⟨5894178420057136925698547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3929452280038091283799031 5894178420057136925698547)
            ·
              refine ⟨8841267630085705388547821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5894178420057136925698547 8841267630085705388547821)
              ·
                refine ⟨3315475361282139520705433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8841267630085705388547821 3315475361282139520705433)
                ·
                  refine ⟨2486606520961604640529075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3315475361282139520705433 2486606520961604640529075)
                  ·
                    refine ⟨3729909781442406960793613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2486606520961604640529075 3729909781442406960793613)
                    ·
                      refine ⟨1398716168040902610297605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3729909781442406960793613 1398716168040902610297605)
                      ·
                        rfl

theorem cell23_2723990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2723990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2723990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2723990 prefixEnd_2723990 := by exact prefixLift 2723990
  have htrace : WordTrace (prefixWord ++ tailWord_2723990) baseStart_2723990 baseEnd_2723990 := by
    simpa [prefixWord, tailWord_2723990, baseEnd_2723990] using wordTrace_append hprefix tailTrace_2723990
  have hstable : (prefixWord ++ tailWord_2723990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2723990).length < 2 ^ (prefixWord ++ tailWord_2723990).sum := by decide
  have hdescent : baseEnd_2723990 < baseStart_2723990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2723990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724072 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2724072 : Nat := 118140960795 + 2724072 * 2 ^ 59
def prefixEnd_2724072 : Nat := 4983230072969 + 3 ^ 40 * 2724072 * 2
def baseEnd_2724072 : Nat := 1398758273454571289472227

theorem tailTrace_2724072 : CollatzResearch.WordTrace tailWord_2724072 prefixEnd_2724072 1398758273454571289472227 := by
  unfold tailWord_2724072
  simp only [CollatzResearch.WordTrace]
  refine ⟨49677534093579926651751235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66236712124773235535668313 49677534093579926651751235)
  ·
    refine ⟨74516301140369889977626853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49677534093579926651751235 74516301140369889977626853)
    ·
      refine ⟨13971806463819354370805035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74516301140369889977626853 13971806463819354370805035)
      ·
        refine ⟨20957709695729031556207553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13971806463819354370805035 20957709695729031556207553)
        ·
          refine ⟨15718282271796773667155665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20957709695729031556207553 15718282271796773667155665)
          ·
            refine ⟨11788711703847580250366749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15718282271796773667155665 11788711703847580250366749)
            ·
              refine ⟨4420766888942842593887531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11788711703847580250366749 4420766888942842593887531)
              ·
                refine ⟨6631150333414263890831297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4420766888942842593887531 6631150333414263890831297)
                ·
                  refine ⟨4973362750060697918123473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631150333414263890831297 4973362750060697918123473)
                  ·
                    refine ⟨3730022062545523438592605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4973362750060697918123473 3730022062545523438592605)
                    ·
                      refine ⟨1398758273454571289472227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3730022062545523438592605 1398758273454571289472227)
                      ·
                        rfl

theorem cell23_2724072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2724072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724072 prefixEnd_2724072 := by exact prefixLift 2724072
  have htrace : WordTrace (prefixWord ++ tailWord_2724072) baseStart_2724072 baseEnd_2724072 := by
    simpa [prefixWord, tailWord_2724072, baseEnd_2724072] using wordTrace_append hprefix tailTrace_2724072
  have hstable : (prefixWord ++ tailWord_2724072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724072).length < 2 ^ (prefixWord ++ tailWord_2724072).sum := by decide
  have hdescent : baseEnd_2724072 < baseStart_2724072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724079 : List Nat := [1, 1, 2, 1, 6, 2, 2, 3, 1, 4]
def baseStart_2724079 : Nat := 118140960795 + 2724079 * 2 ^ 59
def prefixEnd_2724079 : Nat := 4983230072969 + 3 ^ 40 * 2724079 * 2
def baseEnd_2724079 : Nat := 466253955939717587361565

theorem tailTrace_2724079 : CollatzResearch.WordTrace tailWord_2724079 prefixEnd_2724079 466253955939717587361565 := by
  unfold tailWord_2724079
  simp only [CollatzResearch.WordTrace]
  refine ⟨99355323498134493499007291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66236882332089662332671527 99355323498134493499007291)
  ·
    refine ⟨149032985247201740248510937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99355323498134493499007291 149032985247201740248510937)
    ·
      refine ⟨111774738935401305186383203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149032985247201740248510937 111774738935401305186383203)
      ·
        refine ⟨167662108403101957779574805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111774738935401305186383203 167662108403101957779574805)
        ·
          refine ⟨7859161331395404270917569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 167662108403101957779574805 7859161331395404270917569)
          ·
            refine ⟨5894370998546553203188177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859161331395404270917569 5894370998546553203188177)
            ·
              refine ⟨4420778248909914902391133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5894370998546553203188177 4420778248909914902391133)
              ·
                refine ⟨1657791843341218088396675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4420778248909914902391133 1657791843341218088396675)
                ·
                  refine ⟨2486687765011827132595013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657791843341218088396675 2486687765011827132595013)
                  ·
                    refine ⟨466253955939717587361565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2486687765011827132595013 466253955939717587361565)
                    ·
                      rfl

theorem cell23_2724079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 3, 1, 4].length) (baseStart_2724079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724079 prefixEnd_2724079 := by exact prefixLift 2724079
  have htrace : WordTrace (prefixWord ++ tailWord_2724079) baseStart_2724079 baseEnd_2724079 := by
    simpa [prefixWord, tailWord_2724079, baseEnd_2724079] using wordTrace_append hprefix tailTrace_2724079
  have hstable : (prefixWord ++ tailWord_2724079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724079).length < 2 ^ (prefixWord ++ tailWord_2724079).sum := by decide
  have hdescent : baseEnd_2724079 < baseStart_2724079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724092 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 6]
def baseStart_2724092 : Nat := 118140960795 + 2724092 * 2 ^ 59
def prefixEnd_2724092 : Nat := 4983230072969 + 3 ^ 40 * 2724092 * 2
def baseEnd_2724092 : Nat := 155418727007517912358015

theorem tailTrace_2724092 : CollatzResearch.WordTrace tailWord_2724092 prefixEnd_2724092 155418727007517912358015 := by
  unfold tailWord_2724092
  simp only [CollatzResearch.WordTrace]
  refine ⟨49677898823543698359615265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66237198431391597812820353 49677898823543698359615265)
  ·
    refine ⟨37258424117657773769711449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49677898823543698359615265 37258424117657773769711449)
    ·
      refine ⟨27943818088243330327283587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37258424117657773769711449 27943818088243330327283587)
      ·
        refine ⟨41915727132364995490925381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27943818088243330327283587 41915727132364995490925381)
        ·
          refine ⟨7859198837318436654548509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41915727132364995490925381 7859198837318436654548509)
          ·
            refine ⟨2947199563994413745455691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7859198837318436654548509 2947199563994413745455691)
            ·
              refine ⟨4420799345991620618183537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947199563994413745455691 4420799345991620618183537)
              ·
                refine ⟨3315599509493715463637653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4420799345991620618183537 3315599509493715463637653)
                ·
                  refine ⟨155418727007517912358015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3315599509493715463637653 155418727007517912358015)
                  ·
                    rfl

theorem cell23_2724092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_2724092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724092 prefixEnd_2724092 := by exact prefixLift 2724092
  have htrace : WordTrace (prefixWord ++ tailWord_2724092) baseStart_2724092 baseEnd_2724092 := by
    simpa [prefixWord, tailWord_2724092, baseEnd_2724092] using wordTrace_append hprefix tailTrace_2724092
  have hstable : (prefixWord ++ tailWord_2724092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724092).length < 2 ^ (prefixWord ++ tailWord_2724092).sum := by decide
  have hdescent : baseEnd_2724092 < baseStart_2724092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724153 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2724153 : Nat := 118140960795 + 2724153 * 2 ^ 59
def prefixEnd_2724153 : Nat := 4983230072969 + 3 ^ 40 * 2724153 * 2
def baseEnd_2724153 : Nat := 1398799865387585472559355

theorem tailTrace_2724153 : CollatzResearch.WordTrace tailWord_2724153 prefixEnd_2724153 1398799865387585472559355 := by
  unfold tailWord_2724153
  simp only [CollatzResearch.WordTrace]
  refine ⟨99358022499866404137201113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66238681666577602758134075 99358022499866404137201113)
  ·
    refine ⟨74518516874899803102900835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99358022499866404137201113 74518516874899803102900835)
    ·
      refine ⟨111777775312349704654351253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74518516874899803102900835 111777775312349704654351253)
      ·
        refine ⟨5239583217766392405672715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111777775312349704654351253 5239583217766392405672715)
        ·
          refine ⟨7859374826649588608509073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239583217766392405672715 7859374826649588608509073)
          ·
            refine ⟨5894531119987191456381805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859374826649588608509073 5894531119987191456381805)
            ·
              refine ⟨2210449169995196796143177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5894531119987191456381805 2210449169995196796143177)
              ·
                refine ⟨1657836877496397597107383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210449169995196796143177 1657836877496397597107383)
                ·
                  refine ⟨2486755316244596395661075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657836877496397597107383 2486755316244596395661075)
                  ·
                    refine ⟨3730132974366894593491613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2486755316244596395661075 3730132974366894593491613)
                    ·
                      refine ⟨1398799865387585472559355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3730132974366894593491613 1398799865387585472559355)
                      ·
                        rfl

theorem cell23_2724153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2724153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724153 prefixEnd_2724153 := by exact prefixLift 2724153
  have htrace : WordTrace (prefixWord ++ tailWord_2724153) baseStart_2724153 baseEnd_2724153 := by
    simpa [prefixWord, tailWord_2724153, baseEnd_2724153] using wordTrace_append hprefix tailTrace_2724153
  have hstable : (prefixWord ++ tailWord_2724153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724153).length < 2 ^ (prefixWord ++ tailWord_2724153).sum := by decide
  have hdescent : baseEnd_2724153 < baseStart_2724153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724210 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_2724210 : Nat := 118140960795 + 2724210 * 2 ^ 59
def prefixEnd_2724210 : Nat := 4983230072969 + 3 ^ 40 * 2724210 * 2
def baseEnd_2724210 : Nat := 1398829133784891749546593

theorem tailTrace_2724210 : CollatzResearch.WordTrace tailWord_2724210 prefixEnd_2724210 1398829133784891749546593 := by
  unfold tailWord_2724210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24840025365164975718006521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66240067640439935248017389 24840025365164975718006521)
  ·
    refine ⟨18630019023873731788504891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24840025365164975718006521 18630019023873731788504891)
    ·
      refine ⟨27945028535810597682757337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18630019023873731788504891 27945028535810597682757337)
      ·
        refine ⟨20958771401857948262068003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27945028535810597682757337 20958771401857948262068003)
        ·
          refine ⟨31438157102786922393102005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20958771401857948262068003 31438157102786922393102005)
          ·
            refine ⟨2947327228386273974353313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31438157102786922393102005 2947327228386273974353313)
            ·
              refine ⟨2210495421289705480764985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947327228386273974353313 2210495421289705480764985)
              ·
                refine ⟨1657871565967279110573739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2210495421289705480764985 1657871565967279110573739)
                ·
                  refine ⟨2486807348950918665860609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1657871565967279110573739 2486807348950918665860609)
                  ·
                    refine ⟨1865105511713188999395457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2486807348950918665860609 1865105511713188999395457)
                    ·
                      refine ⟨1398829133784891749546593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865105511713188999395457 1398829133784891749546593)
                      ·
                        rfl

theorem cell23_2724210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_2724210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724210 prefixEnd_2724210 := by exact prefixLift 2724210
  have htrace : WordTrace (prefixWord ++ tailWord_2724210) baseStart_2724210 baseEnd_2724210 := by
    simpa [prefixWord, tailWord_2724210, baseEnd_2724210] using wordTrace_append hprefix tailTrace_2724210
  have hstable : (prefixWord ++ tailWord_2724210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724210).length < 2 ^ (prefixWord ++ tailWord_2724210).sum := by decide
  have hdescent : baseEnd_2724210 < baseStart_2724210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724245 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2724245 : Nat := 118140960795 + 2724245 * 2 ^ 59
def prefixEnd_2724245 : Nat := 4983230072969 + 3 ^ 40 * 2724245 * 2
def baseEnd_2724245 : Nat := 1398847105607799112608931

theorem tailTrace_2724245 : CollatzResearch.WordTrace tailWord_2724245 prefixEnd_2724245 1398847105607799112608931 := by
  unfold tailWord_2724245
  simp only [CollatzResearch.WordTrace]
  refine ⟨99361378015533103849550189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66240918677022069233033459 99361378015533103849550189)
  ·
    refine ⟨37260516755824913943581321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99361378015533103849550189 37260516755824913943581321)
    ·
      refine ⟨27945387566868685457685991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37260516755824913943581321 27945387566868685457685991)
      ·
        refine ⟨41918081350303028186528987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27945387566868685457685991 41918081350303028186528987)
        ·
          refine ⟨62877122025454542279793481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41918081350303028186528987 62877122025454542279793481)
          ·
            refine ⟨47157841519090906709845111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62877122025454542279793481 47157841519090906709845111)
            ·
              refine ⟨70736762278636360064767667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47157841519090906709845111 70736762278636360064767667)
              ·
                refine ⟨106105143417954540097151501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70736762278636360064767667 106105143417954540097151501)
                ·
                  refine ⟨39789428781732952536431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106105143417954540097151501 39789428781732952536431813)
                  ·
                    refine ⟨7460517896574928600580965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39789428781732952536431813 7460517896574928600580965)
                    ·
                      refine ⟨1398847105607799112608931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7460517896574928600580965 1398847105607799112608931)
                      ·
                        rfl

theorem cell23_2724245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2724245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724245 prefixEnd_2724245 := by exact prefixLift 2724245
  have htrace : WordTrace (prefixWord ++ tailWord_2724245) baseStart_2724245 baseEnd_2724245 := by
    simpa [prefixWord, tailWord_2724245, baseEnd_2724245] using wordTrace_append hprefix tailTrace_2724245
  have hstable : (prefixWord ++ tailWord_2724245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724245).length < 2 ^ (prefixWord ++ tailWord_2724245).sum := by decide
  have hdescent : baseEnd_2724245 < baseStart_2724245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724249 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 4, 2, 2]
def baseStart_2724249 : Nat := 118140960795 + 2724249 * 2 ^ 59
def prefixEnd_2724249 : Nat := 4983230072969 + 3 ^ 40 * 2724249 * 2
def baseEnd_2724249 : Nat := 1398849159530417096958913

theorem tailTrace_2724249 : CollatzResearch.WordTrace tailWord_2724249 prefixEnd_2724249 1398849159530417096958913 := by
  unfold tailWord_2724249
  simp only [CollatzResearch.WordTrace]
  refine ⟨99361523907518612532695801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66241015938345741688463867 99361523907518612532695801)
  ·
    refine ⟨74521142930638959399521851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99361523907518612532695801 74521142930638959399521851)
    ·
      refine ⟨111781714395958439099282777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74521142930638959399521851 111781714395958439099282777)
      ·
        refine ⟨83836285796968829324462083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111781714395958439099282777 83836285796968829324462083)
        ·
          refine ⟨125754428695453243986693125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83836285796968829324462083 125754428695453243986693125)
          ·
            refine ⟨23578955380397483247504961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125754428695453243986693125 23578955380397483247504961)
            ·
              refine ⟨17684216535298112435628721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23578955380397483247504961 17684216535298112435628721)
              ·
                refine ⟨13263162401473584326721541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17684216535298112435628721 13263162401473584326721541)
                ·
                  refine ⟨2486842950276297061260289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13263162401473584326721541 2486842950276297061260289)
                  ·
                    refine ⟨1865132212707222795945217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2486842950276297061260289 1865132212707222795945217)
                    ·
                      refine ⟨1398849159530417096958913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865132212707222795945217 1398849159530417096958913)
                      ·
                        rfl

theorem cell23_2724249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_2724249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724249 prefixEnd_2724249 := by exact prefixLift 2724249
  have htrace : WordTrace (prefixWord ++ tailWord_2724249) baseStart_2724249 baseEnd_2724249 := by
    simpa [prefixWord, tailWord_2724249, baseEnd_2724249] using wordTrace_append hprefix tailTrace_2724249
  have hstable : (prefixWord ++ tailWord_2724249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724249).length < 2 ^ (prefixWord ++ tailWord_2724249).sum := by decide
  have hdescent : baseEnd_2724249 < baseStart_2724249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724255 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 9]
def baseStart_2724255 : Nat := 118140960795 + 2724255 * 2 ^ 59
def prefixEnd_2724255 : Nat := 4983230072969 + 3 ^ 40 * 2724255 * 2
def baseEnd_2724255 : Nat := 155428026712704897053765

theorem tailTrace_2724255 : CollatzResearch.WordTrace tailWord_2724255 prefixEnd_2724255 155428026712704897053765 := by
  unfold tailWord_2724255
  simp only [CollatzResearch.WordTrace]
  refine ⟨99361742745496875557414219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66241161830331250371609479 99361742745496875557414219)
  ·
    refine ⟨149042614118245313336121329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99361742745496875557414219 149042614118245313336121329)
    ·
      refine ⟨111781960588683985002090997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149042614118245313336121329 111781960588683985002090997)
      ·
        refine ⟨10479558805189123593946031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111781960588683985002090997 10479558805189123593946031)
        ·
          refine ⟨15719338207783685390919047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10479558805189123593946031 15719338207783685390919047)
          ·
            refine ⟨23579007311675528086378571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15719338207783685390919047 23579007311675528086378571)
            ·
              refine ⟨35368510967513292129567857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23579007311675528086378571 35368510967513292129567857)
              ·
                refine ⟨26526383225634969097175893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35368510967513292129567857 26526383225634969097175893)
                ·
                  refine ⟨155428026712704897053765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26526383225634969097175893 155428026712704897053765)
                  ·
                    rfl

theorem cell23_2724255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 9].length) (baseStart_2724255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724255 prefixEnd_2724255 := by exact prefixLift 2724255
  have htrace : WordTrace (prefixWord ++ tailWord_2724255) baseStart_2724255 baseEnd_2724255 := by
    simpa [prefixWord, tailWord_2724255, baseEnd_2724255] using wordTrace_append hprefix tailTrace_2724255
  have hstable : (prefixWord ++ tailWord_2724255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724255).length < 2 ^ (prefixWord ++ tailWord_2724255).sum := by decide
  have hdescent : baseEnd_2724255 < baseStart_2724255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724302 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_2724302 : Nat := 118140960795 + 2724302 * 2 ^ 59
def prefixEnd_2724302 : Nat := 4983230072969 + 3 ^ 40 * 2724302 * 2
def baseEnd_2724302 : Nat := 466292124668368463198723

theorem tailTrace_2724302 : CollatzResearch.WordTrace tailWord_2724302 prefixEnd_2724302 466292124668368463198723 := by
  unfold tailWord_2724302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12420432122040825323046895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66242304650884401722916773 12420432122040825323046895)
  ·
    refine ⟨18630648183061237984570343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12420432122040825323046895 18630648183061237984570343)
    ·
      refine ⟨27945972274591856976855515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18630648183061237984570343 27945972274591856976855515)
      ·
        refine ⟨41918958411887785465283273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27945972274591856976855515 41918958411887785465283273)
        ·
          refine ⟨31439218808915839098962455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41918958411887785465283273 31439218808915839098962455)
          ·
            refine ⟨47158828213373758648443683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31439218808915839098962455 47158828213373758648443683)
            ·
              refine ⟨70738242320060637972665525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47158828213373758648443683 70738242320060637972665525)
              ·
                refine ⟨6631710217505684809937393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70738242320060637972665525 6631710217505684809937393)
                ·
                  refine ⟨4973782663129263607453045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631710217505684809937393 4973782663129263607453045)
                  ·
                    refine ⟨466292124668368463198723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4973782663129263607453045 466292124668368463198723)
                    ·
                      rfl

theorem cell23_2724302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_2724302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724302 prefixEnd_2724302 := by exact prefixLift 2724302
  have htrace : WordTrace (prefixWord ++ tailWord_2724302) baseStart_2724302 baseEnd_2724302 := by
    simpa [prefixWord, tailWord_2724302, baseEnd_2724302] using wordTrace_append hprefix tailTrace_2724302
  have hstable : (prefixWord ++ tailWord_2724302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724302).length < 2 ^ (prefixWord ++ tailWord_2724302).sum := by decide
  have hdescent : baseEnd_2724302 < baseStart_2724302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724356 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2724356 : Nat := 118140960795 + 2724356 * 2 ^ 59
def prefixEnd_2724356 : Nat := 4983230072969 + 3 ^ 40 * 2724356 * 2
def baseEnd_2724356 : Nat := 1398904101960448178320921

theorem tailTrace_2724356 : CollatzResearch.WordTrace tailWord_2724356 prefixEnd_2724356 1398904101960448178320921 := by
  unfold tailWord_2724356
  simp only [CollatzResearch.WordTrace]
  refine ⟨49682713259065484903420461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66243617678753979871227281 49682713259065484903420461)
  ·
    refine ⟨18631017472149556838782673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49682713259065484903420461 18631017472149556838782673)
    ·
      refine ⟨13973263104112167629087005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18631017472149556838782673 13973263104112167629087005)
      ·
        refine ⟨5239973664042062860907627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13973263104112167629087005 5239973664042062860907627)
        ·
          refine ⟨7859960496063094291361441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5239973664042062860907627 7859960496063094291361441)
          ·
            refine ⟨5894970372047320718521081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7859960496063094291361441 5894970372047320718521081)
            ·
              refine ⟨4421227779035490538890811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5894970372047320718521081 4421227779035490538890811)
              ·
                refine ⟨6631841668553235808336217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421227779035490538890811 6631841668553235808336217)
                ·
                  refine ⟨4973881251414926856252163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631841668553235808336217 4973881251414926856252163)
                  ·
                    refine ⟨7460821877122390284378245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4973881251414926856252163 7460821877122390284378245)
                    ·
                      refine ⟨1398904101960448178320921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7460821877122390284378245 1398904101960448178320921)
                      ·
                        rfl

theorem cell23_2724356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2724356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724356 prefixEnd_2724356 := by exact prefixLift 2724356
  have htrace : WordTrace (prefixWord ++ tailWord_2724356) baseStart_2724356 baseEnd_2724356 := by
    simpa [prefixWord, tailWord_2724356, baseEnd_2724356] using wordTrace_append hprefix tailTrace_2724356
  have hstable : (prefixWord ++ tailWord_2724356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724356).length < 2 ^ (prefixWord ++ tailWord_2724356).sum := by decide
  have hdescent : baseEnd_2724356 < baseStart_2724356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724409 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 1, 5]
def baseStart_2724409 : Nat := 118140960795 + 2724409 * 2 ^ 59
def prefixEnd_2724409 : Nat := 4983230072969 + 3 ^ 40 * 2724409 * 2
def baseEnd_2724409 : Nat := 466310438811712156986059

theorem tailTrace_2724409 : CollatzResearch.WordTrace tailWord_2724409 prefixEnd_2724409 466310438811712156986059 := by
  unfold tailWord_2724409
  simp only [CollatzResearch.WordTrace]
  refine ⟨99367359586938959858520281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66244906391292639905680187 99367359586938959858520281)
  ·
    refine ⟨74525519690204219893890211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99367359586938959858520281 74525519690204219893890211)
    ·
      refine ⟨111788279535306329840835317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74525519690204219893890211 111788279535306329840835317)
      ·
        refine ⟨10480151206434968422578311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111788279535306329840835317 10480151206434968422578311)
        ·
          refine ⟨15720226809652452633867467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10480151206434968422578311 15720226809652452633867467)
          ·
            refine ⟨23580340214478678950801201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15720226809652452633867467 23580340214478678950801201)
            ·
              refine ⟨17685255160859009213100901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23580340214478678950801201 17685255160859009213100901)
              ·
                refine ⟨3315985342661064227456419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17685255160859009213100901 3315985342661064227456419)
                ·
                  refine ⟨4973978013991596341184629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3315985342661064227456419 4973978013991596341184629)
                  ·
                    refine ⟨466310438811712156986059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4973978013991596341184629 466310438811712156986059)
                    ·
                      rfl

theorem cell23_2724409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_2724409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724409 prefixEnd_2724409 := by exact prefixLift 2724409
  have htrace : WordTrace (prefixWord ++ tailWord_2724409) baseStart_2724409 baseEnd_2724409 := by
    simpa [prefixWord, tailWord_2724409, baseEnd_2724409] using wordTrace_append hprefix tailTrace_2724409
  have hstable : (prefixWord ++ tailWord_2724409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724409).length < 2 ^ (prefixWord ++ tailWord_2724409).sum := by decide
  have hdescent : baseEnd_2724409 < baseStart_2724409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724416 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 2, 3, 2]
def baseStart_2724416 : Nat := 118140960795 + 2724416 * 2 ^ 59
def prefixEnd_2724416 : Nat := 4983230072969 + 3 ^ 40 * 2724416 * 2
def baseEnd_2724416 : Nat := 1398934910799717943570645

theorem tailTrace_2724416 : CollatzResearch.WordTrace tailWord_2724416 prefixEnd_2724416 1398934910799717943570645 := by
  unfold tailWord_2724416
  simp only [CollatzResearch.WordTrace]
  refine ⟨49683807448956800027012551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66245076598609066702683401 49683807448956800027012551)
  ·
    refine ⟨74525711173435200040518827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49683807448956800027012551 74525711173435200040518827)
    ·
      refine ⟨111788566760152800060778241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74525711173435200040518827 111788566760152800060778241)
      ·
        refine ⟨83841425070114600045583681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111788566760152800060778241 83841425070114600045583681)
        ·
          refine ⟨62881068802585950034187761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83841425070114600045583681 62881068802585950034187761)
          ·
            refine ⟨47160801601939462525640821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62881068802585950034187761 47160801601939462525640821)
            ·
              refine ⟨4421325150181824611778827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47160801601939462525640821 4421325150181824611778827)
              ·
                refine ⟨6631987725272736917668241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421325150181824611778827 6631987725272736917668241)
                ·
                  refine ⟨4973990793954552688251181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6631987725272736917668241 4973990793954552688251181)
                  ·
                    refine ⟨1865246547732957258094193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4973990793954552688251181 1865246547732957258094193)
                    ·
                      refine ⟨1398934910799717943570645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865246547732957258094193 1398934910799717943570645)
                      ·
                        rfl

theorem cell23_2724416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_2724416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724416 prefixEnd_2724416 := by exact prefixLift 2724416
  have htrace : WordTrace (prefixWord ++ tailWord_2724416) baseStart_2724416 baseEnd_2724416 := by
    simpa [prefixWord, tailWord_2724416, baseEnd_2724416] using wordTrace_append hprefix tailTrace_2724416
  have hstable : (prefixWord ++ tailWord_2724416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724416).length < 2 ^ (prefixWord ++ tailWord_2724416).sum := by decide
  have hdescent : baseEnd_2724416 < baseStart_2724416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724423 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_2724423 : Nat := 118140960795 + 2724423 * 2 ^ 59
def prefixEnd_2724423 : Nat := 4983230072969 + 3 ^ 40 * 2724423 * 2
def baseEnd_2724423 : Nat := 1398938505164299416183113

theorem tailTrace_2724423 : CollatzResearch.WordTrace tailWord_2724423 prefixEnd_2724423 1398938505164299416183113 := by
  unfold tailWord_2724423
  simp only [CollatzResearch.WordTrace]
  refine ⟨99367870208888240249529923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66245246805925493499686615 99367870208888240249529923)
  ·
    refine ⟨149051805313332360374294885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99367870208888240249529923 149051805313332360374294885)
    ·
      refine ⟨27947213496249817570180291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149051805313332360374294885 27947213496249817570180291)
      ·
        refine ⟨41920820244374726355270437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27947213496249817570180291 41920820244374726355270437)
        ·
          refine ⟨7860153795820261191613207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41920820244374726355270437 7860153795820261191613207)
          ·
            refine ⟨11790230693730391787419811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7860153795820261191613207 11790230693730391787419811)
            ·
              refine ⟨17685346040595587681129717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11790230693730391787419811 17685346040595587681129717)
              ·
                refine ⟨1658001191305836345105911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17685346040595587681129717 1658001191305836345105911)
                ·
                  refine ⟨2487001786958754517658867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658001191305836345105911 2487001786958754517658867)
                  ·
                    refine ⟨3730502680438131776488301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2487001786958754517658867 3730502680438131776488301)
                    ·
                      refine ⟨1398938505164299416183113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3730502680438131776488301 1398938505164299416183113)
                      ·
                        rfl

theorem cell23_2724423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_2724423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724423 prefixEnd_2724423 := by exact prefixLift 2724423
  have htrace : WordTrace (prefixWord ++ tailWord_2724423) baseStart_2724423 baseEnd_2724423 := by
    simpa [prefixWord, tailWord_2724423, baseEnd_2724423] using wordTrace_append hprefix tailTrace_2724423
  have hstable : (prefixWord ++ tailWord_2724423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724423).length < 2 ^ (prefixWord ++ tailWord_2724423).sum := by decide
  have hdescent : baseEnd_2724423 < baseStart_2724423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724426 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_2724426 : Nat := 118140960795 + 2724426 * 2 ^ 59
def prefixEnd_2724426 : Nat := 4983230072969 + 3 ^ 40 * 2724426 * 2
def baseEnd_2724426 : Nat := 466313348535420968148533

theorem tailTrace_2724426 : CollatzResearch.WordTrace tailWord_2724426 prefixEnd_2724426 466313348535420968148533 := by
  unfold tailWord_2724426
  simp only [CollatzResearch.WordTrace]
  refine ⟨24841994906969342940472283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66245319751918247841259421 24841994906969342940472283)
  ·
    refine ⟨37262992360454014410708425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24841994906969342940472283 37262992360454014410708425)
    ·
      refine ⟨27947244270340510808031319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37262992360454014410708425 27947244270340510808031319)
      ·
        refine ⟨41920866405510766212046979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27947244270340510808031319 41920866405510766212046979)
        ·
          refine ⟨62881299608266149318070469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41920866405510766212046979 62881299608266149318070469)
          ·
            refine ⟨11790243676549902997138213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62881299608266149318070469 11790243676549902997138213)
            ·
              refine ⟨2210670689353106811963415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11790243676549902997138213 2210670689353106811963415)
              ·
                refine ⟨3316006034029660217945123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210670689353106811963415 3316006034029660217945123)
                ·
                  refine ⟨4974009051044490326917685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316006034029660217945123 4974009051044490326917685)
                  ·
                    refine ⟨466313348535420968148533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4974009051044490326917685 466313348535420968148533)
                    ·
                      rfl

theorem cell23_2724426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_2724426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724426 prefixEnd_2724426 := by exact prefixLift 2724426
  have htrace : WordTrace (prefixWord ++ tailWord_2724426) baseStart_2724426 baseEnd_2724426 := by
    simpa [prefixWord, tailWord_2724426, baseEnd_2724426] using wordTrace_append hprefix tailTrace_2724426
  have hstable : (prefixWord ++ tailWord_2724426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724426).length < 2 ^ (prefixWord ++ tailWord_2724426).sum := by decide
  have hdescent : baseEnd_2724426 < baseStart_2724426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724439 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 4, 4]
def baseStart_2724439 : Nat := 118140960795 + 2724439 * 2 ^ 59
def prefixEnd_2724439 : Nat := 4983230072969 + 3 ^ 40 * 2724439 * 2
def baseEnd_2724439 : Nat := 466315573618257117861013

theorem tailTrace_2724439 : CollatzResearch.WordTrace tailWord_2724439 prefixEnd_2724439 466315573618257117861013 := by
  unfold tailWord_2724439
  simp only [CollatzResearch.WordTrace]
  refine ⟨99368453776830274982112371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66245635851220183321408247 99368453776830274982112371)
  ·
    refine ⟨149052680665245412473168557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99368453776830274982112371 149052680665245412473168557)
    ·
      refine ⟨55894755249467029677438209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149052680665245412473168557 55894755249467029677438209)
      ·
        refine ⟨41921066437100272258078657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55894755249467029677438209 41921066437100272258078657)
        ·
          refine ⟨31440799827825204193558993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41921066437100272258078657 31440799827825204193558993)
          ·
            refine ⟨23580599870868903145169245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31440799827825204193558993 23580599870868903145169245)
            ·
              refine ⟨8842724951575838679438467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23580599870868903145169245 8842724951575838679438467)
              ·
                refine ⟨13264087427363758019157701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8842724951575838679438467 13264087427363758019157701)
                ·
                  refine ⟨2487016392630704628592069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13264087427363758019157701 2487016392630704628592069)
                  ·
                    refine ⟨466315573618257117861013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2487016392630704628592069 466315573618257117861013)
                    ·
                      rfl

theorem cell23_2724439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_2724439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724439 prefixEnd_2724439 := by exact prefixLift 2724439
  have htrace : WordTrace (prefixWord ++ tailWord_2724439) baseStart_2724439 baseEnd_2724439 := by
    simpa [prefixWord, tailWord_2724439, baseEnd_2724439] using wordTrace_append hprefix tailTrace_2724439
  have hstable : (prefixWord ++ tailWord_2724439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724439).length < 2 ^ (prefixWord ++ tailWord_2724439).sum := by decide
  have hdescent : baseEnd_2724439 < baseStart_2724439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724442 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_2724442 : Nat := 118140960795 + 2724442 * 2 ^ 59
def prefixEnd_2724442 : Nat := 4983230072969 + 3 ^ 40 * 2724442 * 2
def baseEnd_2724442 : Nat := 1398948261296734841845525

theorem tailTrace_2724442 : CollatzResearch.WordTrace tailWord_2724442 prefixEnd_2724442 1398948261296734841845525 := by
  unfold tailWord_2724442
  simp only [CollatzResearch.WordTrace]
  refine ⟨24842140798954851623617895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66245708797212937662981053 24842140798954851623617895)
  ·
    refine ⟨37263211198432277435426843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24842140798954851623617895 37263211198432277435426843)
    ·
      refine ⟨55894816797648416153140265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37263211198432277435426843 55894816797648416153140265)
      ·
        refine ⟨41921112598236312114855199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55894816797648416153140265 41921112598236312114855199)
        ·
          refine ⟨62881668897354468172282799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41921112598236312114855199 62881668897354468172282799)
          ·
            refine ⟨94322503346031702258424199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62881668897354468172282799 94322503346031702258424199)
            ·
              refine ⟨141483755019047553387636299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94322503346031702258424199 141483755019047553387636299)
              ·
                refine ⟨212225632528571330081454449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141483755019047553387636299 212225632528571330081454449)
                ·
                  refine ⟨159169224396428497561090837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212225632528571330081454449 159169224396428497561090837)
                  ·
                    refine ⟨7461057393582585823176133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 159169224396428497561090837 7461057393582585823176133)
                    ·
                      refine ⟨1398948261296734841845525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7461057393582585823176133 1398948261296734841845525)
                      ·
                        rfl

theorem cell23_2724442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_2724442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724442 prefixEnd_2724442 := by exact prefixLift 2724442
  have htrace : WordTrace (prefixWord ++ tailWord_2724442) baseStart_2724442 baseEnd_2724442 := by
    simpa [prefixWord, tailWord_2724442, baseEnd_2724442] using wordTrace_append hprefix tailTrace_2724442
  have hstable : (prefixWord ++ tailWord_2724442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724442).length < 2 ^ (prefixWord ++ tailWord_2724442).sum := by decide
  have hdescent : baseEnd_2724442 < baseStart_2724442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724449 : List Nat := [1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2724449 : Nat := 118140960795 + 2724449 * 2 ^ 59
def prefixEnd_2724449 : Nat := 4983230072969 + 3 ^ 40 * 2724449 * 2
def baseEnd_2724449 : Nat := 1398951855661316314457993

theorem tailTrace_2724449 : CollatzResearch.WordTrace tailWord_2724449 prefixEnd_2724449 1398951855661316314457993 := by
  unfold tailWord_2724449
  simp only [CollatzResearch.WordTrace]
  refine ⟨99368818506794046689976401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66245879004529364459984267 99368818506794046689976401)
  ·
    refine ⟨74526613880095535017482301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99368818506794046689976401 74526613880095535017482301)
    ·
      refine ⟨27947480205035825631555863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74526613880095535017482301 27947480205035825631555863)
      ·
        refine ⟨41921220307553738447333795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27947480205035825631555863 41921220307553738447333795)
        ·
          refine ⟨62881830461330607671000693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41921220307553738447333795 62881830461330607671000693)
          ·
            refine ⟨5895171605749744469156315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62881830461330607671000693 5895171605749744469156315)
            ·
              refine ⟨8842757408624616703734473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895171605749744469156315 8842757408624616703734473)
              ·
                refine ⟨6632068056468462527800855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8842757408624616703734473 6632068056468462527800855)
                ·
                  refine ⟨9948102084702693791701283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632068056468462527800855 9948102084702693791701283)
                  ·
                    refine ⟨14922153127054040687551925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9948102084702693791701283 14922153127054040687551925)
                    ·
                      refine ⟨1398951855661316314457993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14922153127054040687551925 1398951855661316314457993)
                      ·
                        rfl

theorem cell23_2724449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2724449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724449 prefixEnd_2724449 := by exact prefixLift 2724449
  have htrace : WordTrace (prefixWord ++ tailWord_2724449) baseStart_2724449 baseEnd_2724449 := by
    simpa [prefixWord, tailWord_2724449, baseEnd_2724449] using wordTrace_append hprefix tailTrace_2724449
  have hstable : (prefixWord ++ tailWord_2724449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724449).length < 2 ^ (prefixWord ++ tailWord_2724449).sum := by decide
  have hdescent : baseEnd_2724449 < baseStart_2724449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724452 : List Nat := [2, 3, 1, 1, 2, 2, 2, 10]
def baseStart_2724452 : Nat := 118140960795 + 2724452 * 2 ^ 59
def prefixEnd_2724452 : Nat := 4983230072969 + 3 ^ 40 * 2724452 * 2
def baseEnd_2724452 : Nat := 51813088744565918619277

theorem tailTrace_2724452 : CollatzResearch.WordTrace tailWord_2724452 prefixEnd_2724452 51813088744565918619277 := by
  unfold tailWord_2724452
  simp only [CollatzResearch.WordTrace]
  refine ⟨49684463962891589101167805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66245951950522118801557073 49684463962891589101167805)
  ·
    refine ⟨18631673986084345912937927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49684463962891589101167805 18631673986084345912937927)
    ·
      refine ⟨27947510979126518869406891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18631673986084345912937927 27947510979126518869406891)
      ·
        refine ⟨41921266468689778304110337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27947510979126518869406891 41921266468689778304110337)
        ·
          refine ⟨31440949851517333728082753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41921266468689778304110337 31440949851517333728082753)
          ·
            refine ⟨23580712388638000296062065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31440949851517333728082753 23580712388638000296062065)
            ·
              refine ⟨17685534291478500222046549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23580712388638000296062065 17685534291478500222046549)
              ·
                refine ⟨51813088744565918619277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 17685534291478500222046549 51813088744565918619277)
                ·
                  rfl

theorem cell23_2724452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 10].length) (baseStart_2724452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724452 prefixEnd_2724452 := by exact prefixLift 2724452
  have htrace : WordTrace (prefixWord ++ tailWord_2724452) baseStart_2724452 baseEnd_2724452 := by
    simpa [prefixWord, tailWord_2724452, baseEnd_2724452] using wordTrace_append hprefix tailTrace_2724452
  have hstable : (prefixWord ++ tailWord_2724452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724452).length < 2 ^ (prefixWord ++ tailWord_2724452).sum := by decide
  have hdescent : baseEnd_2724452 < baseStart_2724452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724480 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 1, 2, 2]
def baseStart_2724480 : Nat := 118140960795 + 2724480 * 2 ^ 59
def prefixEnd_2724480 : Nat := 4983230072969 + 3 ^ 40 * 2724480 * 2
def baseEnd_2724480 : Nat := 1398967773561605693170351

theorem tailTrace_2724480 : CollatzResearch.WordTrace tailWord_2724480 prefixEnd_2724480 1398967773561605693170351 := by
  unfold tailWord_2724480
  simp only [CollatzResearch.WordTrace]
  refine ⟨49684974584840869492177447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66246632779787825989569929 49684974584840869492177447)
  ·
    refine ⟨74527461877261304238266171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49684974584840869492177447 74527461877261304238266171)
    ·
      refine ⟨111791192815891956357399257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74527461877261304238266171 111791192815891956357399257)
      ·
        refine ⟨83843394611918967268049443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111791192815891956357399257 83843394611918967268049443)
        ·
          refine ⟨125765091917878450902074165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83843394611918967268049443 125765091917878450902074165)
          ·
            refine ⟨11790477367301104772069453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125765091917878450902074165 11790477367301104772069453)
            ·
              refine ⟨4421429012737914289526045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11790477367301104772069453 4421429012737914289526045)
              ·
                refine ⟨1658035879776717858572267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4421429012737914289526045 1658035879776717858572267)
                ·
                  refine ⟨2487053819665076787858401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658035879776717858572267 2487053819665076787858401)
                  ·
                    refine ⟨1865290364748807590893801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2487053819665076787858401 1865290364748807590893801)
                    ·
                      refine ⟨1398967773561605693170351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865290364748807590893801 1398967773561605693170351)
                      ·
                        rfl

theorem cell23_2724480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_2724480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724480 prefixEnd_2724480 := by exact prefixLift 2724480
  have htrace : WordTrace (prefixWord ++ tailWord_2724480) baseStart_2724480 baseEnd_2724480 := by
    simpa [prefixWord, tailWord_2724480, baseEnd_2724480] using wordTrace_append hprefix tailTrace_2724480
  have hstable : (prefixWord ++ tailWord_2724480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724480).length < 2 ^ (prefixWord ++ tailWord_2724480).sum := by decide
  have hdescent : baseEnd_2724480 < baseStart_2724480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724540 : List Nat := [2, 2, 2, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_2724540 : Nat := 118140960795 + 2724540 * 2 ^ 59
def prefixEnd_2724540 : Nat := 4983230072969 + 3 ^ 40 * 2724540 * 2
def baseEnd_2724540 : Nat := 1398998582400875458420075

theorem tailTrace_2724540 : CollatzResearch.WordTrace tailWord_2724540 prefixEnd_2724540 1398998582400875458420075 := by
  unfold tailWord_2724540
  simp only [CollatzResearch.WordTrace]
  refine ⟨49686068774732184615769537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66248091699642912821026049 49686068774732184615769537)
  ·
    refine ⟨37264551581049138461827153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49686068774732184615769537 37264551581049138461827153)
    ·
      refine ⟨27948413685786853846370365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37264551581049138461827153 27948413685786853846370365)
      ·
        refine ⟨10480655132170070192388887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27948413685786853846370365 10480655132170070192388887)
        ·
          refine ⟨15720982698255105288583331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10480655132170070192388887 15720982698255105288583331)
          ·
            refine ⟨23581474047382657932874997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15720982698255105288583331 23581474047382657932874997)
            ·
              refine ⟨2210763191942124181207031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23581474047382657932874997 2210763191942124181207031)
              ·
                refine ⟨3316144787913186271810547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210763191942124181207031 3316144787913186271810547)
                ·
                  refine ⟨4974217181869779407715821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316144787913186271810547 4974217181869779407715821)
                  ·
                    refine ⟨1865331443201167277893433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4974217181869779407715821 1865331443201167277893433)
                    ·
                      refine ⟨1398998582400875458420075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865331443201167277893433 1398998582400875458420075)
                      ·
                        rfl

theorem cell23_2724540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_2724540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724540 prefixEnd_2724540 := by exact prefixLift 2724540
  have htrace : WordTrace (prefixWord ++ tailWord_2724540) baseStart_2724540 baseEnd_2724540 := by
    simpa [prefixWord, tailWord_2724540, baseEnd_2724540] using wordTrace_append hprefix tailTrace_2724540
  have hstable : (prefixWord ++ tailWord_2724540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724540).length < 2 ^ (prefixWord ++ tailWord_2724540).sum := by decide
  have hdescent : baseEnd_2724540 < baseStart_2724540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724556 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2724556 : Nat := 118140960795 + 2724556 * 2 ^ 59
def prefixEnd_2724556 : Nat := 4983230072969 + 3 ^ 40 * 2724556 * 2
def baseEnd_2724556 : Nat := 1399006798091347395820001

theorem tailTrace_2724556 : CollatzResearch.WordTrace tailWord_2724556 prefixEnd_2724556 1399006798091347395820001 := by
  unfold tailWord_2724556
  simp only [CollatzResearch.WordTrace]
  refine ⟨49686360558703201982060761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66248480744937602642747681 49686360558703201982060761)
  ·
    refine ⟨37264770419027401486545571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49686360558703201982060761 37264770419027401486545571)
    ·
      refine ⟨55897155628541102229818357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37264770419027401486545571 55897155628541102229818357)
      ·
        refine ⟨5240358340175728334045471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55897155628541102229818357 5240358340175728334045471)
        ·
          refine ⟨7860537510263592501068207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5240358340175728334045471 7860537510263592501068207)
          ·
            refine ⟨11790806265395388751602311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7860537510263592501068207 11790806265395388751602311)
            ·
              refine ⟨17686209398093083127403467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11790806265395388751602311 17686209398093083127403467)
              ·
                refine ⟨26529314097139624691105201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17686209398093083127403467 26529314097139624691105201)
                ·
                  refine ⟨19896985572854718518328901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26529314097139624691105201 19896985572854718518328901)
                  ·
                    refine ⟨3730684794910259722186669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19896985572854718518328901 3730684794910259722186669)
                    ·
                      refine ⟨1399006798091347395820001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3730684794910259722186669 1399006798091347395820001)
                      ·
                        rfl

theorem cell23_2724556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2724556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724556 prefixEnd_2724556 := by exact prefixLift 2724556
  have htrace : WordTrace (prefixWord ++ tailWord_2724556) baseStart_2724556 baseEnd_2724556 := by
    simpa [prefixWord, tailWord_2724556, baseEnd_2724556] using wordTrace_append hprefix tailTrace_2724556
  have hstable : (prefixWord ++ tailWord_2724556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724556).length < 2 ^ (prefixWord ++ tailWord_2724556).sum := by decide
  have hdescent : baseEnd_2724556 < baseStart_2724556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724660 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_2724660 : Nat := 118140960795 + 2724660 * 2 ^ 59
def prefixEnd_2724660 : Nat := 4983230072969 + 3 ^ 40 * 2724660 * 2
def baseEnd_2724660 : Nat := 1399060200079414988919523

theorem tailTrace_2724660 : CollatzResearch.WordTrace tailWord_2724660 prefixEnd_2724660 1399060200079414988919523 := by
  unfold tailWord_2724660
  simp only [CollatzResearch.WordTrace]
  refine ⟨49688257154514814862953717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66251009539353086483938289 49688257154514814862953717)
  ·
    refine ⟨4658274108235763893401911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49688257154514814862953717 4658274108235763893401911)
    ·
      refine ⟨6987411162353645840102867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4658274108235763893401911 6987411162353645840102867)
      ·
        refine ⟨10481116743530468760154301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6987411162353645840102867 10481116743530468760154301)
        ·
          refine ⟨3930418778823925785057863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10481116743530468760154301 3930418778823925785057863)
          ·
            refine ⟨5895628168235888677586795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930418778823925785057863 5895628168235888677586795)
            ·
              refine ⟨8843442252353833016380193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5895628168235888677586795 8843442252353833016380193)
              ·
                refine ⟨6632581689265374762285145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8843442252353833016380193 6632581689265374762285145)
                ·
                  refine ⟨4974436266949031071713859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6632581689265374762285145 4974436266949031071713859)
                  ·
                    refine ⟨7461654400423546607570789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4974436266949031071713859 7461654400423546607570789)
                    ·
                      refine ⟨1399060200079414988919523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7461654400423546607570789 1399060200079414988919523)
                      ·
                        rfl

theorem cell23_2724660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_2724660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724660 prefixEnd_2724660 := by exact prefixLift 2724660
  have htrace : WordTrace (prefixWord ++ tailWord_2724660) baseStart_2724660 baseEnd_2724660 := by
    simpa [prefixWord, tailWord_2724660, baseEnd_2724660] using wordTrace_append hprefix tailTrace_2724660
  have hstable : (prefixWord ++ tailWord_2724660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724660).length < 2 ^ (prefixWord ++ tailWord_2724660).sum := by decide
  have hdescent : baseEnd_2724660 < baseStart_2724660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724679 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 2, 9]
def baseStart_2724679 : Nat := 118140960795 + 2724679 * 2 ^ 59
def prefixEnd_2724679 : Nat := 4983230072969 + 3 ^ 40 * 2724679 * 2
def baseEnd_2724679 : Nat := 466356652070616804860645

theorem tailTrace_2724679 : CollatzResearch.WordTrace tailWord_2724679 prefixEnd_2724679 466356652070616804860645 := by
  unfold tailWord_2724679
  simp only [CollatzResearch.WordTrace]
  refine ⟨99377207295960795970849091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66251471530640530647232727 99377207295960795970849091)
  ·
    refine ⟨149065810943941193956273637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99377207295960795970849091 149065810943941193956273637)
    ·
      refine ⟨27949839551988973866801307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149065810943941193956273637 27949839551988973866801307)
      ·
        refine ⟨41924759327983460800201961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27949839551988973866801307 41924759327983460800201961)
        ·
          refine ⟨31443569495987595600151471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41924759327983460800201961 31443569495987595600151471)
          ·
            refine ⟨47165354243981393400227207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31443569495987595600151471 47165354243981393400227207)
            ·
              refine ⟨70748031365972090100340811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47165354243981393400227207 70748031365972090100340811)
              ·
                refine ⟨106122047048958135150511217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70748031365972090100340811 106122047048958135150511217)
                ·
                  refine ⟨79591535286718601362883413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106122047048958135150511217 79591535286718601362883413)
                  ·
                    refine ⟨466356652070616804860645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79591535286718601362883413 466356652070616804860645)
                    ·
                      rfl

theorem cell23_2724679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_2724679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724679 prefixEnd_2724679 := by exact prefixLift 2724679
  have htrace : WordTrace (prefixWord ++ tailWord_2724679) baseStart_2724679 baseEnd_2724679 := by
    simpa [prefixWord, tailWord_2724679, baseEnd_2724679] using wordTrace_append hprefix tailTrace_2724679
  have hstable : (prefixWord ++ tailWord_2724679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724679).length < 2 ^ (prefixWord ++ tailWord_2724679).sum := by decide
  have hdescent : baseEnd_2724679 < baseStart_2724679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724693 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2724693 : Nat := 118140960795 + 2724693 * 2 ^ 59
def prefixEnd_2724693 : Nat := 4983230072969 + 3 ^ 40 * 2724693 * 2
def baseEnd_2724693 : Nat := 1399077144941013359806871

theorem tailTrace_2724693 : CollatzResearch.WordTrace tailWord_2724693 prefixEnd_2724693 1399077144941013359806871 := by
  unfold tailWord_2724693
  simp only [CollatzResearch.WordTrace]
  refine ⟨99377717917910076361858733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66251811945273384241239155 99377717917910076361858733)
  ·
    refine ⟨37266644219216278635697025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99377717917910076361858733 37266644219216278635697025)
    ·
      refine ⟨27949983164412208976772769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37266644219216278635697025 27949983164412208976772769)
      ·
        refine ⟨20962487373309156732579577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27949983164412208976772769 20962487373309156732579577)
        ·
          refine ⟨15721865529981867549434683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20962487373309156732579577 15721865529981867549434683)
          ·
            refine ⟨23582798294972801324152025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15721865529981867549434683 23582798294972801324152025)
            ·
              refine ⟨17687098721229600993114019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23582798294972801324152025 17687098721229600993114019)
              ·
                refine ⟨26530648081844401489671029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17687098721229600993114019 26530648081844401489671029)
                ·
                  refine ⟨2487248257672912639656659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26530648081844401489671029 2487248257672912639656659)
                  ·
                    refine ⟨3730872386509368959484989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2487248257672912639656659 3730872386509368959484989)
                    ·
                      refine ⟨1399077144941013359806871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3730872386509368959484989 1399077144941013359806871)
                      ·
                        rfl

theorem cell23_2724693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2724693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724693 prefixEnd_2724693 := by exact prefixLift 2724693
  have htrace : WordTrace (prefixWord ++ tailWord_2724693) baseStart_2724693 baseEnd_2724693 := by
    simpa [prefixWord, tailWord_2724693, baseEnd_2724693] using wordTrace_append hprefix tailTrace_2724693
  have hstable : (prefixWord ++ tailWord_2724693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724693).length < 2 ^ (prefixWord ++ tailWord_2724693).sum := by decide
  have hdescent : baseEnd_2724693 < baseStart_2724693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724743 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 1, 6]
def baseStart_2724743 : Nat := 118140960795 + 2724743 * 2 ^ 59
def prefixEnd_2724743 : Nat := 4983230072969 + 3 ^ 40 * 2724743 * 2
def baseEnd_2724743 : Nat := 466367606324579388060547

theorem tailTrace_2724743 : CollatzResearch.WordTrace tailWord_2724743 prefixEnd_2724743 466367606324579388060547 := by
  unfold tailWord_2724743
  simp only [CollatzResearch.WordTrace]
  refine ⟨99379541567728934901178883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66253027711819289934119255 99379541567728934901178883)
  ·
    refine ⟨149069312351593402351768325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99379541567728934901178883 149069312351593402351768325)
    ·
      refine ⟨27950496065923762940956561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149069312351593402351768325 27950496065923762940956561)
      ·
        refine ⟨20962872049442822205717421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27950496065923762940956561 20962872049442822205717421)
        ·
          refine ⟨7861077018541058327144033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20962872049442822205717421 7861077018541058327144033)
          ·
            refine ⟨5895807763905793745358025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7861077018541058327144033 5895807763905793745358025)
            ·
              refine ⟨4421855822929345309018519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5895807763905793745358025 4421855822929345309018519)
              ·
                refine ⟨6632783734394017963527779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421855822929345309018519 6632783734394017963527779)
                ·
                  refine ⟨9949175601591026945291669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632783734394017963527779 9949175601591026945291669)
                  ·
                    refine ⟨466367606324579388060547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9949175601591026945291669 466367606324579388060547)
                    ·
                      rfl

theorem cell23_2724743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_2724743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724743 prefixEnd_2724743 := by exact prefixLift 2724743
  have htrace : WordTrace (prefixWord ++ tailWord_2724743) baseStart_2724743 baseEnd_2724743 := by
    simpa [prefixWord, tailWord_2724743, baseEnd_2724743] using wordTrace_append hprefix tailTrace_2724743
  have hstable : (prefixWord ++ tailWord_2724743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724743).length < 2 ^ (prefixWord ++ tailWord_2724743).sum := by decide
  have hdescent : baseEnd_2724743 < baseStart_2724743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724753 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_2724753 : Nat := 118140960795 + 2724753 * 2 ^ 59
def prefixEnd_2724753 : Nat := 4983230072969 + 3 ^ 40 * 2724753 * 2
def baseEnd_2724753 : Nat := 1399107953780283125056595

theorem tailTrace_2724753 : CollatzResearch.WordTrace tailWord_2724753 prefixEnd_2724753 1399107953780283125056595 := by
  unfold tailWord_2724753
  simp only [CollatzResearch.WordTrace]
  refine ⟨99379906297692706609042913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66253270865128471072695275 99379906297692706609042913)
  ·
    refine ⟨74534929723269529956782185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99379906297692706609042913 74534929723269529956782185)
    ·
      refine ⟨55901197292452147467586639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74534929723269529956782185 55901197292452147467586639)
      ·
        refine ⟨83851795938678221201379959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55901197292452147467586639 83851795938678221201379959)
        ·
          refine ⟨125777693908017331802069939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83851795938678221201379959 125777693908017331802069939)
          ·
            refine ⟨188666540862025997703104909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125777693908017331802069939 188666540862025997703104909)
            ·
              refine ⟨70749952823259749138664341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188666540862025997703104909 70749952823259749138664341)
              ·
                refine ⟨3316404038590300740874891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70749952823259749138664341 3316404038590300740874891)
                ·
                  refine ⟨4974606057885451111312337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316404038590300740874891 4974606057885451111312337)
                  ·
                    refine ⟨3730954543414088333484253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974606057885451111312337 3730954543414088333484253)
                    ·
                      refine ⟨1399107953780283125056595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3730954543414088333484253 1399107953780283125056595)
                      ·
                        rfl

theorem cell23_2724753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_2724753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724753 prefixEnd_2724753 := by exact prefixLift 2724753
  have htrace : WordTrace (prefixWord ++ tailWord_2724753) baseStart_2724753 baseEnd_2724753 := by
    simpa [prefixWord, tailWord_2724753, baseEnd_2724753] using wordTrace_append hprefix tailTrace_2724753
  have hstable : (prefixWord ++ tailWord_2724753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724753).length < 2 ^ (prefixWord ++ tailWord_2724753).sum := by decide
  have hdescent : baseEnd_2724753 < baseStart_2724753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724754 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_2724754 : Nat := 118140960795 + 2724754 * 2 ^ 59
def prefixEnd_2724754 : Nat := 4983230072969 + 3 ^ 40 * 2724754 * 2
def baseEnd_2724754 : Nat := 1399108467260937621144091

theorem tailTrace_2724754 : CollatzResearch.WordTrace tailWord_2724754 prefixEnd_2724754 1399108467260937621144091 := by
  unfold tailWord_2724754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24844985692672270944957329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66253295180459389186552877 24844985692672270944957329)
  ·
    refine ⟨18633739269504203208717997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24844985692672270944957329 18633739269504203208717997)
    ·
      refine ⟨6987652226064076203269249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18633739269504203208717997 6987652226064076203269249)
      ·
        refine ⟨5240739169548057152451937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6987652226064076203269249 5240739169548057152451937)
        ·
          refine ⟨3930554377161042864338953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5240739169548057152451937 3930554377161042864338953)
          ·
            refine ⟨2947915782870782148254215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3930554377161042864338953 2947915782870782148254215)
            ·
              refine ⟨4421873674306173222381323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947915782870782148254215 4421873674306173222381323)
              ·
                refine ⟨6632810511459259833571985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421873674306173222381323 6632810511459259833571985)
                ·
                  refine ⟨4974607883594444875178989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6632810511459259833571985 4974607883594444875178989)
                  ·
                    refine ⟨1865477956347916828192121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4974607883594444875178989 1865477956347916828192121)
                    ·
                      refine ⟨1399108467260937621144091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865477956347916828192121 1399108467260937621144091)
                      ·
                        rfl

theorem cell23_2724754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_2724754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724754 prefixEnd_2724754 := by exact prefixLift 2724754
  have htrace : WordTrace (prefixWord ++ tailWord_2724754) baseStart_2724754 baseEnd_2724754 := by
    simpa [prefixWord, tailWord_2724754, baseEnd_2724754] using wordTrace_append hprefix tailTrace_2724754
  have hstable : (prefixWord ++ tailWord_2724754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724754).length < 2 ^ (prefixWord ++ tailWord_2724754).sum := by decide
  have hdescent : baseEnd_2724754 < baseStart_2724754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724764 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2724764 : Nat := 118140960795 + 2724764 * 2 ^ 59
def prefixEnd_2724764 : Nat := 4983230072969 + 3 ^ 40 * 2724764 * 2
def baseEnd_2724764 : Nat := 466371200689160860673015

theorem tailTrace_2724764 : CollatzResearch.WordTrace tailWord_2724764 prefixEnd_2724764 466371200689160860673015 := by
  unfold tailWord_2724764
  simp only [CollatzResearch.WordTrace]
  refine ⟨49690153750326427743846673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66253538333768570325128897 49690153750326427743846673)
  ·
    refine ⟨37267615312744820807885005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49690153750326427743846673 37267615312744820807885005)
    ·
      refine ⟨13975355742279307802956877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37267615312744820807885005 13975355742279307802956877)
      ·
        refine ⟨5240758403354740426108829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13975355742279307802956877 5240758403354740426108829)
        ·
          refine ⟨1965284401258027659790811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5240758403354740426108829 1965284401258027659790811)
          ·
            refine ⟨2947926601887041489686217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965284401258027659790811 2947926601887041489686217)
            ·
              refine ⟨2210944951415281117264663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947926601887041489686217 2210944951415281117264663)
              ·
                refine ⟨3316417427122921675896995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210944951415281117264663 3316417427122921675896995)
                ·
                  refine ⟨4974626140684382513845493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316417427122921675896995 4974626140684382513845493)
                  ·
                    refine ⟨466371200689160860673015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4974626140684382513845493 466371200689160860673015)
                    ·
                      rfl

theorem cell23_2724764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2724764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724764 prefixEnd_2724764 := by exact prefixLift 2724764
  have htrace : WordTrace (prefixWord ++ tailWord_2724764) baseStart_2724764 baseEnd_2724764 := by
    simpa [prefixWord, tailWord_2724764, baseEnd_2724764] using wordTrace_append hprefix tailTrace_2724764
  have hstable : (prefixWord ++ tailWord_2724764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724764).length < 2 ^ (prefixWord ++ tailWord_2724764).sum := by decide
  have hdescent : baseEnd_2724764 < baseStart_2724764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724767 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 1, 1, 4]
def baseStart_2724767 : Nat := 118140960795 + 2724767 * 2 ^ 59
def prefixEnd_2724767 : Nat := 4983230072969 + 3 ^ 40 * 2724767 * 2
def baseEnd_2724767 : Nat := 1399115142509446070281531

theorem tailTrace_2724767 : CollatzResearch.WordTrace tailWord_2724767 prefixEnd_2724767 1399115142509446070281531 := by
  unfold tailWord_2724767
  simp only [CollatzResearch.WordTrace]
  refine ⟨99380416919641987000052555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66253611279761324666701703 99380416919641987000052555)
  ·
    refine ⟨149070625379462980500078833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99380416919641987000052555 149070625379462980500078833)
    ·
      refine ⟨111802969034597235375059125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149070625379462980500078833 111802969034597235375059125)
      ·
        refine ⟨10481528346993490816411793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111802969034597235375059125 10481528346993490816411793)
        ·
          refine ⟨7861146260245118112308845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10481528346993490816411793 7861146260245118112308845)
          ·
            refine ⟨2947929847591919292115817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7861146260245118112308845 2947929847591919292115817)
            ·
              refine ⟨2210947385693939469086863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2947929847591919292115817 2210947385693939469086863)
              ·
                refine ⟨3316421078540909203630295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210947385693939469086863 3316421078540909203630295)
                ·
                  refine ⟨4974631617811363805445443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316421078540909203630295 4974631617811363805445443)
                  ·
                    refine ⟨7461947426717045708168165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4974631617811363805445443 7461947426717045708168165)
                    ·
                      refine ⟨1399115142509446070281531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7461947426717045708168165 1399115142509446070281531)
                      ·
                        rfl

theorem cell23_2724767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_2724767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724767 prefixEnd_2724767 := by exact prefixLift 2724767
  have htrace : WordTrace (prefixWord ++ tailWord_2724767) baseStart_2724767 baseEnd_2724767 := by
    simpa [prefixWord, tailWord_2724767, baseEnd_2724767] using wordTrace_append hprefix tailTrace_2724767
  have hstable : (prefixWord ++ tailWord_2724767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724767).length < 2 ^ (prefixWord ++ tailWord_2724767).sum := by decide
  have hdescent : baseEnd_2724767 < baseStart_2724767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724797 : List Nat := [1, 4, 1, 2, 5, 1, 1, 1, 1, 2, 4]
def baseStart_2724797 : Nat := 118140960795 + 2724797 * 2 ^ 59
def prefixEnd_2724797 : Nat := 4983230072969 + 3 ^ 40 * 2724797 * 2
def baseEnd_2724797 : Nat := 1399130546929080952906393

theorem tailTrace_2724797 : CollatzResearch.WordTrace tailWord_2724797 prefixEnd_2724797 1399130546929080952906393 := by
  unfold tailWord_2724797
  simp only [CollatzResearch.WordTrace]
  refine ⟨99381511109533302123644645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66254340739688868082429763 99381511109533302123644645)
  ·
    refine ⟨18634033333037494148183371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99381511109533302123644645 18634033333037494148183371)
    ·
      refine ⟨27951049999556241222275057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18634033333037494148183371 27951049999556241222275057)
      ·
        refine ⟨20963287499667180916706293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27951049999556241222275057 20963287499667180916706293)
        ·
          refine ⟨1965308203093798210941215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20963287499667180916706293 1965308203093798210941215)
          ·
            refine ⟨2947962304640697316411823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965308203093798210941215 2947962304640697316411823)
            ·
              refine ⟨4421943456961045974617735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947962304640697316411823 4421943456961045974617735)
              ·
                refine ⟨6632915185441568961926603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421943456961045974617735 6632915185441568961926603)
                ·
                  refine ⟨9949372778162353442889905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632915185441568961926603 9949372778162353442889905)
                  ·
                    refine ⟨7462029583621765082167429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9949372778162353442889905 7462029583621765082167429)
                    ·
                      refine ⟨1399130546929080952906393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7462029583621765082167429 1399130546929080952906393)
                      ·
                        rfl

theorem cell23_2724797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_2724797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724797 prefixEnd_2724797 := by exact prefixLift 2724797
  have htrace : WordTrace (prefixWord ++ tailWord_2724797) baseStart_2724797 baseEnd_2724797 := by
    simpa [prefixWord, tailWord_2724797, baseEnd_2724797] using wordTrace_append hprefix tailTrace_2724797
  have hstable : (prefixWord ++ tailWord_2724797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724797).length < 2 ^ (prefixWord ++ tailWord_2724797).sum := by decide
  have hdescent : baseEnd_2724797 < baseStart_2724797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724800 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3]
def baseStart_2724800 : Nat := 118140960795 + 2724800 * 2 ^ 59
def prefixEnd_2724800 : Nat := 4983230072969 + 3 ^ 40 * 2724800 * 2
def baseEnd_2724800 : Nat := 1399132087371044441168879

theorem tailTrace_2724800 : CollatzResearch.WordTrace tailWord_2724800 prefixEnd_2724800 1399132087371044441168879 := by
  unfold tailWord_2724800
  simp only [CollatzResearch.WordTrace]
  refine ⟨49690810264261216818001927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66254413685681622424002569 49690810264261216818001927)
  ·
    refine ⟨74536215396391825227002891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49690810264261216818001927 74536215396391825227002891)
    ·
      refine ⟨111804323094587737840504337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74536215396391825227002891 111804323094587737840504337)
      ·
        refine ⟨83853242320940803380378253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111804323094587737840504337 83853242320940803380378253)
        ·
          refine ⟨31444965870352801267641845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83853242320940803380378253 31444965870352801267641845)
          ·
            refine ⟨2947965550345575118841423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31444965870352801267641845 2947965550345575118841423)
            ·
              refine ⟨4421948325518362678262135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2947965550345575118841423 4421948325518362678262135)
              ·
                refine ⟨6632922488277544017393203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4421948325518362678262135 6632922488277544017393203)
                ·
                  refine ⟨9949383732416316026089805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6632922488277544017393203 9949383732416316026089805)
                  ·
                    refine ⟨3731018899656118509783677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9949383732416316026089805 3731018899656118509783677)
                    ·
                      refine ⟨1399132087371044441168879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731018899656118509783677 1399132087371044441168879)
                      ·
                        rfl

theorem cell23_2724800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_2724800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724800 prefixEnd_2724800 := by exact prefixLift 2724800
  have htrace : WordTrace (prefixWord ++ tailWord_2724800) baseStart_2724800 baseEnd_2724800 := by
    simpa [prefixWord, tailWord_2724800, baseEnd_2724800] using wordTrace_append hprefix tailTrace_2724800
  have hstable : (prefixWord ++ tailWord_2724800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724800).length < 2 ^ (prefixWord ++ tailWord_2724800).sum := by decide
  have hdescent : baseEnd_2724800 < baseStart_2724800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724804 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2724804 : Nat := 118140960795 + 2724804 * 2 ^ 59
def prefixEnd_2724804 : Nat := 4983230072969 + 3 ^ 40 * 2724804 * 2
def baseEnd_2724804 : Nat := 1399134141293662425518861

theorem tailTrace_2724804 : CollatzResearch.WordTrace tailWord_2724804 prefixEnd_2724804 1399134141293662425518861 := by
  unfold tailWord_2724804
  simp only [CollatzResearch.WordTrace]
  refine ⟨49690883210253971159574733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66254510947005294879432977 49690883210253971159574733)
  ·
    refine ⟨18634081203845239184840525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49690883210253971159574733 18634081203845239184840525)
    ·
      refine ⟨6987780451441964694315197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18634081203845239184840525 6987780451441964694315197)
      ·
        refine ⟨2620417669290736760368199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6987780451441964694315197 2620417669290736760368199)
        ·
          refine ⟨3930626503936105140552299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620417669290736760368199 3930626503936105140552299)
          ·
            refine ⟨5895939755904157710828449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3930626503936105140552299 5895939755904157710828449)
            ·
              refine ⟨4421954816928118283121337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5895939755904157710828449 4421954816928118283121337)
              ·
                refine ⟨3316466112696088712341003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4421954816928118283121337 3316466112696088712341003)
                ·
                  refine ⟨4974699169044133068511505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316466112696088712341003 4974699169044133068511505)
                  ·
                    refine ⟨3731024376783099801383629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4974699169044133068511505 3731024376783099801383629)
                    ·
                      refine ⟨1399134141293662425518861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731024376783099801383629 1399134141293662425518861)
                      ·
                        rfl

theorem cell23_2724804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2724804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724804 prefixEnd_2724804 := by exact prefixLift 2724804
  have htrace : WordTrace (prefixWord ++ tailWord_2724804) baseStart_2724804 baseEnd_2724804 := by
    simpa [prefixWord, tailWord_2724804, baseEnd_2724804] using wordTrace_append hprefix tailTrace_2724804
  have hstable : (prefixWord ++ tailWord_2724804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724804).length < 2 ^ (prefixWord ++ tailWord_2724804).sum := by decide
  have hdescent : baseEnd_2724804 < baseStart_2724804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724836 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2724836 : Nat := 118140960795 + 2724836 * 2 ^ 59
def prefixEnd_2724836 : Nat := 4983230072969 + 3 ^ 40 * 2724836 * 2
def baseEnd_2724836 : Nat := 1399150572674606300318713

theorem tailTrace_2724836 : CollatzResearch.WordTrace tailWord_2724836 prefixEnd_2724836 1399150572674606300318713 := by
  unfold tailWord_2724836
  simp only [CollatzResearch.WordTrace]
  refine ⟨49691466778196005892157181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66255289037594674522876241 49691466778196005892157181)
  ·
    refine ⟨18634300041823502209558943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49691466778196005892157181 18634300041823502209558943)
    ·
      refine ⟨27951450062735253314338415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18634300041823502209558943 27951450062735253314338415)
      ·
        refine ⟨41927175094102879971507623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27951450062735253314338415 41927175094102879971507623)
        ·
          refine ⟨62890762641154319957261435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41927175094102879971507623 62890762641154319957261435)
          ·
            refine ⟨94336143961731479935892153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62890762641154319957261435 94336143961731479935892153)
            ·
              refine ⟨70752107971298609951919115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94336143961731479935892153 70752107971298609951919115)
              ·
                refine ⟨106128161956947914927878673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70752107971298609951919115 106128161956947914927878673)
                ·
                  refine ⟨79596121467710936195909005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106128161956947914927878673 79596121467710936195909005)
                  ·
                    refine ⟨29848545550391601073465877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79596121467710936195909005 29848545550391601073465877)
                    ·
                      refine ⟨1399150572674606300318713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29848545550391601073465877 1399150572674606300318713)
                      ·
                        rfl

theorem cell23_2724836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2724836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724836 prefixEnd_2724836 := by exact prefixLift 2724836
  have htrace : WordTrace (prefixWord ++ tailWord_2724836) baseStart_2724836 baseEnd_2724836 := by
    simpa [prefixWord, tailWord_2724836, baseEnd_2724836] using wordTrace_append hprefix tailTrace_2724836
  have hstable : (prefixWord ++ tailWord_2724836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724836).length < 2 ^ (prefixWord ++ tailWord_2724836).sum := by decide
  have hdescent : baseEnd_2724836 < baseStart_2724836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724857 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 2, 2, 2]
def baseStart_2724857 : Nat := 118140960795 + 2724857 * 2 ^ 59
def prefixEnd_2724857 : Nat := 4983230072969 + 3 ^ 40 * 2724857 * 2
def baseEnd_2724857 : Nat := 1399161355768350718156117

theorem tailTrace_2724857 : CollatzResearch.WordTrace tailWord_2724857 prefixEnd_2724857 1399161355768350718156117 := by
  unfold tailWord_2724857
  simp only [CollatzResearch.WordTrace]
  refine ⟨99383699489315932370828825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66255799659543954913885883 99383699489315932370828825)
  ·
    refine ⟨74537774616986949278121619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99383699489315932370828825 74537774616986949278121619)
    ·
      refine ⟨111806661925480423917182429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74537774616986949278121619 111806661925480423917182429)
      ·
        refine ⟨41927498222055158968943411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111806661925480423917182429 41927498222055158968943411)
        ·
          refine ⟨62891247333082738453415117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41927498222055158968943411 62891247333082738453415117)
          ·
            refine ⟨23584217749906026920030669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62891247333082738453415117 23584217749906026920030669)
            ·
              refine ⟨8844081656214760095011501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23584217749906026920030669 8844081656214760095011501)
              ·
                refine ⟨3316530621080535035629313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8844081656214760095011501 3316530621080535035629313)
                ·
                  refine ⟨2487397965810401276721985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3316530621080535035629313 2487397965810401276721985)
                  ·
                    refine ⟨1865548474357800957541489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2487397965810401276721985 1865548474357800957541489)
                    ·
                      refine ⟨1399161355768350718156117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865548474357800957541489 1399161355768350718156117)
                      ·
                        rfl

theorem cell23_2724857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_2724857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724857 prefixEnd_2724857 := by exact prefixLift 2724857
  have htrace : WordTrace (prefixWord ++ tailWord_2724857) baseStart_2724857 baseEnd_2724857 := by
    simpa [prefixWord, tailWord_2724857, baseEnd_2724857] using wordTrace_append hprefix tailTrace_2724857
  have hstable : (prefixWord ++ tailWord_2724857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724857).length < 2 ^ (prefixWord ++ tailWord_2724857).sum := by decide
  have hdescent : baseEnd_2724857 < baseStart_2724857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724897 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 5]
def baseStart_2724897 : Nat := 118140960795 + 2724897 * 2 ^ 59
def prefixEnd_2724897 : Nat := 4983230072969 + 3 ^ 40 * 2724897 * 2
def baseEnd_2724897 : Nat := 155464654999392284628437

theorem tailTrace_2724897 : CollatzResearch.WordTrace tailWord_2724897 prefixEnd_2724897 155464654999392284628437 := by
  unfold tailWord_2724897
  simp only [CollatzResearch.WordTrace]
  refine ⟨99385158409171019202284945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66256772272780679468189963 99385158409171019202284945)
  ·
    refine ⟨74538868806878264401713709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99385158409171019202284945 74538868806878264401713709)
    ·
      refine ⟨27952075802579349150642641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74538868806878264401713709 27952075802579349150642641)
      ·
        refine ⟨20964056851934511862981981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27952075802579349150642641 20964056851934511862981981)
        ·
          refine ⟨7861521319475441948618243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20964056851934511862981981 7861521319475441948618243)
          ·
            refine ⟨11792281979213162922927365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7861521319475441948618243 11792281979213162922927365)
            ·
              refine ⟨2211052871102468048048881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11792281979213162922927365 2211052871102468048048881)
              ·
                refine ⟨1658289653326851036036661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2211052871102468048048881 1658289653326851036036661)
                ·
                  refine ⟨155464654999392284628437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1658289653326851036036661 155464654999392284628437)
                  ·
                    rfl

theorem cell23_2724897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 5].length) (baseStart_2724897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724897 prefixEnd_2724897 := by exact prefixLift 2724897
  have htrace : WordTrace (prefixWord ++ tailWord_2724897) baseStart_2724897 baseEnd_2724897 := by
    simpa [prefixWord, tailWord_2724897, baseEnd_2724897] using wordTrace_append hprefix tailTrace_2724897
  have hstable : (prefixWord ++ tailWord_2724897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724897).length < 2 ^ (prefixWord ++ tailWord_2724897).sum := by decide
  have hdescent : baseEnd_2724897 < baseStart_2724897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724913 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2724913 : Nat := 118140960795 + 2724913 * 2 ^ 59
def prefixEnd_2724913 : Nat := 4983230072969 + 3 ^ 40 * 2724913 * 2
def baseEnd_2724913 : Nat := 1399190110685002499055859

theorem tailTrace_2724913 : CollatzResearch.WordTrace tailWord_2724913 prefixEnd_2724913 1399190110685002499055859 := by
  unfold tailWord_2724913
  simp only [CollatzResearch.WordTrace]
  refine ⟨99385741977113053934867393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66257161318075369289911595 99385741977113053934867393)
  ·
    refine ⟨74539306482834790451150545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99385741977113053934867393 74539306482834790451150545)
    ·
      refine ⟨55904479862126092838362909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74539306482834790451150545 55904479862126092838362909)
      ·
        refine ⟨20964179948297284814386091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55904479862126092838362909 20964179948297284814386091)
        ·
          refine ⟨31446269922445927221579137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20964179948297284814386091 31446269922445927221579137)
          ·
            refine ⟨23584702441834445416184353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31446269922445927221579137 23584702441834445416184353)
            ·
              refine ⟨17688526831375834062138265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23584702441834445416184353 17688526831375834062138265)
              ·
                refine ⟨13266395123531875546603699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17688526831375834062138265 13266395123531875546603699)
                ·
                  refine ⟨19899592685297813319905549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13266395123531875546603699 19899592685297813319905549)
                  ·
                    refine ⟨7462347256986679994964581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19899592685297813319905549 7462347256986679994964581)
                    ·
                      refine ⟨1399190110685002499055859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7462347256986679994964581 1399190110685002499055859)
                      ·
                        rfl

theorem cell23_2724913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2724913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724913 prefixEnd_2724913 := by exact prefixLift 2724913
  have htrace : WordTrace (prefixWord ++ tailWord_2724913) baseStart_2724913 baseEnd_2724913 := by
    simpa [prefixWord, tailWord_2724913, baseEnd_2724913] using wordTrace_append hprefix tailTrace_2724913
  have hstable : (prefixWord ++ tailWord_2724913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724913).length < 2 ^ (prefixWord ++ tailWord_2724913).sum := by decide
  have hdescent : baseEnd_2724913 < baseStart_2724913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2724953 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 6]
def baseStart_2724953 : Nat := 118140960795 + 2724953 * 2 ^ 59
def prefixEnd_2724953 : Nat := 4983230072969 + 3 ^ 40 * 2724953 * 2
def baseEnd_2724953 : Nat := 155467849990131371395075

theorem tailTrace_2724953 : CollatzResearch.WordTrace tailWord_2724953 prefixEnd_2724953 155467849990131371395075 := by
  unfold tailWord_2724953
  simp only [CollatzResearch.WordTrace]
  refine ⟨99387200896968140766323513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66258133931312093844215675 99387200896968140766323513)
  ·
    refine ⟨74540400672726105574742635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99387200896968140766323513 74540400672726105574742635)
    ·
      refine ⟨111810601009089158362113953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74540400672726105574742635 111810601009089158362113953)
      ·
        refine ⟨83857950756816868771585465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111810601009089158362113953 83857950756816868771585465)
        ·
          refine ⟨62893463067612651578689099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83857950756816868771585465 62893463067612651578689099)
          ·
            refine ⟨94340194601418977368033649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62893463067612651578689099 94340194601418977368033649)
            ·
              refine ⟨70755145951064233026025237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94340194601418977368033649 70755145951064233026025237)
              ·
                refine ⟨3316647466456135923094933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70755145951064233026025237 3316647466456135923094933)
                ·
                  refine ⟨155467849990131371395075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3316647466456135923094933 155467849990131371395075)
                  ·
                    rfl

theorem cell23_2724953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_2724953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2724953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2724953 prefixEnd_2724953 := by exact prefixLift 2724953
  have htrace : WordTrace (prefixWord ++ tailWord_2724953) baseStart_2724953 baseEnd_2724953 := by
    simpa [prefixWord, tailWord_2724953, baseEnd_2724953] using wordTrace_append hprefix tailTrace_2724953
  have hstable : (prefixWord ++ tailWord_2724953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2724953).length < 2 ^ (prefixWord ++ tailWord_2724953).sum := by decide
  have hdescent : baseEnd_2724953 < baseStart_2724953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2724953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725013 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2725013 : Nat := 118140960795 + 2725013 * 2 ^ 59
def prefixEnd_2725013 : Nat := 4983230072969 + 3 ^ 40 * 2725013 * 2
def baseEnd_2725013 : Nat := 466413819583484035935133

theorem tailTrace_2725013 : CollatzResearch.WordTrace tailWord_2725013 prefixEnd_2725013 466413819583484035935133 := by
  unfold tailWord_2725013
  simp only [CollatzResearch.WordTrace]
  refine ⟨99389389276750771013507693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66259592851167180675671795 99389389276750771013507693)
  ·
    refine ⟨37271020978781539130065385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99389389276750771013507693 37271020978781539130065385)
    ·
      refine ⟨27953265734086154347549039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37271020978781539130065385 27953265734086154347549039)
      ·
        refine ⟨41929898601129231521323559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27953265734086154347549039 41929898601129231521323559)
        ·
          refine ⟨62894847901693847281985339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41929898601129231521323559 62894847901693847281985339)
          ·
            refine ⟨94342271852540770922978009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62894847901693847281985339 94342271852540770922978009)
            ·
              refine ⟨70756703889405578192233507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94342271852540770922978009 70756703889405578192233507)
              ·
                refine ⟨106135055834108367288350261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70756703889405578192233507 106135055834108367288350261)
                ·
                  refine ⟨9950161484447659433282837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106135055834108367288350261 9950161484447659433282837)
                  ·
                    refine ⟨466413819583484035935133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9950161484447659433282837 466413819583484035935133)
                    ·
                      rfl

theorem cell23_2725013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2725013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725013 prefixEnd_2725013 := by exact prefixLift 2725013
  have htrace : WordTrace (prefixWord ++ tailWord_2725013) baseStart_2725013 baseEnd_2725013 := by
    simpa [prefixWord, tailWord_2725013, baseEnd_2725013] using wordTrace_append hprefix tailTrace_2725013
  have hstable : (prefixWord ++ tailWord_2725013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725013).length < 2 ^ (prefixWord ++ tailWord_2725013).sum := by decide
  have hdescent : baseEnd_2725013 < baseStart_2725013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725034 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_2725034 : Nat := 118140960795 + 2725034 * 2 ^ 59
def prefixEnd_2725034 : Nat := 4983230072969 + 3 ^ 40 * 2725034 * 2
def baseEnd_2725034 : Nat := 466417413948065508547601

theorem tailTrace_2725034 : CollatzResearch.WordTrace tailWord_2725034 prefixEnd_2725034 466417413948065508547601 := by
  unfold tailWord_2725034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24847538802418672900005539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66260103473116461066681437 24847538802418672900005539)
  ·
    refine ⟨37271308203628009350008309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24847538802418672900005539 37271308203628009350008309)
    ·
      refine ⟨3494185144090125876563279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37271308203628009350008309 3494185144090125876563279)
      ·
        refine ⟨5241277716135188814844919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3494185144090125876563279 5241277716135188814844919)
        ·
          refine ⟨7861916574202783222267379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241277716135188814844919 7861916574202783222267379)
          ·
            refine ⟨11792874861304174833401069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7861916574202783222267379 11792874861304174833401069)
            ·
              refine ⟨4422328072989065562525401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11792874861304174833401069 4422328072989065562525401)
              ·
                refine ⟨3316746054741799171894051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422328072989065562525401 3316746054741799171894051)
                ·
                  refine ⟨4975119082112698757841077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316746054741799171894051 4975119082112698757841077)
                  ·
                    refine ⟨466417413948065508547601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4975119082112698757841077 466417413948065508547601)
                    ·
                      rfl

theorem cell23_2725034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_2725034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725034 prefixEnd_2725034 := by exact prefixLift 2725034
  have htrace : WordTrace (prefixWord ++ tailWord_2725034) baseStart_2725034 baseEnd_2725034 := by
    simpa [prefixWord, tailWord_2725034, baseEnd_2725034] using wordTrace_append hprefix tailTrace_2725034
  have hstable : (prefixWord ++ tailWord_2725034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725034).length < 2 ^ (prefixWord ++ tailWord_2725034).sum := by decide
  have hdescent : baseEnd_2725034 < baseStart_2725034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725040 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3]
def baseStart_2725040 : Nat := 118140960795 + 2725040 * 2 ^ 59
def prefixEnd_2725040 : Nat := 4983230072969 + 3 ^ 40 * 2725040 * 2
def baseEnd_2725040 : Nat := 1399255322728123502167775

theorem tailTrace_2725040 : CollatzResearch.WordTrace tailWord_2725040 prefixEnd_2725040 1399255322728123502167775 := by
  unfold tailWord_2725040
  simp only [CollatzResearch.WordTrace]
  refine ⟨49695187023826477312370287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66260249365101969749827049 49695187023826477312370287)
  ·
    refine ⟨74542780535739715968555431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49695187023826477312370287 74542780535739715968555431)
    ·
      refine ⟨111814170803609573952833147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74542780535739715968555431 111814170803609573952833147)
      ·
        refine ⟨167721256205414360929249721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111814170803609573952833147 167721256205414360929249721)
        ·
          refine ⟨125790942154060770696937291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167721256205414360929249721 125790942154060770696937291)
          ·
            refine ⟨188686413231091156045405937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125790942154060770696937291 188686413231091156045405937)
            ·
              refine ⟨141514809923318367034054453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188686413231091156045405937 141514809923318367034054453)
              ·
                refine ⟨13267013430311096909442605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141514809923318367034054453 13267013430311096909442605)
                ·
                  refine ⟨4975130036366661341040977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13267013430311096909442605 4975130036366661341040977)
                  ·
                    refine ⟨3731347527274996005780733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4975130036366661341040977 3731347527274996005780733)
                    ·
                      refine ⟨1399255322728123502167775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731347527274996005780733 1399255322728123502167775)
                      ·
                        rfl

theorem cell23_2725040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_2725040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725040 prefixEnd_2725040 := by exact prefixLift 2725040
  have htrace : WordTrace (prefixWord ++ tailWord_2725040) baseStart_2725040 baseEnd_2725040 := by
    simpa [prefixWord, tailWord_2725040, baseEnd_2725040] using wordTrace_append hprefix tailTrace_2725040
  have hstable : (prefixWord ++ tailWord_2725040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725040).length < 2 ^ (prefixWord ++ tailWord_2725040).sum := by decide
  have hdescent : baseEnd_2725040 < baseStart_2725040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725043 : List Nat := [1, 1, 1, 2, 3, 2, 4, 9]
def baseStart_2725043 : Nat := 118140960795 + 2725043 * 2 ^ 59
def prefixEnd_2725043 : Nat := 4983230072969 + 3 ^ 40 * 2725043 * 2
def baseEnd_2725043 : Nat := 51824328265558777423343

theorem tailTrace_2725043 : CollatzResearch.WordTrace tailWord_2725043 prefixEnd_2725043 51824328265558777423343 := by
  unfold tailWord_2725043
  simp only [CollatzResearch.WordTrace]
  refine ⟨99390483466642086137099783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66260322311094724091399855 99390483466642086137099783)
  ·
    refine ⟨149085725199963129205649675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99390483466642086137099783 149085725199963129205649675)
    ·
      refine ⟨223628587799944693808474513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149085725199963129205649675 223628587799944693808474513)
      ·
        refine ⟨167721440849958520356355885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223628587799944693808474513 167721440849958520356355885)
        ·
          refine ⟨62895540318734445133633457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167721440849958520356355885 62895540318734445133633457)
          ·
            refine ⟨47171655239050833850225093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62895540318734445133633457 47171655239050833850225093)
            ·
              refine ⟨8844685357322031346917205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47171655239050833850225093 8844685357322031346917205)
              ·
                refine ⟨51824328265558777423343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8844685357322031346917205 51824328265558777423343)
                ·
                  rfl

theorem cell23_2725043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 9].length) (baseStart_2725043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725043 prefixEnd_2725043 := by exact prefixLift 2725043
  have htrace : WordTrace (prefixWord ++ tailWord_2725043) baseStart_2725043 baseEnd_2725043 := by
    simpa [prefixWord, tailWord_2725043, baseEnd_2725043] using wordTrace_append hprefix tailTrace_2725043
  have hstable : (prefixWord ++ tailWord_2725043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725043).length < 2 ^ (prefixWord ++ tailWord_2725043).sum := by decide
  have hdescent : baseEnd_2725043 < baseStart_2725043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725060 : List Nat := [2, 3, 3, 1, 3, 11]
def baseStart_2725060 : Nat := 118140960795 + 2725060 * 2 ^ 59
def prefixEnd_2725060 : Nat := 4983230072969 + 3 ^ 40 * 2725060 * 2
def baseEnd_2725060 : Nat := 5758294618688121086081

theorem tailTrace_2725060 : CollatzResearch.WordTrace tailWord_2725060 prefixEnd_2725060 5758294618688121086081 := by
  unfold tailWord_2725060
  simp only [CollatzResearch.WordTrace]
  refine ⟨49695551753790249020234317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66260735671720332026979089 49695551753790249020234317)
  ·
    refine ⟨18635831907671343382587869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49695551753790249020234317 18635831907671343382587869)
    ·
      refine ⟨6988436965376753768470451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18635831907671343382587869 6988436965376753768470451)
      ·
        refine ⟨10482655448065130652705677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6988436965376753768470451 10482655448065130652705677)
        ·
          refine ⟨3930995793024423994764629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10482655448065130652705677 3930995793024423994764629)
          ·
            refine ⟨5758294618688121086081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3930995793024423994764629 5758294618688121086081)
            ·
              rfl

theorem cell23_2725060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 11].length) (baseStart_2725060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725060 prefixEnd_2725060 := by exact prefixLift 2725060
  have htrace : WordTrace (prefixWord ++ tailWord_2725060) baseStart_2725060 baseEnd_2725060 := by
    simpa [prefixWord, tailWord_2725060, baseEnd_2725060] using wordTrace_append hprefix tailTrace_2725060
  have hstable : (prefixWord ++ tailWord_2725060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725060).length < 2 ^ (prefixWord ++ tailWord_2725060).sum := by decide
  have hdescent : baseEnd_2725060 < baseStart_2725060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725077 : List Nat := [1, 3, 2, 4, 1, 3, 1, 8]
def baseStart_2725077 : Nat := 118140960795 + 2725077 * 2 ^ 59
def prefixEnd_2725077 : Nat := 4983230072969 + 3 ^ 40 * 2725077 * 2
def baseEnd_2725077 : Nat := 51824974870827402126115

theorem tailTrace_2725077 : CollatzResearch.WordTrace tailWord_2725077 prefixEnd_2725077 51824974870827402126115 := by
  unfold tailWord_2725077
  simp only [CollatzResearch.WordTrace]
  refine ⟨99391723548518909943837485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66261149032345939962558323 99391723548518909943837485)
  ·
    refine ⟨37271896330694591228939057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99391723548518909943837485 37271896330694591228939057)
    ·
      refine ⟨27953922248020943421704293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37271896330694591228939057 27953922248020943421704293)
      ·
        refine ⟨5241360421503926891569555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27953922248020943421704293 5241360421503926891569555)
        ·
          refine ⟨7862040632255890337354333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241360421503926891569555 7862040632255890337354333)
          ·
            refine ⟨2948265237095958876507875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7862040632255890337354333 2948265237095958876507875)
            ·
              refine ⟨4422397855643938314761813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948265237095958876507875 4422397855643938314761813)
              ·
                refine ⟨51824974870827402126115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4422397855643938314761813 51824974870827402126115)
                ·
                  rfl

theorem cell23_2725077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 8].length) (baseStart_2725077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725077 prefixEnd_2725077 := by exact prefixLift 2725077
  have htrace : WordTrace (prefixWord ++ tailWord_2725077) baseStart_2725077 baseEnd_2725077 := by
    simpa [prefixWord, tailWord_2725077, baseEnd_2725077] using wordTrace_append hprefix tailTrace_2725077
  have hstable : (prefixWord ++ tailWord_2725077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725077).length < 2 ^ (prefixWord ++ tailWord_2725077).sum := by decide
  have hdescent : baseEnd_2725077 < baseStart_2725077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725114 : List Nat := [3, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2]
def baseStart_2725114 : Nat := 118140960795 + 2725114 * 2 ^ 59
def prefixEnd_2725114 : Nat := 4983230072969 + 3 ^ 40 * 2725114 * 2
def baseEnd_2725114 : Nat := 1399293320296556212642435

theorem tailTrace_2725114 : CollatzResearch.WordTrace tailWord_2725114 prefixEnd_2725114 1399293320296556212642435 := by
  unfold tailWord_2725114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24848268262346216315733599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66262048699589910175289597 24848268262346216315733599)
  ·
    refine ⟨37272402393519324473600399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24848268262346216315733599 37272402393519324473600399)
    ·
      refine ⟨55908603590278986710400599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37272402393519324473600399 55908603590278986710400599)
      ·
        refine ⟨83862905385418480065600899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55908603590278986710400599 83862905385418480065600899)
        ·
          refine ⟨125794358078127720098401349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83862905385418480065600899 125794358078127720098401349)
          ·
            refine ⟨23586442139648947518450253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125794358078127720098401349 23586442139648947518450253)
            ·
              refine ⟨8844915802368355319418845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23586442139648947518450253 8844915802368355319418845)
              ·
                refine ⟨3316843425888133244782067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8844915802368355319418845 3316843425888133244782067)
                ·
                  refine ⟨4975265138832199867173101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3316843425888133244782067 4975265138832199867173101)
                  ·
                    refine ⟨1865724427062074950189913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4975265138832199867173101 1865724427062074950189913)
                    ·
                      refine ⟨1399293320296556212642435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865724427062074950189913 1399293320296556212642435)
                      ·
                        rfl

theorem cell23_2725114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_2725114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725114 prefixEnd_2725114 := by exact prefixLift 2725114
  have htrace : WordTrace (prefixWord ++ tailWord_2725114) baseStart_2725114 baseEnd_2725114 := by
    simpa [prefixWord, tailWord_2725114, baseEnd_2725114] using wordTrace_append hprefix tailTrace_2725114
  have hstable : (prefixWord ++ tailWord_2725114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725114).length < 2 ^ (prefixWord ++ tailWord_2725114).sum := by decide
  have hdescent : baseEnd_2725114 < baseStart_2725114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725121 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_2725121 : Nat := 118140960795 + 2725121 * 2 ^ 59
def prefixEnd_2725121 : Nat := 4983230072969 + 3 ^ 40 * 2725121 * 2
def baseEnd_2725121 : Nat := 1399296914661137685254903

theorem tailTrace_2725121 : CollatzResearch.WordTrace tailWord_2725121 prefixEnd_2725121 1399296914661137685254903 := by
  unfold tailWord_2725121
  simp only [CollatzResearch.WordTrace]
  refine ⟨99393328360359505458439217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66262218906906336972292811 99393328360359505458439217)
  ·
    refine ⟨74544996270269629093829413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99393328360359505458439217 74544996270269629093829413)
    ·
      refine ⟨13977186800675555455093015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74544996270269629093829413 13977186800675555455093015)
      ·
        refine ⟨20965780201013333182639523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13977186800675555455093015 20965780201013333182639523)
        ·
          refine ⟨31448670301519999773959285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20965780201013333182639523 31448670301519999773959285)
          ·
            refine ⟨2948312840767499978808683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31448670301519999773959285 2948312840767499978808683)
            ·
              refine ⟨4422469261151249968213025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948312840767499978808683 4422469261151249968213025)
              ·
                refine ⟨3316851945863437476159769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4422469261151249968213025 3316851945863437476159769)
                ·
                  refine ⟨2487638959397578107119827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3316851945863437476159769 2487638959397578107119827)
                  ·
                    refine ⟨3731458439096367160679741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2487638959397578107119827 3731458439096367160679741)
                    ·
                      refine ⟨1399296914661137685254903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731458439096367160679741 1399296914661137685254903)
                      ·
                        rfl

theorem cell23_2725121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_2725121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725121 prefixEnd_2725121 := by exact prefixLift 2725121
  have htrace : WordTrace (prefixWord ++ tailWord_2725121) baseStart_2725121 baseEnd_2725121 := by
    simpa [prefixWord, tailWord_2725121, baseEnd_2725121] using wordTrace_append hprefix tailTrace_2725121
  have hstable : (prefixWord ++ tailWord_2725121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725121).length < 2 ^ (prefixWord ++ tailWord_2725121).sum := by decide
  have hdescent : baseEnd_2725121 < baseStart_2725121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725130 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_2725130 : Nat := 118140960795 + 2725130 * 2 ^ 59
def prefixEnd_2725130 : Nat := 4983230072969 + 3 ^ 40 * 2725130 * 2
def baseEnd_2725130 : Nat := 1399301535987028150042361

theorem tailTrace_2725130 : CollatzResearch.WordTrace tailWord_2725130 prefixEnd_2725130 1399301535987028150042361 := by
  unfold tailWord_2725130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24848414154331724998879211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66262437744884599997011229 24848414154331724998879211)
  ·
    refine ⟨37272621231497587498318817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24848414154331724998879211 37272621231497587498318817)
    ·
      refine ⟨27954465923623190623739113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37272621231497587498318817 27954465923623190623739113)
      ·
        refine ⟨20965849442717392967804335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27954465923623190623739113 20965849442717392967804335)
        ·
          refine ⟨31448774164076089451706503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20965849442717392967804335 31448774164076089451706503)
          ·
            refine ⟨47173161246114134177559755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31448774164076089451706503 47173161246114134177559755)
            ·
              refine ⟨70759741869171201266339633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47173161246114134177559755 70759741869171201266339633)
              ·
                refine ⟨53069806401878400949754725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70759741869171201266339633 53069806401878400949754725)
                ·
                  refine ⟨9950588700352200178079011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53069806401878400949754725 9950588700352200178079011)
                  ·
                    refine ⟨14925883050528300267118517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9950588700352200178079011 14925883050528300267118517)
                    ·
                      refine ⟨1399301535987028150042361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14925883050528300267118517 1399301535987028150042361)
                      ·
                        rfl

theorem cell23_2725130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_2725130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725130 prefixEnd_2725130 := by exact prefixLift 2725130
  have htrace : WordTrace (prefixWord ++ tailWord_2725130) baseStart_2725130 baseEnd_2725130 := by
    simpa [prefixWord, tailWord_2725130, baseEnd_2725130] using wordTrace_append hprefix tailTrace_2725130
  have hstable : (prefixWord ++ tailWord_2725130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725130).length < 2 ^ (prefixWord ++ tailWord_2725130).sum := by decide
  have hdescent : baseEnd_2725130 < baseStart_2725130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725138 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2725138 : Nat := 118140960795 + 2725138 * 2 ^ 59
def prefixEnd_2725138 : Nat := 4983230072969 + 3 ^ 40 * 2725138 * 2
def baseEnd_2725138 : Nat := 1399305643832264118742325

theorem tailTrace_2725138 : CollatzResearch.WordTrace tailWord_2725138 prefixEnd_2725138 1399305643832264118742325 := by
  unfold tailWord_2725138
  simp only [CollatzResearch.WordTrace]
  refine ⟨24848487100324479340452017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66262632267531944907872045 24848487100324479340452017)
  ·
    refine ⟨18636365325243359505339013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24848487100324479340452017 18636365325243359505339013)
    ·
      refine ⟨3494318498483129907251065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18636365325243359505339013 3494318498483129907251065)
      ·
        refine ⟨2620738873862347430438299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3494318498483129907251065 2620738873862347430438299)
        ·
          refine ⟨3931108310793521145657449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2620738873862347430438299 3931108310793521145657449)
          ·
            refine ⟨2948331233095140859243087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3931108310793521145657449 2948331233095140859243087)
            ·
              refine ⟨4422496849642711288864631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948331233095140859243087 4422496849642711288864631)
              ·
                refine ⟨6633745274464066933296947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422496849642711288864631 6633745274464066933296947)
                ·
                  refine ⟨9950617911696100399945421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6633745274464066933296947 9950617911696100399945421)
                  ·
                    refine ⟨3731481716886037649979533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9950617911696100399945421 3731481716886037649979533)
                    ·
                      refine ⟨1399305643832264118742325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731481716886037649979533 1399305643832264118742325)
                      ·
                        rfl

theorem cell23_2725138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2725138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725138 prefixEnd_2725138 := by exact prefixLift 2725138
  have htrace : WordTrace (prefixWord ++ tailWord_2725138) baseStart_2725138 baseEnd_2725138 := by
    simpa [prefixWord, tailWord_2725138, baseEnd_2725138] using wordTrace_append hprefix tailTrace_2725138
  have hstable : (prefixWord ++ tailWord_2725138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725138).length < 2 ^ (prefixWord ++ tailWord_2725138).sum := by decide
  have hdescent : baseEnd_2725138 < baseStart_2725138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725144 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 1, 4, 2]
def baseStart_2725144 : Nat := 118140960795 + 2725144 * 2 ^ 59
def prefixEnd_2725144 : Nat := 4983230072969 + 3 ^ 40 * 2725144 * 2
def baseEnd_2725144 : Nat := 1399308724716191095267297

theorem tailTrace_2725144 : CollatzResearch.WordTrace tailWord_2725144 prefixEnd_2725144 1399308724716191095267297 := by
  unfold tailWord_2725144
  simp only [CollatzResearch.WordTrace]
  refine ⟨49697083619638090193263243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66262778159517453591017657 49697083619638090193263243)
  ·
    refine ⟨74545625429457135289894865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49697083619638090193263243 74545625429457135289894865)
    ·
      refine ⟨55909219072092851467421149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74545625429457135289894865 55909219072092851467421149)
      ·
        refine ⟨20965957152034819300282931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55909219072092851467421149 20965957152034819300282931)
        ·
          refine ⟨31448935728052228950424397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20965957152034819300282931 31448935728052228950424397)
          ·
            refine ⟨11793350898019585856409149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31448935728052228950424397 11793350898019585856409149)
            ·
              refine ⟨4422506586757344696153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11793350898019585856409149 4422506586757344696153431)
              ·
                refine ⟨6633759880136017044230147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4422506586757344696153431 6633759880136017044230147)
                ·
                  refine ⟨9950639820204025566345221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6633759880136017044230147 9950639820204025566345221)
                  ·
                    refine ⟨1865744966288254793689729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9950639820204025566345221 1865744966288254793689729)
                    ·
                      refine ⟨1399308724716191095267297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865744966288254793689729 1399308724716191095267297)
                      ·
                        rfl

theorem cell23_2725144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_2725144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725144 prefixEnd_2725144 := by exact prefixLift 2725144
  have htrace : WordTrace (prefixWord ++ tailWord_2725144) baseStart_2725144 baseEnd_2725144 := by
    simpa [prefixWord, tailWord_2725144, baseEnd_2725144] using wordTrace_append hprefix tailTrace_2725144
  have hstable : (prefixWord ++ tailWord_2725144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725144).length < 2 ^ (prefixWord ++ tailWord_2725144).sum := by decide
  have hdescent : baseEnd_2725144 < baseStart_2725144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725184 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 5]
def baseStart_2725184 : Nat := 118140960795 + 2725184 * 2 ^ 59
def prefixEnd_2725184 : Nat := 4983230072969 + 3 ^ 40 * 2725184 * 2
def baseEnd_2725184 : Nat := 155481029326930104307457

theorem tailTrace_2725184 : CollatzResearch.WordTrace tailWord_2725184 prefixEnd_2725184 155481029326930104307457 := by
  unfold tailWord_2725184
  simp only [CollatzResearch.WordTrace]
  refine ⟨49697813079565633608991303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66263750772754178145321737 49697813079565633608991303)
  ·
    refine ⟨74546719619348450413486955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49697813079565633608991303 74546719619348450413486955)
    ·
      refine ⟨111820079429022675620230433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74546719619348450413486955 111820079429022675620230433)
      ·
        refine ⟨83865059571767006715172825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111820079429022675620230433 83865059571767006715172825)
        ·
          refine ⟨62898794678825255036379619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83865059571767006715172825 62898794678825255036379619)
          ·
            refine ⟨94348192018237882554569429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62898794678825255036379619 94348192018237882554569429)
            ·
              refine ⟨2211285750427450372372721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94348192018237882554569429 2211285750427450372372721)
              ·
                refine ⟨1658464312820587779279541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2211285750427450372372721 1658464312820587779279541)
                ·
                  refine ⟨155481029326930104307457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1658464312820587779279541 155481029326930104307457)
                  ·
                    rfl

theorem cell23_2725184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 5].length) (baseStart_2725184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725184 prefixEnd_2725184 := by exact prefixLift 2725184
  have htrace : WordTrace (prefixWord ++ tailWord_2725184) baseStart_2725184 baseEnd_2725184 := by
    simpa [prefixWord, tailWord_2725184, baseEnd_2725184] using wordTrace_append hprefix tailTrace_2725184
  have hstable : (prefixWord ++ tailWord_2725184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725184).length < 2 ^ (prefixWord ++ tailWord_2725184).sum := by decide
  have hdescent : baseEnd_2725184 < baseStart_2725184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725187 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 2, 5, 2]
def baseStart_2725187 : Nat := 118140960795 + 2725187 * 2 ^ 59
def prefixEnd_2725187 : Nat := 4983230072969 + 3 ^ 40 * 2725187 * 2
def baseEnd_2725187 : Nat := 1399330804384334427029599

theorem tailTrace_2725187 : CollatzResearch.WordTrace tailWord_2725187 prefixEnd_2725187 1399330804384334427029599 := by
  unfold tailWord_2725187
  simp only [CollatzResearch.WordTrace]
  refine ⟨99395735578120398730341815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66263823718746932486894543 99395735578120398730341815)
  ·
    refine ⟨149093603367180598095512723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99395735578120398730341815 149093603367180598095512723)
    ·
      refine ⟨223640405050770897143269085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149093603367180598095512723 223640405050770897143269085)
      ·
        refine ⟨83865151894039086428725907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223640405050770897143269085 83865151894039086428725907)
        ·
          refine ⟨125797727841058629643088861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83865151894039086428725907 125797727841058629643088861)
          ·
            refine ⟨47174147940396986116158323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125797727841058629643088861 47174147940396986116158323)
            ·
              refine ⟨70761221910595479174237485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47174147940396986116158323 70761221910595479174237485)
              ·
                refine ⟨26535458216473304690339057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70761221910595479174237485 26535458216473304690339057)
                ·
                  refine ⟨19901593662354978517754293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26535458216473304690339057 19901593662354978517754293)
                  ·
                    refine ⟨1865774405845779236039465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19901593662354978517754293 1865774405845779236039465)
                    ·
                      refine ⟨1399330804384334427029599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865774405845779236039465 1399330804384334427029599)
                      ·
                        rfl

theorem cell23_2725187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5, 2].length) (baseStart_2725187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725187 prefixEnd_2725187 := by exact prefixLift 2725187
  have htrace : WordTrace (prefixWord ++ tailWord_2725187) baseStart_2725187 baseEnd_2725187 := by
    simpa [prefixWord, tailWord_2725187, baseEnd_2725187] using wordTrace_append hprefix tailTrace_2725187
  have hstable : (prefixWord ++ tailWord_2725187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725187).length < 2 ^ (prefixWord ++ tailWord_2725187).sum := by decide
  have hdescent : baseEnd_2725187 < baseStart_2725187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725210 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_2725210 : Nat := 118140960795 + 2725210 * 2 ^ 59
def prefixEnd_2725210 : Nat := 4983230072969 + 3 ^ 40 * 2725210 * 2
def baseEnd_2725210 : Nat := 466447538146462612347331

theorem tailTrace_2725210 : CollatzResearch.WordTrace tailWord_2725210 prefixEnd_2725210 466447538146462612347331 := by
  unfold tailWord_2725210
  simp only [CollatzResearch.WordTrace]
  refine ⟨24849143614259268414607271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66264382971358049105619389 24849143614259268414607271)
  ·
    refine ⟨37273715421388902621910907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24849143614259268414607271 37273715421388902621910907)
    ·
      refine ⟨55910573132083353932866361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37273715421388902621910907 55910573132083353932866361)
      ·
        refine ⟨41932929849062515449649771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55910573132083353932866361 41932929849062515449649771)
        ·
          refine ⟨62899394773593773174474657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41932929849062515449649771 62899394773593773174474657)
          ·
            refine ⟨47174546080195329880855993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62899394773593773174474657 47174546080195329880855993)
            ·
              refine ⟨35380909560146497410641995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47174546080195329880855993 35380909560146497410641995)
              ·
                refine ⟨53071364340219746115962993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35380909560146497410641995 53071364340219746115962993)
                ·
                  refine ⟨39803523255164809586972245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53071364340219746115962993 39803523255164809586972245)
                  ·
                    refine ⟨466447538146462612347331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39803523255164809586972245 466447538146462612347331)
                    ·
                      rfl

theorem cell23_2725210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_2725210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725210 prefixEnd_2725210 := by exact prefixLift 2725210
  have htrace : WordTrace (prefixWord ++ tailWord_2725210) baseStart_2725210 baseEnd_2725210 := by
    simpa [prefixWord, tailWord_2725210, baseEnd_2725210] using wordTrace_append hprefix tailTrace_2725210
  have hstable : (prefixWord ++ tailWord_2725210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725210).length < 2 ^ (prefixWord ++ tailWord_2725210).sum := by decide
  have hdescent : baseEnd_2725210 < baseStart_2725210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725234 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_2725234 : Nat := 118140960795 + 2725234 * 2 ^ 59
def prefixEnd_2725234 : Nat := 4983230072969 + 3 ^ 40 * 2725234 * 2
def baseEnd_2725234 : Nat := 1399354937975095743141883

theorem tailTrace_2725234 : CollatzResearch.WordTrace tailWord_2725234 prefixEnd_2725234 1399354937975095743141883 := by
  unfold tailWord_2725234
  simp only [CollatzResearch.WordTrace]
  refine ⟨24849362452237531439325689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66264966539300083838201837 24849362452237531439325689)
  ·
    refine ⟨18637021839178148579494267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24849362452237531439325689 18637021839178148579494267)
    ·
      refine ⟨27955532758767222869241401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18637021839178148579494267 27955532758767222869241401)
      ·
        refine ⟨20966649569075417151931051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27955532758767222869241401 20966649569075417151931051)
        ·
          refine ⟨31449974353613125727896577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20966649569075417151931051 31449974353613125727896577)
          ·
            refine ⟨23587480765209844295922433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31449974353613125727896577 23587480765209844295922433)
            ·
              refine ⟨17690610573907383221941825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23587480765209844295922433 17690610573907383221941825)
              ·
                refine ⟨13267957930430537416456369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17690610573907383221941825 13267957930430537416456369)
                ·
                  refine ⟨9950968447822903062342277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13267957930430537416456369 9950968447822903062342277)
                  ·
                    refine ⟨1865806583966794324189177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9950968447822903062342277 1865806583966794324189177)
                    ·
                      refine ⟨1399354937975095743141883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865806583966794324189177 1399354937975095743141883)
                      ·
                        rfl

theorem cell23_2725234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_2725234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725234 prefixEnd_2725234 := by exact prefixLift 2725234
  have htrace : WordTrace (prefixWord ++ tailWord_2725234) baseStart_2725234 baseEnd_2725234 := by
    simpa [prefixWord, tailWord_2725234, baseEnd_2725234] using wordTrace_append hprefix tailTrace_2725234
  have hstable : (prefixWord ++ tailWord_2725234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725234).length < 2 ^ (prefixWord ++ tailWord_2725234).sum := by decide
  have hdescent : baseEnd_2725234 < baseStart_2725234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725284 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_2725284 : Nat := 118140960795 + 2725284 * 2 ^ 59
def prefixEnd_2725284 : Nat := 4983230072969 + 3 ^ 40 * 2725284 * 2
def baseEnd_2725284 : Nat := 1399380612007820547516653

theorem tailTrace_2725284 : CollatzResearch.WordTrace tailWord_2725284 prefixEnd_2725284 1399380612007820547516653 := by
  unfold tailWord_2725284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49699636729384492148311453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66266182305845989531081937 49699636729384492148311453)
  ·
    refine ⟨18637363773519184555616795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49699636729384492148311453 18637363773519184555616795)
    ·
      refine ⟨27956045660278776833425193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18637363773519184555616795 27956045660278776833425193)
      ·
        refine ⟨20967034245209082625068895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27956045660278776833425193 20967034245209082625068895)
        ·
          refine ⟨31450551367813623937603343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20967034245209082625068895 31450551367813623937603343)
          ·
            refine ⟨47175827051720435906405015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31450551367813623937603343 47175827051720435906405015)
            ·
              refine ⟨70763740577580653859607523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47175827051720435906405015 70763740577580653859607523)
              ·
                refine ⟨106145610866370980789411285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70763740577580653859607523 106145610866370980789411285)
                ·
                  refine ⟨2487787754680569862251827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 106145610866370980789411285 2487787754680569862251827)
                  ·
                    refine ⟨3731681632020854793377741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2487787754680569862251827 3731681632020854793377741)
                    ·
                      refine ⟨1399380612007820547516653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731681632020854793377741 1399380612007820547516653)
                      ·
                        rfl

theorem cell23_2725284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_2725284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725284 prefixEnd_2725284 := by exact prefixLift 2725284
  have htrace : WordTrace (prefixWord ++ tailWord_2725284) baseStart_2725284 baseEnd_2725284 := by
    simpa [prefixWord, tailWord_2725284, baseEnd_2725284] using wordTrace_append hprefix tailTrace_2725284
  have hstable : (prefixWord ++ tailWord_2725284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725284).length < 2 ^ (prefixWord ++ tailWord_2725284).sum := by decide
  have hdescent : baseEnd_2725284 < baseStart_2725284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725301 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2725301 : Nat := 118140960795 + 2725301 * 2 ^ 59
def prefixEnd_2725301 : Nat := 4983230072969 + 3 ^ 40 * 2725301 * 2
def baseEnd_2725301 : Nat := 1399389341178946981004075

theorem tailTrace_2725301 : CollatzResearch.WordTrace tailWord_2725301 prefixEnd_2725301 1399389341178946981004075 := by
  unfold tailWord_2725301
  simp only [CollatzResearch.WordTrace]
  refine ⟨99399893499707396199991757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66266595666471597466661171 99399893499707396199991757)
  ·
    refine ⟨37274960062390273574996909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99399893499707396199991757 37274960062390273574996909)
    ·
      refine ⟨13978110023396352590623841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37274960062390273574996909 13978110023396352590623841)
      ·
        refine ⟨10483582517547264442967881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13978110023396352590623841 10483582517547264442967881)
        ·
          refine ⟨7862686888160448332225911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10483582517547264442967881 7862686888160448332225911)
          ·
            refine ⟨11794030332240672498338867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7862686888160448332225911 11794030332240672498338867)
            ·
              refine ⟨17691045498361008747508301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11794030332240672498338867 17691045498361008747508301)
              ·
                refine ⟨6634142061885378280315613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17691045498361008747508301 6634142061885378280315613)
                ·
                  refine ⟨2487803273207016855118355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6634142061885378280315613 2487803273207016855118355)
                  ·
                    refine ⟨3731704909810525282677533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2487803273207016855118355 3731704909810525282677533)
                    ·
                      refine ⟨1399389341178946981004075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731704909810525282677533 1399389341178946981004075)
                      ·
                        rfl

theorem cell23_2725301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2725301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725301 prefixEnd_2725301 := by exact prefixLift 2725301
  have htrace : WordTrace (prefixWord ++ tailWord_2725301) baseStart_2725301 baseEnd_2725301 := by
    simpa [prefixWord, tailWord_2725301, baseEnd_2725301] using wordTrace_append hprefix tailTrace_2725301
  have hstable : (prefixWord ++ tailWord_2725301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725301).length < 2 ^ (prefixWord ++ tailWord_2725301).sum := by decide
  have hdescent : baseEnd_2725301 < baseStart_2725301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725341 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2725341 : Nat := 118140960795 + 2725341 * 2 ^ 59
def prefixEnd_2725341 : Nat := 4983230072969 + 3 ^ 40 * 2725341 * 2
def baseEnd_2725341 : Nat := 1399409880405126824503891

theorem tailTrace_2725341 : CollatzResearch.WordTrace tailWord_2725341 prefixEnd_2725341 1399409880405126824503891 := by
  unfold tailWord_2725341
  simp only [CollatzResearch.WordTrace]
  refine ⟨99401352419562483031447877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66267568279708322020965251 99401352419562483031447877)
  ·
    refine ⟨18637753578667965568396477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99401352419562483031447877 18637753578667965568396477)
    ·
      refine ⟨6989157592000487088148679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18637753578667965568396477 6989157592000487088148679)
      ·
        refine ⟨10483736388000730632223019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6989157592000487088148679 10483736388000730632223019)
        ·
          refine ⟨15725604582001095948334529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10483736388000730632223019 15725604582001095948334529)
          ·
            refine ⟨11794203436500821961250897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15725604582001095948334529 11794203436500821961250897)
            ·
              refine ⟨8845652577375616470938173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11794203436500821961250897 8845652577375616470938173)
              ·
                refine ⟨3317119716515856176601815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8845652577375616470938173 3317119716515856176601815)
                ·
                  refine ⟨4975679574773784264902723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317119716515856176601815 4975679574773784264902723)
                  ·
                    refine ⟨7463519362160676397354085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4975679574773784264902723 7463519362160676397354085)
                    ·
                      refine ⟨1399409880405126824503891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7463519362160676397354085 1399409880405126824503891)
                      ·
                        rfl

theorem cell23_2725341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2725341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725341 prefixEnd_2725341 := by exact prefixLift 2725341
  have htrace : WordTrace (prefixWord ++ tailWord_2725341) baseStart_2725341 baseEnd_2725341 := by
    simpa [prefixWord, tailWord_2725341, baseEnd_2725341] using wordTrace_append hprefix tailTrace_2725341
  have hstable : (prefixWord ++ tailWord_2725341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725341).length < 2 ^ (prefixWord ++ tailWord_2725341).sum := by decide
  have hdescent : baseEnd_2725341 < baseStart_2725341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725347 : List Nat := [1, 1, 1, 6, 2, 1, 11]
def baseStart_2725347 : Nat := 118140960795 + 2725347 * 2 ^ 59
def prefixEnd_2725347 : Nat := 4983230072969 + 3 ^ 40 * 2725347 * 2
def baseEnd_2725347 : Nat := 17276703225790787667023

theorem tailTrace_2725347 : CollatzResearch.WordTrace tailWord_2725347 prefixEnd_2725347 17276703225790787667023 := by
  unfold tailWord_2725347
  simp only [CollatzResearch.WordTrace]
  refine ⟨99401571257540746056166295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66267714171693830704110863 99401571257540746056166295)
  ·
    refine ⟨149102356886311119084249443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99401571257540746056166295 149102356886311119084249443)
    ·
      refine ⟨223653535329466678626374165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149102356886311119084249443 223653535329466678626374165)
      ·
        refine ⟨10483759468568750560611289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 223653535329466678626374165 10483759468568750560611289)
        ·
          refine ⟨7862819601426562920458467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10483759468568750560611289 7862819601426562920458467)
          ·
            refine ⟨11794229402139844380687701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7862819601426562920458467 11794229402139844380687701)
            ·
              refine ⟨17276703225790787667023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11794229402139844380687701 17276703225790787667023)
              ·
                rfl

theorem cell23_2725347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 11].length) (baseStart_2725347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725347 prefixEnd_2725347 := by exact prefixLift 2725347
  have htrace : WordTrace (prefixWord ++ tailWord_2725347) baseStart_2725347 baseEnd_2725347 := by
    simpa [prefixWord, tailWord_2725347, baseEnd_2725347] using wordTrace_append hprefix tailTrace_2725347
  have hstable : (prefixWord ++ tailWord_2725347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725347).length < 2 ^ (prefixWord ++ tailWord_2725347).sum := by decide
  have hdescent : baseEnd_2725347 < baseStart_2725347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725368 : List Nat := [2, 1, 2, 1, 1, 7, 2, 1, 2, 4]
def baseStart_2725368 : Nat := 118140960795 + 2725368 * 2 ^ 59
def prefixEnd_2725368 : Nat := 4983230072969 + 3 ^ 40 * 2725368 * 2
def baseEnd_2725368 : Nat := 466474581460932739622089

theorem tailTrace_2725368 : CollatzResearch.WordTrace tailWord_2725368 prefixEnd_2725368 466474581460932739622089 := by
  unfold tailWord_2725368
  simp only [CollatzResearch.WordTrace]
  refine ⟨49701168595232333321340379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66268224793643111095120505 49701168595232333321340379)
  ·
    refine ⟨74551752892848499982010569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49701168595232333321340379 74551752892848499982010569)
    ·
      refine ⟨55913814669636374986507927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74551752892848499982010569 55913814669636374986507927)
      ·
        refine ⟨83870722004454562479761891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55913814669636374986507927 83870722004454562479761891)
        ·
          refine ⟨125806083006681843719642837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83870722004454562479761891 125806083006681843719642837)
          ·
            refine ⟨2948580070469105712179129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 125806083006681843719642837 2948580070469105712179129)
            ·
              refine ⟨2211435052851829284134347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2948580070469105712179129 2211435052851829284134347)
              ·
                refine ⟨3317152579277743926201521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211435052851829284134347 3317152579277743926201521)
                ·
                  refine ⟨2487864434458307944651141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3317152579277743926201521 2487864434458307944651141)
                  ·
                    refine ⟨466474581460932739622089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2487864434458307944651141 466474581460932739622089)
                    ·
                      rfl

theorem cell23_2725368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_2725368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725368 prefixEnd_2725368 := by exact prefixLift 2725368
  have htrace : WordTrace (prefixWord ++ tailWord_2725368) baseStart_2725368 baseEnd_2725368 := by
    simpa [prefixWord, tailWord_2725368, baseEnd_2725368] using wordTrace_append hprefix tailTrace_2725368
  have hstable : (prefixWord ++ tailWord_2725368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725368).length < 2 ^ (prefixWord ++ tailWord_2725368).sum := by decide
  have hdescent : baseEnd_2725368 < baseStart_2725368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725378 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2725378 : Nat := 118140960795 + 2725378 * 2 ^ 59
def prefixEnd_2725378 : Nat := 4983230072969 + 3 ^ 40 * 2725378 * 2
def baseEnd_2725378 : Nat := 1399428879189343179741221

theorem tailTrace_2725378 : CollatzResearch.WordTrace tailWord_2725378 prefixEnd_2725378 1399428879189343179741221 := by
  unfold tailWord_2725378
  simp only [CollatzResearch.WordTrace]
  refine ⟨24850675480107109587636197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66268467946952292233696525 24850675480107109587636197)
  ·
    refine ⟨4659501652520083047681787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24850675480107109587636197 4659501652520083047681787)
    ·
      refine ⟨6989252478780124571522681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4659501652520083047681787 6989252478780124571522681)
      ·
        refine ⟨5241939359085093428642011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6989252478780124571522681 5241939359085093428642011)
        ·
          refine ⟨7862909038627640142963017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241939359085093428642011 7862909038627640142963017)
          ·
            refine ⟨5897181778970730107222263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7862909038627640142963017 5897181778970730107222263)
            ·
              refine ⟨8845772668456095160833395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5897181778970730107222263 8845772668456095160833395)
              ·
                refine ⟨13268659002684142741250093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8845772668456095160833395 13268659002684142741250093)
                ·
                  refine ⟨4975747126006553527968785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13268659002684142741250093 4975747126006553527968785)
                  ·
                    refine ⟨3731810344504915145976589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4975747126006553527968785 3731810344504915145976589)
                    ·
                      refine ⟨1399428879189343179741221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731810344504915145976589 1399428879189343179741221)
                      ·
                        rfl

theorem cell23_2725378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2725378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725378 prefixEnd_2725378 := by exact prefixLift 2725378
  have htrace : WordTrace (prefixWord ++ tailWord_2725378) baseStart_2725378 baseEnd_2725378 := by
    simpa [prefixWord, tailWord_2725378, baseEnd_2725378] using wordTrace_append hprefix tailTrace_2725378
  have hstable : (prefixWord ++ tailWord_2725378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725378).length < 2 ^ (prefixWord ++ tailWord_2725378).sum := by decide
  have hdescent : baseEnd_2725378 < baseStart_2725378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725408 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2725408 : Nat := 118140960795 + 2725408 * 2 ^ 59
def prefixEnd_2725408 : Nat := 4983230072969 + 3 ^ 40 * 2725408 * 2
def baseEnd_2725408 : Nat := 1399444283608978062366083

theorem tailTrace_2725408 : CollatzResearch.WordTrace tailWord_2725408 prefixEnd_2725408 1399444283608978062366083 := by
  unfold tailWord_2725408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49701898055159876737068439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66269197406879835649424585 49701898055159876737068439)
  ·
    refine ⟨74552847082739815105602659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49701898055159876737068439 74552847082739815105602659)
    ·
      refine ⟨111829270624109722658403989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74552847082739815105602659 111829270624109722658403989)
      ·
        refine ⟨5241997060505143249612687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111829270624109722658403989 5241997060505143249612687)
        ·
          refine ⟨7862995590757714874419031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5241997060505143249612687 7862995590757714874419031)
          ·
            refine ⟨11794493386136572311628547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7862995590757714874419031 11794493386136572311628547)
            ·
              refine ⟨17691740079204858467442821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11794493386136572311628547 17691740079204858467442821)
              ·
                refine ⟨3317201264850910962645529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17691740079204858467442821 3317201264850910962645529)
                ·
                  refine ⟨2487900948638183221984147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3317201264850910962645529 2487900948638183221984147)
                  ·
                    refine ⟨3731851422957274832976221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2487900948638183221984147 3731851422957274832976221)
                    ·
                      refine ⟨1399444283608978062366083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731851422957274832976221 1399444283608978062366083)
                      ·
                        rfl

theorem cell23_2725408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2725408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725408 prefixEnd_2725408 := by exact prefixLift 2725408
  have htrace : WordTrace (prefixWord ++ tailWord_2725408) baseStart_2725408 baseEnd_2725408 := by
    simpa [prefixWord, tailWord_2725408, baseEnd_2725408] using wordTrace_append hprefix tailTrace_2725408
  have hstable : (prefixWord ++ tailWord_2725408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725408).length < 2 ^ (prefixWord ++ tailWord_2725408).sum := by decide
  have hdescent : baseEnd_2725408 < baseStart_2725408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725431 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 1, 4, 2]
def baseStart_2725431 : Nat := 118140960795 + 2725431 * 2 ^ 59
def prefixEnd_2725431 : Nat := 4983230072969 + 3 ^ 40 * 2725431 * 2
def baseEnd_2725431 : Nat := 1399456093664031472378477

theorem tailTrace_2725431 : CollatzResearch.WordTrace tailWord_2725431 prefixEnd_2725431 1399456093664031472378477 := by
  unfold tailWord_2725431
  simp only [CollatzResearch.WordTrace]
  refine ⟨99404634989236428402224147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66269756659490952268149431 99404634989236428402224147)
  ·
    refine ⟨149106952483854642603336221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99404634989236428402224147 149106952483854642603336221)
    ·
      refine ⟨55915107181445490976251083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149106952483854642603336221 55915107181445490976251083)
      ·
        refine ⟨83872660772168236464376625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55915107181445490976251083 83872660772168236464376625)
        ·
          refine ⟨62904495579126177348282469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83872660772168236464376625 62904495579126177348282469)
          ·
            refine ⟨11794592921086158252802963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62904495579126177348282469 11794592921086158252802963)
            ·
              refine ⟨17691889381629237379204445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11794592921086158252802963 17691889381629237379204445)
              ·
                refine ⟨6634458518110964017201667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17691889381629237379204445 6634458518110964017201667)
                ·
                  refine ⟨9951687777166446025802501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6634458518110964017201667 9951687777166446025802501)
                  ·
                    refine ⟨1865941458218708629837969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9951687777166446025802501 1865941458218708629837969)
                    ·
                      refine ⟨1399456093664031472378477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865941458218708629837969 1399456093664031472378477)
                      ·
                        rfl

theorem cell23_2725431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_2725431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725431 prefixEnd_2725431 := by exact prefixLift 2725431
  have htrace : WordTrace (prefixWord ++ tailWord_2725431) baseStart_2725431 baseEnd_2725431 := by
    simpa [prefixWord, tailWord_2725431, baseEnd_2725431] using wordTrace_append hprefix tailTrace_2725431
  have hstable : (prefixWord ++ tailWord_2725431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725431).length < 2 ^ (prefixWord ++ tailWord_2725431).sum := by decide
  have hdescent : baseEnd_2725431 < baseStart_2725431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725434 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_2725434 : Nat := 118140960795 + 2725434 * 2 ^ 59
def prefixEnd_2725434 : Nat := 4983230072969 + 3 ^ 40 * 2725434 * 2
def baseEnd_2725434 : Nat := 1399457634105994960640963

theorem tailTrace_2725434 : CollatzResearch.WordTrace tailWord_2725434 prefixEnd_2725434 1399457634105994960640963 := by
  unfold tailWord_2725434
  simp only [CollatzResearch.WordTrace]
  refine ⟨24851186102056389978645839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66269829605483706609722237 24851186102056389978645839)
  ·
    refine ⟨37276779153084584967968759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24851186102056389978645839 37276779153084584967968759)
    ·
      refine ⟨55915168729626877451953139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37276779153084584967968759 55915168729626877451953139)
      ·
        refine ⟨83872753094440316177929709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55915168729626877451953139 83872753094440316177929709)
        ·
          refine ⟨31452282410415118566723641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83872753094440316177929709 31452282410415118566723641)
          ·
            refine ⟨23589211807811338925042731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31452282410415118566723641 23589211807811338925042731)
            ·
              refine ⟨35383817711717008387564097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23589211807811338925042731 35383817711717008387564097)
              ·
                refine ⟨26537863283787756290673073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35383817711717008387564097 26537863283787756290673073)
                ·
                  refine ⟨19903397462840817218004805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26537863283787756290673073 19903397462840817218004805)
                  ·
                    refine ⟨3731887024282653228375901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19903397462840817218004805 3731887024282653228375901)
                    ·
                      refine ⟨1399457634105994960640963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3731887024282653228375901 1399457634105994960640963)
                      ·
                        rfl

theorem cell23_2725434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_2725434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725434 prefixEnd_2725434 := by exact prefixLift 2725434
  have htrace : WordTrace (prefixWord ++ tailWord_2725434) baseStart_2725434 baseEnd_2725434 := by
    simpa [prefixWord, tailWord_2725434, baseEnd_2725434] using wordTrace_append hprefix tailTrace_2725434
  have hstable : (prefixWord ++ tailWord_2725434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725434).length < 2 ^ (prefixWord ++ tailWord_2725434).sum := by decide
  have hdescent : baseEnd_2725434 < baseStart_2725434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725482 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_2725482 : Nat := 118140960795 + 2725482 * 2 ^ 59
def prefixEnd_2725482 : Nat := 4983230072969 + 3 ^ 40 * 2725482 * 2
def baseEnd_2725482 : Nat := 1399482281177410772840743

theorem tailTrace_2725482 : CollatzResearch.WordTrace tailWord_2725482 prefixEnd_2725482 1399482281177410772840743 := by
  unfold tailWord_2725482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24851623778012916028082675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66270996741367776074887133 24851623778012916028082675)
  ·
    refine ⟨37277435667019374042124013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24851623778012916028082675 37277435667019374042124013)
    ·
      refine ⟨13979038375132265265796505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37277435667019374042124013 13979038375132265265796505)
      ·
        refine ⟨10484278781349198949347379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13979038375132265265796505 10484278781349198949347379)
        ·
          refine ⟨15726418172023798424021069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10484278781349198949347379 15726418172023798424021069)
          ·
            refine ⟨5897406814508924409007901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15726418172023798424021069 5897406814508924409007901)
            ·
              refine ⟨2211527555440846653377963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5897406814508924409007901 2211527555440846653377963)
              ·
                refine ⟨3317291333161269980066945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211527555440846653377963 3317291333161269980066945)
                ·
                  refine ⟨2487968499870952485050209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3317291333161269980066945 2487968499870952485050209)
                  ·
                    refine ⟨1865976374903214363787657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2487968499870952485050209 1865976374903214363787657)
                    ·
                      refine ⟨1399482281177410772840743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1865976374903214363787657 1399482281177410772840743)
                      ·
                        rfl

theorem cell23_2725482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_2725482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725482 prefixEnd_2725482 := by exact prefixLift 2725482
  have htrace : WordTrace (prefixWord ++ tailWord_2725482) baseStart_2725482 baseEnd_2725482 := by
    simpa [prefixWord, tailWord_2725482, baseEnd_2725482] using wordTrace_append hprefix tailTrace_2725482
  have hstable : (prefixWord ++ tailWord_2725482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725482).length < 2 ^ (prefixWord ++ tailWord_2725482).sum := by decide
  have hdescent : baseEnd_2725482 < baseStart_2725482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725504 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4]
def baseStart_2725504 : Nat := 118140960795 + 2725504 * 2 ^ 59
def prefixEnd_2725504 : Nat := 4983230072969 + 3 ^ 40 * 2725504 * 2
def baseEnd_2725504 : Nat := 1399493577751809686765641

theorem tailTrace_2725504 : CollatzResearch.WordTrace tailWord_2725504 prefixEnd_2725504 1399493577751809686765641 := by
  unfold tailWord_2725504
  simp only [CollatzResearch.WordTrace]
  refine ⟨49703648758985980934815783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66271531678647974579754377 49703648758985980934815783)
  ·
    refine ⟨74555473138478971402223675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49703648758985980934815783 74555473138478971402223675)
    ·
      refine ⟨111833209707718457103335513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74555473138478971402223675 111833209707718457103335513)
      ·
        refine ⟨83874907280788842827501635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111833209707718457103335513 83874907280788842827501635)
        ·
          refine ⟨125812360921183264241252453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83874907280788842827501635 125812360921183264241252453)
          ·
            refine ⟨23589817672721862045234835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125812360921183264241252453 23589817672721862045234835)
            ·
              refine ⟨35384726509082793067852253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23589817672721862045234835 35384726509082793067852253)
              ·
                refine ⟨13269272440906047400444595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35384726509082793067852253 13269272440906047400444595)
                ·
                  refine ⟨19903908661359071100666893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13269272440906047400444595 19903908661359071100666893)
                  ·
                    refine ⟨7463965748009651662750085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19903908661359071100666893 7463965748009651662750085)
                    ·
                      refine ⟨1399493577751809686765641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7463965748009651662750085 1399493577751809686765641)
                      ·
                        rfl

theorem cell23_2725504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_2725504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725504 prefixEnd_2725504 := by exact prefixLift 2725504
  have htrace : WordTrace (prefixWord ++ tailWord_2725504) baseStart_2725504 baseEnd_2725504 := by
    simpa [prefixWord, tailWord_2725504, baseEnd_2725504] using wordTrace_append hprefix tailTrace_2725504
  have hstable : (prefixWord ++ tailWord_2725504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725504).length < 2 ^ (prefixWord ++ tailWord_2725504).sum := by decide
  have hdescent : baseEnd_2725504 < baseStart_2725504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725521 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 2, 4, 2]
def baseStart_2725521 : Nat := 118140960795 + 2725521 * 2 ^ 59
def prefixEnd_2725521 : Nat := 4983230072969 + 3 ^ 40 * 2725521 * 2
def baseEnd_2725521 : Nat := 1399502306922936120253063

theorem tailTrace_2725521 : CollatzResearch.WordTrace tailWord_2725521 prefixEnd_2725521 1399502306922936120253063 := by
  unfold tailWord_2725521
  simp only [CollatzResearch.WordTrace]
  refine ⟨99407917558910373773000417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66271945039273582515333611 99407917558910373773000417)
  ·
    refine ⟨74555938169182780329750313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99407917558910373773000417 74555938169182780329750313)
    ·
      refine ⟨55916953626887085247312735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74555938169182780329750313 55916953626887085247312735)
      ·
        refine ⟨83875430440330627870969103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55916953626887085247312735 83875430440330627870969103)
        ·
          refine ⟨125813145660495941806453655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83875430440330627870969103 125813145660495941806453655)
          ·
            refine ⟨188719718490743912709680483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125813145660495941806453655 188719718490743912709680483)
            ·
              refine ⟨283079577736115869064520725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188719718490743912709680483 283079577736115869064520725)
              ·
                refine ⟨13269355206380431362399409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283079577736115869064520725 13269355206380431362399409)
                ·
                  refine ⟨9952016404785323521799557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13269355206380431362399409 9952016404785323521799557)
                  ·
                    refine ⟨1866003075897248160337417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9952016404785323521799557 1866003075897248160337417)
                    ·
                      refine ⟨1399502306922936120253063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866003075897248160337417 1399502306922936120253063)
                      ·
                        rfl

theorem cell23_2725521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_2725521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725521 prefixEnd_2725521 := by exact prefixLift 2725521
  have htrace : WordTrace (prefixWord ++ tailWord_2725521) baseStart_2725521 baseEnd_2725521 := by
    simpa [prefixWord, tailWord_2725521, baseEnd_2725521] using wordTrace_append hprefix tailTrace_2725521
  have hstable : (prefixWord ++ tailWord_2725521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725521).length < 2 ^ (prefixWord ++ tailWord_2725521).sum := by decide
  have hdescent : baseEnd_2725521 < baseStart_2725521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725578 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_2725578 : Nat := 118140960795 + 2725578 * 2 ^ 59
def prefixEnd_2725578 : Nat := 4983230072969 + 3 ^ 40 * 2725578 * 2
def baseEnd_2725578 : Nat := 155503508368915821915589

theorem tailTrace_2725578 : CollatzResearch.WordTrace tailWord_2725578 prefixEnd_2725578 155503508368915821915589 := by
  unfold tailWord_2725578
  simp only [CollatzResearch.WordTrace]
  refine ⟨24852499129925968126956347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66273331013135915005216925 24852499129925968126956347)
  ·
    refine ⟨37278748694888952190434521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24852499129925968126956347 37278748694888952190434521)
    ·
      refine ⟨27959061521166714142825891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37278748694888952190434521 27959061521166714142825891)
      ·
        refine ⟨41938592281750071214238837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27959061521166714142825891 41938592281750071214238837)
        ·
          refine ⟨3931743026414069176334891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41938592281750071214238837 3931743026414069176334891)
          ·
            refine ⟨5897614539621103764502337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3931743026414069176334891 5897614539621103764502337)
            ·
              refine ⟨4423210904715827823376753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5897614539621103764502337 4423210904715827823376753)
              ·
                refine ⟨3317408178536870867532565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4423210904715827823376753 3317408178536870867532565)
                ·
                  refine ⟨155503508368915821915589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3317408178536870867532565 155503508368915821915589)
                  ·
                    rfl

theorem cell23_2725578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_2725578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725578 prefixEnd_2725578 := by exact prefixLift 2725578
  have htrace : WordTrace (prefixWord ++ tailWord_2725578) baseStart_2725578 baseEnd_2725578 := by
    simpa [prefixWord, tailWord_2725578, baseEnd_2725578] using wordTrace_append hprefix tailTrace_2725578
  have hstable : (prefixWord ++ tailWord_2725578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725578).length < 2 ^ (prefixWord ++ tailWord_2725578).sum := by decide
  have hdescent : baseEnd_2725578 < baseStart_2725578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725611 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 4]
def baseStart_2725611 : Nat := 118140960795 + 2725611 * 2 ^ 59
def prefixEnd_2725611 : Nat := 4983230072969 + 3 ^ 40 * 2725611 * 2
def baseEnd_2725611 : Nat := 1399548520181840768127649

theorem tailTrace_2725611 : CollatzResearch.WordTrace tailWord_2725611 prefixEnd_2725611 1399548520181840768127649 := by
  unfold tailWord_2725611
  simp only [CollatzResearch.WordTrace]
  refine ⟨99411200128584319143776687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66274133419056212762517791 99411200128584319143776687)
  ·
    refine ⟨149116800192876478715665031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99411200128584319143776687 149116800192876478715665031)
    ·
      refine ⟨223675200289314718073497547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149116800192876478715665031 223675200289314718073497547)
      ·
        refine ⟨335512800433972077110246321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223675200289314718073497547 335512800433972077110246321)
        ·
          refine ⟨251634600325479057832684741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335512800433972077110246321 251634600325479057832684741)
          ·
            refine ⟨47181487561027323343628389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 251634600325479057832684741 47181487561027323343628389)
            ·
              refine ⟨8846528917692623126930323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47181487561027323343628389 8846528917692623126930323)
              ·
                refine ⟨13269793376538934690395485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8846528917692623126930323 13269793376538934690395485)
                ·
                  refine ⟨4976172516202100508898307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13269793376538934690395485 4976172516202100508898307)
                  ·
                    refine ⟨7464258774303150763347461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976172516202100508898307 7464258774303150763347461)
                    ·
                      refine ⟨1399548520181840768127649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7464258774303150763347461 1399548520181840768127649)
                      ·
                        rfl

theorem cell23_2725611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 4].length) (baseStart_2725611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725611 prefixEnd_2725611 := by exact prefixLift 2725611
  have htrace : WordTrace (prefixWord ++ tailWord_2725611) baseStart_2725611 baseEnd_2725611 := by
    simpa [prefixWord, tailWord_2725611, baseEnd_2725611] using wordTrace_append hprefix tailTrace_2725611
  have hstable : (prefixWord ++ tailWord_2725611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725611).length < 2 ^ (prefixWord ++ tailWord_2725611).sum := by decide
  have hdescent : baseEnd_2725611 < baseStart_2725611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725622 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_2725622 : Nat := 118140960795 + 2725622 * 2 ^ 59
def prefixEnd_2725622 : Nat := 4983230072969 + 3 ^ 40 * 2725622 * 2
def baseEnd_2725622 : Nat := 1399554168469040225090099

theorem tailTrace_2725622 : CollatzResearch.WordTrace tailWord_2725622 prefixEnd_2725622 1399554168469040225090099 := by
  unfold tailWord_2725622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213225083221529251401695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66274400887696312014951413 6213225083221529251401695)
  ·
    refine ⟨9319837624832293877102543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213225083221529251401695 9319837624832293877102543)
    ·
      refine ⟨13979756437248440815653815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9319837624832293877102543 13979756437248440815653815)
      ·
        refine ⟨20969634655872661223480723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13979756437248440815653815 20969634655872661223480723)
        ·
          refine ⟨31454451983808991835221085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20969634655872661223480723 31454451983808991835221085)
          ·
            refine ⟨11795419493928371938207907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31454451983808991835221085 11795419493928371938207907)
            ·
              refine ⟨17693129240892557907311861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11795419493928371938207907 17693129240892557907311861)
              ·
                refine ⟨1658730866333677303810487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17693129240892557907311861 1658730866333677303810487)
                ·
                  refine ⟨2488096299500515955715731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658730866333677303810487 2488096299500515955715731)
                  ·
                    refine ⟨3732144449250773933573597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2488096299500515955715731 3732144449250773933573597)
                    ·
                      refine ⟨1399554168469040225090099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3732144449250773933573597 1399554168469040225090099)
                      ·
                        rfl

theorem cell23_2725622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_2725622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725622 prefixEnd_2725622 := by exact prefixLift 2725622
  have htrace : WordTrace (prefixWord ++ tailWord_2725622) baseStart_2725622 baseEnd_2725622 := by
    simpa [prefixWord, tailWord_2725622, baseEnd_2725622] using wordTrace_append hprefix tailTrace_2725622
  have hstable : (prefixWord ++ tailWord_2725622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725622).length < 2 ^ (prefixWord ++ tailWord_2725622).sum := by decide
  have hdescent : baseEnd_2725622 < baseStart_2725622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725628 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_2725628 : Nat := 118140960795 + 2725628 * 2 ^ 59
def prefixEnd_2725628 : Nat := 4983230072969 + 3 ^ 40 * 2725628 * 2
def baseEnd_2725628 : Nat := 1399557249352967201615071

theorem tailTrace_2725628 : CollatzResearch.WordTrace tailWord_2725628 prefixEnd_2725628 1399557249352967201615071 := by
  unfold tailWord_2725628
  simp only [CollatzResearch.WordTrace]
  refine ⟨49705910084761365523572769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66274546779681820698097025 49705910084761365523572769)
  ·
    refine ⟨37279432563571024142679577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49705910084761365523572769 37279432563571024142679577)
    ·
      refine ⟨27959574422678268107009683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37279432563571024142679577 27959574422678268107009683)
      ·
        refine ⟨41939361634017402160514525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27959574422678268107009683 41939361634017402160514525)
        ·
          refine ⟨15727260612756525810192947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41939361634017402160514525 15727260612756525810192947)
          ·
            refine ⟨23590890919134788715289421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15727260612756525810192947 23590890919134788715289421)
            ·
              refine ⟨8846584094675545768233533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23590890919134788715289421 8846584094675545768233533)
              ·
                refine ⟨3317469035503329663087575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8846584094675545768233533 3317469035503329663087575)
                ·
                  refine ⟨4976203553254994494631363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317469035503329663087575 4976203553254994494631363)
                  ·
                    refine ⟨7464305329882491741947045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4976203553254994494631363 7464305329882491741947045)
                    ·
                      refine ⟨1399557249352967201615071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7464305329882491741947045 1399557249352967201615071)
                      ·
                        rfl

theorem cell23_2725628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_2725628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725628 prefixEnd_2725628 := by exact prefixLift 2725628
  have htrace : WordTrace (prefixWord ++ tailWord_2725628) baseStart_2725628 baseEnd_2725628 := by
    simpa [prefixWord, tailWord_2725628, baseEnd_2725628] using wordTrace_append hprefix tailTrace_2725628
  have hstable : (prefixWord ++ tailWord_2725628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725628).length < 2 ^ (prefixWord ++ tailWord_2725628).sum := by decide
  have hdescent : baseEnd_2725628 < baseStart_2725628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725658 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_2725658 : Nat := 118140960795 + 2725658 * 2 ^ 59
def prefixEnd_2725658 : Nat := 4983230072969 + 3 ^ 40 * 2725658 * 2
def baseEnd_2725658 : Nat := 1399572653772602084239933

theorem tailTrace_2725658 : CollatzResearch.WordTrace tailWord_2725658 prefixEnd_2725658 1399572653772602084239933 := by
  unfold tailWord_2725658
  simp only [CollatzResearch.WordTrace]
  refine ⟨24853228589853511542684407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66275276239609364113825085 24853228589853511542684407)
  ·
    refine ⟨37279842884780267314026611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24853228589853511542684407 37279842884780267314026611)
    ·
      refine ⟨55919764327170400971039917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37279842884780267314026611 55919764327170400971039917)
      ·
        refine ⟨20969911622688900364139969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55919764327170400971039917 20969911622688900364139969)
        ·
          refine ⟨15727433717016675273104977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20969911622688900364139969 15727433717016675273104977)
          ·
            refine ⟨11795575287762506454828733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15727433717016675273104977 11795575287762506454828733)
            ·
              refine ⟨4423340732910939920560775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11795575287762506454828733 4423340732910939920560775)
              ·
                refine ⟨6635011099366409880841163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423340732910939920560775 6635011099366409880841163)
                ·
                  refine ⟨9952516649049614821261745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6635011099366409880841163 9952516649049614821261745)
                  ·
                    refine ⟨7464387486787211115946309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9952516649049614821261745 7464387486787211115946309)
                    ·
                      refine ⟨1399572653772602084239933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7464387486787211115946309 1399572653772602084239933)
                      ·
                        rfl

theorem cell23_2725658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_2725658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725658 prefixEnd_2725658 := by exact prefixLift 2725658
  have htrace : WordTrace (prefixWord ++ tailWord_2725658) baseStart_2725658 baseEnd_2725658 := by
    simpa [prefixWord, tailWord_2725658, baseEnd_2725658] using wordTrace_append hprefix tailTrace_2725658
  have hstable : (prefixWord ++ tailWord_2725658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725658).length < 2 ^ (prefixWord ++ tailWord_2725658).sum := by decide
  have hdescent : baseEnd_2725658 < baseStart_2725658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725665 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2725665 : Nat := 118140960795 + 2725665 * 2 ^ 59
def prefixEnd_2725665 : Nat := 4983230072969 + 3 ^ 40 * 2725665 * 2
def baseEnd_2725665 : Nat := 1399576248137183556852401

theorem tailTrace_2725665 : CollatzResearch.WordTrace tailWord_2725665 prefixEnd_2725665 1399576248137183556852401 := by
  unfold tailWord_2725665
  simp only [CollatzResearch.WordTrace]
  refine ⟨99413169670388686366242449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66275446446925790910828299 99413169670388686366242449)
  ·
    refine ⟨74559877252791514774681837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99413169670388686366242449 74559877252791514774681837)
    ·
      refine ⟨27959953969796818040505689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74559877252791514774681837 27959953969796818040505689)
      ·
        refine ⟨20969965477347613530379267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27959953969796818040505689 20969965477347613530379267)
        ·
          refine ⟨31454948216021420295568901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20969965477347613530379267 31454948216021420295568901)
          ·
            refine ⟨5897802790504016305419169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31454948216021420295568901 5897802790504016305419169)
            ·
              refine ⟨4423352092878012229064377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5897802790504016305419169 4423352092878012229064377)
              ·
                refine ⟨3317514069658509171798283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4423352092878012229064377 3317514069658509171798283)
                ·
                  refine ⟨4976271104487763757697425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317514069658509171798283 4976271104487763757697425)
                  ·
                    refine ⟨3732203328365822818273069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4976271104487763757697425 3732203328365822818273069)
                    ·
                      refine ⟨1399576248137183556852401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3732203328365822818273069 1399576248137183556852401)
                      ·
                        rfl

theorem cell23_2725665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2725665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725665 prefixEnd_2725665 := by exact prefixLift 2725665
  have htrace : WordTrace (prefixWord ++ tailWord_2725665) baseStart_2725665 baseEnd_2725665 := by
    simpa [prefixWord, tailWord_2725665, baseEnd_2725665] using wordTrace_append hprefix tailTrace_2725665
  have hstable : (prefixWord ++ tailWord_2725665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725665).length < 2 ^ (prefixWord ++ tailWord_2725665).sum := by decide
  have hdescent : baseEnd_2725665 < baseStart_2725665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725668 : List Nat := [2, 3, 1, 3, 2, 1, 4, 7]
def baseStart_2725668 : Nat := 118140960795 + 2725668 * 2 ^ 59
def prefixEnd_2725668 : Nat := 4983230072969 + 3 ^ 40 * 2725668 * 2
def baseEnd_2725668 : Nat := 51836214391820260930181

theorem tailTrace_2725668 : CollatzResearch.WordTrace tailWord_2725668 prefixEnd_2725668 51836214391820260930181 := by
  unfold tailWord_2725668
  simp only [CollatzResearch.WordTrace]
  refine ⟨49706639544688908939300829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66275519392918545252401105 49706639544688908939300829)
  ·
    refine ⟨18639989829258340852237811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49706639544688908939300829 18639989829258340852237811)
    ·
      refine ⟨27959984743887511278356717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18639989829258340852237811 27959984743887511278356717)
      ·
        refine ⟨10484994278957816729383769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27959984743887511278356717 10484994278957816729383769)
        ·
          refine ⟨7863745709218362547037827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10484994278957816729383769 7863745709218362547037827)
          ·
            refine ⟨11795618563827543820556741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7863745709218362547037827 11795618563827543820556741)
            ·
              refine ⟨2211678480717664466354389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11795618563827543820556741 2211678480717664466354389)
              ·
                refine ⟨51836214391820260930181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2211678480717664466354389 51836214391820260930181)
                ·
                  rfl

theorem cell23_2725668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 7].length) (baseStart_2725668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725668 prefixEnd_2725668 := by exact prefixLift 2725668
  have htrace : WordTrace (prefixWord ++ tailWord_2725668) baseStart_2725668 baseEnd_2725668 := by
    simpa [prefixWord, tailWord_2725668, baseEnd_2725668] using wordTrace_append hprefix tailTrace_2725668
  have hstable : (prefixWord ++ tailWord_2725668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725668).length < 2 ^ (prefixWord ++ tailWord_2725668).sum := by decide
  have hdescent : baseEnd_2725668 < baseStart_2725668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725701 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_2725701 : Nat := 118140960795 + 2725701 * 2 ^ 59
def prefixEnd_2725701 : Nat := 4983230072969 + 3 ^ 40 * 2725701 * 2
def baseEnd_2725701 : Nat := 1399594733440745416002235

theorem tailTrace_2725701 : CollatzResearch.WordTrace tailWord_2725701 prefixEnd_2725701 1399594733440745416002235 := by
  unfold tailWord_2725701
  simp only [CollatzResearch.WordTrace]
  refine ⟨99414482698258264514552957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66276321798838843009701971 99414482698258264514552957)
  ·
    refine ⟨37280431011846849192957359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99414482698258264514552957 37280431011846849192957359)
    ·
      refine ⟨55920646517770273789436039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37280431011846849192957359 55920646517770273789436039)
      ·
        refine ⟨83880969776655410684154059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55920646517770273789436039 83880969776655410684154059)
        ·
          refine ⟨125821454664983116026231089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83880969776655410684154059 125821454664983116026231089)
          ·
            refine ⟨94366090998737337019673317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125821454664983116026231089 94366090998737337019673317)
            ·
              refine ⟨17693642062263250691188747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94366090998737337019673317 17693642062263250691188747)
              ·
                refine ⟨26540463093394876036783121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17693642062263250691188747 26540463093394876036783121)
                ·
                  refine ⟨19905347320046157027587341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26540463093394876036783121 19905347320046157027587341)
                  ·
                    refine ⟨7464505245017308885345253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19905347320046157027587341 7464505245017308885345253)
                    ·
                      refine ⟨1399594733440745416002235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7464505245017308885345253 1399594733440745416002235)
                      ·
                        rfl

theorem cell23_2725701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_2725701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725701 prefixEnd_2725701 := by exact prefixLift 2725701
  have htrace : WordTrace (prefixWord ++ tailWord_2725701) baseStart_2725701 baseEnd_2725701 := by
    simpa [prefixWord, tailWord_2725701, baseEnd_2725701] using wordTrace_append hprefix tailTrace_2725701
  have hstable : (prefixWord ++ tailWord_2725701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725701).length < 2 ^ (prefixWord ++ tailWord_2725701).sum := by decide
  have hdescent : baseEnd_2725701 < baseStart_2725701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725721 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2725721 : Nat := 118140960795 + 2725721 * 2 ^ 59
def prefixEnd_2725721 : Nat := 4983230072969 + 3 ^ 40 * 2725721 * 2
def baseEnd_2725721 : Nat := 1399605003053835337752143

theorem tailTrace_2725721 : CollatzResearch.WordTrace tailWord_2725721 prefixEnd_2725721 1399605003053835337752143 := by
  unfold tailWord_2725721
  simp only [CollatzResearch.WordTrace]
  refine ⟨99415212158185807930281017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66276808105457205286854011 99415212158185807930281017)
  ·
    refine ⟨74561409118639355947710763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99415212158185807930281017 74561409118639355947710763)
    ·
      refine ⟨111842113677959033921566145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74561409118639355947710763 111842113677959033921566145)
      ·
        refine ⟨83881585258469275441174609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111842113677959033921566145 83881585258469275441174609)
        ·
          refine ⟨62911188943851956580880957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83881585258469275441174609 62911188943851956580880957)
          ·
            refine ⟨23591695853944483717830359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62911188943851956580880957 23591695853944483717830359)
            ·
              refine ⟨35387543780916725576745539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23591695853944483717830359 35387543780916725576745539)
              ·
                refine ⟨53081315671375088365118309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35387543780916725576745539 53081315671375088365118309)
                ·
                  refine ⟨9952746688382829068459683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53081315671375088365118309 9952746688382829068459683)
                  ·
                    refine ⟨14929120032574243602689525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9952746688382829068459683 14929120032574243602689525)
                    ·
                      refine ⟨1399605003053835337752143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14929120032574243602689525 1399605003053835337752143)
                      ·
                        rfl

theorem cell23_2725721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2725721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725721 prefixEnd_2725721 := by exact prefixLift 2725721
  have htrace : WordTrace (prefixWord ++ tailWord_2725721) baseStart_2725721 baseEnd_2725721 := by
    simpa [prefixWord, tailWord_2725721, baseEnd_2725721] using wordTrace_append hprefix tailTrace_2725721
  have hstable : (prefixWord ++ tailWord_2725721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725721).length < 2 ^ (prefixWord ++ tailWord_2725721).sum := by decide
  have hdescent : baseEnd_2725721 < baseStart_2725721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725735 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_2725735 : Nat := 118140960795 + 2725735 * 2 ^ 59
def prefixEnd_2725735 : Nat := 4983230072969 + 3 ^ 40 * 2725735 * 2
def baseEnd_2725735 : Nat := 1399612191782998282977079

theorem tailTrace_2725735 : CollatzResearch.WordTrace tailWord_2725735 prefixEnd_2725735 1399612191782998282977079 := by
  unfold tailWord_2725735
  simp only [CollatzResearch.WordTrace]
  refine ⟨99415722780135088321290659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66277148520090058880860439 99415722780135088321290659)
  ·
    refine ⟨149123584170202632481935989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99415722780135088321290659 149123584170202632481935989)
    ·
      refine ⟨13980336015956496795181499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149123584170202632481935989 13980336015956496795181499)
      ·
        refine ⟨20970504023934745192772249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13980336015956496795181499 20970504023934745192772249)
        ·
          refine ⟨15727878017951058894579187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20970504023934745192772249 15727878017951058894579187)
          ·
            refine ⟨23591817026926588341868781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15727878017951058894579187 23591817026926588341868781)
            ·
              refine ⟨8846931385097470628200793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23591817026926588341868781 8846931385097470628200793)
              ·
                refine ⟨6635198538823102971150595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8846931385097470628200793 6635198538823102971150595)
                ·
                  refine ⟨9952797808234654456725893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6635198538823102971150595 9952797808234654456725893)
                  ·
                    refine ⟨1866149589043997710636105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9952797808234654456725893 1866149589043997710636105)
                    ·
                      refine ⟨1399612191782998282977079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866149589043997710636105 1399612191782998282977079)
                      ·
                        rfl

theorem cell23_2725735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_2725735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725735 prefixEnd_2725735 := by exact prefixLift 2725735
  have htrace : WordTrace (prefixWord ++ tailWord_2725735) baseStart_2725735 baseEnd_2725735 := by
    simpa [prefixWord, tailWord_2725735, baseEnd_2725735] using wordTrace_append hprefix tailTrace_2725735
  have hstable : (prefixWord ++ tailWord_2725735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725735).length < 2 ^ (prefixWord ++ tailWord_2725735).sum := by decide
  have hdescent : baseEnd_2725735 < baseStart_2725735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725771 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 1, 7]
def baseStart_2725771 : Nat := 118140960795 + 2725771 * 2 ^ 59
def prefixEnd_2725771 : Nat := 4983230072969 + 3 ^ 40 * 2725771 * 2
def baseEnd_2725771 : Nat := 466543559028853380708971

theorem tailTrace_2725771 : CollatzResearch.WordTrace tailWord_2725771 prefixEnd_2725771 466543559028853380708971 := by
  unfold tailWord_2725771
  simp only [CollatzResearch.WordTrace]
  refine ⟨99417035808004666469601167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66278023872003110979734111 99417035808004666469601167)
  ·
    refine ⟨149125553712006999704401751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99417035808004666469601167 149125553712006999704401751)
    ·
      refine ⟨223688330568010499556602627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149125553712006999704401751 223688330568010499556602627)
      ·
        refine ⟨335532495852015749334903941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223688330568010499556602627 335532495852015749334903941)
        ·
          refine ⟨62912342972252953000294489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335532495852015749334903941 62912342972252953000294489)
          ·
            refine ⟨47184257229189714750220867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62912342972252953000294489 47184257229189714750220867)
            ·
              refine ⟨70776385843784572125331301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47184257229189714750220867 70776385843784572125331301)
              ·
                refine ⟨13270572345709607273499619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70776385843784572125331301 13270572345709607273499619)
                ·
                  refine ⟨19905858518564410910249429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13270572345709607273499619 19905858518564410910249429)
                  ·
                    refine ⟨466543559028853380708971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19905858518564410910249429 466543559028853380708971)
                    ·
                      rfl

theorem cell23_2725771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_2725771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725771 prefixEnd_2725771 := by exact prefixLift 2725771
  have htrace : WordTrace (prefixWord ++ tailWord_2725771) baseStart_2725771 baseEnd_2725771 := by
    simpa [prefixWord, tailWord_2725771, baseEnd_2725771] using wordTrace_append hprefix tailTrace_2725771
  have hstable : (prefixWord ++ tailWord_2725771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725771).length < 2 ^ (prefixWord ++ tailWord_2725771).sum := by decide
  have hdescent : baseEnd_2725771 < baseStart_2725771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725790 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2725790 : Nat := 118140960795 + 2725790 * 2 ^ 59
def prefixEnd_2725790 : Nat := 4983230072969 + 3 ^ 40 * 2725790 * 2
def baseEnd_2725790 : Nat := 1399640433218995567789327

theorem tailTrace_2725790 : CollatzResearch.WordTrace tailWord_2725790 prefixEnd_2725790 1399640433218995567789327 := by
  unfold tailWord_2725790
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427216099366979089317853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66278485863290555143028549 12427216099366979089317853)
  ·
    refine ⟨4660206037262617158494195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12427216099366979089317853 4660206037262617158494195)
    ·
      refine ⟨6990309055893925737741293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4660206037262617158494195 6990309055893925737741293)
      ·
        refine ⟨2621365895960222151652985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6990309055893925737741293 2621365895960222151652985)
        ·
          refine ⟨1966024421970166613739739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2621365895960222151652985 1966024421970166613739739)
          ·
            refine ⟨2949036632955249920609609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966024421970166613739739 2949036632955249920609609)
            ·
              refine ⟨2211777474716437440457207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2949036632955249920609609 2211777474716437440457207)
              ·
                refine ⟨3317666212074656160685811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211777474716437440457207 3317666212074656160685811)
                ·
                  refine ⟨4976499318111984241028717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317666212074656160685811 4976499318111984241028717)
                  ·
                    refine ⟨1866187244291994090385769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4976499318111984241028717 1866187244291994090385769)
                    ·
                      refine ⟨1399640433218995567789327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866187244291994090385769 1399640433218995567789327)
                      ·
                        rfl

theorem cell23_2725790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2725790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725790 prefixEnd_2725790 := by exact prefixLift 2725790
  have htrace : WordTrace (prefixWord ++ tailWord_2725790) baseStart_2725790 baseEnd_2725790 := by
    simpa [prefixWord, tailWord_2725790, baseEnd_2725790] using wordTrace_append hprefix tailTrace_2725790
  have hstable : (prefixWord ++ tailWord_2725790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725790).length < 2 ^ (prefixWord ++ tailWord_2725790).sum := by decide
  have hdescent : baseEnd_2725790 < baseStart_2725790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725838 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2725838 : Nat := 118140960795 + 2725838 * 2 ^ 59
def prefixEnd_2725838 : Nat := 4983230072969 + 3 ^ 40 * 2725838 * 2
def baseEnd_2725838 : Nat := 1399665080290411379989105

theorem tailTrace_2725838 : CollatzResearch.WordTrace tailWord_2725838 prefixEnd_2725838 1399665080290411379989105 := by
  unfold tailWord_2725838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12427434937345242114036271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66279652999174624608193445 12427434937345242114036271)
  ·
    refine ⟨18641152406017863171054407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12427434937345242114036271 18641152406017863171054407)
    ·
      refine ⟨27961728609026794756581611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18641152406017863171054407 27961728609026794756581611)
      ·
        refine ⟨41942592913540192134872417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27961728609026794756581611 41942592913540192134872417)
        ·
          refine ⟨31456944685155144101154313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41942592913540192134872417 31456944685155144101154313)
          ·
            refine ⟨23592708513866358075865735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31456944685155144101154313 23592708513866358075865735)
            ·
              refine ⟨35389062770799537113798603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23592708513866358075865735 35389062770799537113798603)
              ·
                refine ⟨53083594156199305670697905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35389062770799537113798603 53083594156199305670697905)
                ·
                  refine ⟨39812695617149479253023429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53083594156199305670697905 39812695617149479253023429)
                  ·
                    refine ⟨7464880428215527359941893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39812695617149479253023429 7464880428215527359941893)
                    ·
                      refine ⟨1399665080290411379989105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7464880428215527359941893 1399665080290411379989105)
                      ·
                        rfl

theorem cell23_2725838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2725838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725838 prefixEnd_2725838 := by exact prefixLift 2725838
  have htrace : WordTrace (prefixWord ++ tailWord_2725838) baseStart_2725838 baseEnd_2725838 := by
    simpa [prefixWord, tailWord_2725838, baseEnd_2725838] using wordTrace_append hprefix tailTrace_2725838
  have hstable : (prefixWord ++ tailWord_2725838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725838).length < 2 ^ (prefixWord ++ tailWord_2725838).sum := by decide
  have hdescent : baseEnd_2725838 < baseStart_2725838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725845 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2725845 : Nat := 118140960795 + 2725845 * 2 ^ 59
def prefixEnd_2725845 : Nat := 4983230072969 + 3 ^ 40 * 2725845 * 2
def baseEnd_2725845 : Nat := 1399668674654992852601573

theorem tailTrace_2725845 : CollatzResearch.WordTrace tailWord_2725845 prefixEnd_2725845 1399668674654992852601573 := by
  unfold tailWord_2725845
  simp only [CollatzResearch.WordTrace]
  refine ⟨99419734809736577107794989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66279823206491051405196659 99419734809736577107794989)
  ·
    refine ⟨37282400553651216415423121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99419734809736577107794989 37282400553651216415423121)
    ·
      refine ⟨27961800415238412311567341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37282400553651216415423121 27961800415238412311567341)
      ·
        refine ⟨10485675155714404616837753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27961800415238412311567341 10485675155714404616837753)
        ·
          refine ⟨7864256366785803462628315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10485675155714404616837753 7864256366785803462628315)
          ·
            refine ⟨11796384550178705193942473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864256366785803462628315 11796384550178705193942473)
            ·
              refine ⟨8847288412634028895456855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11796384550178705193942473 8847288412634028895456855)
              ·
                refine ⟨13270932618951043343185283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8847288412634028895456855 13270932618951043343185283)
                ·
                  refine ⟨19906398928426565014777925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13270932618951043343185283 19906398928426565014777925)
                  ·
                    refine ⟨3732449799079980940270861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19906398928426565014777925 3732449799079980940270861)
                    ·
                      refine ⟨1399668674654992852601573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3732449799079980940270861 1399668674654992852601573)
                      ·
                        rfl

theorem cell23_2725845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2725845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725845 prefixEnd_2725845 := by exact prefixLift 2725845
  have htrace : WordTrace (prefixWord ++ tailWord_2725845) baseStart_2725845 baseEnd_2725845 := by
    simpa [prefixWord, tailWord_2725845, baseEnd_2725845] using wordTrace_append hprefix tailTrace_2725845
  have hstable : (prefixWord ++ tailWord_2725845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725845).length < 2 ^ (prefixWord ++ tailWord_2725845).sum := by decide
  have hdescent : baseEnd_2725845 < baseStart_2725845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725885 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 3, 5, 2]
def baseStart_2725885 : Nat := 118140960795 + 2725885 * 2 ^ 59
def prefixEnd_2725885 : Nat := 4983230072969 + 3 ^ 40 * 2725885 * 2
def baseEnd_2725885 : Nat := 1399689213881172696101389

theorem tailTrace_2725885 : CollatzResearch.WordTrace tailWord_2725885 prefixEnd_2725885 1399689213881172696101389 := by
  unfold tailWord_2725885
  simp only [CollatzResearch.WordTrace]
  refine ⟨99421193729591663939251109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66280795819727775959500739 99421193729591663939251109)
  ·
    refine ⟨18641473824298436988609583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99421193729591663939251109 18641473824298436988609583)
    ·
      refine ⟨27962210736447655482914375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18641473824298436988609583 27962210736447655482914375)
      ·
        refine ⟨41943316104671483224371563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27962210736447655482914375 41943316104671483224371563)
        ·
          refine ⟨62914974157007224836557345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41943316104671483224371563 62914974157007224836557345)
          ·
            refine ⟨47186230617755418627418009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62914974157007224836557345 47186230617755418627418009)
            ·
              refine ⟨35389672963316563970563507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47186230617755418627418009 35389672963316563970563507)
              ·
                refine ⟨53084509444974845955845261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35389672963316563970563507 53084509444974845955845261)
                ·
                  refine ⟨19906691041865567233441973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53084509444974845955845261 19906691041865567233441973)
                  ·
                    refine ⟨1866252285174896928135185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19906691041865567233441973 1866252285174896928135185)
                    ·
                      refine ⟨1399689213881172696101389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866252285174896928135185 1399689213881172696101389)
                      ·
                        rfl

theorem cell23_2725885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_2725885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725885 prefixEnd_2725885 := by exact prefixLift 2725885
  have htrace : WordTrace (prefixWord ++ tailWord_2725885) baseStart_2725885 baseEnd_2725885 := by
    simpa [prefixWord, tailWord_2725885, baseEnd_2725885] using wordTrace_append hprefix tailTrace_2725885
  have hstable : (prefixWord ++ tailWord_2725885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725885).length < 2 ^ (prefixWord ++ tailWord_2725885).sum := by decide
  have hdescent : baseEnd_2725885 < baseStart_2725885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725895 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 3, 5]
def baseStart_2725895 : Nat := 118140960795 + 2725895 * 2 ^ 59
def prefixEnd_2725895 : Nat := 4983230072969 + 3 ^ 40 * 2725895 * 2
def baseEnd_2725895 : Nat := 466564782895905885658781

theorem tailTrace_2725895 : CollatzResearch.WordTrace tailWord_2725895 prefixEnd_2725895 466564782895905885658781 := by
  unfold tailWord_2725895
  simp only [CollatzResearch.WordTrace]
  refine ⟨99421558459555435647115139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66281038973036957098076759 99421558459555435647115139)
  ·
    refine ⟨149132337689333153470672709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99421558459555435647115139 149132337689333153470672709)
    ·
      refine ⟨27962313316749966275751133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149132337689333153470672709 27962313316749966275751133)
      ·
        refine ⟨10485867493781237353406675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27962313316749966275751133 10485867493781237353406675)
        ·
          refine ⟨15728801240671856030110013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10485867493781237353406675 15728801240671856030110013)
          ·
            refine ⟨5898300465251946011291255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15728801240671856030110013 5898300465251946011291255)
            ·
              refine ⟨8847450697877919016936883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898300465251946011291255 8847450697877919016936883)
              ·
                refine ⟨13271176046816878525405325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8847450697877919016936883 13271176046816878525405325)
                ·
                  refine ⟨4976691017556329447026997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13271176046816878525405325 4976691017556329447026997)
                  ·
                    refine ⟨466564782895905885658781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4976691017556329447026997 466564782895905885658781)
                    ·
                      rfl

theorem cell23_2725895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_2725895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725895 prefixEnd_2725895 := by exact prefixLift 2725895
  have htrace : WordTrace (prefixWord ++ tailWord_2725895) baseStart_2725895 baseEnd_2725895 := by
    simpa [prefixWord, tailWord_2725895, baseEnd_2725895] using wordTrace_append hprefix tailTrace_2725895
  have hstable : (prefixWord ++ tailWord_2725895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725895).length < 2 ^ (prefixWord ++ tailWord_2725895).sum := by decide
  have hdescent : baseEnd_2725895 < baseStart_2725895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725912 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 1, 5]
def baseStart_2725912 : Nat := 118140960795 + 2725912 * 2 ^ 59
def prefixEnd_2725912 : Nat := 4983230072969 + 3 ^ 40 * 2725912 * 2
def baseEnd_2725912 : Nat := 466567692619614696821255

theorem tailTrace_2725912 : CollatzResearch.WordTrace tailWord_2725912 prefixEnd_2725912 466567692619614696821255 := by
  unfold tailWord_2725912
  simp only [CollatzResearch.WordTrace]
  refine ⟨49711089250246923775241995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66281452333662565033655993 49711089250246923775241995)
  ·
    refine ⟨74566633875370385662862993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49711089250246923775241995 74566633875370385662862993)
    ·
      refine ⟨55924975406527789247147245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74566633875370385662862993 55924975406527789247147245)
      ·
        refine ⟨20971865777447920967680217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55924975406527789247147245 20971865777447920967680217)
        ·
          refine ⟨15728899333085940725760163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20971865777447920967680217 15728899333085940725760163)
          ·
            refine ⟨23593348999628911088640245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15728899333085940725760163 23593348999628911088640245)
            ·
              refine ⟨2211876468715210414560023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23593348999628911088640245 2211876468715210414560023)
              ·
                refine ⟨3317814703072815621840035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2211876468715210414560023 3317814703072815621840035)
                ·
                  refine ⟨4976722054609223432760053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317814703072815621840035 4976722054609223432760053)
                  ·
                    refine ⟨466567692619614696821255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4976722054609223432760053 466567692619614696821255)
                    ·
                      rfl

theorem cell23_2725912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_2725912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725912 prefixEnd_2725912 := by exact prefixLift 2725912
  have htrace : WordTrace (prefixWord ++ tailWord_2725912) baseStart_2725912 baseEnd_2725912 := by
    simpa [prefixWord, tailWord_2725912, baseEnd_2725912] using wordTrace_append hprefix tailTrace_2725912
  have hstable : (prefixWord ++ tailWord_2725912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725912).length < 2 ^ (prefixWord ++ tailWord_2725912).sum := by decide
  have hdescent : baseEnd_2725912 < baseStart_2725912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725942 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2725942 : Nat := 118140960795 + 2725942 * 2 ^ 59
def prefixEnd_2725942 : Nat := 4983230072969 + 3 ^ 40 * 2725942 * 2
def baseEnd_2725942 : Nat := 466572827426159657696209

theorem tailTrace_2725942 : CollatzResearch.WordTrace tailWord_2725942 prefixEnd_2725942 466572827426159657696209 := by
  unfold tailWord_2725942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6213954543149072667129755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 66282181793590108449384053 6213954543149072667129755)
  ·
    refine ⟨9320931814723609000694633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6213954543149072667129755 9320931814723609000694633)
    ·
      refine ⟨6990698861042706750520975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9320931814723609000694633 6990698861042706750520975)
      ·
        refine ⟨10486048291564060125781463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6990698861042706750520975 10486048291564060125781463)
        ·
          refine ⟨15729072437346090188672195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486048291564060125781463 15729072437346090188672195)
          ·
            refine ⟨23593608656019135283008293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15729072437346090188672195 23593608656019135283008293)
            ·
              refine ⟨4423801623003587865564055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23593608656019135283008293 4423801623003587865564055)
              ·
                refine ⟨6635702434505381798346083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4423801623003587865564055 6635702434505381798346083)
                ·
                  refine ⟨9953553651758072697519125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6635702434505381798346083 9953553651758072697519125)
                  ·
                    refine ⟨466572827426159657696209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9953553651758072697519125 466572827426159657696209)
                    ·
                      rfl

theorem cell23_2725942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2725942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725942 prefixEnd_2725942 := by exact prefixLift 2725942
  have htrace : WordTrace (prefixWord ++ tailWord_2725942) baseStart_2725942 baseEnd_2725942 := by
    simpa [prefixWord, tailWord_2725942, baseEnd_2725942] using wordTrace_append hprefix tailTrace_2725942
  have hstable : (prefixWord ++ tailWord_2725942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725942).length < 2 ^ (prefixWord ++ tailWord_2725942).sum := by decide
  have hdescent : baseEnd_2725942 < baseStart_2725942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725949 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2725949 : Nat := 118140960795 + 2725949 * 2 ^ 59
def prefixEnd_2725949 : Nat := 4983230072969 + 3 ^ 40 * 2725949 * 2
def baseEnd_2725949 : Nat := 1399722076643060445701095

theorem tailTrace_2725949 : CollatzResearch.WordTrace tailWord_2725949 prefixEnd_2725949 1399722076643060445701095 := by
  unfold tailWord_2725949
  simp only [CollatzResearch.WordTrace]
  refine ⟨99423528001359802869580901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66282352000906535246387267 99423528001359802869580901)
  ·
    refine ⟨18641911500254963038046419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99423528001359802869580901 18641911500254963038046419)
    ·
      refine ⟨27962867250382444557069629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18641911500254963038046419 27962867250382444557069629)
      ·
        refine ⟨10486075218893416708901111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27962867250382444557069629 10486075218893416708901111)
        ·
          refine ⟨15729112828340125063351667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486075218893416708901111 15729112828340125063351667)
          ·
            refine ⟨23593669242510187595027501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15729112828340125063351667 23593669242510187595027501)
            ·
              refine ⟨8847625965941320348135313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23593669242510187595027501 8847625965941320348135313)
              ·
                refine ⟨6635719474455990261101485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8847625965941320348135313 6635719474455990261101485)
                ·
                  refine ⟨2488394802920996347913057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6635719474455990261101485 2488394802920996347913057)
                  ·
                    refine ⟨1866296102190747260934793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2488394802920996347913057 1866296102190747260934793)
                    ·
                      refine ⟨1399722076643060445701095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866296102190747260934793 1399722076643060445701095)
                      ·
                        rfl

theorem cell23_2725949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2725949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725949 prefixEnd_2725949 := by exact prefixLift 2725949
  have htrace : WordTrace (prefixWord ++ tailWord_2725949) baseStart_2725949 baseEnd_2725949 := by
    simpa [prefixWord, tailWord_2725949, baseEnd_2725949] using wordTrace_append hprefix tailTrace_2725949
  have hstable : (prefixWord ++ tailWord_2725949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725949).length < 2 ^ (prefixWord ++ tailWord_2725949).sum := by decide
  have hdescent : baseEnd_2725949 < baseStart_2725949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2725966 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_2725966 : Nat := 118140960795 + 2725966 * 2 ^ 59
def prefixEnd_2725966 : Nat := 4983230072969 + 3 ^ 40 * 2725966 * 2
def baseEnd_2725966 : Nat := 1399730805814186879188517

theorem tailTrace_2725966 : CollatzResearch.WordTrace tailWord_2725966 prefixEnd_2725966 1399730805814186879188517 := by
  unfold tailWord_2725966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428018505287276846618719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66282765361532143181966501 12428018505287276846618719)
  ·
    refine ⟨18642027757930915269928079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12428018505287276846618719 18642027757930915269928079)
    ·
      refine ⟨27963041636896372904892119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18642027757930915269928079 27963041636896372904892119)
      ·
        refine ⟨41944562455344559357338179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27963041636896372904892119 41944562455344559357338179)
        ·
          refine ⟨62916843683016839036007269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41944562455344559357338179 62916843683016839036007269)
          ·
            refine ⟨11796908190565657319251363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62916843683016839036007269 11796908190565657319251363)
            ·
              refine ⟨17695362285848485978877045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11796908190565657319251363 17695362285848485978877045)
              ·
                refine ⟨1658940214298295560519723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17695362285848485978877045 1658940214298295560519723)
                ·
                  refine ⟨2488410321447443340779585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1658940214298295560519723 2488410321447443340779585)
                  ·
                    refine ⟨1866307741085582505584689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2488410321447443340779585 1866307741085582505584689)
                    ·
                      refine ⟨1399730805814186879188517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866307741085582505584689 1399730805814186879188517)
                      ·
                        rfl

theorem cell23_2725966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_2725966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2725966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2725966 prefixEnd_2725966 := by exact prefixLift 2725966
  have htrace : WordTrace (prefixWord ++ tailWord_2725966) baseStart_2725966 baseEnd_2725966 := by
    simpa [prefixWord, tailWord_2725966, baseEnd_2725966] using wordTrace_append hprefix tailTrace_2725966
  have hstable : (prefixWord ++ tailWord_2725966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2725966).length < 2 ^ (prefixWord ++ tailWord_2725966).sum := by decide
  have hdescent : baseEnd_2725966 < baseStart_2725966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2725966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726009 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 1, 3, 2]
def baseStart_2726009 : Nat := 118140960795 + 2726009 * 2 ^ 59
def prefixEnd_2726009 : Nat := 4983230072969 + 3 ^ 40 * 2726009 * 2
def baseEnd_2726009 : Nat := 1399752885482330210950819

theorem tailTrace_2726009 : CollatzResearch.WordTrace tailWord_2726009 prefixEnd_2726009 1399752885482330210950819 := by
  unfold tailWord_2726009
  simp only [CollatzResearch.WordTrace]
  refine ⟨99425716381142433116765081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66283810920761622077843387 99425716381142433116765081)
  ·
    refine ⟨74569287285856824837573811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99425716381142433116765081 74569287285856824837573811)
    ·
      refine ⟨111853930928785237256360717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74569287285856824837573811 111853930928785237256360717)
      ·
        refine ⟨41945224098294463971135269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111853930928785237256360717 41945224098294463971135269)
        ·
          refine ⟨7864729518430211994587863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41945224098294463971135269 7864729518430211994587863)
          ·
            refine ⟨11797094277645317991881795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7864729518430211994587863 11797094277645317991881795)
            ·
              refine ⟨17695641416467976987822693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11797094277645317991881795 17695641416467976987822693)
              ·
                refine ⟨3317932765587745685216755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17695641416467976987822693 3317932765587745685216755)
                ·
                  refine ⟨4976899148381618527825133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3317932765587745685216755 4976899148381618527825133)
                  ·
                    refine ⟨1866337180643106947934425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4976899148381618527825133 1866337180643106947934425)
                    ·
                      refine ⟨1399752885482330210950819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866337180643106947934425 1399752885482330210950819)
                      ·
                        rfl

theorem cell23_2726009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_2726009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726009 prefixEnd_2726009 := by exact prefixLift 2726009
  have htrace : WordTrace (prefixWord ++ tailWord_2726009) baseStart_2726009 baseEnd_2726009 := by
    simpa [prefixWord, tailWord_2726009, baseEnd_2726009] using wordTrace_append hprefix tailTrace_2726009
  have hstable : (prefixWord ++ tailWord_2726009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726009).length < 2 ^ (prefixWord ++ tailWord_2726009).sum := by decide
  have hdescent : baseEnd_2726009 < baseStart_2726009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726025 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_2726025 : Nat := 118140960795 + 2726025 * 2 ^ 59
def prefixEnd_2726025 : Nat := 4983230072969 + 3 ^ 40 * 2726025 * 2
def baseEnd_2726025 : Nat := 1399761101172802148350745

theorem tailTrace_2726025 : CollatzResearch.WordTrace tailWord_2726025 prefixEnd_2726025 1399761101172802148350745 := by
  unfold tailWord_2726025
  simp only [CollatzResearch.WordTrace]
  refine ⟨99426299949084467849347529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66284199966056311899565019 99426299949084467849347529)
  ·
    refine ⟨74569724961813350887010647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99426299949084467849347529 74569724961813350887010647)
    ·
      refine ⟨111854587442720026330515971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74569724961813350887010647 111854587442720026330515971)
      ·
        refine ⟨167781881164080039495773957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111854587442720026330515971 167781881164080039495773957)
        ·
          refine ⟨31459102718265007405457617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167781881164080039495773957 31459102718265007405457617)
          ·
            refine ⟨23594327038698755554093213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31459102718265007405457617 23594327038698755554093213)
            ·
              refine ⟨8847872639512033332784955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23594327038698755554093213 8847872639512033332784955)
              ·
                refine ⟨13271808959268049999177433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8847872639512033332784955 13271808959268049999177433)
                ·
                  refine ⟨9953856719451037499383075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13271808959268049999177433 9953856719451037499383075)
                  ·
                    refine ⟨14930785079176556249074613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9953856719451037499383075 14930785079176556249074613)
                    ·
                      refine ⟨1399761101172802148350745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14930785079176556249074613 1399761101172802148350745)
                      ·
                        rfl

theorem cell23_2726025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_2726025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726025 prefixEnd_2726025 := by exact prefixLift 2726025
  have htrace : WordTrace (prefixWord ++ tailWord_2726025) baseStart_2726025 baseEnd_2726025 := by
    simpa [prefixWord, tailWord_2726025, baseEnd_2726025] using wordTrace_append hprefix tailTrace_2726025
  have hstable : (prefixWord ++ tailWord_2726025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726025).length < 2 ^ (prefixWord ++ tailWord_2726025).sum := by decide
  have hdescent : baseEnd_2726025 < baseStart_2726025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726085 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_2726085 : Nat := 118140960795 + 2726085 * 2 ^ 59
def prefixEnd_2726085 : Nat := 4983230072969 + 3 ^ 40 * 2726085 * 2
def baseEnd_2726085 : Nat := 1399791910012071913600469

theorem tailTrace_2726085 : CollatzResearch.WordTrace tailWord_2726085 prefixEnd_2726085 1399791910012071913600469 := by
  unfold tailWord_2726085
  simp only [CollatzResearch.WordTrace]
  refine ⟨99428488328867098096531709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66285658885911398731021139 99428488328867098096531709)
  ·
    refine ⟨37285683123325161786199391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99428488328867098096531709 37285683123325161786199391)
    ·
      refine ⟨55928524684987742679299087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37285683123325161786199391 55928524684987742679299087)
      ·
        refine ⟨83892787027481614018948631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55928524684987742679299087 83892787027481614018948631)
        ·
          refine ⟨125839180541222421028422947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83892787027481614018948631 125839180541222421028422947)
          ·
            refine ⟨188758770811833631542634421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125839180541222421028422947 188758770811833631542634421)
            ·
              refine ⟨17696134763609402957121977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188758770811833631542634421 17696134763609402957121977)
              ·
                refine ⟨13272101072707052217841483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17696134763609402957121977 13272101072707052217841483)
                ·
                  refine ⟨19908151609060578326762225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13272101072707052217841483 19908151609060578326762225)
                  ·
                    refine ⟨14931113706795433745071669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19908151609060578326762225 14931113706795433745071669)
                    ·
                      refine ⟨1399791910012071913600469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14931113706795433745071669 1399791910012071913600469)
                      ·
                        rfl

theorem cell23_2726085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_2726085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726085 prefixEnd_2726085 := by exact prefixLift 2726085
  have htrace : WordTrace (prefixWord ++ tailWord_2726085) baseStart_2726085 baseEnd_2726085 := by
    simpa [prefixWord, tailWord_2726085, baseEnd_2726085] using wordTrace_append hprefix tailTrace_2726085
  have hstable : (prefixWord ++ tailWord_2726085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726085).length < 2 ^ (prefixWord ++ tailWord_2726085).sum := by decide
  have hdescent : baseEnd_2726085 < baseStart_2726085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726142 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2726142 : Nat := 118140960795 + 2726142 * 2 ^ 59
def prefixEnd_2726142 : Nat := 4983230072969 + 3 ^ 40 * 2726142 * 2
def baseEnd_2726142 : Nat := 1399821178409378190587707

theorem tailTrace_2726142 : CollatzResearch.WordTrace tailWord_2726142 prefixEnd_2726142 1399821178409378190587707 := by
  unfold tailWord_2726142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428820911207574603919585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66287044859773731220904453 12428820911207574603919585)
  ·
    refine ⟨9321615683405680952939689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12428820911207574603919585 9321615683405680952939689)
    ·
      refine ⟨6991211762554260714704767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9321615683405680952939689 6991211762554260714704767)
      ·
        refine ⟨10486817643831391072057151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6991211762554260714704767 10486817643831391072057151)
        ·
          refine ⟨15730226465747086608085727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10486817643831391072057151 15730226465747086608085727)
          ·
            refine ⟨23595339698620629912128591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15730226465747086608085727 23595339698620629912128591)
            ·
              refine ⟨35393009547930944868192887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23595339698620629912128591 35393009547930944868192887)
              ·
                refine ⟨53089514321896417302289331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35393009547930944868192887 53089514321896417302289331)
                ·
                  refine ⟨79634271482844625953433997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53089514321896417302289331 79634271482844625953433997)
                  ·
                    refine ⟨29862851806066734732537749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79634271482844625953433997 29862851806066734732537749)
                    ·
                      refine ⟨1399821178409378190587707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29862851806066734732537749 1399821178409378190587707)
                      ·
                        rfl

theorem cell23_2726142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2726142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726142 prefixEnd_2726142 := by exact prefixLift 2726142
  have htrace : WordTrace (prefixWord ++ tailWord_2726142) baseStart_2726142 baseEnd_2726142 := by
    simpa [prefixWord, tailWord_2726142, baseEnd_2726142] using wordTrace_append hprefix tailTrace_2726142
  have hstable : (prefixWord ++ tailWord_2726142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726142).length < 2 ^ (prefixWord ++ tailWord_2726142).sum := by decide
  have hdescent : baseEnd_2726142 < baseStart_2726142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726146 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_2726146 : Nat := 118140960795 + 2726146 * 2 ^ 59
def prefixEnd_2726146 : Nat := 4983230072969 + 3 ^ 40 * 2726146 * 2
def baseEnd_2726146 : Nat := 1399823232331996174937689

theorem tailTrace_2726146 : CollatzResearch.WordTrace tailWord_2726146 prefixEnd_2726146 1399823232331996174937689 := by
  unfold tailWord_2726146
  simp only [CollatzResearch.WordTrace]
  refine ⟨24857678295411526378625573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66287142121097403676334861 24857678295411526378625573)
  ·
    refine ⟨4660814680389661195992295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24857678295411526378625573 4660814680389661195992295)
    ·
      refine ⟨6991222020584491793988443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4660814680389661195992295 6991222020584491793988443)
      ·
        refine ⟨10486833030876737690982665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6991222020584491793988443 10486833030876737690982665)
        ·
          refine ⟨7865124773157553268236999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10486833030876737690982665 7865124773157553268236999)
          ·
            refine ⟨11797687159736329902355499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865124773157553268236999 11797687159736329902355499)
            ·
              refine ⟨17696530739604494853533249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11797687159736329902355499 17696530739604494853533249)
              ·
                refine ⟨13272398054703371140149937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17696530739604494853533249 13272398054703371140149937)
                ·
                  refine ⟨9954298541027528355112453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13272398054703371140149937 9954298541027528355112453)
                  ·
                    refine ⟨1866430976442661566583585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9954298541027528355112453 1866430976442661566583585)
                    ·
                      refine ⟨1399823232331996174937689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866430976442661566583585 1399823232331996174937689)
                      ·
                        rfl

theorem cell23_2726146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_2726146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726146 prefixEnd_2726146 := by exact prefixLift 2726146
  have htrace : WordTrace (prefixWord ++ tailWord_2726146) baseStart_2726146 baseEnd_2726146 := by
    simpa [prefixWord, tailWord_2726146, baseEnd_2726146] using wordTrace_append hprefix tailTrace_2726146
  have hstable : (prefixWord ++ tailWord_2726146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726146).length < 2 ^ (prefixWord ++ tailWord_2726146).sum := by decide
  have hdescent : baseEnd_2726146 < baseStart_2726146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726152 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 8]
def baseStart_2726152 : Nat := 118140960795 + 2726152 * 2 ^ 59
def prefixEnd_2726152 : Nat := 4983230072969 + 3 ^ 40 * 2726152 * 2
def baseEnd_2726152 : Nat := 155536257023991461273629

theorem tailTrace_2726152 : CollatzResearch.WordTrace tailWord_2726152 prefixEnd_2726152 155536257023991461273629 := by
  unfold tailWord_2726152
  simp only [CollatzResearch.WordTrace]
  refine ⟨49715466009812184269610355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66287288013082912359480473 49715466009812184269610355)
  ·
    refine ⟨74573199014718276404415533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49715466009812184269610355 74573199014718276404415533)
    ·
      refine ⟨27964949630519353651655825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74573199014718276404415533 27964949630519353651655825)
      ·
        refine ⟨20973712222889515238741869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27964949630519353651655825 20973712222889515238741869)
        ·
          refine ⟨7865142083583568214528201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20973712222889515238741869 7865142083583568214528201)
          ·
            refine ⟨5898856562687676160896151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7865142083583568214528201 5898856562687676160896151)
            ·
              refine ⟨8848284844031514241344227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898856562687676160896151 8848284844031514241344227)
              ·
                refine ⟨13272427266047271362016341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8848284844031514241344227 13272427266047271362016341)
                ·
                  refine ⟨155536257023991461273629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13272427266047271362016341 155536257023991461273629)
                  ·
                    rfl

theorem cell23_2726152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_2726152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726152 prefixEnd_2726152 := by exact prefixLift 2726152
  have htrace : WordTrace (prefixWord ++ tailWord_2726152) baseStart_2726152 baseEnd_2726152 := by
    simpa [prefixWord, tailWord_2726152, baseEnd_2726152] using wordTrace_append hprefix tailTrace_2726152
  have hstable : (prefixWord ++ tailWord_2726152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726152).length < 2 ^ (prefixWord ++ tailWord_2726152).sum := by decide
  have hdescent : baseEnd_2726152 < baseStart_2726152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726155 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_2726155 : Nat := 118140960795 + 2726155 * 2 ^ 59
def prefixEnd_2726155 : Nat := 4983230072969 + 3 ^ 40 * 2726155 * 2
def baseEnd_2726155 : Nat := 1399827853657886639725147

theorem tailTrace_2726155 : CollatzResearch.WordTrace tailWord_2726155 prefixEnd_2726155 1399827853657886639725147 := by
  unfold tailWord_2726155
  simp only [CollatzResearch.WordTrace]
  refine ⟨99431041438613500051579919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66287360959075666701053279 99431041438613500051579919)
  ·
    refine ⟨149146562157920250077369879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99431041438613500051579919 149146562157920250077369879)
    ·
      refine ⟨223719843236880375116054819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149146562157920250077369879 223719843236880375116054819)
      ·
        refine ⟨335579764855320562674082229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223719843236880375116054819 335579764855320562674082229)
        ·
          refine ⟨31460602955186302750695209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 335579764855320562674082229 31460602955186302750695209)
          ·
            refine ⟨23595452216389727063021407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31460602955186302750695209 23595452216389727063021407)
            ·
              refine ⟨35393178324584590594532111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23595452216389727063021407 35393178324584590594532111)
              ·
                refine ⟨53089767486876885891798167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35393178324584590594532111 53089767486876885891798167)
                ·
                  refine ⟨79634651230315328837697251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53089767486876885891798167 79634651230315328837697251)
                  ·
                    refine ⟨119451976845472993256545877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79634651230315328837697251 119451976845472993256545877)
                    ·
                      refine ⟨1399827853657886639725147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 119451976845472993256545877 1399827853657886639725147)
                      ·
                        rfl

theorem cell23_2726155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_2726155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726155 prefixEnd_2726155 := by exact prefixLift 2726155
  have htrace : WordTrace (prefixWord ++ tailWord_2726155) baseStart_2726155 baseEnd_2726155 := by
    simpa [prefixWord, tailWord_2726155, baseEnd_2726155] using wordTrace_append hprefix tailTrace_2726155
  have hstable : (prefixWord ++ tailWord_2726155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726155).length < 2 ^ (prefixWord ++ tailWord_2726155).sum := by decide
  have hdescent : baseEnd_2726155 < baseStart_2726155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726179 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 3]
def baseStart_2726179 : Nat := 118140960795 + 2726179 * 2 ^ 59
def prefixEnd_2726179 : Nat := 4983230072969 + 3 ^ 40 * 2726179 * 2
def baseEnd_2726179 : Nat := 1399840177193594545825037

theorem tailTrace_2726179 : CollatzResearch.WordTrace tailWord_2726179 prefixEnd_2726179 1399840177193594545825037 := by
  unfold tailWord_2726179
  simp only [CollatzResearch.WordTrace]
  refine ⟨99431916790526552150453591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66287944527017701433635727 99431916790526552150453591)
  ·
    refine ⟨149147875185789828225680387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99431916790526552150453591 149147875185789828225680387)
    ·
      refine ⟨223721812778684742338520581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149147875185789828225680387 223721812778684742338520581)
      ·
        refine ⟨41947839896003389188472609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223721812778684742338520581 41947839896003389188472609)
        ·
          refine ⟨31460879922002541891354457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41947839896003389188472609 31460879922002541891354457)
          ·
            refine ⟨23595659941501906418515843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31460879922002541891354457 23595659941501906418515843)
            ·
              refine ⟨35393489912252859627773765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23595659941501906418515843 35393489912252859627773765)
              ·
                refine ⟨6636279358547411180207581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35393489912252859627773765 6636279358547411180207581)
                ·
                  refine ⟨2488604759455279192577843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6636279358547411180207581 2488604759455279192577843)
                  ·
                    refine ⟨3732907139182918788866765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2488604759455279192577843 3732907139182918788866765)
                    ·
                      refine ⟨1399840177193594545825037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3732907139182918788866765 1399840177193594545825037)
                      ·
                        rfl

theorem cell23_2726179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_2726179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726179 prefixEnd_2726179 := by exact prefixLift 2726179
  have htrace : WordTrace (prefixWord ++ tailWord_2726179) baseStart_2726179 baseEnd_2726179 := by
    simpa [prefixWord, tailWord_2726179, baseEnd_2726179] using wordTrace_append hprefix tailTrace_2726179
  have hstable : (prefixWord ++ tailWord_2726179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726179).length < 2 ^ (prefixWord ++ tailWord_2726179).sum := by decide
  have hdescent : baseEnd_2726179 < baseStart_2726179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726206 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_2726206 : Nat := 118140960795 + 2726206 * 2 ^ 59
def prefixEnd_2726206 : Nat := 4983230072969 + 3 ^ 40 * 2726206 * 2
def baseEnd_2726206 : Nat := 1399854041171265940187413

theorem tailTrace_2726206 : CollatzResearch.WordTrace tailWord_2726206 prefixEnd_2726206 1399854041171265940187413 := by
  unfold tailWord_2726206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429112695178591970210809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66288601040952490507790981 12429112695178591970210809)
  ·
    refine ⟨9321834521383943977658107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12429112695178591970210809 9321834521383943977658107)
    ·
      refine ⟨13982751782075915966487161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9321834521383943977658107 13982751782075915966487161)
      ·
        refine ⟨10487063836556936974865371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13982751782075915966487161 10487063836556936974865371)
        ·
          refine ⟨15730595754835405462298057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10487063836556936974865371 15730595754835405462298057)
          ·
            refine ⟨11797946816126554096723543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15730595754835405462298057 11797946816126554096723543)
            ·
              refine ⟨17696920224189831145085315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11797946816126554096723543 17696920224189831145085315)
              ·
                refine ⟨26545380336284746717627973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17696920224189831145085315 26545380336284746717627973)
                ·
                  refine ⟨4977258813053390009555245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26545380336284746717627973 4977258813053390009555245)
                  ·
                    refine ⟨1866472054895021253583217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4977258813053390009555245 1866472054895021253583217)
                    ·
                      refine ⟨1399854041171265940187413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866472054895021253583217 1399854041171265940187413)
                      ·
                        rfl

theorem cell23_2726206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_2726206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726206 prefixEnd_2726206 := by exact prefixLift 2726206
  have htrace : WordTrace (prefixWord ++ tailWord_2726206) baseStart_2726206 baseEnd_2726206 := by
    simpa [prefixWord, tailWord_2726206, baseEnd_2726206] using wordTrace_append hprefix tailTrace_2726206
  have hstable : (prefixWord ++ tailWord_2726206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726206).length < 2 ^ (prefixWord ++ tailWord_2726206).sum := by decide
  have hdescent : baseEnd_2726206 < baseStart_2726206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726222 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2726222 : Nat := 118140960795 + 2726222 * 2 ^ 59
def prefixEnd_2726222 : Nat := 4983230072969 + 3 ^ 40 * 2726222 * 2
def baseEnd_2726222 : Nat := 1399862256861737877587339

theorem tailTrace_2726222 : CollatzResearch.WordTrace tailWord_2726222 prefixEnd_2726222 1399862256861737877587339 := by
  unfold tailWord_2726222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429185641171346311783615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66288990086247180329512613 12429185641171346311783615)
  ·
    refine ⟨18643778461757019467675423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12429185641171346311783615 18643778461757019467675423)
    ·
      refine ⟨27965667692635529201513135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18643778461757019467675423 27965667692635529201513135)
      ·
        refine ⟨41948501538953293802269703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27965667692635529201513135 41948501538953293802269703)
        ·
          refine ⟨62922752308429940703404555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41948501538953293802269703 62922752308429940703404555)
          ·
            refine ⟨94384128462644911055106833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62922752308429940703404555 94384128462644911055106833)
            ·
              refine ⟨70788096346983683291330125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94384128462644911055106833 70788096346983683291330125)
              ·
                refine ⟨26545536130118881234248797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70788096346983683291330125 26545536130118881234248797)
                ·
                  refine ⟨9954576048794580462843299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26545536130118881234248797 9954576048794580462843299)
                  ·
                    refine ⟨14931864073191870694264949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9954576048794580462843299 14931864073191870694264949)
                    ·
                      refine ⟨1399862256861737877587339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14931864073191870694264949 1399862256861737877587339)
                      ·
                        rfl

theorem cell23_2726222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2726222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726222 prefixEnd_2726222 := by exact prefixLift 2726222
  have htrace : WordTrace (prefixWord ++ tailWord_2726222) baseStart_2726222 baseEnd_2726222 := by
    simpa [prefixWord, tailWord_2726222, baseEnd_2726222] using wordTrace_append hprefix tailTrace_2726222
  have hstable : (prefixWord ++ tailWord_2726222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726222).length < 2 ^ (prefixWord ++ tailWord_2726222).sum := by decide
  have hdescent : baseEnd_2726222 < baseStart_2726222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726286 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2726286 : Nat := 118140960795 + 2726286 * 2 ^ 59
def prefixEnd_2726286 : Nat := 4983230072969 + 3 ^ 40 * 2726286 * 2
def baseEnd_2726286 : Nat := 1399895119623625627187045

theorem tailTrace_2726286 : CollatzResearch.WordTrace tailWord_2726286 prefixEnd_2726286 1399895119623625627187045 := by
  unfold tailWord_2726286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12429477425142363678074839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66290546267425939616399141 12429477425142363678074839)
  ·
    refine ⟨18644216137713545517112259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12429477425142363678074839 18644216137713545517112259)
    ·
      refine ⟨27966324206570318275668389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18644216137713545517112259 27966324206570318275668389)
      ·
        refine ⟨5243685788731934676687823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27966324206570318275668389 5243685788731934676687823)
        ·
          refine ⟨7865528683097902015031735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5243685788731934676687823 7865528683097902015031735)
          ·
            refine ⟨11798293024646853022547603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7865528683097902015031735 11798293024646853022547603)
            ·
              refine ⟨17697439536970279533821405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11798293024646853022547603 17697439536970279533821405)
              ·
                refine ⟨6636539826363854825183027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17697439536970279533821405 6636539826363854825183027)
                ·
                  refine ⟨9954809739545782237774541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6636539826363854825183027 9954809739545782237774541)
                  ·
                    refine ⟨3733053652329668339165453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9954809739545782237774541 3733053652329668339165453)
                    ·
                      refine ⟨1399895119623625627187045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3733053652329668339165453 1399895119623625627187045)
                      ·
                        rfl

theorem cell23_2726286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2726286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726286 prefixEnd_2726286 := by exact prefixLift 2726286
  have htrace : WordTrace (prefixWord ++ tailWord_2726286) baseStart_2726286 baseEnd_2726286 := by
    simpa [prefixWord, tailWord_2726286, baseEnd_2726286] using wordTrace_append hprefix tailTrace_2726286
  have hstable : (prefixWord ++ tailWord_2726286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726286).length < 2 ^ (prefixWord ++ tailWord_2726286).sum := by decide
  have hdescent : baseEnd_2726286 < baseStart_2726286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726314 : List Nat := [3, 1, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2726314 : Nat := 118140960795 + 2726314 * 2 ^ 59
def prefixEnd_2726314 : Nat := 4983230072969 + 3 ^ 40 * 2726314 * 2
def baseEnd_2726314 : Nat := 466636499027317172545639

theorem tailTrace_2726314 : CollatzResearch.WordTrace tailWord_2726314 prefixEnd_2726314 466636499027317172545639 := by
  unfold tailWord_2726314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24859210161259367551654499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66291227096691646804411997 24859210161259367551654499)
  ·
    refine ⟨37288815241889051327481749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24859210161259367551654499 37288815241889051327481749)
    ·
      refine ⟨1747913214463549280975707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37288815241889051327481749 1747913214463549280975707)
      ·
        refine ⟨2621869821695323921463561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747913214463549280975707 2621869821695323921463561)
        ·
          refine ⟨1966402366271492941097671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2621869821695323921463561 1966402366271492941097671)
          ·
            refine ⟨2949603549407239411646507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1966402366271492941097671 2949603549407239411646507)
            ·
              refine ⟨4424405324110859117469761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949603549407239411646507 4424405324110859117469761)
              ·
                refine ⟨3318303993083144338102321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424405324110859117469761 3318303993083144338102321)
                ·
                  refine ⟨2488727994812358253576741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3318303993083144338102321 2488727994812358253576741)
                  ·
                    refine ⟨466636499027317172545639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2488727994812358253576741 466636499027317172545639)
                    ·
                      rfl

theorem cell23_2726314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2726314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726314 prefixEnd_2726314 := by exact prefixLift 2726314
  have htrace : WordTrace (prefixWord ++ tailWord_2726314) baseStart_2726314 baseEnd_2726314 := by
    simpa [prefixWord, tailWord_2726314, baseEnd_2726314] using wordTrace_append hprefix tailTrace_2726314
  have hstable : (prefixWord ++ tailWord_2726314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726314).length < 2 ^ (prefixWord ++ tailWord_2726314).sum := by decide
  have hdescent : baseEnd_2726314 < baseStart_2726314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726337 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2726337 : Nat := 118140960795 + 2726337 * 2 ^ 59
def prefixEnd_2726337 : Nat := 4983230072969 + 3 ^ 40 * 2726337 * 2
def baseEnd_2726337 : Nat := 1399921307137004927649311

theorem tailTrace_2726337 : CollatzResearch.WordTrace tailWord_2726337 prefixEnd_2726337 1399921307137004927649311 := by
  unfold tailWord_2726337
  simp only [CollatzResearch.WordTrace]
  refine ⟨99437679523954145134705265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66291786349302763423136843 99437679523954145134705265)
  ·
    refine ⟨74578259642965608851028949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99437679523954145134705265 74578259642965608851028949)
    ·
      refine ⟨1747927960382006457445991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 74578259642965608851028949 1747927960382006457445991)
      ·
        refine ⟨2621891940573009686168987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747927960382006457445991 2621891940573009686168987)
        ·
          refine ⟨3932837910859514529253481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621891940573009686168987 3932837910859514529253481)
          ·
            refine ⟨2949628433144635896940111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932837910859514529253481 2949628433144635896940111)
            ·
              refine ⟨4424442649716953845410167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949628433144635896940111 4424442649716953845410167)
              ·
                refine ⟨6636663974575430768115251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424442649716953845410167 6636663974575430768115251)
                ·
                  refine ⟨9954995961863146152172877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6636663974575430768115251 9954995961863146152172877)
                  ·
                    refine ⟨3733123485698679807064829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9954995961863146152172877 3733123485698679807064829)
                    ·
                      refine ⟨1399921307137004927649311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3733123485698679807064829 1399921307137004927649311)
                      ·
                        rfl

theorem cell23_2726337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2726337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726337 prefixEnd_2726337 := by exact prefixLift 2726337
  have htrace : WordTrace (prefixWord ++ tailWord_2726337) baseStart_2726337 baseEnd_2726337 := by
    simpa [prefixWord, tailWord_2726337, baseEnd_2726337] using wordTrace_append hprefix tailTrace_2726337
  have hstable : (prefixWord ++ tailWord_2726337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726337).length < 2 ^ (prefixWord ++ tailWord_2726337).sum := by decide
  have hdescent : baseEnd_2726337 < baseStart_2726337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726343 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_2726343 : Nat := 118140960795 + 2726343 * 2 ^ 59
def prefixEnd_2726343 : Nat := 4983230072969 + 3 ^ 40 * 2726343 * 2
def baseEnd_2726343 : Nat := 1399924388020931904174283

theorem tailTrace_2726343 : CollatzResearch.WordTrace tailWord_2726343 prefixEnd_2726343 1399924388020931904174283 := by
  unfold tailWord_2726343
  simp only [CollatzResearch.WordTrace]
  refine ⟨99437898361932408159423683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66291932241288272106282455 99437898361932408159423683)
  ·
    refine ⟨149156847542898612239135525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99437898361932408159423683 149156847542898612239135525)
    ·
      refine ⟨27966908914293489794837911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149156847542898612239135525 27966908914293489794837911)
      ·
        refine ⟨41950363371440234692256867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27966908914293489794837911 41950363371440234692256867)
        ·
          refine ⟨62925545057160352038385301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41950363371440234692256867 62925545057160352038385301)
          ·
            refine ⟨2949634924554391501799311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62925545057160352038385301 2949634924554391501799311)
            ·
              refine ⟨4424452386831587252698967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949634924554391501799311 4424452386831587252698967)
              ·
                refine ⟨6636678580247380879048451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424452386831587252698967 6636678580247380879048451)
                ·
                  refine ⟨9955017870371071318572677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6636678580247380879048451 9955017870371071318572677)
                  ·
                    refine ⟨1866565850694575872232377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9955017870371071318572677 1866565850694575872232377)
                    ·
                      refine ⟨1399924388020931904174283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866565850694575872232377 1399924388020931904174283)
                      ·
                        rfl

theorem cell23_2726343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_2726343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726343 prefixEnd_2726343 := by exact prefixLift 2726343
  have htrace : WordTrace (prefixWord ++ tailWord_2726343) baseStart_2726343 baseEnd_2726343 := by
    simpa [prefixWord, tailWord_2726343, baseEnd_2726343] using wordTrace_append hprefix tailTrace_2726343
  have hstable : (prefixWord ++ tailWord_2726343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726343).length < 2 ^ (prefixWord ++ tailWord_2726343).sum := by decide
  have hdescent : baseEnd_2726343 < baseStart_2726343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726379 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 2, 5]
def baseStart_2726379 : Nat := 118140960795 + 2726379 * 2 ^ 59
def prefixEnd_2726379 : Nat := 4983230072969 + 3 ^ 40 * 2726379 * 2
def baseEnd_2726379 : Nat := 466647624441497921108039

theorem tailTrace_2726379 : CollatzResearch.WordTrace tailWord_2726379 prefixEnd_2726379 466647624441497921108039 := by
  unfold tailWord_2726379
  simp only [CollatzResearch.WordTrace]
  refine ⟨99439211389801986307734191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66292807593201324205156127 99439211389801986307734191)
  ·
    refine ⟨149158817084702979461601287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99439211389801986307734191 149158817084702979461601287)
    ·
      refine ⟨223738225627054469192401931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149158817084702979461601287 223738225627054469192401931)
      ·
        refine ⟨335607338440581703788602897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223738225627054469192401931 335607338440581703788602897)
        ·
          refine ⟨251705503830436277841452173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335607338440581703788602897 251705503830436277841452173)
          ·
            refine ⟨94389563936413604190544565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251705503830436277841452173 94389563936413604190544565)
            ·
              refine ⟨8849021619038775392863553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94389563936413604190544565 8849021619038775392863553)
              ·
                refine ⟨6636766214279081544647665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8849021619038775392863553 6636766214279081544647665)
                ·
                  refine ⟨4977574660709311158485749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6636766214279081544647665 4977574660709311158485749)
                  ·
                    refine ⟨466647624441497921108039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4977574660709311158485749 466647624441497921108039)
                    ·
                      rfl

theorem cell23_2726379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 5].length) (baseStart_2726379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726379 prefixEnd_2726379 := by exact prefixLift 2726379
  have htrace : WordTrace (prefixWord ++ tailWord_2726379) baseStart_2726379 baseEnd_2726379 := by
    simpa [prefixWord, tailWord_2726379, baseEnd_2726379] using wordTrace_append hprefix tailTrace_2726379
  have hstable : (prefixWord ++ tailWord_2726379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726379).length < 2 ^ (prefixWord ++ tailWord_2726379).sum := by decide
  have hdescent : baseEnd_2726379 < baseStart_2726379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726399 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_2726399 : Nat := 118140960795 + 2726399 * 2 ^ 59
def prefixEnd_2726399 : Nat := 4983230072969 + 3 ^ 40 * 2726399 * 2
def baseEnd_2726399 : Nat := 1399953142937583685074025

theorem tailTrace_2726399 : CollatzResearch.WordTrace tailWord_2726399 prefixEnd_2726399 1399953142937583685074025 := by
  unfold tailWord_2726399
  simp only [CollatzResearch.WordTrace]
  refine ⟨99439940849729529723462251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66293293899819686482308167 99439940849729529723462251)
  ·
    refine ⟨149159911274594294585193377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99439940849729529723462251 149159911274594294585193377)
    ·
      refine ⟨111869933455945720938895033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149159911274594294585193377 111869933455945720938895033)
      ·
        refine ⟨83902450091959290704171275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111869933455945720938895033 83902450091959290704171275)
        ·
          refine ⟨125853675137938936056256913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83902450091959290704171275 125853675137938936056256913)
          ·
            refine ⟨94390256353454202042192685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125853675137938936056256913 94390256353454202042192685)
            ·
              refine ⟨35396346132545325765822257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94390256353454202042192685 35396346132545325765822257)
              ·
                refine ⟨26547259599408994324366693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35396346132545325765822257 26547259599408994324366693)
                ·
                  refine ⟨4977611174889186435818755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26547259599408994324366693 4977611174889186435818755)
                  ·
                    refine ⟨7466416762333779653728133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4977611174889186435818755 7466416762333779653728133)
                    ·
                      refine ⟨1399953142937583685074025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7466416762333779653728133 1399953142937583685074025)
                      ·
                        rfl

theorem cell23_2726399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_2726399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726399 prefixEnd_2726399 := by exact prefixLift 2726399
  have htrace : WordTrace (prefixWord ++ tailWord_2726399) baseStart_2726399 baseEnd_2726399 := by
    simpa [prefixWord, tailWord_2726399, baseEnd_2726399] using wordTrace_append hprefix tailTrace_2726399
  have hstable : (prefixWord ++ tailWord_2726399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726399).length < 2 ^ (prefixWord ++ tailWord_2726399).sum := by decide
  have hdescent : baseEnd_2726399 < baseStart_2726399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726470 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2726470 : Nat := 118140960795 + 2726470 * 2 ^ 59
def prefixEnd_2726470 : Nat := 4983230072969 + 3 ^ 40 * 2726470 * 2
def baseEnd_2726470 : Nat := 1399989600064052907286199

theorem tailTrace_2726470 : CollatzResearch.WordTrace tailWord_2726470 prefixEnd_2726470 1399989600064052907286199 := by
  unfold tailWord_2726470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3107579076014759651540527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66295020288314872566197909 3107579076014759651540527)
  ·
    refine ⟨4661368614022139477310791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3107579076014759651540527 4661368614022139477310791)
    ·
      refine ⟨6992052921033209215966187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661368614022139477310791 6992052921033209215966187)
      ·
        refine ⟨10488079381549813823949281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992052921033209215966187 10488079381549813823949281)
        ·
          refine ⟨7866059536162360367961961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10488079381549813823949281 7866059536162360367961961)
          ·
            refine ⟨5899544652121770275971471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7866059536162360367961961 5899544652121770275971471)
            ·
              refine ⟨8849316978182655413957207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899544652121770275971471 8849316978182655413957207)
              ·
                refine ⟨13273975467273983120935811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8849316978182655413957207 13273975467273983120935811)
                ·
                  refine ⟨19910963200910974681403717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13273975467273983120935811 19910963200910974681403717)
                  ·
                    refine ⟨3733305600170807752763197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19910963200910974681403717 3733305600170807752763197)
                    ·
                      refine ⟨1399989600064052907286199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3733305600170807752763197 1399989600064052907286199)
                      ·
                        rfl

theorem cell23_2726470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2726470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726470 prefixEnd_2726470 := by exact prefixLift 2726470
  have htrace : WordTrace (prefixWord ++ tailWord_2726470) baseStart_2726470 baseEnd_2726470 := by
    simpa [prefixWord, tailWord_2726470, baseEnd_2726470] using wordTrace_append hprefix tailTrace_2726470
  have hstable : (prefixWord ++ tailWord_2726470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726470).length < 2 ^ (prefixWord ++ tailWord_2726470).sum := by decide
  have hdescent : baseEnd_2726470 < baseStart_2726470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726477 : List Nat := [1, 6, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_2726477 : Nat := 118140960795 + 2726477 * 2 ^ 59
def prefixEnd_2726477 : Nat := 4983230072969 + 3 ^ 40 * 2726477 * 2
def baseEnd_2726477 : Nat := 466664398142878126632889

theorem tailTrace_2726477 : CollatzResearch.WordTrace tailWord_2726477 prefixEnd_2726477 466664398142878126632889 := by
  unfold tailWord_2726477
  simp only [CollatzResearch.WordTrace]
  refine ⟨99442785743446949044801685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66295190495631299363201123 99442785743446949044801685)
  ·
    refine ⟨4661380581724075736475079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99442785743446949044801685 4661380581724075736475079)
    ·
      refine ⟨6992070872586113604712619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661380581724075736475079 6992070872586113604712619)
      ·
        refine ⟨10488106308879170407068929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992070872586113604712619 10488106308879170407068929)
        ·
          refine ⟨7866079731659377805301697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10488106308879170407068929 7866079731659377805301697)
          ·
            refine ⟨5899559798744533353976273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7866079731659377805301697 5899559798744533353976273)
            ·
              refine ⟨4424669849058400015482205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899559798744533353976273 4424669849058400015482205)
              ·
                refine ⟨1659251193396900005805827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4424669849058400015482205 1659251193396900005805827)
                ·
                  refine ⟨2488876790095350008708741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659251193396900005805827 2488876790095350008708741)
                  ·
                    refine ⟨466664398142878126632889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2488876790095350008708741 466664398142878126632889)
                    ·
                      rfl

theorem cell23_2726477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_2726477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726477 prefixEnd_2726477 := by exact prefixLift 2726477
  have htrace : WordTrace (prefixWord ++ tailWord_2726477) baseStart_2726477 baseEnd_2726477 := by
    simpa [prefixWord, tailWord_2726477, baseEnd_2726477] using wordTrace_append hprefix tailTrace_2726477
  have hstable : (prefixWord ++ tailWord_2726477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726477).length < 2 ^ (prefixWord ++ tailWord_2726477).sum := by decide
  have hdescent : baseEnd_2726477 < baseStart_2726477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726494 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2726494 : Nat := 118140960795 + 2726494 * 2 ^ 59
def prefixEnd_2726494 : Nat := 4983230072969 + 3 ^ 40 * 2726494 * 2
def baseEnd_2726494 : Nat := 466667307866586937795363

theorem tailTrace_2726494 : CollatzResearch.WordTrace tailWord_2726494 prefixEnd_2726494 466667307866586937795363 := by
  unfold tailWord_2726494
  simp only [CollatzResearch.WordTrace]
  refine ⟨12430425723048170118521317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66295603856256907298780357 12430425723048170118521317)
  ·
    refine ⟨2330704823071531897222747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12430425723048170118521317 2330704823071531897222747)
    ·
      refine ⟨3496057234607297845834121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2330704823071531897222747 3496057234607297845834121)
      ·
        refine ⟨2622042925955473384375591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3496057234607297845834121 2622042925955473384375591)
        ·
          refine ⟨3933064388933210076563387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622042925955473384375591 3933064388933210076563387)
          ·
            refine ⟨5899596583399815114845081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933064388933210076563387 5899596583399815114845081)
            ·
              refine ⟨4424697437549861336133811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5899596583399815114845081 4424697437549861336133811)
              ·
                refine ⟨6637046156324792004200717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4424697437549861336133811 6637046156324792004200717)
                ·
                  refine ⟨2488892308621797001575269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6637046156324792004200717 2488892308621797001575269)
                  ·
                    refine ⟨466667307866586937795363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2488892308621797001575269 466667307866586937795363)
                    ·
                      rfl

theorem cell23_2726494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2726494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726494 prefixEnd_2726494 := by exact prefixLift 2726494
  have htrace : WordTrace (prefixWord ++ tailWord_2726494) baseStart_2726494 baseEnd_2726494 := by
    simpa [prefixWord, tailWord_2726494, baseEnd_2726494] using wordTrace_append hprefix tailTrace_2726494
  have hstable : (prefixWord ++ tailWord_2726494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726494).length < 2 ^ (prefixWord ++ tailWord_2726494).sum := by decide
  have hdescent : baseEnd_2726494 < baseStart_2726494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726500 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_2726500 : Nat := 118140960795 + 2726500 * 2 ^ 59
def prefixEnd_2726500 : Nat := 4983230072969 + 3 ^ 40 * 2726500 * 2
def baseEnd_2726500 : Nat := 1400005004483687789911061

theorem tailTrace_2726500 : CollatzResearch.WordTrace tailWord_2726500 prefixEnd_2726500 1400005004483687789911061 := by
  unfold tailWord_2726500
  simp only [CollatzResearch.WordTrace]
  refine ⟨49721812311181811986444477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66295749748242415981925969 49721812311181811986444477)
  ·
    refine ⟨18645679616693179494916679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49721812311181811986444477 18645679616693179494916679)
    ·
      refine ⟨27968519425039769242375019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18645679616693179494916679 27968519425039769242375019)
      ·
        refine ⟨41952779137559653863562529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27968519425039769242375019 41952779137559653863562529)
        ·
          refine ⟨31464584353169740397671897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41952779137559653863562529 31464584353169740397671897)
          ·
            refine ⟨23598438264877305298253923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31464584353169740397671897 23598438264877305298253923)
            ·
              refine ⟨35397657397315957947380885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23598438264877305298253923 35397657397315957947380885)
              ·
                refine ⟨1659265190499185528783479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35397657397315957947380885 1659265190499185528783479)
                ·
                  refine ⟨2488897785748778293175219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659265190499185528783479 2488897785748778293175219)
                  ·
                    refine ⟨3733346678623167439762829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2488897785748778293175219 3733346678623167439762829)
                    ·
                      refine ⟨1400005004483687789911061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3733346678623167439762829 1400005004483687789911061)
                      ·
                        rfl

theorem cell23_2726500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_2726500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726500 prefixEnd_2726500 := by exact prefixLift 2726500
  have htrace : WordTrace (prefixWord ++ tailWord_2726500) baseStart_2726500 baseEnd_2726500 := by
    simpa [prefixWord, tailWord_2726500, baseEnd_2726500] using wordTrace_append hprefix tailTrace_2726500
  have hstable : (prefixWord ++ tailWord_2726500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726500).length < 2 ^ (prefixWord ++ tailWord_2726500).sum := by decide
  have hdescent : baseEnd_2726500 < baseStart_2726500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726523 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 5, 2, 2]
def baseStart_2726523 : Nat := 118140960795 + 2726523 * 2 ^ 59
def prefixEnd_2726523 : Nat := 4983230072969 + 3 ^ 40 * 2726523 * 2
def baseEnd_2726523 : Nat := 1400016814538741199923455

theorem tailTrace_2726523 : CollatzResearch.WordTrace tailWord_2726523 prefixEnd_2726523 1400016814538741199923455 := by
  unfold tailWord_2726523
  simp only [CollatzResearch.WordTrace]
  refine ⟨99444463501280298900976223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66296309000853532600650815 99444463501280298900976223)
  ·
    refine ⟨149166695251920448351464335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99444463501280298900976223 149166695251920448351464335)
    ·
      refine ⟨223750042877880672527196503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149166695251920448351464335 223750042877880672527196503)
      ·
        refine ⟨335625064316821008790794755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223750042877880672527196503 335625064316821008790794755)
        ·
          refine ⟨503437596475231513186192133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335625064316821008790794755 503437596475231513186192133)
          ·
            refine ⟨94394549339105908722411025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 503437596475231513186192133 94394549339105908722411025)
            ·
              refine ⟨70795912004329431541808269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94394549339105908722411025 70795912004329431541808269)
              ·
                refine ⟨26548467001623536828178101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70795912004329431541808269 26548467001623536828178101)
                ·
                  refine ⟨2488918781402206577641697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26548467001623536828178101 2488918781402206577641697)
                  ·
                    refine ⟨1866689086051654933231273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2488918781402206577641697 1866689086051654933231273)
                    ·
                      refine ⟨1400016814538741199923455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866689086051654933231273 1400016814538741199923455)
                      ·
                        rfl

theorem cell23_2726523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 2, 2].length) (baseStart_2726523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726523 prefixEnd_2726523 := by exact prefixLift 2726523
  have htrace : WordTrace (prefixWord ++ tailWord_2726523) baseStart_2726523 baseEnd_2726523 := by
    simpa [prefixWord, tailWord_2726523, baseEnd_2726523] using wordTrace_append hprefix tailTrace_2726523
  have hstable : (prefixWord ++ tailWord_2726523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726523).length < 2 ^ (prefixWord ++ tailWord_2726523).sum := by decide
  have hdescent : baseEnd_2726523 < baseStart_2726523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726546 : List Nat := [3, 2, 3, 1, 2, 1, 11]
def baseStart_2726546 : Nat := 118140960795 + 2726546 * 2 ^ 59
def prefixEnd_2726546 : Nat := 4983230072969 + 3 ^ 40 * 2726546 * 2
def baseEnd_2726546 : Nat := 17284304007330797653529

theorem tailTrace_2726546 : CollatzResearch.WordTrace tailWord_2726546 prefixEnd_2726546 17284304007330797653529 := by
  unfold tailWord_2726546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24861325595049243457265873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66296868253464649219375661 24861325595049243457265873)
  ·
    refine ⟨18645994196286932592949405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24861325595049243457265873 18645994196286932592949405)
    ·
      refine ⟨6992247823607599722356027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18645994196286932592949405 6992247823607599722356027)
      ·
        refine ⟨10488371735411399583534041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6992247823607599722356027 10488371735411399583534041)
        ·
          refine ⟨7866278801558549687650531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10488371735411399583534041 7866278801558549687650531)
          ·
            refine ⟨11799418202337824531475797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7866278801558549687650531 11799418202337824531475797)
            ·
              refine ⟨17284304007330797653529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11799418202337824531475797 17284304007330797653529)
              ·
                rfl

theorem cell23_2726546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 11].length) (baseStart_2726546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726546 prefixEnd_2726546 := by exact prefixLift 2726546
  have htrace : WordTrace (prefixWord ++ tailWord_2726546) baseStart_2726546 baseEnd_2726546 := by
    simpa [prefixWord, tailWord_2726546, baseEnd_2726546] using wordTrace_append hprefix tailTrace_2726546
  have hstable : (prefixWord ++ tailWord_2726546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726546).length < 2 ^ (prefixWord ++ tailWord_2726546).sum := by decide
  have hdescent : baseEnd_2726546 < baseStart_2726546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726557 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_2726557 : Nat := 118140960795 + 2726557 * 2 ^ 59
def prefixEnd_2726557 : Nat := 4983230072969 + 3 ^ 40 * 2726557 * 2
def baseEnd_2726557 : Nat := 1400034272880994066898299

theorem tailTrace_2726557 : CollatzResearch.WordTrace tailWord_2726557 prefixEnd_2726557 1400034272880994066898299 := by
  unfold tailWord_2726557
  simp only [CollatzResearch.WordTrace]
  refine ⟨99445703583157122707713925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66297135722104748471809283 99445703583157122707713925)
  ·
    refine ⟨18646069421841960507696361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99445703583157122707713925 18646069421841960507696361)
    ·
      refine ⟨13984552066381470380772271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18646069421841960507696361 13984552066381470380772271)
      ·
        refine ⟨20976828099572205571158407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13984552066381470380772271 20976828099572205571158407)
        ·
          refine ⟨31465242149358308356737611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20976828099572205571158407 31465242149358308356737611)
          ·
            refine ⟨47197863224037462535106417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31465242149358308356737611 47197863224037462535106417)
            ·
              refine ⟨35398397418028096901329813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47197863224037462535106417 35398397418028096901329813)
              ·
                refine ⟨1659299878970067042249835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35398397418028096901329813 1659299878970067042249835)
                ·
                  refine ⟨2488949818455100563374753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659299878970067042249835 2488949818455100563374753)
                  ·
                    refine ⟨1866712363841325422531065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2488949818455100563374753 1866712363841325422531065)
                    ·
                      refine ⟨1400034272880994066898299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866712363841325422531065 1400034272880994066898299)
                      ·
                        rfl

theorem cell23_2726557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_2726557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726557 prefixEnd_2726557 := by exact prefixLift 2726557
  have htrace : WordTrace (prefixWord ++ tailWord_2726557) baseStart_2726557 baseEnd_2726557 := by
    simpa [prefixWord, tailWord_2726557, baseEnd_2726557] using wordTrace_append hprefix tailTrace_2726557
  have hstable : (prefixWord ++ tailWord_2726557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726557).length < 2 ^ (prefixWord ++ tailWord_2726557).sum := by decide
  have hdescent : baseEnd_2726557 < baseStart_2726557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726567 : List Nat := [1, 1, 6, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2726567 : Nat := 118140960795 + 2726567 * 2 ^ 59
def prefixEnd_2726567 : Nat := 4983230072969 + 3 ^ 40 * 2726567 * 2
def baseEnd_2726567 : Nat := 466679802562513009257751

theorem tailTrace_2726567 : CollatzResearch.WordTrace tailWord_2726567 prefixEnd_2726567 466679802562513009257751 := by
  unfold tailWord_2726567
  simp only [CollatzResearch.WordTrace]
  refine ⟨99446068313120894415577955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66297378875413929610385303 99446068313120894415577955)
  ·
    refine ⟨149169102469681341623366933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99446068313120894415577955 149169102469681341623366933)
    ·
      refine ⟨6992301678266312888595325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149169102469681341623366933 6992301678266312888595325)
      ·
        refine ⟨2622113129349867333223247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6992301678266312888595325 2622113129349867333223247)
        ·
          refine ⟨3933169694024800999834871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2622113129349867333223247 3933169694024800999834871)
          ·
            refine ⟨5899754541037201499752307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3933169694024800999834871 5899754541037201499752307)
            ·
              refine ⟨8849631811555802249628461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5899754541037201499752307 8849631811555802249628461)
              ·
                refine ⟨3318611929333425843610673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8849631811555802249628461 3318611929333425843610673)
                ·
                  refine ⟨2488958947000069382708005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3318611929333425843610673 2488958947000069382708005)
                  ·
                    refine ⟨466679802562513009257751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2488958947000069382708005 466679802562513009257751)
                    ·
                      rfl

theorem cell23_2726567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2726567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726567 prefixEnd_2726567 := by exact prefixLift 2726567
  have htrace : WordTrace (prefixWord ++ tailWord_2726567) baseStart_2726567 baseEnd_2726567 := by
    simpa [prefixWord, tailWord_2726567, baseEnd_2726567] using wordTrace_append hprefix tailTrace_2726567
  have hstable : (prefixWord ++ tailWord_2726567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726567).length < 2 ^ (prefixWord ++ tailWord_2726567).sum := by decide
  have hdescent : baseEnd_2726567 < baseStart_2726567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726664 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_2726664 : Nat := 118140960795 + 2726664 * 2 ^ 59
def prefixEnd_2726664 : Nat := 4983230072969 + 3 ^ 40 * 2726664 * 2
def baseEnd_2726664 : Nat := 1400089215311025148260307

theorem tailTrace_2726664 : CollatzResearch.WordTrace tailWord_2726664 prefixEnd_2726664 1400089215311025148260307 := by
  unfold tailWord_2726664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49724803096884739990929523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66299737462512986654572697 49724803096884739990929523)
  ·
    refine ⟨74587204645327109986394285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49724803096884739990929523 74587204645327109986394285)
    ·
      refine ⟨27970201741997666244897857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74587204645327109986394285 27970201741997666244897857)
      ·
        refine ⟨20977651306498249683673393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27970201741997666244897857 20977651306498249683673393)
        ·
          refine ⟨15733238479873687262755045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20977651306498249683673393 15733238479873687262755045)
          ·
            refine ⟨2949982214976316361766571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15733238479873687262755045 2949982214976316361766571)
            ·
              refine ⟨4424973322464474542649857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2949982214976316361766571 4424973322464474542649857)
              ·
                refine ⟨3318729991848355906987393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4424973322464474542649857 3318729991848355906987393)
                ·
                  refine ⟨2489047493886266930240545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3318729991848355906987393 2489047493886266930240545)
                  ·
                    refine ⟨1866785620414700197680409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2489047493886266930240545 1866785620414700197680409)
                    ·
                      refine ⟨1400089215311025148260307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866785620414700197680409 1400089215311025148260307)
                      ·
                        rfl

theorem cell23_2726664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_2726664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726664 prefixEnd_2726664 := by exact prefixLift 2726664
  have htrace : WordTrace (prefixWord ++ tailWord_2726664) baseStart_2726664 baseEnd_2726664 := by
    simpa [prefixWord, tailWord_2726664, baseEnd_2726664] using wordTrace_append hprefix tailTrace_2726664
  have hstable : (prefixWord ++ tailWord_2726664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726664).length < 2 ^ (prefixWord ++ tailWord_2726664).sum := by decide
  have hdescent : baseEnd_2726664 < baseStart_2726664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726673 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 7, 2]
def baseStart_2726673 : Nat := 118140960795 + 2726673 * 2 ^ 59
def prefixEnd_2726673 : Nat := 4983230072969 + 3 ^ 40 * 2726673 * 2
def baseEnd_2726673 : Nat := 1400093836636915613047765

theorem tailTrace_2726673 : CollatzResearch.WordTrace tailWord_2726673 prefixEnd_2726673 1400093836636915613047765 := by
  unfold tailWord_2726673
  simp only [CollatzResearch.WordTrace]
  refine ⟨99449934450736874518936673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66299956300491249679291115 99449934450736874518936673)
  ·
    refine ⟨74587450838052655889202505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99449934450736874518936673 74587450838052655889202505)
    ·
      refine ⟨55940588128539491916901879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74587450838052655889202505 55940588128539491916901879)
      ·
        refine ⟨83910882192809237875352819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55940588128539491916901879 83910882192809237875352819)
        ·
          refine ⟨125866323289213856813029229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83910882192809237875352819 125866323289213856813029229)
          ·
            refine ⟨47199871233455196304885961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125866323289213856813029229 47199871233455196304885961)
            ·
              refine ⟨35399903425091397228664471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47199871233455196304885961 35399903425091397228664471)
              ·
                refine ⟨53099855137637095842996707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35399903425091397228664471 53099855137637095842996707)
                ·
                  refine ⟨79649782706455643764495061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53099855137637095842996707 79649782706455643764495061)
                  ·
                    refine ⟨1866791782182554150730353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79649782706455643764495061 1866791782182554150730353)
                    ·
                      refine ⟨1400093836636915613047765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866791782182554150730353 1400093836636915613047765)
                      ·
                        rfl

theorem cell23_2726673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_2726673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726673 prefixEnd_2726673 := by exact prefixLift 2726673
  have htrace : WordTrace (prefixWord ++ tailWord_2726673) baseStart_2726673 baseEnd_2726673 := by
    simpa [prefixWord, tailWord_2726673, baseEnd_2726673] using wordTrace_append hprefix tailTrace_2726673
  have hstable : (prefixWord ++ tailWord_2726673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726673).length < 2 ^ (prefixWord ++ tailWord_2726673).sum := by decide
  have hdescent : baseEnd_2726673 < baseStart_2726673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726820 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_2726820 : Nat := 118140960795 + 2726820 * 2 ^ 59
def prefixEnd_2726820 : Nat := 4983230072969 + 3 ^ 40 * 2726820 * 2
def baseEnd_2726820 : Nat := 466723106097708845969863

theorem tailTrace_2726820 : CollatzResearch.WordTrace tailWord_2726820 prefixEnd_2726820 466723106097708845969863 := by
  unfold tailWord_2726820
  simp only [CollatzResearch.WordTrace]
  refine ⟨49727647990602159312268957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66303530654136212416358609 49727647990602159312268957)
  ·
    refine ⟨18647867996475809742100859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49727647990602159312268957 18647867996475809742100859)
    ·
      refine ⟨27971801994713714613151289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18647867996475809742100859 27971801994713714613151289)
      ·
        refine ⟨20978851496035285959863467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27971801994713714613151289 20978851496035285959863467)
        ·
          refine ⟨31468277244052928939795201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20978851496035285959863467 31468277244052928939795201)
          ·
            refine ⟨23601207933039696704846401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31468277244052928939795201 23601207933039696704846401)
            ·
              refine ⟨17700905949779772528634801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23601207933039696704846401 17700905949779772528634801)
              ·
                refine ⟨13275679462334829396476101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17700905949779772528634801 13275679462334829396476101)
                ·
                  refine ⟨2489189899187780511839269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13275679462334829396476101 2489189899187780511839269)
                  ·
                    refine ⟨466723106097708845969863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489189899187780511839269 466723106097708845969863)
                    ·
                      rfl

theorem cell23_2726820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_2726820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726820 prefixEnd_2726820 := by exact prefixLift 2726820
  have htrace : WordTrace (prefixWord ++ tailWord_2726820) baseStart_2726820 baseEnd_2726820 := by
    simpa [prefixWord, tailWord_2726820, baseEnd_2726820] using wordTrace_append hprefix tailTrace_2726820
  have hstable : (prefixWord ++ tailWord_2726820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726820).length < 2 ^ (prefixWord ++ tailWord_2726820).sum := by decide
  have hdescent : baseEnd_2726820 < baseStart_2726820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726917 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 1, 4, 2]
def baseStart_2726917 : Nat := 118140960795 + 2726917 * 2 ^ 59
def prefixEnd_2726917 : Nat := 4983230072969 + 3 ^ 40 * 2726917 * 2
def baseEnd_2726917 : Nat := 1400219125916612658396643

theorem tailTrace_2726917 : CollatzResearch.WordTrace tailWord_2726917 prefixEnd_2726917 1400219125916612658396643 := by
  unfold tailWord_2726917
  simp only [CollatzResearch.WordTrace]
  refine ⟨99458833861852904190819005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66305889241235269460546003 99458833861852904190819005)
  ·
    refine ⟨37297062698194839071557127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99458833861852904190819005 37297062698194839071557127)
    ·
      refine ⟨55945594047292258607335691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37297062698194839071557127 55945594047292258607335691)
      ·
        refine ⟨83918391070938387911003537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55945594047292258607335691 83918391070938387911003537)
        ·
          refine ⟨62938793303203790933252653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83918391070938387911003537 62938793303203790933252653)
          ·
            refine ⟨23602047488701421599969745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62938793303203790933252653 23602047488701421599969745)
            ·
              refine ⟨17701535616526066199977309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23602047488701421599969745 17701535616526066199977309)
              ·
                refine ⟨6638075856197274824991491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17701535616526066199977309 6638075856197274824991491)
                ·
                  refine ⟨9957113784295912237487237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6638075856197274824991491 9957113784295912237487237)
                  ·
                    refine ⟨1866958834555483544528857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9957113784295912237487237 1866958834555483544528857)
                    ·
                      refine ⟨1400219125916612658396643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1866958834555483544528857 1400219125916612658396643)
                      ·
                        rfl

theorem cell23_2726917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_2726917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726917 prefixEnd_2726917 := by exact prefixLift 2726917
  have htrace : WordTrace (prefixWord ++ tailWord_2726917) baseStart_2726917 baseEnd_2726917 := by
    simpa [prefixWord, tailWord_2726917, baseEnd_2726917] using wordTrace_append hprefix tailTrace_2726917
  have hstable : (prefixWord ++ tailWord_2726917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726917).length < 2 ^ (prefixWord ++ tailWord_2726917).sum := by decide
  have hdescent : baseEnd_2726917 < baseStart_2726917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726920 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2726920 : Nat := 118140960795 + 2726920 * 2 ^ 59
def prefixEnd_2726920 : Nat := 4983230072969 + 3 ^ 40 * 2726920 * 2
def baseEnd_2726920 : Nat := 1400220666358576146659129

theorem tailTrace_2726920 : CollatzResearch.WordTrace tailWord_2726920 prefixEnd_2726920 1400220666358576146659129 := by
  unfold tailWord_2726920
  simp only [CollatzResearch.WordTrace]
  refine ⟨49729471640421017851589107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66305962187228023802118809 49729471640421017851589107)
  ·
    refine ⟨74594207460631526777383661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49729471640421017851589107 74594207460631526777383661)
    ·
      refine ⟨27972827797736822541518873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74594207460631526777383661 27972827797736822541518873)
      ·
        refine ⟨20979620848302616906139155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27972827797736822541518873 20979620848302616906139155)
        ·
          refine ⟨31469431272453925359208733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20979620848302616906139155 31469431272453925359208733)
          ·
            refine ⟨11801036727170222009703275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31469431272453925359208733 11801036727170222009703275)
            ·
              refine ⟨17701555090755333014554913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11801036727170222009703275 17701555090755333014554913)
              ·
                refine ⟨13276166318066499760916185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17701555090755333014554913 13276166318066499760916185)
                ·
                  refine ⟨9957124738549874820687139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13276166318066499760916185 9957124738549874820687139)
                  ·
                    refine ⟨14935687107824812231030709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9957124738549874820687139 14935687107824812231030709)
                    ·
                      refine ⟨1400220666358576146659129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14935687107824812231030709 1400220666358576146659129)
                      ·
                        rfl

theorem cell23_2726920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2726920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726920 prefixEnd_2726920 := by exact prefixLift 2726920
  have htrace : WordTrace (prefixWord ++ tailWord_2726920) baseStart_2726920 baseEnd_2726920 := by
    simpa [prefixWord, tailWord_2726920, baseEnd_2726920] using wordTrace_append hprefix tailTrace_2726920
  have hstable : (prefixWord ++ tailWord_2726920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726920).length < 2 ^ (prefixWord ++ tailWord_2726920).sum := by decide
  have hdescent : baseEnd_2726920 < baseStart_2726920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726964 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2726964 : Nat := 118140960795 + 2726964 * 2 ^ 59
def prefixEnd_2726964 : Nat := 4983230072969 + 3 ^ 40 * 2726964 * 2
def baseEnd_2726964 : Nat := 1400243259507373974508927

theorem tailTrace_2726964 : CollatzResearch.WordTrace tailWord_2726964 prefixEnd_2726964 1400243259507373974508927 := by
  unfold tailWord_2726964
  simp only [CollatzResearch.WordTrace]
  refine ⟨49730274046341315608889973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66307032061788420811853297 49730274046341315608889973)
  ·
    refine ⟨4662213191844498338333435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49730274046341315608889973 4662213191844498338333435)
    ·
      refine ⟨6993319787766747507500153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662213191844498338333435 6993319787766747507500153)
      ·
        refine ⟨5244989840825060630625115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6993319787766747507500153 5244989840825060630625115)
        ·
          refine ⟨7867484761237590945937673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244989840825060630625115 7867484761237590945937673)
          ·
            refine ⟨5900613570928193209453255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7867484761237590945937673 5900613570928193209453255)
            ·
              refine ⟨8850920356392289814179883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5900613570928193209453255 8850920356392289814179883)
              ·
                refine ⟨13276380534588434721269825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8850920356392289814179883 13276380534588434721269825)
                ·
                  refine ⟨9957285400941326040952369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13276380534588434721269825 9957285400941326040952369)
                  ·
                    refine ⟨7467964050705994530714277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9957285400941326040952369 7467964050705994530714277)
                    ·
                      refine ⟨1400243259507373974508927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7467964050705994530714277 1400243259507373974508927)
                      ·
                        rfl

theorem cell23_2726964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2726964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726964 prefixEnd_2726964 := by exact prefixLift 2726964
  have htrace : WordTrace (prefixWord ++ tailWord_2726964) baseStart_2726964 baseEnd_2726964 := by
    simpa [prefixWord, tailWord_2726964, baseEnd_2726964] using wordTrace_append hprefix tailTrace_2726964
  have hstable : (prefixWord ++ tailWord_2726964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726964).length < 2 ^ (prefixWord ++ tailWord_2726964).sum := by decide
  have hdescent : baseEnd_2726964 < baseStart_2726964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2726970 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_2726970 : Nat := 118140960795 + 2726970 * 2 ^ 59
def prefixEnd_2726970 : Nat := 4983230072969 + 3 ^ 40 * 2726970 * 2
def baseEnd_2726970 : Nat := 466748780130433650344633

theorem tailTrace_2726970 : CollatzResearch.WordTrace tailWord_2726970 prefixEnd_2726970 466748780130433650344633 := by
  unfold tailWord_2726970
  simp only [CollatzResearch.WordTrace]
  refine ⟨24865191732665223560624591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66307177953773929494998909 24865191732665223560624591)
  ·
    refine ⟨37297787598997835340936887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24865191732665223560624591 37297787598997835340936887)
    ·
      refine ⟨55946681398496753011405331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37297787598997835340936887 55946681398496753011405331)
      ·
        refine ⟨83920022097745129517107997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55946681398496753011405331 83920022097745129517107997)
        ·
          refine ⟨31470008286654423568915499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83920022097745129517107997 31470008286654423568915499)
          ·
            refine ⟨47205012429981635353373249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31470008286654423568915499 47205012429981635353373249)
            ·
              refine ⟨35403759322486226515029937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47205012429981635353373249 35403759322486226515029937)
              ·
                refine ⟨26552819491864669886272453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35403759322486226515029937 26552819491864669886272453)
                ·
                  refine ⟨4978653654724625603676085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26552819491864669886272453 4978653654724625603676085)
                  ·
                    refine ⟨466748780130433650344633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4978653654724625603676085 466748780130433650344633)
                    ·
                      rfl

theorem cell23_2726970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_2726970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2726970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2726970 prefixEnd_2726970 := by exact prefixLift 2726970
  have htrace : WordTrace (prefixWord ++ tailWord_2726970) baseStart_2726970 baseEnd_2726970 := by
    simpa [prefixWord, tailWord_2726970, baseEnd_2726970] using wordTrace_append hprefix tailTrace_2726970
  have hstable : (prefixWord ++ tailWord_2726970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2726970).length < 2 ^ (prefixWord ++ tailWord_2726970).sum := by decide
  have hdescent : baseEnd_2726970 < baseStart_2726970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2726970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727007 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 4, 4, 2]
def baseStart_2727007 : Nat := 118140960795 + 2727007 * 2 ^ 59
def prefixEnd_2727007 : Nat := 4983230072969 + 3 ^ 40 * 2727007 * 2
def baseEnd_2727007 : Nat := 1400265339175517306271229

theorem tailTrace_2727007 : CollatzResearch.WordTrace tailWord_2727007 prefixEnd_2727007 1400265339175517306271229 := by
  unfold tailWord_2727007
  simp only [CollatzResearch.WordTrace]
  refine ⟨99462116431526849561595275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66308077621017899707730183 99462116431526849561595275)
  ·
    refine ⟨149193174647290274342392913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99462116431526849561595275 149193174647290274342392913)
    ·
      refine ⟨111894880985467705756794685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149193174647290274342392913 111894880985467705756794685)
      ·
        refine ⟨41960580369550389658798007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111894880985467705756794685 41960580369550389658798007)
        ·
          refine ⟨62940870554325584488197011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41960580369550389658798007 62940870554325584488197011)
          ·
            refine ⟨94411305831488376732295517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62940870554325584488197011 94411305831488376732295517)
            ·
              refine ⟨35404239686808141274610819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94411305831488376732295517 35404239686808141274610819)
              ·
                refine ⟨53106359530212211911916229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35404239686808141274610819 53106359530212211911916229)
                ·
                  refine ⟨9957442411914789733484293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53106359530212211911916229 9957442411914789733484293)
                  ·
                    refine ⟨1867020452234023075028305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9957442411914789733484293 1867020452234023075028305)
                    ·
                      refine ⟨1400265339175517306271229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867020452234023075028305 1400265339175517306271229)
                      ·
                        rfl

theorem cell23_2727007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_2727007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727007 prefixEnd_2727007 := by exact prefixLift 2727007
  have htrace : WordTrace (prefixWord ++ tailWord_2727007) baseStart_2727007 baseEnd_2727007 := by
    simpa [prefixWord, tailWord_2727007, baseEnd_2727007] using wordTrace_append hprefix tailTrace_2727007
  have hstable : (prefixWord ++ tailWord_2727007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727007).length < 2 ^ (prefixWord ++ tailWord_2727007).sum := by decide
  have hdescent : baseEnd_2727007 < baseStart_2727007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727017 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 3, 4]
def baseStart_2727017 : Nat := 118140960795 + 2727017 * 2 ^ 59
def prefixEnd_2727017 : Nat := 4983230072969 + 3 ^ 40 * 2727017 * 2
def baseEnd_2727017 : Nat := 466756824660687422382061

theorem tailTrace_2727017 : CollatzResearch.WordTrace tailWord_2727017 prefixEnd_2727017 466756824660687422382061 := by
  unfold tailWord_2727017
  simp only [CollatzResearch.WordTrace]
  refine ⟨99462481161490621269459305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66308320774327080846306203 99462481161490621269459305)
  ·
    refine ⟨74596860871117965952094479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99462481161490621269459305 74596860871117965952094479)
    ·
      refine ⟨111895291306676948928141719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74596860871117965952094479 111895291306676948928141719)
      ·
        refine ⟨167842936960015423392212579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111895291306676948928141719 167842936960015423392212579)
        ·
          refine ⟨251764405440023135088318869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167842936960015423392212579 251764405440023135088318869)
          ·
            refine ⟨11801456505001084457264947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 251764405440023135088318869 11801456505001084457264947)
            ·
              refine ⟨17702184757501626685897421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11801456505001084457264947 17702184757501626685897421)
              ·
                refine ⟨6638319284063110007211533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17702184757501626685897421 6638319284063110007211533)
                ·
                  refine ⟨2489369731523666252704325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6638319284063110007211533 2489369731523666252704325)
                  ·
                    refine ⟨466756824660687422382061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489369731523666252704325 466756824660687422382061)
                    ·
                      rfl

theorem cell23_2727017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_2727017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727017 prefixEnd_2727017 := by exact prefixLift 2727017
  have htrace : WordTrace (prefixWord ++ tailWord_2727017) baseStart_2727017 baseEnd_2727017 := by
    simpa [prefixWord, tailWord_2727017, baseEnd_2727017] using wordTrace_append hprefix tailTrace_2727017
  have hstable : (prefixWord ++ tailWord_2727017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727017).length < 2 ^ (prefixWord ++ tailWord_2727017).sum := by decide
  have hdescent : baseEnd_2727017 < baseStart_2727017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727020 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2727020 : Nat := 118140960795 + 2727020 * 2 ^ 59
def prefixEnd_2727020 : Nat := 4983230072969 + 3 ^ 40 * 2727020 * 2
def baseEnd_2727020 : Nat := 1400272014424025755408669

theorem tailTrace_2727020 : CollatzResearch.WordTrace tailWord_2727020 prefixEnd_2727020 1400272014424025755408669 := by
  unfold tailWord_2727020
  simp only [CollatzResearch.WordTrace]
  refine ⟨49731295290239876390909257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66308393720319835187879009 49731295290239876390909257)
  ·
    refine ⟨37298471467679907293181943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49731295290239876390909257 37298471467679907293181943)
    ·
      refine ⟨55947707201519860939772915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37298471467679907293181943 55947707201519860939772915)
      ·
        refine ⟨83921560802279791409659373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55947707201519860939772915 83921560802279791409659373)
        ·
          refine ⟨31470585300854921778622265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83921560802279791409659373 31470585300854921778622265)
          ·
            refine ⟨23602938975641191333966699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31470585300854921778622265 23602938975641191333966699)
            ·
              refine ⟨35404408463461787000950049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23602938975641191333966699 35404408463461787000950049)
              ·
                refine ⟨26553306347596340250712537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35404408463461787000950049 26553306347596340250712537)
                ·
                  refine ⟨19914979760697255188034403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26553306347596340250712537 19914979760697255188034403)
                  ·
                    refine ⟨29872469641045882782051605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19914979760697255188034403 29872469641045882782051605)
                    ·
                      refine ⟨1400272014424025755408669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29872469641045882782051605 1400272014424025755408669)
                      ·
                        rfl

theorem cell23_2727020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2727020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727020 prefixEnd_2727020 := by exact prefixLift 2727020
  have htrace : WordTrace (prefixWord ++ tailWord_2727020) baseStart_2727020 baseEnd_2727020 := by
    simpa [prefixWord, tailWord_2727020, baseEnd_2727020] using wordTrace_append hprefix tailTrace_2727020
  have hstable : (prefixWord ++ tailWord_2727020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727020).length < 2 ^ (prefixWord ++ tailWord_2727020).sum := by decide
  have hdescent : baseEnd_2727020 < baseStart_2727020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727067 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 5, 5, 2]
def baseStart_2727067 : Nat := 118140960795 + 2727067 * 2 ^ 59
def prefixEnd_2727067 : Nat := 4983230072969 + 3 ^ 40 * 2727067 * 2
def baseEnd_2727067 : Nat := 1400296148014787071520953

theorem tailTrace_2727067 : CollatzResearch.WordTrace tailWord_2727067 prefixEnd_2727067 1400296148014787071520953 := by
  unfold tailWord_2727067
  simp only [CollatzResearch.WordTrace]
  refine ⟨99464304811309479808779455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66309536540872986539186303 99464304811309479808779455)
  ·
    refine ⟨149196457216964219713169183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99464304811309479808779455 149196457216964219713169183)
    ·
      refine ⟨223794685825446329569753775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149196457216964219713169183 223794685825446329569753775)
      ·
        refine ⟨335692028738169494354630663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223794685825446329569753775 335692028738169494354630663)
        ·
          refine ⟨503538043107254241531945995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335692028738169494354630663 503538043107254241531945995)
          ·
            refine ⟨755307064660881362297918993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503538043107254241531945995 755307064660881362297918993)
            ·
              refine ⟨566480298495661021723439245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755307064660881362297918993 566480298495661021723439245)
              ·
                refine ⟨212430111935872883146289717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566480298495661021723439245 212430111935872883146289717)
                ·
                  refine ⟨19915322993988082794964661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212430111935872883146289717 19915322993988082794964661)
                  ·
                    refine ⟨1867061530686382762027937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19915322993988082794964661 1867061530686382762027937)
                    ·
                      refine ⟨1400296148014787071520953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867061530686382762027937 1400296148014787071520953)
                      ·
                        rfl

theorem cell23_2727067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 5, 2].length) (baseStart_2727067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727067 prefixEnd_2727067 := by exact prefixLift 2727067
  have htrace : WordTrace (prefixWord ++ tailWord_2727067) baseStart_2727067 baseEnd_2727067 := by
    simpa [prefixWord, tailWord_2727067, baseEnd_2727067] using wordTrace_append hprefix tailTrace_2727067
  have hstable : (prefixWord ++ tailWord_2727067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727067).length < 2 ^ (prefixWord ++ tailWord_2727067).sum := by decide
  have hdescent : baseEnd_2727067 < baseStart_2727067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727068 : List Nat := [2, 2, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2727068 : Nat := 118140960795 + 2727068 * 2 ^ 59
def prefixEnd_2727068 : Nat := 4983230072969 + 3 ^ 40 * 2727068 * 2
def baseEnd_2727068 : Nat := 466765553831813855869483

theorem tailTrace_2727068 : CollatzResearch.WordTrace tailWord_2727068 prefixEnd_2727068 466765553831813855869483 := by
  unfold tailWord_2727068
  simp only [CollatzResearch.WordTrace]
  refine ⟨49732170642152928489782929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66309560856203904653043905 49732170642152928489782929)
  ·
    refine ⟨37299127981614696367337197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49732170642152928489782929 37299127981614696367337197)
    ·
      refine ⟨13987172993105511137751449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37299127981614696367337197 13987172993105511137751449)
      ·
        refine ⟨10490379744829133353313587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13987172993105511137751449 10490379744829133353313587)
        ·
          refine ⟨15735569617243700029970381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10490379744829133353313587 15735569617243700029970381)
          ·
            refine ⟨5900838606466387511238893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15735569617243700029970381 5900838606466387511238893)
            ·
              refine ⟨2212814477424895316714585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5900838606466387511238893 2212814477424895316714585)
              ·
                refine ⟨1659610858068671487535939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212814477424895316714585 1659610858068671487535939)
                ·
                  refine ⟨2489416287103007231303909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659610858068671487535939 2489416287103007231303909)
                  ·
                    refine ⟨466765553831813855869483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489416287103007231303909 466765553831813855869483)
                    ·
                      rfl

theorem cell23_2727068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2727068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727068 prefixEnd_2727068 := by exact prefixLift 2727068
  have htrace : WordTrace (prefixWord ++ tailWord_2727068) baseStart_2727068 baseEnd_2727068 := by
    simpa [prefixWord, tailWord_2727068, baseEnd_2727068] using wordTrace_append hprefix tailTrace_2727068
  have hstable : (prefixWord ++ tailWord_2727068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727068).length < 2 ^ (prefixWord ++ tailWord_2727068).sum := by decide
  have hdescent : baseEnd_2727068 < baseStart_2727068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727107 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 4, 4]
def baseStart_2727107 : Nat := 118140960795 + 2727107 * 2 ^ 59
def prefixEnd_2727107 : Nat := 4983230072969 + 3 ^ 40 * 2727107 * 2
def baseEnd_2727107 : Nat := 466772229080322305006923

theorem tailTrace_2727107 : CollatzResearch.WordTrace tailWord_2727107 prefixEnd_2727107 466772229080322305006923 := by
  unfold tailWord_2727107
  simp only [CollatzResearch.WordTrace]
  refine ⟨99465763731164566640235575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66310509154109711093490383 99465763731164566640235575)
  ·
    refine ⟨149198645596746849960353363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99465763731164566640235575 149198645596746849960353363)
    ·
      refine ⟨223797968395120274940530045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149198645596746849960353363 223797968395120274940530045)
      ·
        refine ⟨83924238148170103102698767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223797968395120274940530045 83924238148170103102698767)
        ·
          refine ⟨125886357222255154654048151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83924238148170103102698767 125886357222255154654048151)
          ·
            refine ⟨188829535833382731981072227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125886357222255154654048151 188829535833382731981072227)
            ·
              refine ⟨283244303750074097971608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188829535833382731981072227 283244303750074097971608341)
              ·
                refine ⟨13277076738284723342419141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283244303750074097971608341 13277076738284723342419141)
                ·
                  refine ⟨2489451888428385626703589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13277076738284723342419141 2489451888428385626703589)
                  ·
                    refine ⟨466772229080322305006923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489451888428385626703589 466772229080322305006923)
                    ·
                      rfl

theorem cell23_2727107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 4].length) (baseStart_2727107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727107 prefixEnd_2727107 := by exact prefixLift 2727107
  have htrace : WordTrace (prefixWord ++ tailWord_2727107) baseStart_2727107 baseEnd_2727107 := by
    simpa [prefixWord, tailWord_2727107, baseEnd_2727107] using wordTrace_append hprefix tailTrace_2727107
  have hstable : (prefixWord ++ tailWord_2727107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727107).length < 2 ^ (prefixWord ++ tailWord_2727107).sum := by decide
  have hdescent : baseEnd_2727107 < baseStart_2727107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727125 : List Nat := [1, 3, 2, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2727125 : Nat := 118140960795 + 2727125 * 2 ^ 59
def prefixEnd_2727125 : Nat := 4983230072969 + 3 ^ 40 * 2727125 * 2
def baseEnd_2727125 : Nat := 1400325929892747844595687

theorem tailTrace_2727125 : CollatzResearch.WordTrace tailWord_2727125 prefixEnd_2727125 1400325929892747844595687 := by
  unfold tailWord_2727125
  simp only [CollatzResearch.WordTrace]
  refine ⟨99466420245099355714390829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66310946830066237142927219 99466420245099355714390829)
  ·
    refine ⟨37299907591912258392896561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99466420245099355714390829 37299907591912258392896561)
    ·
      refine ⟨27974930693934193794672421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37299907591912258392896561 27974930693934193794672421)
      ·
        refine ⟨5245299505112661336501079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27974930693934193794672421 5245299505112661336501079)
        ·
          refine ⟨7867949257668992004751619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245299505112661336501079 7867949257668992004751619)
          ·
            refine ⟨11801923886503488007127429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867949257668992004751619 11801923886503488007127429)
            ·
              refine ⟨2212860728719404001336393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11801923886503488007127429 2212860728719404001336393)
              ·
                refine ⟨1659645546539553001002295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2212860728719404001336393 1659645546539553001002295)
                ·
                  refine ⟨2489468319809329501503443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659645546539553001002295 2489468319809329501503443)
                  ·
                    refine ⟨3734202479713994252255165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2489468319809329501503443 3734202479713994252255165)
                    ·
                      refine ⟨1400325929892747844595687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3734202479713994252255165 1400325929892747844595687)
                      ·
                        rfl

theorem cell23_2727125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2727125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727125 prefixEnd_2727125 := by exact prefixLift 2727125
  have htrace : WordTrace (prefixWord ++ tailWord_2727125) baseStart_2727125 baseEnd_2727125 := by
    simpa [prefixWord, tailWord_2727125, baseEnd_2727125] using wordTrace_append hprefix tailTrace_2727125
  have hstable : (prefixWord ++ tailWord_2727125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727125).length < 2 ^ (prefixWord ++ tailWord_2727125).sum := by decide
  have hdescent : baseEnd_2727125 < baseStart_2727125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727137 : List Nat := [1, 2, 3, 1, 3, 2, 3, 8]
def baseStart_2727137 : Nat := 118140960795 + 2727137 * 2 ^ 59
def prefixEnd_2727137 : Nat := 4983230072969 + 3 ^ 40 * 2727137 * 2
def baseEnd_2727137 : Nat := 51864151542985251764653

theorem tailTrace_2727137 : CollatzResearch.WordTrace tailWord_2727137 prefixEnd_2727137 51864151542985251764653 := by
  unfold tailWord_2727137
  simp only [CollatzResearch.WordTrace]
  refine ⟨99466857921055881763827665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66311238614037254509218443 99466857921055881763827665)
  ·
    refine ⟨74600143440791911322870749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99466857921055881763827665 74600143440791911322870749)
    ·
      refine ⟨27975053790296966746076531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74600143440791911322870749 27975053790296966746076531)
      ·
        refine ⟨41962580685445450119114797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27975053790296966746076531 41962580685445450119114797)
        ·
          refine ⟨15735967757042043794668049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41962580685445450119114797 15735967757042043794668049)
          ·
            refine ⟨11801975817781532846001037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15735967757042043794668049 11801975817781532846001037)
            ·
              refine ⟨4425740931668074817250389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11801975817781532846001037 4425740931668074817250389)
              ·
                refine ⟨51864151542985251764653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4425740931668074817250389 51864151542985251764653)
                ·
                  rfl

theorem cell23_2727137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 8].length) (baseStart_2727137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727137 prefixEnd_2727137 := by exact prefixLift 2727137
  have htrace : WordTrace (prefixWord ++ tailWord_2727137) baseStart_2727137 baseEnd_2727137 := by
    simpa [prefixWord, tailWord_2727137, baseEnd_2727137] using wordTrace_append hprefix tailTrace_2727137
  have hstable : (prefixWord ++ tailWord_2727137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727137).length < 2 ^ (prefixWord ++ tailWord_2727137).sum := by decide
  have hdescent : baseEnd_2727137 < baseStart_2727137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727144 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2727144 : Nat := 118140960795 + 2727144 * 2 ^ 59
def prefixEnd_2727144 : Nat := 4983230072969 + 3 ^ 40 * 2727144 * 2
def baseEnd_2727144 : Nat := 1400335686025183270258099

theorem tailTrace_2727144 : CollatzResearch.WordTrace tailWord_2727144 prefixEnd_2727144 1400335686025183270258099 := by
  unfold tailWord_2727144
  simp only [CollatzResearch.WordTrace]
  refine ⟨49733556616015260979666243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66311408821353681306221657 49733556616015260979666243)
  ·
    refine ⟨74600334924022891469499365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49733556616015260979666243 74600334924022891469499365)
    ·
      refine ⟨13987562798254292150531131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74600334924022891469499365 13987562798254292150531131)
      ·
        refine ⟨20981344197381438225796697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13987562798254292150531131 20981344197381438225796697)
        ·
          refine ⟨15736008148036078669347523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20981344197381438225796697 15736008148036078669347523)
          ·
            refine ⟨23604012222054118004021285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15736008148036078669347523 23604012222054118004021285)
            ·
              refine ⟨4425752291635147125753991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23604012222054118004021285 4425752291635147125753991)
              ·
                refine ⟨6638628437452720688630987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425752291635147125753991 6638628437452720688630987)
                ·
                  refine ⟨9957942656179081032946481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6638628437452720688630987 9957942656179081032946481)
                  ·
                    refine ⟨7468456992134310774709861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9957942656179081032946481 7468456992134310774709861)
                    ·
                      refine ⟨1400335686025183270258099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7468456992134310774709861 1400335686025183270258099)
                      ·
                        rfl

theorem cell23_2727144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2727144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727144 prefixEnd_2727144 := by exact prefixLift 2727144
  have htrace : WordTrace (prefixWord ++ tailWord_2727144) baseStart_2727144 baseEnd_2727144 := by
    simpa [prefixWord, tailWord_2727144, baseEnd_2727144] using wordTrace_append hprefix tailTrace_2727144
  have hstable : (prefixWord ++ tailWord_2727144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727144).length < 2 ^ (prefixWord ++ tailWord_2727144).sum := by decide
  have hdescent : baseEnd_2727144 < baseStart_2727144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727208 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_2727208 : Nat := 118140960795 + 2727208 * 2 ^ 59
def prefixEnd_2727208 : Nat := 4983230072969 + 3 ^ 40 * 2727208 * 2
def baseEnd_2727208 : Nat := 1400368548787071019857805

theorem tailTrace_2727208 : CollatzResearch.WordTrace tailWord_2727208 prefixEnd_2727208 1400368548787071019857805 := by
  unfold tailWord_2727208
  simp only [CollatzResearch.WordTrace]
  refine ⟨49734723751899330444831139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66312965002532440593108185 49734723751899330444831139)
  ·
    refine ⟨74602085627848995667246709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49734723751899330444831139 74602085627848995667246709)
    ·
      refine ⟨6993945527610843343804379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74602085627848995667246709 6993945527610843343804379)
      ·
        refine ⟨10490918291416265015706569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993945527610843343804379 10490918291416265015706569)
        ·
          refine ⟨7868188718562198761779927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10490918291416265015706569 7868188718562198761779927)
          ·
            refine ⟨11802283077843298142669891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868188718562198761779927 11802283077843298142669891)
            ·
              refine ⟨17703424616764947214004837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11802283077843298142669891 17703424616764947214004837)
              ·
                refine ⟨3319392115643427602625907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17703424616764947214004837 3319392115643427602625907)
                ·
                  refine ⟨4979088173465141403938861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319392115643427602625907 4979088173465141403938861)
                  ·
                    refine ⟨1867158065049428026477073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4979088173465141403938861 1867158065049428026477073)
                    ·
                      refine ⟨1400368548787071019857805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867158065049428026477073 1400368548787071019857805)
                      ·
                        rfl

theorem cell23_2727208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_2727208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727208 prefixEnd_2727208 := by exact prefixLift 2727208
  have htrace : WordTrace (prefixWord ++ tailWord_2727208) baseStart_2727208 baseEnd_2727208 := by
    simpa [prefixWord, tailWord_2727208, baseEnd_2727208] using wordTrace_append hprefix tailTrace_2727208
  have hstable : (prefixWord ++ tailWord_2727208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727208).length < 2 ^ (prefixWord ++ tailWord_2727208).sum := by decide
  have hdescent : baseEnd_2727208 < baseStart_2727208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727244 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 7]
def baseStart_2727244 : Nat := 118140960795 + 2727244 * 2 ^ 59
def prefixEnd_2727244 : Nat := 4983230072969 + 3 ^ 40 * 2727244 * 2
def baseEnd_2727244 : Nat := 155598559343403653223071

theorem tailTrace_2727244 : CollatzResearch.WordTrace tailWord_2727244 prefixEnd_2727244 155598559343403653223071 := by
  unfold tailWord_2727244
  simp only [CollatzResearch.WordTrace]
  refine ⟨49735380265834119518986393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66313840354445492691981857 49735380265834119518986393)
  ·
    refine ⟨37301535199375589639239795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49735380265834119518986393 37301535199375589639239795)
    ·
      refine ⟨55952302799063384458859693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37301535199375589639239795 55952302799063384458859693)
      ·
        refine ⟨20982113549648769172072385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55952302799063384458859693 20982113549648769172072385)
        ·
          refine ⟨15736585162236576879054289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20982113549648769172072385 15736585162236576879054289)
          ·
            refine ⟨11802438871677432659290717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15736585162236576879054289 11802438871677432659290717)
            ·
              refine ⟨4425914576879037247234019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11802438871677432659290717 4425914576879037247234019)
              ·
                refine ⟨6638871865318555870851029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4425914576879037247234019 6638871865318555870851029)
                ·
                  refine ⟨155598559343403653223071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6638871865318555870851029 155598559343403653223071)
                  ·
                    rfl

theorem cell23_2727244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_2727244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727244 prefixEnd_2727244 := by exact prefixLift 2727244
  have htrace : WordTrace (prefixWord ++ tailWord_2727244) baseStart_2727244 baseEnd_2727244 := by
    simpa [prefixWord, tailWord_2727244, baseEnd_2727244] using wordTrace_append hprefix tailTrace_2727244
  have hstable : (prefixWord ++ tailWord_2727244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727244).length < 2 ^ (prefixWord ++ tailWord_2727244).sum := by decide
  have hdescent : baseEnd_2727244 < baseStart_2727244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727255 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 2, 2, 2]
def baseStart_2727255 : Nat := 118140960795 + 2727255 * 2 ^ 59
def prefixEnd_2727255 : Nat := 4983230072969 + 3 ^ 40 * 2727255 * 2
def baseEnd_2727255 : Nat := 1400392682377832335970089

theorem tailTrace_2727255 : CollatzResearch.WordTrace tailWord_2727255 prefixEnd_2727255 1400392682377832335970089 := by
  unfold tailWord_2727255
  simp only [CollatzResearch.WordTrace]
  refine ⟨99471161734628387916623219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66314107823085591944415479 99471161734628387916623219)
  ·
    refine ⟨149206742601942581874934829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99471161734628387916623219 149206742601942581874934829)
    ·
      refine ⟨55952528475728468203100561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149206742601942581874934829 55952528475728468203100561)
      ·
        refine ⟨41964396356796351152325421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55952528475728468203100561 41964396356796351152325421)
        ·
          refine ⟨15736648633798631682122033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41964396356796351152325421 15736648633798631682122033)
          ·
            refine ⟨11802486475348973761591525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15736648633798631682122033 11802486475348973761591525)
            ·
              refine ⟨2212966214127932580298411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11802486475348973761591525 2212966214127932580298411)
              ·
                refine ⟨3319449321191898870447617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2212966214127932580298411 3319449321191898870447617)
                ·
                  refine ⟨2489586990893924152835713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3319449321191898870447617 2489586990893924152835713)
                  ·
                    refine ⟨1867190243170443114626785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2489586990893924152835713 1867190243170443114626785)
                    ·
                      refine ⟨1400392682377832335970089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867190243170443114626785 1400392682377832335970089)
                      ·
                        rfl

theorem cell23_2727255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_2727255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727255 prefixEnd_2727255 := by exact prefixLift 2727255
  have htrace : WordTrace (prefixWord ++ tailWord_2727255) baseStart_2727255 baseEnd_2727255 := by
    simpa [prefixWord, tailWord_2727255, baseEnd_2727255] using wordTrace_append hprefix tailTrace_2727255
  have hstable : (prefixWord ++ tailWord_2727255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727255).length < 2 ^ (prefixWord ++ tailWord_2727255).sum := by decide
  have hdescent : baseEnd_2727255 < baseStart_2727255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727257 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 3, 7]
def baseStart_2727257 : Nat := 118140960795 + 2727257 * 2 ^ 59
def prefixEnd_2727257 : Nat := 4983230072969 + 3 ^ 40 * 2727257 * 2
def baseEnd_2727257 : Nat := 466797903113047109381693

theorem tailTrace_2727257 : CollatzResearch.WordTrace tailWord_2727257 prefixEnd_2727257 466797903113047109381693 := by
  unfold tailWord_2727257
  simp only [CollatzResearch.WordTrace]
  refine ⟨99471234680621142258196025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66314156453747428172130683 99471234680621142258196025)
  ·
    refine ⟨74603426010465856693647019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99471234680621142258196025 74603426010465856693647019)
    ·
      refine ⟨111905139015698785040470529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74603426010465856693647019 111905139015698785040470529)
      ·
        refine ⟨83928854261774088780352897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111905139015698785040470529 83928854261774088780352897)
        ·
          refine ⟨62946640696330566585264673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83928854261774088780352897 62946640696330566585264673)
          ·
            refine ⟨47209980522247924938948505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62946640696330566585264673 47209980522247924938948505)
            ·
              refine ⟨35407485391685943704211379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47209980522247924938948505 35407485391685943704211379)
              ·
                refine ⟨53111228087528915556317069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35407485391685943704211379 53111228087528915556317069)
                ·
                  refine ⟨19916710532823343333618901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53111228087528915556317069 19916710532823343333618901)
                  ·
                    refine ⟨466797903113047109381693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19916710532823343333618901 466797903113047109381693)
                    ·
                      rfl

theorem cell23_2727257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_2727257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727257 prefixEnd_2727257 := by exact prefixLift 2727257
  have htrace : WordTrace (prefixWord ++ tailWord_2727257) baseStart_2727257 baseEnd_2727257 := by
    simpa [prefixWord, tailWord_2727257, baseEnd_2727257] using wordTrace_append hprefix tailTrace_2727257
  have hstable : (prefixWord ++ tailWord_2727257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727257).length < 2 ^ (prefixWord ++ tailWord_2727257).sum := by decide
  have hdescent : baseEnd_2727257 < baseStart_2727257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727321 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 3, 4]
def baseStart_2727321 : Nat := 118140960795 + 2727321 * 2 ^ 59
def prefixEnd_2727321 : Nat := 4983230072969 + 3 ^ 40 * 2727321 * 2
def baseEnd_2727321 : Nat := 466808857367009692581595

theorem tailTrace_2727321 : CollatzResearch.WordTrace tailWord_2727321 prefixEnd_2727321 466808857367009692581595 := by
  unfold tailWord_2727321
  simp only [CollatzResearch.WordTrace]
  refine ⟨99473568952389281188525817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66315712634926187459017211 99473568952389281188525817)
  ·
    refine ⟨74605176714291960891394363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99473568952389281188525817 74605176714291960891394363)
    ·
      refine ⟨111907765071437941337091545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74605176714291960891394363 111907765071437941337091545)
      ·
        refine ⟨83930823803578456002818659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111907765071437941337091545 83930823803578456002818659)
        ·
          refine ⟨125896235705367684004227989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83930823803578456002818659 125896235705367684004227989)
          ·
            refine ⟨5901386048689110187698187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125896235705367684004227989 5901386048689110187698187)
            ·
              refine ⟨8852079073033665281547281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901386048689110187698187 8852079073033665281547281)
              ·
                refine ⟨6639059304775248961160461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8852079073033665281547281 6639059304775248961160461)
                ·
                  refine ⟨2489647239290718360435173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6639059304775248961160461 2489647239290718360435173)
                  ·
                    refine ⟨466808857367009692581595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2489647239290718360435173 466808857367009692581595)
                    ·
                      rfl

theorem cell23_2727321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_2727321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727321 prefixEnd_2727321 := by exact prefixLift 2727321
  have htrace : WordTrace (prefixWord ++ tailWord_2727321) baseStart_2727321 baseEnd_2727321 := by
    simpa [prefixWord, tailWord_2727321, baseEnd_2727321] using wordTrace_append hprefix tailTrace_2727321
  have hstable : (prefixWord ++ tailWord_2727321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727321).length < 2 ^ (prefixWord ++ tailWord_2727321).sum := by decide
  have hdescent : baseEnd_2727321 < baseStart_2727321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727341 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2727341 : Nat := 118140960795 + 2727341 * 2 ^ 59
def prefixEnd_2727341 : Nat := 4983230072969 + 3 ^ 40 * 2727341 * 2
def baseEnd_2727341 : Nat := 1400436841714118999494693

theorem tailTrace_2727341 : CollatzResearch.WordTrace tailWord_2727341 prefixEnd_2727341 1400436841714118999494693 := by
  unfold tailWord_2727341
  simp only [CollatzResearch.WordTrace]
  refine ⟨99474298412316824604253877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66316198941544549736169251 99474298412316824604253877)
  ·
    refine ⟨9325715476154702306648801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99474298412316824604253877 9325715476154702306648801)
    ·
      refine ⟨6994286607116026729986601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9325715476154702306648801 6994286607116026729986601)
      ·
        refine ⟨5245714955337020047489951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6994286607116026729986601 5245714955337020047489951)
        ·
          refine ⟨7868572433005530071234927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5245714955337020047489951 7868572433005530071234927)
          ·
            refine ⟨11802858649508295106852391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868572433005530071234927 11802858649508295106852391)
            ·
              refine ⟨17704287974262442660278587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11802858649508295106852391 17704287974262442660278587)
              ·
                refine ⟨26556431961393663990417881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17704287974262442660278587 26556431961393663990417881)
                ·
                  refine ⟨19917323971045247992813411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26556431961393663990417881 19917323971045247992813411)
                  ·
                    refine ⟨29875985956567871989220117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19917323971045247992813411 29875985956567871989220117)
                    ·
                      refine ⟨1400436841714118999494693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29875985956567871989220117 1400436841714118999494693)
                      ·
                        rfl

theorem cell23_2727341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2727341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727341 prefixEnd_2727341 := by exact prefixLift 2727341
  have htrace : WordTrace (prefixWord ++ tailWord_2727341) baseStart_2727341 baseEnd_2727341 := by
    simpa [prefixWord, tailWord_2727341, baseEnd_2727341] using wordTrace_append hprefix tailTrace_2727341
  have hstable : (prefixWord ++ tailWord_2727341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727341).length < 2 ^ (prefixWord ++ tailWord_2727341).sum := by decide
  have hdescent : baseEnd_2727341 < baseStart_2727341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727371 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 1, 5, 2]
def baseStart_2727371 : Nat := 118140960795 + 2727371 * 2 ^ 59
def prefixEnd_2727371 : Nat := 4983230072969 + 3 ^ 40 * 2727371 * 2
def baseEnd_2727371 : Nat := 1400452246133753882119555

theorem tailTrace_2727371 : CollatzResearch.WordTrace tailWord_2727371 prefixEnd_2727371 1400452246133753882119555 := by
  unfold tailWord_2727371
  simp only [CollatzResearch.WordTrace]
  refine ⟨99475392602208139727845967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66316928401472093151897311 99475392602208139727845967)
  ·
    refine ⟨149213088903312209591768951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99475392602208139727845967 149213088903312209591768951)
    ·
      refine ⟨223819633354968314387653427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149213088903312209591768951 223819633354968314387653427)
      ·
        refine ⟨335729450032452471581480141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223819633354968314387653427 335729450032452471581480141)
        ·
          refine ⟨125898543762169676843055053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335729450032452471581480141 125898543762169676843055053)
          ·
            refine ⟨47211953910813628816145645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125898543762169676843055053 47211953910813628816145645)
            ·
              refine ⟨17704482716555110806054617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47211953910813628816145645 17704482716555110806054617)
              ·
                refine ⟨13278362037416333104540963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17704482716555110806054617 13278362037416333104540963)
                ·
                  refine ⟨19917543056124499656811445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13278362037416333104540963 19917543056124499656811445)
                  ·
                    refine ⟨1867269661511671842826073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19917543056124499656811445 1867269661511671842826073)
                    ·
                      refine ⟨1400452246133753882119555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867269661511671842826073 1400452246133753882119555)
                      ·
                        rfl

theorem cell23_2727371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 5, 2].length) (baseStart_2727371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727371 prefixEnd_2727371 := by exact prefixLift 2727371
  have htrace : WordTrace (prefixWord ++ tailWord_2727371) baseStart_2727371 baseEnd_2727371 := by
    simpa [prefixWord, tailWord_2727371, baseEnd_2727371] using wordTrace_append hprefix tailTrace_2727371
  have hstable : (prefixWord ++ tailWord_2727371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727371).length < 2 ^ (prefixWord ++ tailWord_2727371).sum := by decide
  have hdescent : baseEnd_2727371 < baseStart_2727371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727374 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2727374 : Nat := 118140960795 + 2727374 * 2 ^ 59
def prefixEnd_2727374 : Nat := 4983230072969 + 3 ^ 40 * 2727374 * 2
def baseEnd_2727374 : Nat := 1400453786575717370382041

theorem tailTrace_2727374 : CollatzResearch.WordTrace tailWord_2727374 prefixEnd_2727374 1400453786575717370382041 := by
  unfold tailWord_2727374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12434437752649658905025647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66317001347464847493470117 12434437752649658905025647)
  ·
    refine ⟨18651656628974488357538471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12434437752649658905025647 18651656628974488357538471)
    ·
      refine ⟨27977484943461732536307707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18651656628974488357538471 27977484943461732536307707)
      ·
        refine ⟨41966227415192598804461561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27977484943461732536307707 41966227415192598804461561)
        ·
          refine ⟨31474670561394449103346171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41966227415192598804461561 31474670561394449103346171)
          ·
            refine ⟨47212005842091673655019257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31474670561394449103346171 47212005842091673655019257)
            ·
              refine ⟨35409004381568755241264443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47212005842091673655019257 35409004381568755241264443)
              ·
                refine ⟨53113506572353132861896665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35409004381568755241264443 53113506572353132861896665)
                ·
                  refine ⟨39835129929264849646422499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53113506572353132861896665 39835129929264849646422499)
                  ·
                    refine ⟨59752694893897274469633749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39835129929264849646422499 59752694893897274469633749)
                    ·
                      refine ⟨1400453786575717370382041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59752694893897274469633749 1400453786575717370382041)
                      ·
                        rfl

theorem cell23_2727374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2727374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727374 prefixEnd_2727374 := by exact prefixLift 2727374
  have htrace : WordTrace (prefixWord ++ tailWord_2727374) baseStart_2727374 baseEnd_2727374 := by
    simpa [prefixWord, tailWord_2727374, baseEnd_2727374] using wordTrace_append hprefix tailTrace_2727374
  have hstable : (prefixWord ++ tailWord_2727374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727374).length < 2 ^ (prefixWord ++ tailWord_2727374).sum := by decide
  have hdescent : baseEnd_2727374 < baseStart_2727374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727421 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_2727421 : Nat := 118140960795 + 2727421 * 2 ^ 59
def prefixEnd_2727421 : Nat := 4983230072969 + 3 ^ 40 * 2727421 * 2
def baseEnd_2727421 : Nat := 1400477920166478686494325

theorem tailTrace_2727421 : CollatzResearch.WordTrace tailWord_2727421 prefixEnd_2727421 1400477920166478686494325 := by
  unfold tailWord_2727421
  simp only [CollatzResearch.WordTrace]
  refine ⟨99477216252026998267166117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66318144168017998844777411 99477216252026998267166117)
  ·
    refine ⟨18651978047255062175093647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99477216252026998267166117 18651978047255062175093647)
    ·
      refine ⟨27977967070882593262640471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18651978047255062175093647 27977967070882593262640471)
      ·
        refine ⟨41966950606323889893960707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27977967070882593262640471 41966950606323889893960707)
        ·
          refine ⟨62950425909485834840941061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41966950606323889893960707 62950425909485834840941061)
          ·
            refine ⟨11803204858028594032676449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62950425909485834840941061 11803204858028594032676449)
            ·
              refine ⟨8852403643521445524507337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11803204858028594032676449 8852403643521445524507337)
              ·
                refine ⟨6639302732641084143380503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8852403643521445524507337 6639302732641084143380503)
                ·
                  refine ⟨9958954098961626215070755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639302732641084143380503 9958954098961626215070755)
                  ·
                    refine ⟨14938431148442439322606133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9958954098961626215070755 14938431148442439322606133)
                    ·
                      refine ⟨1400477920166478686494325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14938431148442439322606133 1400477920166478686494325)
                      ·
                        rfl

theorem cell23_2727421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_2727421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727421 prefixEnd_2727421 := by exact prefixLift 2727421
  have htrace : WordTrace (prefixWord ++ tailWord_2727421) baseStart_2727421 baseEnd_2727421 := by
    simpa [prefixWord, tailWord_2727421, baseEnd_2727421] using wordTrace_append hprefix tailTrace_2727421
  have hstable : (prefixWord ++ tailWord_2727421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727421).length < 2 ^ (prefixWord ++ tailWord_2727421).sum := by decide
  have hdescent : baseEnd_2727421 < baseStart_2727421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727431 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_2727431 : Nat := 118140960795 + 2727431 * 2 ^ 59
def prefixEnd_2727431 : Nat := 4983230072969 + 3 ^ 40 * 2727431 * 2
def baseEnd_2727431 : Nat := 1400483054973023647369279

theorem tailTrace_2727431 : CollatzResearch.WordTrace tailWord_2727431 prefixEnd_2727431 1400483054973023647369279 := by
  unfold tailWord_2727431
  simp only [CollatzResearch.WordTrace]
  refine ⟨99477580981990769975030147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66318387321327179983353431 99477580981990769975030147)
  ·
    refine ⟨149216371472986154962545221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99477580981990769975030147 149216371472986154962545221)
    ·
      refine ⟨27978069651184904055477229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149216371472986154962545221 27978069651184904055477229)
      ·
        refine ⟨10491776119194339020803961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27978069651184904055477229 10491776119194339020803961)
        ·
          refine ⟨7868832089395754265602971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10491776119194339020803961 7868832089395754265602971)
          ·
            refine ⟨11803248134093631398404457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7868832089395754265602971 11803248134093631398404457)
            ·
              refine ⟨8852436100570223548803343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11803248134093631398404457 8852436100570223548803343)
              ·
                refine ⟨13278654150855335323205015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852436100570223548803343 13278654150855335323205015)
                ·
                  refine ⟨19917981226283002984807523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13278654150855335323205015 19917981226283002984807523)
                  ·
                    refine ⟨29876971839424504477211285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19917981226283002984807523 29876971839424504477211285)
                    ·
                      refine ⟨1400483054973023647369279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29876971839424504477211285 1400483054973023647369279)
                      ·
                        rfl

theorem cell23_2727431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_2727431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727431 prefixEnd_2727431 := by exact prefixLift 2727431
  have htrace : WordTrace (prefixWord ++ tailWord_2727431) baseStart_2727431 baseEnd_2727431 := by
    simpa [prefixWord, tailWord_2727431, baseEnd_2727431] using wordTrace_append hprefix tailTrace_2727431
  have hstable : (prefixWord ++ tailWord_2727431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727431).length < 2 ^ (prefixWord ++ tailWord_2727431).sum := by decide
  have hdescent : baseEnd_2727431 < baseStart_2727431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727435 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 4]
def baseStart_2727435 : Nat := 118140960795 + 2727435 * 2 ^ 59
def prefixEnd_2727435 : Nat := 4983230072969 + 3 ^ 40 * 2727435 * 2
def baseEnd_2727435 : Nat := 1400485108895641631719261

theorem tailTrace_2727435 : CollatzResearch.WordTrace tailWord_2727435 prefixEnd_2727435 1400485108895641631719261 := by
  unfold tailWord_2727435
  simp only [CollatzResearch.WordTrace]
  refine ⟨99477726873976278658175759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66318484582650852438783839 99477726873976278658175759)
  ·
    refine ⟨149216590310964417987263639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99477726873976278658175759 149216590310964417987263639)
    ·
      refine ⟨223824885466446626980895459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149216590310964417987263639 223824885466446626980895459)
      ·
        refine ⟨335737328199669940471343189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223824885466446626980895459 335737328199669940471343189)
        ·
          refine ⟨3934421814839882114898553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 335737328199669940471343189 3934421814839882114898553)
          ·
            refine ⟨2950816361129911586173915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3934421814839882114898553 2950816361129911586173915)
            ·
              refine ⟨4426224541694867379260873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2950816361129911586173915 4426224541694867379260873)
              ·
                refine ⟨3319668406271150534445655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4426224541694867379260873 3319668406271150534445655)
                ·
                  refine ⟨4979502609406725801668483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3319668406271150534445655 4979502609406725801668483)
                  ·
                    refine ⟨7469253914110088702502725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4979502609406725801668483 7469253914110088702502725)
                    ·
                      refine ⟨1400485108895641631719261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7469253914110088702502725 1400485108895641631719261)
                      ·
                        rfl

theorem cell23_2727435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 4].length) (baseStart_2727435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727435 prefixEnd_2727435 := by exact prefixLift 2727435
  have htrace : WordTrace (prefixWord ++ tailWord_2727435) baseStart_2727435 baseEnd_2727435 := by
    simpa [prefixWord, tailWord_2727435, baseEnd_2727435] using wordTrace_append hprefix tailTrace_2727435
  have hstable : (prefixWord ++ tailWord_2727435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727435).length < 2 ^ (prefixWord ++ tailWord_2727435).sum := by decide
  have hdescent : baseEnd_2727435 < baseStart_2727435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727448 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 1, 2, 4]
def baseStart_2727448 : Nat := 118140960795 + 2727448 * 2 ^ 59
def prefixEnd_2727448 : Nat := 4983230072969 + 3 ^ 40 * 2727448 * 2
def baseEnd_2727448 : Nat := 1400491784144150080856701

theorem tailTrace_2727448 : CollatzResearch.WordTrace tailWord_2727448 prefixEnd_2727448 1400491784144150080856701 := by
  unfold tailWord_2727448
  simp only [CollatzResearch.WordTrace]
  refine ⟨49739100511464590939199499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66318800681952787918932665 49739100511464590939199499)
  ·
    refine ⟨74608650767196886408799249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49739100511464590939199499 74608650767196886408799249)
    ·
      refine ⟨55956488075397664806599437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74608650767196886408799249 55956488075397664806599437)
      ·
        refine ⟨20983683028274124302474789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55956488075397664806599437 20983683028274124302474789)
        ·
          refine ⟨3934440567801398306714023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20983683028274124302474789 3934440567801398306714023)
          ·
            refine ⟨5901660851702097460071035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934440567801398306714023 5901660851702097460071035)
            ·
              refine ⟨8852491277553146190106553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5901660851702097460071035 8852491277553146190106553)
              ·
                refine ⟨6639368458164859642579915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8852491277553146190106553 6639368458164859642579915)
                ·
                  refine ⟨9959052687247289463869873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639368458164859642579915 9959052687247289463869873)
                  ·
                    refine ⟨7469289515435467097902405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9959052687247289463869873 7469289515435467097902405)
                    ·
                      refine ⟨1400491784144150080856701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7469289515435467097902405 1400491784144150080856701)
                      ·
                        rfl

theorem cell23_2727448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_2727448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727448 prefixEnd_2727448 := by exact prefixLift 2727448
  have htrace : WordTrace (prefixWord ++ tailWord_2727448) baseStart_2727448 baseEnd_2727448 := by
    simpa [prefixWord, tailWord_2727448, baseEnd_2727448] using wordTrace_append hprefix tailTrace_2727448
  have hstable : (prefixWord ++ tailWord_2727448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727448).length < 2 ^ (prefixWord ++ tailWord_2727448).sum := by decide
  have hdescent : baseEnd_2727448 < baseStart_2727448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727452 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_2727452 : Nat := 118140960795 + 2727452 * 2 ^ 59
def prefixEnd_2727452 : Nat := 4983230072969 + 3 ^ 40 * 2727452 * 2
def baseEnd_2727452 : Nat := 1400493838066768065206683

theorem tailTrace_2727452 : CollatzResearch.WordTrace tailWord_2727452 prefixEnd_2727452 1400493838066768065206683 := by
  unfold tailWord_2727452
  simp only [CollatzResearch.WordTrace]
  refine ⟨49739173457457345280772305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66318897943276460374363073 49739173457457345280772305)
  ·
    refine ⟨37304380093093008960579229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49739173457457345280772305 37304380093093008960579229)
    ·
      refine ⟨13989142534909878360217211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37304380093093008960579229 13989142534909878360217211)
      ·
        refine ⟨20983713802364817540325817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13989142534909878360217211 20983713802364817540325817)
        ·
          refine ⟨15737785351773613155244363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20983713802364817540325817 15737785351773613155244363)
          ·
            refine ⟨23606678027660419732866545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15737785351773613155244363 23606678027660419732866545)
            ·
              refine ⟨17705008520745314799649909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23606678027660419732866545 17705008520745314799649909)
              ·
                refine ⟨1659844548819873262467179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17705008520745314799649909 1659844548819873262467179)
                ·
                  refine ⟨2489766823229809893700769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1659844548819873262467179 2489766823229809893700769)
                  ·
                    refine ⟨1867325117422357420275577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2489766823229809893700769 1867325117422357420275577)
                    ·
                      refine ⟨1400493838066768065206683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1867325117422357420275577 1400493838066768065206683)
                      ·
                        rfl

theorem cell23_2727452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_2727452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727452 prefixEnd_2727452 := by exact prefixLift 2727452
  have htrace : WordTrace (prefixWord ++ tailWord_2727452) baseStart_2727452 baseEnd_2727452 := by
    simpa [prefixWord, tailWord_2727452, baseEnd_2727452] using wordTrace_append hprefix tailTrace_2727452
  have hstable : (prefixWord ++ tailWord_2727452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727452).length < 2 ^ (prefixWord ++ tailWord_2727452).sum := by decide
  have hdescent : baseEnd_2727452 < baseStart_2727452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727485 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2727485 : Nat := 118140960795 + 2727485 * 2 ^ 59
def prefixEnd_2727485 : Nat := 4983230072969 + 3 ^ 40 * 2727485 * 2
def baseEnd_2727485 : Nat := 1400510782928366436094031

theorem tailTrace_2727485 : CollatzResearch.WordTrace tailWord_2727485 prefixEnd_2727485 1400510782928366436094031 := by
  unfold tailWord_2727485
  simp only [CollatzResearch.WordTrace]
  refine ⟨99479550523795137197495909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66319700349196758131663939 99479550523795137197495909)
  ·
    refine ⟨18652415723211588224530483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99479550523795137197495909 18652415723211588224530483)
    ·
      refine ⟨27978623584817382336795725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18652415723211588224530483 27978623584817382336795725)
      ·
        refine ⟨10491983844306518376298397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27978623584817382336795725 10491983844306518376298397)
        ·
          refine ⟨3934493941614944391111899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10491983844306518376298397 3934493941614944391111899)
          ·
            refine ⟨5901740912422416586667849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3934493941614944391111899 5901740912422416586667849)
            ·
              refine ⟨4426305684316812440000887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5901740912422416586667849 4426305684316812440000887)
              ·
                refine ⟨6639458526475218660001331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4426305684316812440000887 6639458526475218660001331)
                ·
                  refine ⟨9959187789712827990001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6639458526475218660001331 9959187789712827990001997)
                  ·
                    refine ⟨3734695421142310496250749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9959187789712827990001997 3734695421142310496250749)
                    ·
                      refine ⟨1400510782928366436094031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3734695421142310496250749 1400510782928366436094031)
                      ·
                        rfl

theorem cell23_2727485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2727485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727485 prefixEnd_2727485 := by exact prefixLift 2727485
  have htrace : WordTrace (prefixWord ++ tailWord_2727485) baseStart_2727485 baseEnd_2727485 := by
    simpa [prefixWord, tailWord_2727485, baseEnd_2727485] using wordTrace_append hprefix tailTrace_2727485
  have hstable : (prefixWord ++ tailWord_2727485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727485).length < 2 ^ (prefixWord ++ tailWord_2727485).sum := by decide
  have hdescent : baseEnd_2727485 < baseStart_2727485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727521 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2727521 : Nat := 118140960795 + 2727521 * 2 ^ 59
def prefixEnd_2727521 : Nat := 4983230072969 + 3 ^ 40 * 2727521 * 2
def baseEnd_2727521 : Nat := 1400529268231928295243865

theorem tailTrace_2727521 : CollatzResearch.WordTrace tailWord_2727521 prefixEnd_2727521 1400529268231928295243865 := by
  unfold tailWord_2727521
  simp only [CollatzResearch.WordTrace]
  refine ⟨99480863551664715345806417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66320575701109810230537611 99480863551664715345806417)
  ·
    refine ⟨74610647663748536509354813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99480863551664715345806417 74610647663748536509354813)
    ·
      refine ⟨27978992873905701191008055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74610647663748536509354813 27978992873905701191008055)
      ·
        refine ⟨41968489310858551786512083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27978992873905701191008055 41968489310858551786512083)
        ·
          refine ⟨62952733966287827679768125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41968489310858551786512083 62952733966287827679768125)
          ·
            refine ⟨23607275237357935379913047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62952733966287827679768125 23607275237357935379913047)
            ·
              refine ⟨35410912856036903069869571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23607275237357935379913047 35410912856036903069869571)
              ·
                refine ⟨53116369284055354604804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35410912856036903069869571 53116369284055354604804357)
                ·
                  refine ⟨9959319240760378988400817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53116369284055354604804357 9959319240760378988400817)
                  ·
                    refine ⟨7469489430570284241300613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9959319240760378988400817 7469489430570284241300613)
                    ·
                      refine ⟨1400529268231928295243865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7469489430570284241300613 1400529268231928295243865)
                      ·
                        rfl

theorem cell23_2727521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2727521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727521 prefixEnd_2727521 := by exact prefixLift 2727521
  have htrace : WordTrace (prefixWord ++ tailWord_2727521) baseStart_2727521 baseEnd_2727521 := by
    simpa [prefixWord, tailWord_2727521, baseEnd_2727521] using wordTrace_append hprefix tailTrace_2727521
  have hstable : (prefixWord ++ tailWord_2727521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727521).length < 2 ^ (prefixWord ++ tailWord_2727521).sum := by decide
  have hdescent : baseEnd_2727521 < baseStart_2727521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2727538 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_2727538 : Nat := 118140960795 + 2727538 * 2 ^ 59
def prefixEnd_2727538 : Nat := 4983230072969 + 3 ^ 40 * 2727538 * 2
def baseEnd_2727538 : Nat := 1400537997403054728731287

theorem tailTrace_2727538 : CollatzResearch.WordTrace tailWord_2727538 prefixEnd_2727538 1400537997403054728731287 := by
  unfold tailWord_2727538
  simp only [CollatzResearch.WordTrace]
  refine ⟨24870370898150781812293817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66320989061735418166116845 24870370898150781812293817)
  ·
    refine ⟨18652778173613086359220363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24870370898150781812293817 18652778173613086359220363)
    ·
      refine ⟨27979167260419629538830545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18652778173613086359220363 27979167260419629538830545)
      ·
        refine ⟨20984375445314722154122909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27979167260419629538830545 20984375445314722154122909)
        ·
          refine ⟨7869140791993020807796091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20984375445314722154122909 7869140791993020807796091)
          ·
            refine ⟨11803711187989531211694137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7869140791993020807796091 11803711187989531211694137)
            ·
              refine ⟨8852783390992148408770603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11803711187989531211694137 8852783390992148408770603)
              ·
                refine ⟨13279175086488222613155905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8852783390992148408770603 13279175086488222613155905)
                ·
                  refine ⟨9959381314866166959866929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13279175086488222613155905 9959381314866166959866929)
                  ·
                    refine ⟨7469535986149625219900197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9959381314866166959866929 7469535986149625219900197)
                    ·
                      refine ⟨1400537997403054728731287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7469535986149625219900197 1400537997403054728731287)
                      ·
                        rfl

theorem cell23_2727538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_2727538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2727538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2727538 prefixEnd_2727538 := by exact prefixLift 2727538
  have htrace : WordTrace (prefixWord ++ tailWord_2727538) baseStart_2727538 baseEnd_2727538 := by
    simpa [prefixWord, tailWord_2727538, baseEnd_2727538] using wordTrace_append hprefix tailTrace_2727538
  have hstable : (prefixWord ++ tailWord_2727538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2727538).length < 2 ^ (prefixWord ++ tailWord_2727538).sum := by decide
  have hdescent : baseEnd_2727538 < baseStart_2727538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2727538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
