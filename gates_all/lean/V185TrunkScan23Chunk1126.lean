import V185TrunkScan23Chunk1125

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6669358 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_6669358 : Nat := 118140960795 + 6669358 * 2 ^ 59
def prefixEnd_6669358 : Nat := 4983230072969 + 3 ^ 40 * 6669358 * 2
def baseEnd_6669358 : Nat := 3424586310908822339853187

theorem tailTrace_6669358 : CollatzResearch.WordTrace tailWord_6669358 prefixEnd_6669358 3424586310908822339853187 := by
  unfold tailWord_6669358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30406433771507809563531091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162167646781374984338832485 30406433771507809563531091)
  ·
    refine ⟨45609650657261714345296637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30406433771507809563531091 45609650657261714345296637)
    ·
      refine ⟨17103618996473142879486239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45609650657261714345296637 17103618996473142879486239)
      ·
        refine ⟨25655428494709714319229359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17103618996473142879486239 25655428494709714319229359)
        ·
          refine ⟨38483142742064571478844039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25655428494709714319229359 38483142742064571478844039)
          ·
            refine ⟨57724714113096857218266059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38483142742064571478844039 57724714113096857218266059)
            ·
              refine ⟨86587071169645285827399089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57724714113096857218266059 86587071169645285827399089)
              ·
                refine ⟨64940303377233964370549317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86587071169645285827399089 64940303377233964370549317)
                ·
                  refine ⟨12176306883231368319477997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64940303377233964370549317 12176306883231368319477997)
                  ·
                    refine ⟨4566115081211763119804249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12176306883231368319477997 4566115081211763119804249)
                    ·
                      refine ⟨3424586310908822339853187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566115081211763119804249 3424586310908822339853187)
                      ·
                        rfl

theorem cell23_6669358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_6669358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669358 prefixEnd_6669358 := by exact prefixLift 6669358
  have htrace : WordTrace (prefixWord ++ tailWord_6669358) baseStart_6669358 baseEnd_6669358 := by
    simpa [prefixWord, tailWord_6669358, baseEnd_6669358] using wordTrace_append hprefix tailTrace_6669358
  have hstable : (prefixWord ++ tailWord_6669358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669358).length < 2 ^ (prefixWord ++ tailWord_6669358).sum := by decide
  have hdescent : baseEnd_6669358 < baseStart_6669358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669368 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 1, 5]
def baseStart_6669368 : Nat := 118140960795 + 6669368 * 2 ^ 59
def prefixEnd_6669368 : Nat := 4983230072969 + 3 ^ 40 * 6669368 * 2
def baseEnd_6669368 : Nat := 1141530481905122433576047

theorem tailTrace_6669368 : CollatzResearch.WordTrace tailWord_6669368 prefixEnd_6669368 1141530481905122433576047 := by
  unfold tailWord_6669368
  simp only [CollatzResearch.WordTrace]
  refine ⟨121625917451013124108056379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162167889934684165477408505 121625917451013124108056379)
  ·
    refine ⟨182438876176519686162084569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121625917451013124108056379 182438876176519686162084569)
    ·
      refine ⟨136829157132389764621563427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182438876176519686162084569 136829157132389764621563427)
      ·
        refine ⟨205243735698584646932345141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136829157132389764621563427 205243735698584646932345141)
        ·
          refine ⟨19241600221742310649907357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205243735698584646932345141 19241600221742310649907357)
          ·
            refine ⟨7215600083153366493715259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19241600221742310649907357 7215600083153366493715259)
            ·
              refine ⟨10823400124730049740572889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215600083153366493715259 10823400124730049740572889)
              ·
                refine ⟨8117550093547537305429667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10823400124730049740572889 8117550093547537305429667)
                ·
                  refine ⟨12176325140321305958144501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8117550093547537305429667 12176325140321305958144501)
                  ·
                    refine ⟨1141530481905122433576047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12176325140321305958144501 1141530481905122433576047)
                    ·
                      rfl

theorem cell23_6669368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_6669368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669368 prefixEnd_6669368 := by exact prefixLift 6669368
  have htrace : WordTrace (prefixWord ++ tailWord_6669368) baseStart_6669368 baseEnd_6669368 := by
    simpa [prefixWord, tailWord_6669368, baseEnd_6669368] using wordTrace_append hprefix tailTrace_6669368
  have hstable : (prefixWord ++ tailWord_6669368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669368).length < 2 ^ (prefixWord ++ tailWord_6669368).sum := by decide
  have hdescent : baseEnd_6669368 < baseStart_6669368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669394 : List Nat := [3, 2, 2, 1, 3, 12]
def baseStart_6669394 : Nat := 118140960795 + 6669394 * 2 ^ 59
def prefixEnd_6669394 : Nat := 4983230072969 + 3 ^ 40 * 6669394 * 2
def baseEnd_6669394 : Nat := 14093023852725860901247

theorem tailTrace_6669394 : CollatzResearch.WordTrace tailWord_6669394 prefixEnd_6669394 14093023852725860901247 := by
  unfold tailWord_6669394
  simp only [CollatzResearch.WordTrace]
  refine ⟨60813195799983013664139809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162168522133288036437706157 60813195799983013664139809)
  ·
    refine ⟨45609896849987260248104857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60813195799983013664139809 45609896849987260248104857)
    ·
      refine ⟨34207422637490445186078643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45609896849987260248104857 34207422637490445186078643)
      ·
        refine ⟨51311133956235667779117965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34207422637490445186078643 51311133956235667779117965)
        ·
          refine ⟨19241675233588375417169237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51311133956235667779117965 19241675233588375417169237)
          ·
            refine ⟨14093023852725860901247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19241675233588375417169237 14093023852725860901247)
            ·
              rfl

theorem cell23_6669394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 12].length) (baseStart_6669394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669394 prefixEnd_6669394 := by exact prefixLift 6669394
  have htrace : WordTrace (prefixWord ++ tailWord_6669394) baseStart_6669394 baseEnd_6669394 := by
    simpa [prefixWord, tailWord_6669394, baseEnd_6669394] using wordTrace_append hprefix tailTrace_6669394
  have hstable : (prefixWord ++ tailWord_6669394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669394).length < 2 ^ (prefixWord ++ tailWord_6669394).sum := by decide
  have hdescent : baseEnd_6669394 < baseStart_6669394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669418 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_6669418 : Nat := 118140960795 + 6669418 * 2 ^ 59
def prefixEnd_6669418 : Nat := 4983230072969 + 3 ^ 40 * 6669418 * 2
def baseEnd_6669418 : Nat := 3424617119748092105102911

theorem tailTrace_6669418 : CollatzResearch.WordTrace tailWord_6669418 prefixEnd_6669418 3424617119748092105102911 := by
  unfold tailWord_6669418
  simp only [CollatzResearch.WordTrace]
  refine ⟨60813414637961276688858227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162169105701230071170288605 60813414637961276688858227)
  ·
    refine ⟨91220121956941915033287341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60813414637961276688858227 91220121956941915033287341)
    ·
      refine ⟨34207545733853218137482753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91220121956941915033287341 34207545733853218137482753)
      ·
        refine ⟨25655659300389913603112065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34207545733853218137482753 25655659300389913603112065)
        ·
          refine ⟨19241744475292435202334049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25655659300389913603112065 19241744475292435202334049)
          ·
            refine ⟨14431308356469326401750537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19241744475292435202334049 14431308356469326401750537)
            ·
              refine ⟨10823481267351994801312903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14431308356469326401750537 10823481267351994801312903)
              ·
                refine ⟨16235221901027992201969355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10823481267351994801312903 16235221901027992201969355)
                ·
                  refine ⟨24352832851541988302954033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16235221901027992201969355 24352832851541988302954033)
                  ·
                    refine ⟨18264624638656491227215525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24352832851541988302954033 18264624638656491227215525)
                    ·
                      refine ⟨3424617119748092105102911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18264624638656491227215525 3424617119748092105102911)
                      ·
                        rfl

theorem cell23_6669418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_6669418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669418 prefixEnd_6669418 := by exact prefixLift 6669418
  have htrace : WordTrace (prefixWord ++ tailWord_6669418) baseStart_6669418 baseEnd_6669418 := by
    simpa [prefixWord, tailWord_6669418, baseEnd_6669418] using wordTrace_append hprefix tailTrace_6669418
  have hstable : (prefixWord ++ tailWord_6669418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669418).length < 2 ^ (prefixWord ++ tailWord_6669418).sum := by decide
  have hdescent : baseEnd_6669418 < baseStart_6669418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669424 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_6669424 : Nat := 118140960795 + 6669424 * 2 ^ 59
def prefixEnd_6669424 : Nat := 4983230072969 + 3 ^ 40 * 6669424 * 2
def baseEnd_6669424 : Nat := 1141540066877339693875961

theorem tailTrace_6669424 : CollatzResearch.WordTrace tailWord_6669424 prefixEnd_6669424 1141540066877339693875961 := by
  unfold tailWord_6669424
  simp only [CollatzResearch.WordTrace]
  refine ⟨121626938694911684890075663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162169251593215579853434217 121626938694911684890075663)
  ·
    refine ⟨182440408042367527335113495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121626938694911684890075663 182440408042367527335113495)
    ·
      refine ⟨273660612063551291002670243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182440408042367527335113495 273660612063551291002670243)
      ·
        refine ⟨410490918095326936504005365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273660612063551291002670243 410490918095326936504005365)
        ·
          refine ⟨38483523571436900297250503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 410490918095326936504005365 38483523571436900297250503)
          ·
            refine ⟨57725285357155350445875755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38483523571436900297250503 57725285357155350445875755)
            ·
              refine ⟨86587928035733025668813633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57725285357155350445875755 86587928035733025668813633)
              ·
                refine ⟨64940946026799769251610225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86587928035733025668813633 64940946026799769251610225)
                ·
                  refine ⟨48705709520099826938707669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64940946026799769251610225 48705709520099826938707669)
                  ·
                    refine ⟨1141540066877339693875961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48705709520099826938707669 1141540066877339693875961)
                    ·
                      rfl

theorem cell23_6669424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_6669424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669424 prefixEnd_6669424 := by exact prefixLift 6669424
  have htrace : WordTrace (prefixWord ++ tailWord_6669424) baseStart_6669424 baseEnd_6669424 := by
    simpa [prefixWord, tailWord_6669424, baseEnd_6669424] using wordTrace_append hprefix tailTrace_6669424
  have hstable : (prefixWord ++ tailWord_6669424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669424).length < 2 ^ (prefixWord ++ tailWord_6669424).sum := by decide
  have hdescent : baseEnd_6669424 < baseStart_6669424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669482 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6669482 : Nat := 118140960795 + 6669482 * 2 ^ 59
def prefixEnd_6669482 : Nat := 4983230072969 + 3 ^ 40 * 6669482 * 2
def baseEnd_6669482 : Nat := 3424649982509979854702617

theorem tailTrace_6669482 : CollatzResearch.WordTrace tailWord_6669482 prefixEnd_6669482 3424649982509979854702617 := by
  unfold tailWord_6669482
  simp only [CollatzResearch.WordTrace]
  refine ⟨60813998205903311421440675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162170661882408830457175133 60813998205903311421440675)
  ·
    refine ⟨91220997308854967132161013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60813998205903311421440675 91220997308854967132161013)
    ·
      refine ⟨8551968497705153168640095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91220997308854967132161013 8551968497705153168640095)
      ·
        refine ⟨12827952746557729752960143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8551968497705153168640095 12827952746557729752960143)
        ·
          refine ⟨19241929119836594629440215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827952746557729752960143 19241929119836594629440215)
          ·
            refine ⟨28862893679754891944160323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19241929119836594629440215 28862893679754891944160323)
            ·
              refine ⟨43294340519632337916240485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28862893679754891944160323 43294340519632337916240485)
              ·
                refine ⟨8117688847431063359295091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43294340519632337916240485 8117688847431063359295091)
                ·
                  refine ⟨12176533271146595038942637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8117688847431063359295091 12176533271146595038942637)
                  ·
                    refine ⟨4566199976679973139603489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12176533271146595038942637 4566199976679973139603489)
                    ·
                      refine ⟨3424649982509979854702617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566199976679973139603489 3424649982509979854702617)
                      ·
                        rfl

theorem cell23_6669482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6669482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669482 prefixEnd_6669482 := by exact prefixLift 6669482
  have htrace : WordTrace (prefixWord ++ tailWord_6669482) baseStart_6669482 baseEnd_6669482 := by
    simpa [prefixWord, tailWord_6669482, baseEnd_6669482] using wordTrace_append hprefix tailTrace_6669482
  have hstable : (prefixWord ++ tailWord_6669482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669482).length < 2 ^ (prefixWord ++ tailWord_6669482).sum := by decide
  have hdescent : baseEnd_6669482 < baseStart_6669482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669484 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 9]
def baseStart_6669484 : Nat := 118140960795 + 6669484 * 2 ^ 59
def prefixEnd_6669484 : Nat := 4983230072969 + 3 ^ 40 * 6669484 * 2
def baseEnd_6669484 : Nat := 380516778830143205208623

theorem tailTrace_6669484 : CollatzResearch.WordTrace tailWord_6669484 prefixEnd_6669484 380516778830143205208623 := by
  unfold tailWord_6669484
  simp only [CollatzResearch.WordTrace]
  refine ⟨121628032884803000013667753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162170710513070666684890337 121628032884803000013667753)
  ·
    refine ⟨91221024663602250010250815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121628032884803000013667753 91221024663602250010250815)
    ·
      refine ⟨136831536995403375015376223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91221024663602250010250815 136831536995403375015376223)
      ·
        refine ⟨205247305493105062523064335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136831536995403375015376223 205247305493105062523064335)
        ·
          refine ⟨307870958239657593784596503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205247305493105062523064335 307870958239657593784596503)
          ·
            refine ⟨461806437359486390676894755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307870958239657593784596503 461806437359486390676894755)
            ·
              refine ⟨692709656039229586015342133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461806437359486390676894755 692709656039229586015342133)
              ·
                refine ⟨64941530253677773688938325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692709656039229586015342133 64941530253677773688938325)
                ·
                  refine ⟨380516778830143205208623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64941530253677773688938325 380516778830143205208623)
                  ·
                    rfl

theorem cell23_6669484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_6669484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669484 prefixEnd_6669484 := by exact prefixLift 6669484
  have htrace : WordTrace (prefixWord ++ tailWord_6669484) baseStart_6669484 baseEnd_6669484 := by
    simpa [prefixWord, tailWord_6669484, baseEnd_6669484] using wordTrace_append hprefix tailTrace_6669484
  have hstable : (prefixWord ++ tailWord_6669484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669484).length < 2 ^ (prefixWord ++ tailWord_6669484).sum := by decide
  have hdescent : baseEnd_6669484 < baseStart_6669484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669511 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_6669511 : Nat := 118140960795 + 6669511 * 2 ^ 59
def prefixEnd_6669511 : Nat := 4983230072969 + 3 ^ 40 * 6669511 * 2
def baseEnd_6669511 : Nat := 3424664873448960241239983

theorem tailTrace_6669511 : CollatzResearch.WordTrace tailWord_6669511 prefixEnd_6669511 3424664873448960241239983 := by
  unfold tailWord_6669511
  simp only [CollatzResearch.WordTrace]
  refine ⟨243257050540508183638568387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162171367027005455759045591 243257050540508183638568387)
  ·
    refine ⟨364885575810762275457852581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243257050540508183638568387 364885575810762275457852581)
    ·
      refine ⟨68416045464517926648347359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364885575810762275457852581 68416045464517926648347359)
      ·
        refine ⟨102624068196776889972521039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68416045464517926648347359 102624068196776889972521039)
        ·
          refine ⟨153936102295165334958781559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102624068196776889972521039 153936102295165334958781559)
          ·
            refine ⟨230904153442748002438172339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153936102295165334958781559 230904153442748002438172339)
            ·
              refine ⟨346356230164122003657258509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230904153442748002438172339 346356230164122003657258509)
              ·
                refine ⟨129883586311545751371471941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346356230164122003657258509 129883586311545751371471941)
                ·
                  refine ⟨24353172433414828382150989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129883586311545751371471941 24353172433414828382150989)
                  ·
                    refine ⟨9132439662530560643306621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24353172433414828382150989 9132439662530560643306621)
                    ·
                      refine ⟨3424664873448960241239983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9132439662530560643306621 3424664873448960241239983)
                      ·
                        rfl

theorem cell23_6669511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_6669511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669511 prefixEnd_6669511 := by exact prefixLift 6669511
  have htrace : WordTrace (prefixWord ++ tailWord_6669511) baseStart_6669511 baseEnd_6669511 := by
    simpa [prefixWord, tailWord_6669511, baseEnd_6669511] using wordTrace_append hprefix tailTrace_6669511
  have hstable : (prefixWord ++ tailWord_6669511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669511).length < 2 ^ (prefixWord ++ tailWord_6669511).sum := by decide
  have hdescent : baseEnd_6669511 < baseStart_6669511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669548 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_6669548 : Nat := 118140960795 + 6669548 * 2 ^ 59
def prefixEnd_6669548 : Nat := 4983230072969 + 3 ^ 40 * 6669548 * 2
def baseEnd_6669548 : Nat := 1141561290744392198825771

theorem tailTrace_6669548 : CollatzResearch.WordTrace tailWord_6669548 prefixEnd_6669548 1141561290744392198825771 := by
  unfold tailWord_6669548
  simp only [CollatzResearch.WordTrace]
  refine ⟨121629200020687069478832649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162172266694249425971776865 121629200020687069478832649)
  ·
    refine ⟨91221900015515302109124487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121629200020687069478832649 91221900015515302109124487)
    ·
      refine ⟨136832850023272953163686731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91221900015515302109124487 136832850023272953163686731)
      ·
        refine ⟨205249275034909429745530097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136832850023272953163686731 205249275034909429745530097)
        ·
          refine ⟨153936956276182072309147573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205249275034909429745530097 153936956276182072309147573)
          ·
            refine ⟨14431589650892069278982585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153936956276182072309147573 14431589650892069278982585)
            ·
              refine ⟨10823692238169051959236939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14431589650892069278982585 10823692238169051959236939)
              ·
                refine ⟨16235538357253577938855409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10823692238169051959236939 16235538357253577938855409)
                ·
                  refine ⟨12176653767940183454141557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16235538357253577938855409 12176653767940183454141557)
                  ·
                    refine ⟨1141561290744392198825771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12176653767940183454141557 1141561290744392198825771)
                    ·
                      rfl

theorem cell23_6669548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_6669548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669548 prefixEnd_6669548 := by exact prefixLift 6669548
  have htrace : WordTrace (prefixWord ++ tailWord_6669548) baseStart_6669548 baseEnd_6669548 := by
    simpa [prefixWord, tailWord_6669548, baseEnd_6669548] using wordTrace_append hprefix tailTrace_6669548
  have hstable : (prefixWord ++ tailWord_6669548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669548).length < 2 ^ (prefixWord ++ tailWord_6669548).sum := by decide
  have hdescent : baseEnd_6669548 < baseStart_6669548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669568 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 2, 4, 2]
def baseStart_6669568 : Nat := 118140960795 + 6669568 * 2 ^ 59
def prefixEnd_6669568 : Nat := 4983230072969 + 3 ^ 40 * 6669568 * 2
def baseEnd_6669568 : Nat := 3424694141846266518227221

theorem tailTrace_6669568 : CollatzResearch.WordTrace tailWord_6669568 prefixEnd_6669568 3424694141846266518227221 := by
  unfold tailWord_6669568
  simp only [CollatzResearch.WordTrace]
  refine ⟨121629564750650841186696679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162172753000867788248928905 121629564750650841186696679)
  ·
    refine ⟨182444347125976261780045019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121629564750650841186696679 182444347125976261780045019)
    ·
      refine ⟨273666520688964392670067529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182444347125976261780045019 273666520688964392670067529)
      ·
        refine ⟨205249890516723294502550647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273666520688964392670067529 205249890516723294502550647)
        ·
          refine ⟨307874835775084941753825971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205249890516723294502550647 307874835775084941753825971)
          ·
            refine ⟨461812253662627412630738957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307874835775084941753825971 461812253662627412630738957)
            ·
              refine ⟨173179595123485279736527109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461812253662627412630738957 173179595123485279736527109)
              ·
                refine ⟨32471174085653489950598833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173179595123485279736527109 32471174085653489950598833)
                ·
                  refine ⟨24353380564240117462949125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32471174085653489950598833 24353380564240117462949125)
                  ·
                    refine ⟨4566258855795022024302961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24353380564240117462949125 4566258855795022024302961)
                    ·
                      refine ⟨3424694141846266518227221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566258855795022024302961 3424694141846266518227221)
                      ·
                        rfl

theorem cell23_6669568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_6669568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669568 prefixEnd_6669568 := by exact prefixLift 6669568
  have htrace : WordTrace (prefixWord ++ tailWord_6669568) baseStart_6669568 baseEnd_6669568 := by
    simpa [prefixWord, tailWord_6669568, baseEnd_6669568] using wordTrace_append hprefix tailTrace_6669568
  have hstable : (prefixWord ++ tailWord_6669568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669568).length < 2 ^ (prefixWord ++ tailWord_6669568).sum := by decide
  have hdescent : baseEnd_6669568 < baseStart_6669568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669578 : List Nat := [3, 1, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_6669578 : Nat := 118140960795 + 6669578 * 2 ^ 59
def prefixEnd_6669578 : Nat := 4983230072969 + 3 ^ 40 * 6669578 * 2
def baseEnd_6669578 : Nat := 1141566425550937159700725

theorem tailTrace_6669578 : CollatzResearch.WordTrace tailWord_6669578 prefixEnd_6669578 1141566425550937159700725 := by
  unfold tailWord_6669578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60814873557816363520314347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162172996154176969387504925 60814873557816363520314347)
  ·
    refine ⟨91222310336724545280471521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60814873557816363520314347 91222310336724545280471521)
    ·
      refine ⟨68416732752543408960353641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91222310336724545280471521 68416732752543408960353641)
      ·
        refine ⟨51312549564407556720265231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68416732752543408960353641 51312549564407556720265231)
        ·
          refine ⟨76968824346611335080397847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51312549564407556720265231 76968824346611335080397847)
          ·
            refine ⟨115453236519917002620596771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76968824346611335080397847 115453236519917002620596771)
            ·
              refine ⟨173179854779875503930895157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115453236519917002620596771 173179854779875503930895157)
              ·
                refine ⟨16235611385613328493521421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173179854779875503930895157 16235611385613328493521421)
                ·
                  refine ⟨6088354269604998185070533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16235611385613328493521421 6088354269604998185070533)
                  ·
                    refine ⟨1141566425550937159700725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088354269604998185070533 1141566425550937159700725)
                    ·
                      rfl

theorem cell23_6669578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_6669578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669578 prefixEnd_6669578 := by exact prefixLift 6669578
  have htrace : WordTrace (prefixWord ++ tailWord_6669578) baseStart_6669578 baseEnd_6669578 := by
    simpa [prefixWord, tailWord_6669578, baseEnd_6669578] using wordTrace_append hprefix tailTrace_6669578
  have hstable : (prefixWord ++ tailWord_6669578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669578).length < 2 ^ (prefixWord ++ tailWord_6669578).sum := by decide
  have hdescent : baseEnd_6669578 < baseStart_6669578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669602 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_6669602 : Nat := 118140960795 + 6669602 * 2 ^ 59
def prefixEnd_6669602 : Nat := 4983230072969 + 3 ^ 40 * 6669602 * 2
def baseEnd_6669602 : Nat := 3424711600188519385202065

theorem tailTrace_6669602 : CollatzResearch.WordTrace tailWord_6669602 prefixEnd_6669602 3424711600188519385202065 := by
  unfold tailWord_6669602
  simp only [CollatzResearch.WordTrace]
  refine ⟨60815092395794626545032765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162173579722119004120087373 60815092395794626545032765)
  ·
    refine ⟨22805659648422984954387287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60815092395794626545032765 22805659648422984954387287)
    ·
      refine ⟨34208489472634477431580931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22805659648422984954387287 34208489472634477431580931)
      ·
        refine ⟨51312734208951716147371397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34208489472634477431580931 51312734208951716147371397)
        ·
          refine ⟨9621137664178446777632137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51312734208951716147371397 9621137664178446777632137)
          ·
            refine ⟨7215853248133835083224103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9621137664178446777632137 7215853248133835083224103)
            ·
              refine ⟨10823779872200752624836155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7215853248133835083224103 10823779872200752624836155)
              ·
                refine ⟨16235669808301128937254233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10823779872200752624836155 16235669808301128937254233)
                ·
                  refine ⟨12176752356225846702940675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16235669808301128937254233 12176752356225846702940675)
                  ·
                    refine ⟨18265128534338770054411013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12176752356225846702940675 18265128534338770054411013)
                    ·
                      refine ⟨3424711600188519385202065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18265128534338770054411013 3424711600188519385202065)
                      ·
                        rfl

theorem cell23_6669602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_6669602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669602 prefixEnd_6669602 := by exact prefixLift 6669602
  have htrace : WordTrace (prefixWord ++ tailWord_6669602) baseStart_6669602 baseEnd_6669602 := by
    simpa [prefixWord, tailWord_6669602, baseEnd_6669602] using wordTrace_append hprefix tailTrace_6669602
  have hstable : (prefixWord ++ tailWord_6669602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669602).length < 2 ^ (prefixWord ++ tailWord_6669602).sum := by decide
  have hdescent : baseEnd_6669602 < baseStart_6669602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669605 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_6669605 : Nat := 118140960795 + 6669605 * 2 ^ 59
def prefixEnd_6669605 : Nat := 4983230072969 + 3 ^ 40 * 6669605 * 2
def baseEnd_6669605 : Nat := 3424713140630482873464551

theorem tailTrace_6669605 : CollatzResearch.WordTrace tailWord_6669605 prefixEnd_6669605 3424713140630482873464551 := by
  unfold tailWord_6669605
  simp only [CollatzResearch.WordTrace]
  refine ⟨243260479002167637692490269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162173652668111758461660179 243260479002167637692490269)
  ·
    refine ⟨91222679625812864134683851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243260479002167637692490269 91222679625812864134683851)
    ·
      refine ⟨136834019438719296202025777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91222679625812864134683851 136834019438719296202025777)
      ·
        refine ⟨102625514579039472151519333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136834019438719296202025777 102625514579039472151519333)
        ·
          refine ⟨19242283983569901028409875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102625514579039472151519333 19242283983569901028409875)
          ·
            refine ⟨28863425975354851542614813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19242283983569901028409875 28863425975354851542614813)
            ·
              refine ⟨10823784740758069328480555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28863425975354851542614813 10823784740758069328480555)
              ·
                refine ⟨16235677111137103992720833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10823784740758069328480555 16235677111137103992720833)
                ·
                  refine ⟨12176757833352827994540625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16235677111137103992720833 12176757833352827994540625)
                  ·
                    refine ⟨9132568375014620995905469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12176757833352827994540625 9132568375014620995905469)
                    ·
                      refine ⟨3424713140630482873464551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9132568375014620995905469 3424713140630482873464551)
                      ·
                        rfl

theorem cell23_6669605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_6669605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669605 prefixEnd_6669605 := by exact prefixLift 6669605
  have htrace : WordTrace (prefixWord ++ tailWord_6669605) baseStart_6669605 baseEnd_6669605 := by
    simpa [prefixWord, tailWord_6669605, baseEnd_6669605] using wordTrace_append hprefix tailTrace_6669605
  have hstable : (prefixWord ++ tailWord_6669605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669605).length < 2 ^ (prefixWord ++ tailWord_6669605).sum := by decide
  have hdescent : baseEnd_6669605 < baseStart_6669605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669655 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 1, 5]
def baseStart_6669655 : Nat := 118140960795 + 6669655 * 2 ^ 59
def prefixEnd_6669655 : Nat := 4983230072969 + 3 ^ 40 * 6669655 * 2
def baseEnd_6669655 : Nat := 1141579604887735892613107

theorem tailTrace_6669655 : CollatzResearch.WordTrace tailWord_6669655 prefixEnd_6669655 1141579604887735892613107 := by
  unfold tailWord_6669655
  simp only [CollatzResearch.WordTrace]
  refine ⟨243262302651986496231810419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162174868434657664154540279 243262302651986496231810419)
  ·
    refine ⟨364893453977979744347715629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243262302651986496231810419 364893453977979744347715629)
    ·
      refine ⟨136835045241742404130393361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364893453977979744347715629 136835045241742404130393361)
      ·
        refine ⟨102626283931306803097795021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136835045241742404130393361 102626283931306803097795021)
        ·
          refine ⟨38484856474240051161673133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102626283931306803097795021 38484856474240051161673133)
          ·
            refine ⟨14431821177840019185627425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38484856474240051161673133 14431821177840019185627425)
            ·
              refine ⟨10823865883380014389220569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14431821177840019185627425 10823865883380014389220569)
              ·
                refine ⟨8117899412535010791915427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10823865883380014389220569 8117899412535010791915427)
                ·
                  refine ⟨12176849118802516187873141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8117899412535010791915427 12176849118802516187873141)
                  ·
                    refine ⟨1141579604887735892613107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12176849118802516187873141 1141579604887735892613107)
                    ·
                      rfl

theorem cell23_6669655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_6669655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669655 prefixEnd_6669655 := by exact prefixLift 6669655
  have htrace : WordTrace (prefixWord ++ tailWord_6669655) baseStart_6669655 baseEnd_6669655 := by
    simpa [prefixWord, tailWord_6669655, baseEnd_6669655] using wordTrace_append hprefix tailTrace_6669655
  have hstable : (prefixWord ++ tailWord_6669655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669655).length < 2 ^ (prefixWord ++ tailWord_6669655).sum := by decide
  have hdescent : baseEnd_6669655 < baseStart_6669655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669658 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_6669658 : Nat := 118140960795 + 6669658 * 2 ^ 59
def prefixEnd_6669658 : Nat := 4983230072969 + 3 ^ 40 * 6669658 * 2
def baseEnd_6669658 : Nat := 3424740355105171166101807

theorem tailTrace_6669658 : CollatzResearch.WordTrace tailWord_6669658 prefixEnd_6669658 3424740355105171166101807 := by
  unfold tailWord_6669658
  simp only [CollatzResearch.WordTrace]
  refine ⟨60815603017743906936042407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162174941380650418496113085 60815603017743906936042407)
  ·
    refine ⟨91223404526615860404063611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60815603017743906936042407 91223404526615860404063611)
    ·
      refine ⟨136835106789923790606095417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91223404526615860404063611 136835106789923790606095417)
      ·
        refine ⟨102626330092442842954571563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136835106789923790606095417 102626330092442842954571563)
        ·
          refine ⟨153939495138664264431857345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102626330092442842954571563 153939495138664264431857345)
          ·
            refine ⟨115454621353998198323893009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153939495138664264431857345 115454621353998198323893009)
            ·
              refine ⟨86590966015498648742919757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115454621353998198323893009 86590966015498648742919757)
              ·
                refine ⟨32471612255811993278594909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86590966015498648742919757 32471612255811993278594909)
                ·
                  refine ⟨12176854595929497479473091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32471612255811993278594909 12176854595929497479473091)
                  ·
                    refine ⟨18265281893894246219209637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12176854595929497479473091 18265281893894246219209637)
                    ·
                      refine ⟨3424740355105171166101807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18265281893894246219209637 3424740355105171166101807)
                      ·
                        rfl

theorem cell23_6669658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_6669658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669658 prefixEnd_6669658 := by exact prefixLift 6669658
  have htrace : WordTrace (prefixWord ++ tailWord_6669658) baseStart_6669658 baseEnd_6669658 := by
    simpa [prefixWord, tailWord_6669658, baseEnd_6669658] using wordTrace_append hprefix tailTrace_6669658
  have hstable : (prefixWord ++ tailWord_6669658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669658).length < 2 ^ (prefixWord ++ tailWord_6669658).sum := by decide
  have hdescent : baseEnd_6669658 < baseStart_6669658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669681 : List Nat := [1, 2, 2, 2, 1, 2, 13]
def baseStart_6669681 : Nat := 118140960795 + 6669681 * 2 ^ 59
def prefixEnd_6669681 : Nat := 4983230072969 + 3 ^ 40 * 6669681 * 2
def baseEnd_6669681 : Nat := 42280890927904007112521

theorem tailTrace_6669681 : CollatzResearch.WordTrace tailWord_6669681 prefixEnd_6669681 42280890927904007112521 := by
  unfold tailWord_6669681
  simp only [CollatzResearch.WordTrace]
  refine ⟨243263250949892302672256897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162175500633261535114837931 243263250949892302672256897)
  ·
    refine ⟨182447438212419227004192673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243263250949892302672256897 182447438212419227004192673)
    ·
      refine ⟨136835578659314420253144505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182447438212419227004192673 136835578659314420253144505)
      ·
        refine ⟨102626683994485815189858379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136835578659314420253144505 102626683994485815189858379)
        ·
          refine ⟨153940025991728722784787569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102626683994485815189858379 153940025991728722784787569)
          ·
            refine ⟨115455019493796542088590677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153940025991728722784787569 115455019493796542088590677)
            ·
              refine ⟨42280890927904007112521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 115455019493796542088590677 42280890927904007112521)
              ·
                rfl

theorem cell23_6669681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 13].length) (baseStart_6669681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669681 prefixEnd_6669681 := by exact prefixLift 6669681
  have htrace : WordTrace (prefixWord ++ tailWord_6669681) baseStart_6669681 baseEnd_6669681 := by
    simpa [prefixWord, tailWord_6669681, baseEnd_6669681] using wordTrace_append hprefix tailTrace_6669681
  have hstable : (prefixWord ++ tailWord_6669681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669681).length < 2 ^ (prefixWord ++ tailWord_6669681).sum := by decide
  have hdescent : baseEnd_6669681 < baseStart_6669681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669725 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_6669725 : Nat := 118140960795 + 6669725 * 2 ^ 59
def prefixEnd_6669725 : Nat := 4983230072969 + 3 ^ 40 * 6669725 * 2
def baseEnd_6669725 : Nat := 3424774758309022403963999

theorem tailTrace_6669725 : CollatzResearch.WordTrace tailWord_6669725 prefixEnd_6669725 3424774758309022403963999 := by
  unfold tailWord_6669725
  simp only [CollatzResearch.WordTrace]
  refine ⟨243264855761732898186858629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162176570507821932124572419 243264855761732898186858629)
  ·
    refine ⟨45612160455324918410035993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243264855761732898186858629 45612160455324918410035993)
    ·
      refine ⟨34209120341493688807526995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45612160455324918410035993 34209120341493688807526995)
      ·
        refine ⟨51313680512240533211290493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34209120341493688807526995 51313680512240533211290493)
        ·
          refine ⟨19242630192090199954233935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51313680512240533211290493 19242630192090199954233935)
          ·
            refine ⟨28863945288135299931350903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19242630192090199954233935 28863945288135299931350903)
            ·
              refine ⟨43295917932202949897026355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28863945288135299931350903 43295917932202949897026355)
              ·
                refine ⟨64943876898304424845539533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43295917932202949897026355 64943876898304424845539533)
                ·
                  refine ⟨24353953836864159317077325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64943876898304424845539533 24353953836864159317077325)
                  ·
                    refine ⟨9132732688824059743903997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24353953836864159317077325 9132732688824059743903997)
                    ·
                      refine ⟨3424774758309022403963999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9132732688824059743903997 3424774758309022403963999)
                      ·
                        rfl

theorem cell23_6669725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_6669725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669725 prefixEnd_6669725 := by exact prefixLift 6669725
  have htrace : WordTrace (prefixWord ++ tailWord_6669725) baseStart_6669725 baseEnd_6669725 := by
    simpa [prefixWord, tailWord_6669725, baseEnd_6669725] using wordTrace_append hprefix tailTrace_6669725
  have hstable : (prefixWord ++ tailWord_6669725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669725).length < 2 ^ (prefixWord ++ tailWord_6669725).sum := by decide
  have hdescent : baseEnd_6669725 < baseStart_6669725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669726 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6669726 : Nat := 118140960795 + 6669726 * 2 ^ 59
def prefixEnd_6669726 : Nat := 4983230072969 + 3 ^ 40 * 6669726 * 2
def baseEnd_6669726 : Nat := 3424775271789676900051495

theorem tailTrace_6669726 : CollatzResearch.WordTrace tailWord_6669726 prefixEnd_6669726 3424775271789676900051495 := by
  unfold tailWord_6669726
  simp only [CollatzResearch.WordTrace]
  refine ⟨30408111529341159419705629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162176594823152850238430021 30408111529341159419705629)
  ·
    refine ⟨11403041823502934782389611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30408111529341159419705629 11403041823502934782389611)
    ·
      refine ⟨17104562735254402173584417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11403041823502934782389611 17104562735254402173584417)
      ·
        refine ⟨12828422051440801630188313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17104562735254402173584417 12828422051440801630188313)
        ·
          refine ⟨9621316538580601222641235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12828422051440801630188313 9621316538580601222641235)
          ·
            refine ⟨14431974807870901833961853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9621316538580601222641235 14431974807870901833961853)
            ·
              refine ⟨5411990552951588187735695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14431974807870901833961853 5411990552951588187735695)
              ·
                refine ⟨8117985829427382281603543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5411990552951588187735695 8117985829427382281603543)
                ·
                  refine ⟨12176978744141073422405315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8117985829427382281603543 12176978744141073422405315)
                  ·
                    refine ⟨18265468116211610133607973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12176978744141073422405315 18265468116211610133607973)
                    ·
                      refine ⟨3424775271789676900051495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18265468116211610133607973 3424775271789676900051495)
                      ·
                        rfl

theorem cell23_6669726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6669726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669726 prefixEnd_6669726 := by exact prefixLift 6669726
  have htrace : WordTrace (prefixWord ++ tailWord_6669726) baseStart_6669726 baseEnd_6669726 := by
    simpa [prefixWord, tailWord_6669726, baseEnd_6669726] using wordTrace_append hprefix tailTrace_6669726
  have hstable : (prefixWord ++ tailWord_6669726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669726).length < 2 ^ (prefixWord ++ tailWord_6669726).sum := by decide
  have hdescent : baseEnd_6669726 < baseStart_6669726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669786 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2]
def baseStart_6669786 : Nat := 118140960795 + 6669786 * 2 ^ 59
def prefixEnd_6669786 : Nat := 4983230072969 + 3 ^ 40 * 6669786 * 2
def baseEnd_6669786 : Nat := 3424806080628946665301219

theorem tailTrace_6669786 : CollatzResearch.WordTrace tailWord_6669786 prefixEnd_6669786 3424806080628946665301219 := by
  unfold tailWord_6669786
  simp only [CollatzResearch.WordTrace]
  refine ⟨60816770153627976401207303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162178053743007937069886141 60816770153627976401207303)
  ·
    refine ⟨91225155230441964601810955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60816770153627976401207303 91225155230441964601810955)
    ·
      refine ⟨136837732845662946902716433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91225155230441964601810955 136837732845662946902716433)
      ·
        refine ⟨102628299634247210177037325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136837732845662946902716433 102628299634247210177037325)
        ·
          refine ⟨38485612362842703816388997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102628299634247210177037325 38485612362842703816388997)
          ·
            refine ⟨7216052318033006965572937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38485612362842703816388997 7216052318033006965572937)
            ·
              refine ⟨5412039238524755224179703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216052318033006965572937 5412039238524755224179703)
              ·
                refine ⟨8118058857787132836269555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412039238524755224179703 8118058857787132836269555)
                ·
                  refine ⟨12177088286680699254404333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118058857787132836269555 12177088286680699254404333)
                  ·
                    refine ⟨4566408107505262220401625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12177088286680699254404333 4566408107505262220401625)
                    ·
                      refine ⟨3424806080628946665301219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566408107505262220401625 3424806080628946665301219)
                      ·
                        rfl

theorem cell23_6669786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_6669786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669786 prefixEnd_6669786 := by exact prefixLift 6669786
  have htrace : WordTrace (prefixWord ++ tailWord_6669786) baseStart_6669786 baseEnd_6669786 := by
    simpa [prefixWord, tailWord_6669786, baseEnd_6669786] using wordTrace_append hprefix tailTrace_6669786
  have hstable : (prefixWord ++ tailWord_6669786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669786).length < 2 ^ (prefixWord ++ tailWord_6669786).sum := by decide
  have hdescent : baseEnd_6669786 < baseStart_6669786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669795 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6669795 : Nat := 118140960795 + 6669795 * 2 ^ 59
def prefixEnd_6669795 : Nat := 4983230072969 + 3 ^ 40 * 6669795 * 2
def baseEnd_6669795 : Nat := 3424810701954837130088677

theorem tailTrace_6669795 : CollatzResearch.WordTrace tailWord_6669795 prefixEnd_6669795 3424810701954837130088677 := by
  unfold tailWord_6669795
  simp only [CollatzResearch.WordTrace]
  refine ⟨243267408871479300141906839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162178272580986200094604559 243267408871479300141906839)
  ·
    refine ⟨364901113307218950212860259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243267408871479300141906839 364901113307218950212860259)
    ·
      refine ⟨547351669960828425319290389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364901113307218950212860259 547351669960828425319290389)
      ·
        refine ⟨25657109529413832436841737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 547351669960828425319290389 25657109529413832436841737)
        ·
          refine ⟨19242832147060374327631303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25657109529413832436841737 19242832147060374327631303)
          ·
            refine ⟨28864248220590561491446955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19242832147060374327631303 28864248220590561491446955)
            ·
              refine ⟨43296372330885842237170433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28864248220590561491446955 43296372330885842237170433)
              ·
                refine ⟨32472279248164381677877825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43296372330885842237170433 32472279248164381677877825)
                ·
                  refine ⟨24354209436123286258408369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32472279248164381677877825 24354209436123286258408369)
                  ·
                    refine ⟨18265657077092464693806277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24354209436123286258408369 18265657077092464693806277)
                    ·
                      refine ⟨3424810701954837130088677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18265657077092464693806277 3424810701954837130088677)
                      ·
                        rfl

theorem cell23_6669795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6669795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669795 prefixEnd_6669795 := by exact prefixLift 6669795
  have htrace : WordTrace (prefixWord ++ tailWord_6669795) baseStart_6669795 baseEnd_6669795 := by
    simpa [prefixWord, tailWord_6669795, baseEnd_6669795] using wordTrace_append hprefix tailTrace_6669795
  have hstable : (prefixWord ++ tailWord_6669795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669795).length < 2 ^ (prefixWord ++ tailWord_6669795).sum := by decide
  have hdescent : baseEnd_6669795 < baseStart_6669795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669799 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_6669799 : Nat := 118140960795 + 6669799 * 2 ^ 59
def prefixEnd_6669799 : Nat := 4983230072969 + 3 ^ 40 * 6669799 * 2
def baseEnd_6669799 : Nat := 3424812755877455114438659

theorem tailTrace_6669799 : CollatzResearch.WordTrace tailWord_6669799 prefixEnd_6669799 3424812755877455114438659 := by
  unfold tailWord_6669799
  simp only [CollatzResearch.WordTrace]
  refine ⟨243267554763464808825052451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162178369842309872550034967 243267554763464808825052451)
  ·
    refine ⟨364901332145197213237578677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243267554763464808825052451 364901332145197213237578677)
    ·
      refine ⟨34209499888612238741023001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 364901332145197213237578677 34209499888612238741023001)
      ·
        refine ⟨25657124916459179055767251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34209499888612238741023001 25657124916459179055767251)
        ·
          refine ⟨38485687374688768583650877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25657124916459179055767251 38485687374688768583650877)
          ·
            refine ⟨14432132765508288218869079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38485687374688768583650877 14432132765508288218869079)
            ·
              refine ⟨21648199148262432328303619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14432132765508288218869079 21648199148262432328303619)
              ·
                refine ⟨32472298722393648492455429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21648199148262432328303619 32472298722393648492455429)
                ·
                  refine ⟨6088556010448809092335393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32472298722393648492455429 6088556010448809092335393)
                  ·
                    refine ⟨4566417007836606819251545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6088556010448809092335393 4566417007836606819251545)
                    ·
                      refine ⟨3424812755877455114438659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566417007836606819251545 3424812755877455114438659)
                      ·
                        rfl

theorem cell23_6669799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_6669799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669799 prefixEnd_6669799 := by exact prefixLift 6669799
  have htrace : WordTrace (prefixWord ++ tailWord_6669799) baseStart_6669799 baseEnd_6669799 := by
    simpa [prefixWord, tailWord_6669799, baseEnd_6669799] using wordTrace_append hprefix tailTrace_6669799
  have hstable : (prefixWord ++ tailWord_6669799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669799).length < 2 ^ (prefixWord ++ tailWord_6669799).sum := by decide
  have hdescent : baseEnd_6669799 < baseStart_6669799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669816 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 2, 2, 2]
def baseStart_6669816 : Nat := 118140960795 + 6669816 * 2 ^ 59
def prefixEnd_6669816 : Nat := 4983230072969 + 3 ^ 40 * 6669816 * 2
def baseEnd_6669816 : Nat := 3424821485048581547926081

theorem tailTrace_6669816 : CollatzResearch.WordTrace tailWord_6669816 prefixEnd_6669816 3424821485048581547926081 := by
  unfold tailWord_6669816
  simp only [CollatzResearch.WordTrace]
  refine ⟨121634087402201610364210651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162178783202935480485614201 121634087402201610364210651)
  ·
    refine ⟨182451131103302415546315977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121634087402201610364210651 182451131103302415546315977)
    ·
      refine ⟨136838348327476811659736983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182451131103302415546315977 136838348327476811659736983)
      ·
        refine ⟨205257522491215217489605475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136838348327476811659736983 205257522491215217489605475)
        ·
          refine ⟨307886283736822826234408213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205257522491215217489605475 307886283736822826234408213)
          ·
            refine ⟨14432169550163569979737885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 307886283736822826234408213 14432169550163569979737885)
            ·
              refine ⟨5412063581311338742401707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14432169550163569979737885 5412063581311338742401707)
              ·
                refine ⟨8118095371967008113602561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412063581311338742401707 8118095371967008113602561)
                ·
                  refine ⟨6088571528975256085201921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118095371967008113602561 6088571528975256085201921)
                  ·
                    refine ⟨4566428646731442063901441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6088571528975256085201921 4566428646731442063901441)
                    ·
                      refine ⟨3424821485048581547926081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566428646731442063901441 3424821485048581547926081)
                      ·
                        rfl

theorem cell23_6669816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 2, 2, 2].length) (baseStart_6669816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669816 prefixEnd_6669816 := by exact prefixLift 6669816
  have htrace : WordTrace (prefixWord ++ tailWord_6669816) baseStart_6669816 baseEnd_6669816 := by
    simpa [prefixWord, tailWord_6669816, baseEnd_6669816] using wordTrace_append hprefix tailTrace_6669816
  have hstable : (prefixWord ++ tailWord_6669816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669816).length < 2 ^ (prefixWord ++ tailWord_6669816).sum := by decide
  have hdescent : baseEnd_6669816 < baseStart_6669816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669818 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_6669818 : Nat := 118140960795 + 6669818 * 2 ^ 59
def prefixEnd_6669818 : Nat := 4983230072969 + 3 ^ 40 * 6669818 * 2
def baseEnd_6669818 : Nat := 1141607504003296846700357

theorem tailTrace_6669818 : CollatzResearch.WordTrace tailWord_6669818 prefixEnd_6669818 1141607504003296846700357 := by
  unfold tailWord_6669818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60817061937598993767498527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162178831833597316713329405 60817061937598993767498527)
  ·
    refine ⟨91225592906398490651247791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60817061937598993767498527 91225592906398490651247791)
    ·
      refine ⟨136838389359597735976871687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91225592906398490651247791 136838389359597735976871687)
      ·
        refine ⟨205257584039396603965307531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136838389359597735976871687 205257584039396603965307531)
        ·
          refine ⟨307886376059094905947961297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205257584039396603965307531 307886376059094905947961297)
          ·
            refine ⟨230914782044321179460970973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307886376059094905947961297 230914782044321179460970973)
            ·
              refine ⟨86593043266620442297864115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230914782044321179460970973 86593043266620442297864115)
              ·
                refine ⟨129889564899930663446796173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86593043266620442297864115 129889564899930663446796173)
                ·
                  refine ⟨48708586837473998792548565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129889564899930663446796173 48708586837473998792548565)
                  ·
                    refine ⟨1141607504003296846700357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48708586837473998792548565 1141607504003296846700357)
                    ·
                      rfl

theorem cell23_6669818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_6669818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669818 prefixEnd_6669818 := by exact prefixLift 6669818
  have htrace : WordTrace (prefixWord ++ tailWord_6669818) baseStart_6669818 baseEnd_6669818 := by
    simpa [prefixWord, tailWord_6669818, baseEnd_6669818] using wordTrace_append hprefix tailTrace_6669818
  have hstable : (prefixWord ++ tailWord_6669818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669818).length < 2 ^ (prefixWord ++ tailWord_6669818).sum := by decide
  have hdescent : baseEnd_6669818 < baseStart_6669818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669855 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_6669855 : Nat := 118140960795 + 6669855 * 2 ^ 59
def prefixEnd_6669855 : Nat := 4983230072969 + 3 ^ 40 * 6669855 * 2
def baseEnd_6669855 : Nat := 3424841510794106895338401

theorem tailTrace_6669855 : CollatzResearch.WordTrace tailWord_6669855 prefixEnd_6669855 3424841510794106895338401 := by
  unfold tailWord_6669855
  simp only [CollatzResearch.WordTrace]
  refine ⟨243269597251261930389091019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162179731500841286926060679 243269597251261930389091019)
  ·
    refine ⟨364904395876892895583636529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243269597251261930389091019 364904395876892895583636529)
    ·
      refine ⟨273678296907669671687727397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364904395876892895583636529 273678296907669671687727397)
      ·
        refine ⟨51314680670188063441448887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273678296907669671687727397 51314680670188063441448887)
        ·
          refine ⟨76972021005282095162173331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51314680670188063441448887 76972021005282095162173331)
          ·
            refine ⟨115458031507923142743259997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76972021005282095162173331 115458031507923142743259997)
            ·
              refine ⟨43296761815471178528722499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115458031507923142743259997 43296761815471178528722499)
              ·
                refine ⟨64945142723206767793083749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43296761815471178528722499 64945142723206767793083749)
                ·
                  refine ⟨12177214260601268961203203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64945142723206767793083749 12177214260601268961203203)
                  ·
                    refine ⟨18265821390901903441804805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12177214260601268961203203 18265821390901903441804805)
                    ·
                      refine ⟨3424841510794106895338401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18265821390901903441804805 3424841510794106895338401)
                      ·
                        rfl

theorem cell23_6669855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_6669855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669855 prefixEnd_6669855 := by exact prefixLift 6669855
  have htrace : WordTrace (prefixWord ++ tailWord_6669855) baseStart_6669855 baseEnd_6669855 := by
    simpa [prefixWord, tailWord_6669855, baseEnd_6669855] using wordTrace_append hprefix tailTrace_6669855
  have hstable : (prefixWord ++ tailWord_6669855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669855).length < 2 ^ (prefixWord ++ tailWord_6669855).sum := by decide
  have hdescent : baseEnd_6669855 < baseStart_6669855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669916 : List Nat := [2, 2, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6669916 : Nat := 118140960795 + 6669916 * 2 ^ 59
def prefixEnd_6669916 : Nat := 4983230072969 + 3 ^ 40 * 6669916 * 2
def baseEnd_6669916 : Nat := 1141624277704677052225207

theorem tailTrace_6669916 : CollatzResearch.WordTrace tailWord_6669916 prefixEnd_6669916 1141624277704677052225207 := by
  unfold tailWord_6669916
  simp only [CollatzResearch.WordTrace]
  refine ⟨121635911052020468903530801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162181214736027291871374401 121635911052020468903530801)
  ·
    refine ⟨91226933289015351677648101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121635911052020468903530801 91226933289015351677648101)
    ·
      refine ⟨17105049991690378439559019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91226933289015351677648101 17105049991690378439559019)
      ·
        refine ⟨25657574987535567659338529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17105049991690378439559019 25657574987535567659338529)
        ·
          refine ⟨19243181240651675744503897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25657574987535567659338529 19243181240651675744503897)
          ·
            refine ⟨14432385930488756808377923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19243181240651675744503897 14432385930488756808377923)
            ·
              refine ⟨21648578895733135212566885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14432385930488756808377923 21648578895733135212566885)
              ·
                refine ⟨4059108542949962852356291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21648578895733135212566885 4059108542949962852356291)
                ·
                  refine ⟨6088662814424944278534437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059108542949962852356291 6088662814424944278534437)
                  ·
                    refine ⟨1141624277704677052225207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088662814424944278534437 1141624277704677052225207)
                    ·
                      rfl

theorem cell23_6669916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6669916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669916 prefixEnd_6669916 := by exact prefixLift 6669916
  have htrace : WordTrace (prefixWord ++ tailWord_6669916) baseStart_6669916 baseEnd_6669916 := by
    simpa [prefixWord, tailWord_6669916, baseEnd_6669916] using wordTrace_append hprefix tailTrace_6669916
  have hstable : (prefixWord ++ tailWord_6669916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669916).length < 2 ^ (prefixWord ++ tailWord_6669916).sum := by decide
  have hdescent : baseEnd_6669916 < baseStart_6669916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669932 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 1, 5, 2]
def baseStart_6669932 : Nat := 118140960795 + 6669932 * 2 ^ 59
def prefixEnd_6669932 : Nat := 4983230072969 + 3 ^ 40 * 6669932 * 2
def baseEnd_6669932 : Nat := 3424881048804503094075547

theorem tailTrace_6669932 : CollatzResearch.WordTrace tailWord_6669932 prefixEnd_6669932 3424881048804503094075547 := by
  unfold tailWord_6669932
  simp only [CollatzResearch.WordTrace]
  refine ⟨121636202835991486269822025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162181603781321981693096033 121636202835991486269822025)
  ·
    refine ⟨91227152126993614702366519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121636202835991486269822025 91227152126993614702366519)
    ·
      refine ⟨136840728190490422053549779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91227152126993614702366519 136840728190490422053549779)
      ·
        refine ⟨205261092285735633080324669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136840728190490422053549779 205261092285735633080324669)
        ·
          refine ⟨76972909607150862405121751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205261092285735633080324669 76972909607150862405121751)
          ·
            refine ⟨115459364410726293607682627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76972909607150862405121751 115459364410726293607682627)
            ·
              refine ⟨173189046616089440411523941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115459364410726293607682627 173189046616089440411523941)
              ·
                refine ⟨32472946240516770077160739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173189046616089440411523941 32472946240516770077160739)
                ·
                  refine ⟨48709419360775155115741109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32472946240516770077160739 48709419360775155115741109)
                  ·
                    refine ⟨4566508065072670792100729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48709419360775155115741109 4566508065072670792100729)
                    ·
                      refine ⟨3424881048804503094075547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566508065072670792100729 3424881048804503094075547)
                      ·
                        rfl

theorem cell23_6669932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_6669932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669932 prefixEnd_6669932 := by exact prefixLift 6669932
  have htrace : WordTrace (prefixWord ++ tailWord_6669932) baseStart_6669932 baseEnd_6669932 := by
    simpa [prefixWord, tailWord_6669932, baseEnd_6669932] using wordTrace_append hprefix tailTrace_6669932
  have hstable : (prefixWord ++ tailWord_6669932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669932).length < 2 ^ (prefixWord ++ tailWord_6669932).sum := by decide
  have hdescent : baseEnd_6669932 < baseStart_6669932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669949 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 1, 5, 2]
def baseStart_6669949 : Nat := 118140960795 + 6669949 * 2 ^ 59
def prefixEnd_6669949 : Nat := 4983230072969 + 3 ^ 40 * 6669949 * 2
def baseEnd_6669949 : Nat := 3424889777975629527562969

theorem tailTrace_6669949 : CollatzResearch.WordTrace tailWord_6669949 prefixEnd_6669949 3424889777975629527562969 := by
  unfold tailWord_6669949
  simp only [CollatzResearch.WordTrace]
  refine ⟨243273025712921384443012901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162182017141947589628675267 243273025712921384443012901)
  ·
    refine ⟨45613692321172759583064919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243273025712921384443012901 45613692321172759583064919)
    ·
      refine ⟨68420538481759139374597379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45613692321172759583064919 68420538481759139374597379)
      ·
        refine ⟨102630807722638709061896069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68420538481759139374597379 102630807722638709061896069)
        ·
          refine ⟨19243276447994757949105513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102630807722638709061896069 19243276447994757949105513)
          ·
            refine ⟨14432457335996068461829135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19243276447994757949105513 14432457335996068461829135)
            ·
              refine ⟨21648686003994102692743703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14432457335996068461829135 21648686003994102692743703)
              ·
                refine ⟨32473029005991154039115555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21648686003994102692743703 32473029005991154039115555)
                ·
                  refine ⟨48709543508986731058673333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32473029005991154039115555 48709543508986731058673333)
                  ·
                    refine ⟨4566519703967506036750625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48709543508986731058673333 4566519703967506036750625)
                    ·
                      refine ⟨3424889777975629527562969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566519703967506036750625 3424889777975629527562969)
                      ·
                        rfl

theorem cell23_6669949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 5, 2].length) (baseStart_6669949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669949 prefixEnd_6669949 := by exact prefixLift 6669949
  have htrace : WordTrace (prefixWord ++ tailWord_6669949) baseStart_6669949 baseEnd_6669949 := by
    simpa [prefixWord, tailWord_6669949, baseEnd_6669949] using wordTrace_append hprefix tailTrace_6669949
  have hstable : (prefixWord ++ tailWord_6669949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669949).length < 2 ^ (prefixWord ++ tailWord_6669949).sum := by decide
  have hdescent : baseEnd_6669949 < baseStart_6669949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669959 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 1, 5]
def baseStart_6669959 : Nat := 118140960795 + 6669959 * 2 ^ 59
def prefixEnd_6669959 : Nat := 4983230072969 + 3 ^ 40 * 6669959 * 2
def baseEnd_6669959 : Nat := 1141631637594058162812641

theorem tailTrace_6669959 : CollatzResearch.WordTrace tailWord_6669959 prefixEnd_6669959 1141631637594058162812641 := by
  unfold tailWord_6669959
  simp only [CollatzResearch.WordTrace]
  refine ⟨243273390442885156150876931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162182260295256770767251287 243273390442885156150876931)
  ·
    refine ⟨364910085664327734226315397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243273390442885156150876931 364910085664327734226315397)
    ·
      refine ⟨68420641062061450167434137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364910085664327734226315397 68420641062061450167434137)
      ·
        refine ⟨51315480796546087625575603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68420641062061450167434137 51315480796546087625575603)
        ·
          refine ⟨76973221194819131438363405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51315480796546087625575603 76973221194819131438363405)
          ·
            refine ⟨28864957948057174289386277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76973221194819131438363405 28864957948057174289386277)
            ·
              refine ⟨5412179615260720179259927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28864957948057174289386277 5412179615260720179259927)
              ·
                refine ⟨8118269422891080268889891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412179615260720179259927 8118269422891080268889891)
                ·
                  refine ⟨12177404134336620403334837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118269422891080268889891 12177404134336620403334837)
                  ·
                    refine ⟨1141631637594058162812641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12177404134336620403334837 1141631637594058162812641)
                    ·
                      rfl

theorem cell23_6669959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_6669959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669959 prefixEnd_6669959 := by exact prefixLift 6669959
  have htrace : WordTrace (prefixWord ++ tailWord_6669959) baseStart_6669959 baseEnd_6669959 := by
    simpa [prefixWord, tailWord_6669959, baseEnd_6669959] using wordTrace_append hprefix tailTrace_6669959
  have hstable : (prefixWord ++ tailWord_6669959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669959).length < 2 ^ (prefixWord ++ tailWord_6669959).sum := by decide
  have hdescent : baseEnd_6669959 < baseStart_6669959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6669999 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 3]
def baseStart_6669999 : Nat := 118140960795 + 6669999 * 2 ^ 59
def prefixEnd_6669999 : Nat := 4983230072969 + 3 ^ 40 * 6669999 * 2
def baseEnd_6669999 : Nat := 3424915452008354331937739

theorem tailTrace_6669999 : CollatzResearch.WordTrace tailWord_6669999 prefixEnd_6669999 3424915452008354331937739 := by
  unfold tailWord_6669999
  simp only [CollatzResearch.WordTrace]
  refine ⟨243274849362740242982333051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162183232908493495321555367 243274849362740242982333051)
  ·
    refine ⟨364912274044110364473499577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243274849362740242982333051 364912274044110364473499577)
    ·
      refine ⟨273684205533082773355124683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364912274044110364473499577 273684205533082773355124683)
      ·
        refine ⟨410526308299624160032687025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273684205533082773355124683 410526308299624160032687025)
        ·
          refine ⟨307894731224718120024515269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410526308299624160032687025 307894731224718120024515269)
          ·
            refine ⟨57730262104634647504596613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307894731224718120024515269 57730262104634647504596613)
            ·
              refine ⟨10824424144618996407111865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57730262104634647504596613 10824424144618996407111865)
              ·
                refine ⟨8118318108464247305333899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10824424144618996407111865 8118318108464247305333899)
                ·
                  refine ⟨12177477162696370958000849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118318108464247305333899 12177477162696370958000849)
                  ·
                    refine ⟨9133107872022278218500637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12177477162696370958000849 9133107872022278218500637)
                    ·
                      refine ⟨3424915452008354331937739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133107872022278218500637 3424915452008354331937739)
                      ·
                        rfl

theorem cell23_6669999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_6669999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6669999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6669999 prefixEnd_6669999 := by exact prefixLift 6669999
  have htrace : WordTrace (prefixWord ++ tailWord_6669999) baseStart_6669999 baseEnd_6669999 := by
    simpa [prefixWord, tailWord_6669999, baseEnd_6669999] using wordTrace_append hprefix tailTrace_6669999
  have hstable : (prefixWord ++ tailWord_6669999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6669999).length < 2 ^ (prefixWord ++ tailWord_6669999).sum := by decide
  have hdescent : baseEnd_6669999 < baseStart_6669999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6669999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670002 : List Nat := [3, 2, 1, 1, 1, 2, 6, 7]
def baseStart_6670002 : Nat := 118140960795 + 6670002 * 2 ^ 59
def prefixEnd_6670002 : Nat := 4983230072969 + 3 ^ 40 * 6670002 * 2
def baseEnd_6670002 : Nat := 126848777498159919266675

theorem tailTrace_6670002 : CollatzResearch.WordTrace tailWord_6670002 prefixEnd_6670002 126848777498159919266675 := by
  unfold tailWord_6670002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60818739695432343623673065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162183305854486249663128173 60818739695432343623673065)
  ·
    refine ⟨45614054771574257717754799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60818739695432343623673065 45614054771574257717754799)
    ·
      refine ⟨68421082157361386576632199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45614054771574257717754799 68421082157361386576632199)
      ·
        refine ⟨102631623236042079864948299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68421082157361386576632199 102631623236042079864948299)
        ·
          refine ⟨153947434854063119797422449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102631623236042079864948299 153947434854063119797422449)
          ·
            refine ⟨115460576140547339848066837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153947434854063119797422449 115460576140547339848066837)
            ·
              refine ⟨5412214506588156555378133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115460576140547339848066837 5412214506588156555378133)
              ·
                refine ⟨126848777498159919266675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5412214506588156555378133 126848777498159919266675)
                ·
                  rfl

theorem cell23_6670002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_6670002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670002 prefixEnd_6670002 := by exact prefixLift 6670002
  have htrace : WordTrace (prefixWord ++ tailWord_6670002) baseStart_6670002 baseEnd_6670002 := by
    simpa [prefixWord, tailWord_6670002, baseEnd_6670002] using wordTrace_append hprefix tailTrace_6670002
  have hstable : (prefixWord ++ tailWord_6670002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670002).length < 2 ^ (prefixWord ++ tailWord_6670002).sum := by decide
  have hdescent : baseEnd_6670002 < baseStart_6670002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670006 : List Nat := [5, 1, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6670006 : Nat := 118140960795 + 6670006 * 2 ^ 59
def prefixEnd_6670006 : Nat := 4983230072969 + 3 ^ 40 * 6670006 * 2
def baseEnd_6670006 : Nat := 1141639682124311934850069

theorem tailTrace_6670006 : CollatzResearch.WordTrace tailWord_6670006 prefixEnd_6670006 1141639682124311934850069 := by
  unfold tailWord_6670006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15204694042107180198614867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162183403115809922118558581 15204694042107180198614867)
  ·
    refine ⟨22807041063160770297922301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15204694042107180198614867 22807041063160770297922301)
    ·
      refine ⟨8552640398685288861720863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22807041063160770297922301 8552640398685288861720863)
      ·
        refine ⟨12828960598027933292581295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8552640398685288861720863 12828960598027933292581295)
        ·
          refine ⟨19243440897041899938871943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12828960598027933292581295 19243440897041899938871943)
          ·
            refine ⟨28865161345562849908307915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19243440897041899938871943 28865161345562849908307915)
            ·
              refine ⟨43297742018344274862461873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28865161345562849908307915 43297742018344274862461873)
              ·
                refine ⟨32473306513758206146846405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43297742018344274862461873 32473306513758206146846405)
                ·
                  refine ⟨6088744971329663652533701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32473306513758206146846405 6088744971329663652533701)
                  ·
                    refine ⟨1141639682124311934850069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088744971329663652533701 1141639682124311934850069)
                    ·
                      rfl

theorem cell23_6670006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6670006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670006 prefixEnd_6670006 := by exact prefixLift 6670006
  have htrace : WordTrace (prefixWord ++ tailWord_6670006) baseStart_6670006 baseEnd_6670006 := by
    simpa [prefixWord, tailWord_6670006, baseEnd_6670006] using wordTrace_append hprefix tailTrace_6670006
  have hstable : (prefixWord ++ tailWord_6670006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670006).length < 2 ^ (prefixWord ++ tailWord_6670006).sum := by decide
  have hdescent : baseEnd_6670006 < baseStart_6670006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670030 : List Nat := [4, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_6670030 : Nat := 118140960795 + 6670030 * 2 ^ 59
def prefixEnd_6670030 : Nat := 4983230072969 + 3 ^ 40 * 6670030 * 2
def baseEnd_6670030 : Nat := 3424931369908643710650097

theorem tailTrace_6670030 : CollatzResearch.WordTrace tailWord_6670030 prefixEnd_6670030 3424931369908643710650097 := by
  unfold tailWord_6670030
  simp only [CollatzResearch.WordTrace]
  refine ⟨30409497503203491909588943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162183986683751956851141029 30409497503203491909588943)
  ·
    refine ⟨45614246254805237864383415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30409497503203491909588943 45614246254805237864383415)
    ·
      refine ⟨68421369382207856796575123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45614246254805237864383415 68421369382207856796575123)
      ·
        refine ⟨102632054073311785194862685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68421369382207856796575123 102632054073311785194862685)
        ·
          refine ⟨38487020277491919448073507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102632054073311785194862685 38487020277491919448073507)
          ·
            refine ⟨57730530416237879172110261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38487020277491919448073507 57730530416237879172110261)
            ·
              refine ⟨5412237226522301172385337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57730530416237879172110261 5412237226522301172385337)
              ·
                refine ⟨4059177919891725879289003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5412237226522301172385337 4059177919891725879289003)
                ·
                  refine ⟨6088766879837588818933505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059177919891725879289003 6088766879837588818933505)
                  ·
                    refine ⟨4566575159878191614200129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6088766879837588818933505 4566575159878191614200129)
                    ·
                      refine ⟨3424931369908643710650097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566575159878191614200129 3424931369908643710650097)
                      ·
                        rfl

theorem cell23_6670030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_6670030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670030 prefixEnd_6670030 := by exact prefixLift 6670030
  have htrace : WordTrace (prefixWord ++ tailWord_6670030) baseStart_6670030 baseEnd_6670030 := by
    simpa [prefixWord, tailWord_6670030, baseEnd_6670030] using wordTrace_append hprefix tailTrace_6670030
  have hstable : (prefixWord ++ tailWord_6670030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670030).length < 2 ^ (prefixWord ++ tailWord_6670030).sum := by decide
  have hdescent : baseEnd_6670030 < baseStart_6670030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670039 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 3, 3, 2]
def baseStart_6670039 : Nat := 118140960795 + 6670039 * 2 ^ 59
def prefixEnd_6670039 : Nat := 4983230072969 + 3 ^ 40 * 6670039 * 2
def baseEnd_6670039 : Nat := 3424935991234534175437555

theorem tailTrace_6670039 : CollatzResearch.WordTrace tailWord_6670039 prefixEnd_6670039 3424935991234534175437555 := by
  unfold tailWord_6670039
  simp only [CollatzResearch.WordTrace]
  refine ⟨243276308282595329813789171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162184205521730219875859447 243276308282595329813789171)
  ·
    refine ⟨364914462423892994720683757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243276308282595329813789171 364914462423892994720683757)
    ·
      refine ⟨136842923408959873020256409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364914462423892994720683757 136842923408959873020256409)
      ·
        refine ⟨102632192556719904765192307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136842923408959873020256409 102632192556719904765192307)
        ·
          refine ⟨153948288835079857147788461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102632192556719904765192307 153948288835079857147788461)
          ·
            refine ⟨57730608313154946430420673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153948288835079857147788461 57730608313154946430420673)
            ·
              refine ⟨43297956234866209822815505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57730608313154946430420673 43297956234866209822815505)
              ·
                refine ⟨32473467176149657367111629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43297956234866209822815505 32473467176149657367111629)
                ·
                  refine ⟨12177550191056121512666861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32473467176149657367111629 12177550191056121512666861)
                  ·
                    refine ⟨4566581321646045567250073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12177550191056121512666861 4566581321646045567250073)
                    ·
                      refine ⟨3424935991234534175437555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566581321646045567250073 3424935991234534175437555)
                      ·
                        rfl

theorem cell23_6670039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_6670039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670039 prefixEnd_6670039 := by exact prefixLift 6670039
  have htrace : WordTrace (prefixWord ++ tailWord_6670039) baseStart_6670039 baseEnd_6670039 := by
    simpa [prefixWord, tailWord_6670039, baseEnd_6670039] using wordTrace_append hprefix tailTrace_6670039
  have hstable : (prefixWord ++ tailWord_6670039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670039).length < 2 ^ (prefixWord ++ tailWord_6670039).sum := by decide
  have hdescent : baseEnd_6670039 < baseStart_6670039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670056 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6670056 : Nat := 118140960795 + 6670056 * 2 ^ 59
def prefixEnd_6670056 : Nat := 4983230072969 + 3 ^ 40 * 6670056 * 2
def baseEnd_6670056 : Nat := 3424944720405660608924977

theorem tailTrace_6670056 : CollatzResearch.WordTrace tailWord_6670056 prefixEnd_6670056 3424944720405660608924977 := by
  unfold tailWord_6670056
  simp only [CollatzResearch.WordTrace]
  refine ⟨121638464161766870858579011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162184618882355827811438681 121638464161766870858579011)
  ·
    refine ⟨182457696242650306287868517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121638464161766870858579011 182457696242650306287868517)
    ·
      refine ⟨34210818045496932428975347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182457696242650306287868517 34210818045496932428975347)
      ·
        refine ⟨51316227068245398643463021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34210818045496932428975347 51316227068245398643463021)
        ·
          refine ⟨19243585150592024491298633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51316227068245398643463021 19243585150592024491298633)
          ·
            refine ⟨14432688862944018368473975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19243585150592024491298633 14432688862944018368473975)
            ·
              refine ⟨21649033294416027552710963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14432688862944018368473975 21649033294416027552710963)
              ·
                refine ⟨32473549941624041329066445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21649033294416027552710963 32473549941624041329066445)
                ·
                  refine ⟨12177581228109015498399917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32473549941624041329066445 12177581228109015498399917)
                  ·
                    refine ⟨4566592960540880811899969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12177581228109015498399917 4566592960540880811899969)
                    ·
                      refine ⟨3424944720405660608924977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566592960540880811899969 3424944720405660608924977)
                      ·
                        rfl

theorem cell23_6670056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6670056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670056 prefixEnd_6670056 := by exact prefixLift 6670056
  have htrace : WordTrace (prefixWord ++ tailWord_6670056) baseStart_6670056 baseEnd_6670056 := by
    simpa [prefixWord, tailWord_6670056, baseEnd_6670056] using wordTrace_append hprefix tailTrace_6670056
  have hstable : (prefixWord ++ tailWord_6670056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670056).length < 2 ^ (prefixWord ++ tailWord_6670056).sum := by decide
  have hdescent : baseEnd_6670056 < baseStart_6670056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670075 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 11]
def baseStart_6670075 : Nat := 118140960795 + 6670075 * 2 ^ 59
def prefixEnd_6670075 : Nat := 4983230072969 + 3 ^ 40 * 6670075 * 2
def baseEnd_6670075 : Nat := 380550497393121781620821

theorem tailTrace_6670075 : CollatzResearch.WordTrace tailWord_6670075 prefixEnd_6670075 380550497393121781620821 := by
  unfold tailWord_6670075
  simp only [CollatzResearch.WordTrace]
  refine ⟨243277621310464907962099679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162185080873643271974733119 243277621310464907962099679)
  ·
    refine ⟨364916431965697361943149519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243277621310464907962099679 364916431965697361943149519)
    ·
      refine ⟨547374647948546042914724279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364916431965697361943149519 547374647948546042914724279)
      ·
        refine ⟨821061971922819064372086419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547374647948546042914724279 821061971922819064372086419)
        ·
          refine ⟨1231592957884228596558129629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821061971922819064372086419 1231592957884228596558129629)
          ·
            refine ⟨461847359206585723709298611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1231592957884228596558129629 461847359206585723709298611)
            ·
              refine ⟨692771038809878585563947917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461847359206585723709298611 692771038809878585563947917)
              ·
                refine ⟨259789139553704469586480469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 692771038809878585563947917 259789139553704469586480469)
                ·
                  refine ⟨380550497393121781620821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 259789139553704469586480469 380550497393121781620821)
                  ·
                    rfl

theorem cell23_6670075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 11].length) (baseStart_6670075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670075 prefixEnd_6670075 := by exact prefixLift 6670075
  have htrace : WordTrace (prefixWord ++ tailWord_6670075) baseStart_6670075 baseEnd_6670075 := by
    simpa [prefixWord, tailWord_6670075, baseEnd_6670075] using wordTrace_append hprefix tailTrace_6670075
  have hstable : (prefixWord ++ tailWord_6670075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670075).length < 2 ^ (prefixWord ++ tailWord_6670075).sum := by decide
  have hdescent : baseEnd_6670075 < baseStart_6670075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670103 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 2, 2, 2]
def baseStart_6670103 : Nat := 118140960795 + 6670103 * 2 ^ 59
def prefixEnd_6670103 : Nat := 4983230072969 + 3 ^ 40 * 6670103 * 2
def baseEnd_6670103 : Nat := 3424968853996421925037261

theorem tailTrace_6670103 : CollatzResearch.WordTrace tailWord_6670103 prefixEnd_6670103 3424968853996421925037261 := by
  unfold tailWord_6670103
  simp only [CollatzResearch.WordTrace]
  refine ⟨243278642554363468744118963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162185761702908979162745975 243278642554363468744118963)
  ·
    refine ⟨364917963831545203116178445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243278642554363468744118963 364917963831545203116178445)
    ·
      refine ⟨136844236436829451168566917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364917963831545203116178445 136844236436829451168566917)
      ·
        refine ⟨25658294331905522094106297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136844236436829451168566917 25658294331905522094106297)
        ·
          refine ⟨19243720748929141570579723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25658294331905522094106297 19243720748929141570579723)
          ·
            refine ⟨28865581123393712355869585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19243720748929141570579723 28865581123393712355869585)
            ·
              refine ⟨21649185842545284266902189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28865581123393712355869585 21649185842545284266902189)
              ·
                refine ⟨8118444690954481600088321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21649185842545284266902189 8118444690954481600088321)
                ·
                  refine ⟨6088833518215861200066241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118444690954481600088321 6088833518215861200066241)
                  ·
                    refine ⟨4566625138661895900049681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6088833518215861200066241 4566625138661895900049681)
                    ·
                      refine ⟨3424968853996421925037261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566625138661895900049681 3424968853996421925037261)
                      ·
                        rfl

theorem cell23_6670103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_6670103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670103 prefixEnd_6670103 := by exact prefixLift 6670103
  have htrace : WordTrace (prefixWord ++ tailWord_6670103) baseStart_6670103 baseEnd_6670103 := by
    simpa [prefixWord, tailWord_6670103, baseEnd_6670103] using wordTrace_append hprefix tailTrace_6670103
  have hstable : (prefixWord ++ tailWord_6670103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670103).length < 2 ^ (prefixWord ++ tailWord_6670103).sum := by decide
  have hdescent : baseEnd_6670103 < baseStart_6670103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670137 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6670137 : Nat := 118140960795 + 6670137 * 2 ^ 59
def prefixEnd_6670137 : Nat := 4983230072969 + 3 ^ 40 * 6670137 * 2
def baseEnd_6670137 : Nat := 3424986312338674792012105

theorem tailTrace_6670137 : CollatzResearch.WordTrace tailWord_6670137 prefixEnd_6670137 3424986312338674792012105 := by
  unfold tailWord_6670137
  simp only [CollatzResearch.WordTrace]
  refine ⟨243279882636240292550856665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162186588424160195033904443 243279882636240292550856665)
  ·
    refine ⟨182459911977180219413142499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243279882636240292550856665 182459911977180219413142499)
    ·
      refine ⟨273689867965770329119713749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182459911977180219413142499 273689867965770329119713749)
      ·
        refine ⟨6414606280447742088743291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 273689867965770329119713749 6414606280447742088743291)
        ·
          refine ⟨9621909420671613133114937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414606280447742088743291 9621909420671613133114937)
          ·
            refine ⟨7216432065503709849836203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9621909420671613133114937 7216432065503709849836203)
            ·
              refine ⟨10824648098255564774754305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216432065503709849836203 10824648098255564774754305)
              ·
                refine ⟨8118486073691673581065729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10824648098255564774754305 8118486073691673581065729)
                ·
                  refine ⟨6088864555268755185799297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118486073691673581065729 6088864555268755185799297)
                  ·
                    refine ⟨4566648416451566389349473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6088864555268755185799297 4566648416451566389349473)
                    ·
                      refine ⟨3424986312338674792012105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566648416451566389349473 3424986312338674792012105)
                      ·
                        rfl

theorem cell23_6670137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6670137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670137 prefixEnd_6670137 := by exact prefixLift 6670137
  have htrace : WordTrace (prefixWord ++ tailWord_6670137) baseStart_6670137 baseEnd_6670137 := by
    simpa [prefixWord, tailWord_6670137, baseEnd_6670137] using wordTrace_append hprefix tailTrace_6670137
  have hstable : (prefixWord ++ tailWord_6670137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670137).length < 2 ^ (prefixWord ++ tailWord_6670137).sum := by decide
  have hdescent : baseEnd_6670137 < baseStart_6670137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670169 : List Nat := [1, 2, 1, 2, 2, 3, 1, 4, 3, 4]
def baseStart_6670169 : Nat := 118140960795 + 6670169 * 2 ^ 59
def prefixEnd_6670169 : Nat := 4983230072969 + 3 ^ 40 * 6670169 * 2
def baseEnd_6670169 : Nat := 1141667581239872888937319

theorem tailTrace_6670169 : CollatzResearch.WordTrace tailWord_6670169 prefixEnd_6670169 1141667581239872888937319 := by
  unfold tailWord_6670169
  simp only [CollatzResearch.WordTrace]
  refine ⟨243281049772124362016021561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162187366514749574677347707 243281049772124362016021561)
  ·
    refine ⟨182460787329093271512016171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243281049772124362016021561 182460787329093271512016171)
    ·
      refine ⟨273691180993639907268024257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182460787329093271512016171 273691180993639907268024257)
      ·
        refine ⟨205268385745229930451018193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273691180993639907268024257 205268385745229930451018193)
        ·
          refine ⟨153951289308922447838263645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205268385745229930451018193 153951289308922447838263645)
          ·
            refine ⟨57731733490845917939348867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153951289308922447838263645 57731733490845917939348867)
            ·
              refine ⟨86597600236268876909023301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57731733490845917939348867 86597600236268876909023301)
              ·
                refine ⟨16237050044300414420441869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86597600236268876909023301 16237050044300414420441869)
                ·
                  refine ⟨6088893766612655407665701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16237050044300414420441869 6088893766612655407665701)
                  ·
                    refine ⟨1141667581239872888937319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088893766612655407665701 1141667581239872888937319)
                    ·
                      rfl

theorem cell23_6670169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 4].length) (baseStart_6670169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670169 prefixEnd_6670169 := by exact prefixLift 6670169
  have htrace : WordTrace (prefixWord ++ tailWord_6670169) baseStart_6670169 baseEnd_6670169 := by
    simpa [prefixWord, tailWord_6670169, baseEnd_6670169] using wordTrace_append hprefix tailTrace_6670169
  have hstable : (prefixWord ++ tailWord_6670169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670169).length < 2 ^ (prefixWord ++ tailWord_6670169).sum := by decide
  have hdescent : baseEnd_6670169 < baseStart_6670169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670202 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_6670202 : Nat := 118140960795 + 6670202 * 2 ^ 59
def prefixEnd_6670202 : Nat := 4983230072969 + 3 ^ 40 * 6670202 * 2
def baseEnd_6670202 : Nat := 3425019688581217037699305

theorem tailTrace_6670202 : CollatzResearch.WordTrace tailWord_6670202 prefixEnd_6670202 3425019688581217037699305 := by
  unfold tailWord_6670202
  simp only [CollatzResearch.WordTrace]
  refine ⟨60820563345251202162993215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162188168920669872434648573 60820563345251202162993215)
  ·
    refine ⟨91230845017876803244489823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60820563345251202162993215 91230845017876803244489823)
    ·
      refine ⟨136846267526815204866734735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91230845017876803244489823 136846267526815204866734735)
      ·
        refine ⟨205269401290222807300102103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136846267526815204866734735 205269401290222807300102103)
        ·
          refine ⟨307904101935334210950153155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205269401290222807300102103 307904101935334210950153155)
          ·
            refine ⟨461856152903001316425229733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307904101935334210950153155 461856152903001316425229733)
            ·
              refine ⟨86598028669312746829730575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461856152903001316425229733 86598028669312746829730575)
              ·
                refine ⟨129897043003969120244595863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86598028669312746829730575 129897043003969120244595863)
                ·
                  refine ⟨194845564505953680366893795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129897043003969120244595863 194845564505953680366893795)
                  ·
                    refine ⟨292268346758930520550340693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194845564505953680366893795 292268346758930520550340693)
                    ·
                      refine ⟨3425019688581217037699305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 292268346758930520550340693 3425019688581217037699305)
                      ·
                        rfl

theorem cell23_6670202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_6670202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670202 prefixEnd_6670202 := by exact prefixLift 6670202
  have htrace : WordTrace (prefixWord ++ tailWord_6670202) baseStart_6670202 baseEnd_6670202 := by
    simpa [prefixWord, tailWord_6670202, baseEnd_6670202] using wordTrace_append hprefix tailTrace_6670202
  have hstable : (prefixWord ++ tailWord_6670202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670202).length < 2 ^ (prefixWord ++ tailWord_6670202).sum := by decide
  have hdescent : baseEnd_6670202 < baseStart_6670202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670216 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 6]
def baseStart_6670216 : Nat := 118140960795 + 6670216 * 2 ^ 59
def prefixEnd_6670216 : Nat := 4983230072969 + 3 ^ 40 * 6670216 * 2
def baseEnd_6670216 : Nat := 380558541923375553658249

theorem tailTrace_6670216 : CollatzResearch.WordTrace tailWord_6670216 prefixEnd_6670216 380558541923375553658249 := by
  unfold tailWord_6670216
  simp only [CollatzResearch.WordTrace]
  refine ⟨121641382001477044521491251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162188509335302726028655001 121641382001477044521491251)
  ·
    refine ⟨182462073002215566782236877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121641382001477044521491251 182462073002215566782236877)
    ·
      refine ⟨68423277375830837543338829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182462073002215566782236877 68423277375830837543338829)
      ·
        refine ⟨25658729015936564078752061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68423277375830837543338829 25658729015936564078752061)
        ·
          refine ⟨9622023380976211529532023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25658729015936564078752061 9622023380976211529532023)
          ·
            refine ⟨14433035071464317294298035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9622023380976211529532023 14433035071464317294298035)
            ·
              refine ⟨21649552607196475941447053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14433035071464317294298035 21649552607196475941447053)
              ·
                refine ⟨8118582227698678478042645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21649552607196475941447053 8118582227698678478042645)
                ·
                  refine ⟨380558541923375553658249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8118582227698678478042645 380558541923375553658249)
                  ·
                    rfl

theorem cell23_6670216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 6].length) (baseStart_6670216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670216 prefixEnd_6670216 := by exact prefixLift 6670216
  have htrace : WordTrace (prefixWord ++ tailWord_6670216) baseStart_6670216 baseEnd_6670216 := by
    simpa [prefixWord, tailWord_6670216, baseEnd_6670216] using wordTrace_append hprefix tailTrace_6670216
  have hstable : (prefixWord ++ tailWord_6670216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670216).length < 2 ^ (prefixWord ++ tailWord_6670216).sum := by decide
  have hdescent : baseEnd_6670216 < baseStart_6670216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670229 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_6670229 : Nat := 118140960795 + 6670229 * 2 ^ 59
def prefixEnd_6670229 : Nat := 4983230072969 + 3 ^ 40 * 6670229 * 2
def baseEnd_6670229 : Nat := 1141677850852962810687227

theorem tailTrace_6670229 : CollatzResearch.WordTrace tailWord_6670229 prefixEnd_6670229 1141677850852962810687227 := by
  unfold tailWord_6670229
  simp only [CollatzResearch.WordTrace]
  refine ⟨243283238151906992263205741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162188825434604661508803827 243283238151906992263205741)
  ·
    refine ⟨91231214306965122098702153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243283238151906992263205741 91231214306965122098702153)
    ·
      refine ⟨68423410730223841574026615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91231214306965122098702153 68423410730223841574026615)
      ·
        refine ⟨102635116095335762361039923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68423410730223841574026615 102635116095335762361039923)
        ·
          refine ⟨153952674143003643541559885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102635116095335762361039923 153952674143003643541559885)
          ·
            refine ⟨57732252803626366328084957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153952674143003643541559885 57732252803626366328084957)
            ·
              refine ⟨21649594801359887373031859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57732252803626366328084957 21649594801359887373031859)
              ·
                refine ⟨32474392202039831059547789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21649594801359887373031859 32474392202039831059547789)
                ·
                  refine ⟨12177897075764936647330421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32474392202039831059547789 12177897075764936647330421)
                  ·
                    refine ⟨1141677850852962810687227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12177897075764936647330421 1141677850852962810687227)
                    ·
                      rfl

theorem cell23_6670229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_6670229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670229 prefixEnd_6670229 := by exact prefixLift 6670229
  have htrace : WordTrace (prefixWord ++ tailWord_6670229) baseStart_6670229 baseEnd_6670229 := by
    simpa [prefixWord, tailWord_6670229, baseEnd_6670229] using wordTrace_append hprefix tailTrace_6670229
  have hstable : (prefixWord ++ tailWord_6670229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670229).length < 2 ^ (prefixWord ++ tailWord_6670229).sum := by decide
  have hdescent : baseEnd_6670229 < baseStart_6670229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670243 : List Nat := [1, 1, 1, 4, 1, 2, 1, 7, 1, 1, 3]
def baseStart_6670243 : Nat := 118140960795 + 6670243 * 2 ^ 59
def prefixEnd_6670243 : Nat := 4983230072969 + 3 ^ 40 * 6670243 * 2
def baseEnd_6670243 : Nat := 3425040741288051377286617

theorem tailTrace_6670243 : CollatzResearch.WordTrace tailWord_6670243 prefixEnd_6670243 3425040741288051377286617 := by
  unfold tailWord_6670243
  simp only [CollatzResearch.WordTrace]
  refine ⟨243283748773856272654215383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162189165849237515102810255 243283748773856272654215383)
  ·
    refine ⟨364925623160784408981323075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243283748773856272654215383 364925623160784408981323075)
    ·
      refine ⟨547388434741176613471984613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364925623160784408981323075 547388434741176613471984613)
      ·
        refine ⟨102635331513970615025997115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 547388434741176613471984613 102635331513970615025997115)
        ·
          refine ⟨153952997270955922538995673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102635331513970615025997115 153952997270955922538995673)
          ·
            refine ⟨115464747953216941904246755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153952997270955922538995673 115464747953216941904246755)
            ·
              refine ⟨173197121929825412856370133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115464747953216941904246755 173197121929825412856370133)
              ·
                refine ⟨4059307545230283113821175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173197121929825412856370133 4059307545230283113821175)
                ·
                  refine ⟨6088961317845424670731763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059307545230283113821175 6088961317845424670731763)
                  ·
                    refine ⟨9133441976768137006097645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6088961317845424670731763 9133441976768137006097645)
                    ·
                      refine ⟨3425040741288051377286617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133441976768137006097645 3425040741288051377286617)
                      ·
                        rfl

theorem cell23_6670243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_6670243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670243 prefixEnd_6670243 := by exact prefixLift 6670243
  have htrace : WordTrace (prefixWord ++ tailWord_6670243) baseStart_6670243 baseEnd_6670243 := by
    simpa [prefixWord, tailWord_6670243, baseEnd_6670243] using wordTrace_append hprefix tailTrace_6670243
  have hstable : (prefixWord ++ tailWord_6670243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670243).length < 2 ^ (prefixWord ++ tailWord_6670243).sum := by decide
  have hdescent : baseEnd_6670243 < baseStart_6670243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670254 : List Nat := [4, 1, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6670254 : Nat := 118140960795 + 6670254 * 2 ^ 59
def prefixEnd_6670254 : Nat := 4983230072969 + 3 ^ 40 * 6670254 * 2
def baseEnd_6670254 : Nat := 1141682129858416944749689

theorem tailTrace_6670254 : CollatzResearch.WordTrace tailWord_6670254 prefixEnd_6670254 1141682129858416944749689 := by
  unfold tailWord_6670254
  simp only [CollatzResearch.WordTrace]
  refine ⟨30410518747102052691608227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162189433317877614355243877 30410518747102052691608227)
  ·
    refine ⟨45615778120653079037412341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30410518747102052691608227 45615778120653079037412341)
    ·
      refine ⟨4276479198811226159757407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45615778120653079037412341 4276479198811226159757407)
      ·
        refine ⟨6414718798216839239636111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276479198811226159757407 6414718798216839239636111)
        ·
          refine ⟨9622078197325258859454167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414718798216839239636111 9622078197325258859454167)
          ·
            refine ⟨14433117295987888289181251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9622078197325258859454167 14433117295987888289181251)
            ·
              refine ⟨21649675943981832433771877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14433117295987888289181251 21649675943981832433771877)
              ·
                refine ⟨4059314239496593581332227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21649675943981832433771877 4059314239496593581332227)
                ·
                  refine ⟨6088971359244890371998341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059314239496593581332227 6088971359244890371998341)
                  ·
                    refine ⟨1141682129858416944749689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6088971359244890371998341 1141682129858416944749689)
                    ·
                      rfl

theorem cell23_6670254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6670254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670254 prefixEnd_6670254 := by exact prefixLift 6670254
  have htrace : WordTrace (prefixWord ++ tailWord_6670254) baseStart_6670254 baseEnd_6670254 := by
    simpa [prefixWord, tailWord_6670254, baseEnd_6670254] using wordTrace_append hprefix tailTrace_6670254
  have hstable : (prefixWord ++ tailWord_6670254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670254).length < 2 ^ (prefixWord ++ tailWord_6670254).sum := by decide
  have hdescent : baseEnd_6670254 < baseStart_6670254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670283 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 3, 2, 2]
def baseStart_6670283 : Nat := 118140960795 + 6670283 * 2 ^ 59
def prefixEnd_6670283 : Nat := 4983230072969 + 3 ^ 40 * 6670283 * 2
def baseEnd_6670283 : Nat := 3425061280514231220786433

theorem tailTrace_6670283 : CollatzResearch.WordTrace tailWord_6670283 prefixEnd_6670283 3425061280514231220786433 := by
  unfold tailWord_6670283
  simp only [CollatzResearch.WordTrace]
  refine ⟨243285207693711359485671503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162190138462474239657114335 243285207693711359485671503)
  ·
    refine ⟨364927811540567039228507255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243285207693711359485671503 364927811540567039228507255)
    ·
      refine ⟨547391717310850558842760883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364927811540567039228507255 547391717310850558842760883)
      ·
        refine ⟨821087575966275838264141325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547391717310850558842760883 821087575966275838264141325)
        ·
          refine ⟨307907840987353439349052997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 821087575966275838264141325 307907840987353439349052997)
          ·
            refine ⟨57732720185128769877947437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307907840987353439349052997 57732720185128769877947437)
            ·
              refine ⟨21649770069423288704230289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57732720185128769877947437 21649770069423288704230289)
              ·
                refine ⟨16237327552067466528172717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21649770069423288704230289 16237327552067466528172717)
                ·
                  refine ⟨6088997832025299948064769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16237327552067466528172717 6088997832025299948064769)
                  ·
                    refine ⟨4566748374018974961048577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6088997832025299948064769 4566748374018974961048577)
                    ·
                      refine ⟨3425061280514231220786433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566748374018974961048577 3425061280514231220786433)
                      ·
                        rfl

theorem cell23_6670283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 2, 2].length) (baseStart_6670283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670283 prefixEnd_6670283 := by exact prefixLift 6670283
  have htrace : WordTrace (prefixWord ++ tailWord_6670283) baseStart_6670283 baseEnd_6670283 := by
    simpa [prefixWord, tailWord_6670283, baseEnd_6670283] using wordTrace_append hprefix tailTrace_6670283
  have hstable : (prefixWord ++ tailWord_6670283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670283).length < 2 ^ (prefixWord ++ tailWord_6670283).sum := by decide
  have hdescent : baseEnd_6670283 < baseStart_6670283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670286 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_6670286 : Nat := 118140960795 + 6670286 * 2 ^ 59
def prefixEnd_6670286 : Nat := 4983230072969 + 3 ^ 40 * 6670286 * 2
def baseEnd_6670286 : Nat := 3425062820956194709048919

theorem tailTrace_6670286 : CollatzResearch.WordTrace tailWord_6670286 prefixEnd_6670286 3425062820956194709048919 := by
  unfold tailWord_6670286
  simp only [CollatzResearch.WordTrace]
  refine ⟨30410664639087561374753839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162190211408466993998687141 30410664639087561374753839)
  ·
    refine ⟨45615996958631342062130759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30410664639087561374753839 45615996958631342062130759)
    ·
      refine ⟨68423995437947013093196139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45615996958631342062130759 68423995437947013093196139)
      ·
        refine ⟨102635993156920519639794209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68423995437947013093196139 102635993156920519639794209)
        ·
          refine ⟨76976994867690389729845657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102635993156920519639794209 76976994867690389729845657)
          ·
            refine ⟨57732746150767792297384243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76976994867690389729845657 57732746150767792297384243)
            ·
              refine ⟨86599119226151688446076365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57732746150767792297384243 86599119226151688446076365)
              ·
                refine ⟨32474669709806883167278637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86599119226151688446076365 32474669709806883167278637)
                ·
                  refine ⟨12178001141177581187729489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32474669709806883167278637 12178001141177581187729489)
                  ·
                    refine ⟨9133500855883185890797117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12178001141177581187729489 9133500855883185890797117)
                    ·
                      refine ⟨3425062820956194709048919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133500855883185890797117 3425062820956194709048919)
                      ·
                        rfl

theorem cell23_6670286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_6670286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670286 prefixEnd_6670286 := by exact prefixLift 6670286
  have htrace : WordTrace (prefixWord ++ tailWord_6670286) baseStart_6670286 baseEnd_6670286 := by
    simpa [prefixWord, tailWord_6670286, baseEnd_6670286] using wordTrace_append hprefix tailTrace_6670286
  have hstable : (prefixWord ++ tailWord_6670286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670286).length < 2 ^ (prefixWord ++ tailWord_6670286).sum := by decide
  have hdescent : baseEnd_6670286 < baseStart_6670286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670294 : List Nat := [5, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_6670294 : Nat := 118140960795 + 6670294 * 2 ^ 59
def prefixEnd_6670294 : Nat := 4983230072969 + 3 ^ 40 * 6670294 * 2
def baseEnd_6670294 : Nat := 3425066928801430677748883

theorem tailTrace_6670294 : CollatzResearch.WordTrace tailWord_6670294 prefixEnd_6670294 3425066928801430677748883 := by
  unfold tailWord_6670294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205350556041969272770121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162190405931114338909547957 15205350556041969272770121)
  ·
    refine ⟨11404012917031476954577591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15205350556041969272770121 11404012917031476954577591)
    ·
      refine ⟨17106019375547215431866387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11404012917031476954577591 17106019375547215431866387)
      ·
        refine ⟨25659029063320823147799581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17106019375547215431866387 25659029063320823147799581)
        ·
          refine ⟨9622135898745308680424843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25659029063320823147799581 9622135898745308680424843)
          ·
            refine ⟨14433203848117963020637265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9622135898745308680424843 14433203848117963020637265)
            ·
              refine ⟨10824902886088472265477949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14433203848117963020637265 10824902886088472265477949)
              ·
                refine ⟨4059338582283177099554231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10824902886088472265477949 4059338582283177099554231)
                ·
                  refine ⟨6089007873424765649331347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059338582283177099554231 6089007873424765649331347)
                  ·
                    refine ⟨9133511810137148473997021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089007873424765649331347 9133511810137148473997021)
                    ·
                      refine ⟨3425066928801430677748883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133511810137148473997021 3425066928801430677748883)
                      ·
                        rfl

theorem cell23_6670294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_6670294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670294 prefixEnd_6670294 := by exact prefixLift 6670294
  have htrace : WordTrace (prefixWord ++ tailWord_6670294) baseStart_6670294 baseEnd_6670294 := by
    simpa [prefixWord, tailWord_6670294, baseEnd_6670294] using wordTrace_append hprefix tailTrace_6670294
  have hstable : (prefixWord ++ tailWord_6670294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670294).length < 2 ^ (prefixWord ++ tailWord_6670294).sum := by decide
  have hdescent : baseEnd_6670294 < baseStart_6670294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670303 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 3]
def baseStart_6670303 : Nat := 118140960795 + 6670303 * 2 ^ 59
def prefixEnd_6670303 : Nat := 4983230072969 + 3 ^ 40 * 6670303 * 2
def baseEnd_6670303 : Nat := 3425071550127321142536341

theorem tailTrace_6670303 : CollatzResearch.WordTrace tailWord_6670303 prefixEnd_6670303 3425071550127321142536341 := by
  unfold tailWord_6670303
  simp only [CollatzResearch.WordTrace]
  refine ⟨243285937153638902901399563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162190624769092601934266375 243285937153638902901399563)
  ·
    refine ⟨364928905730458354352099345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243285937153638902901399563 364928905730458354352099345)
    ·
      refine ⟨273696679297843765764074509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364928905730458354352099345 273696679297843765764074509)
      ·
        refine ⟨102636254736691412161527941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273696679297843765764074509 102636254736691412161527941)
        ·
          refine ⟨19244297763129639780286489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102636254736691412161527941 19244297763129639780286489)
          ·
            refine ⟨14433223322347229835214867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19244297763129639780286489 14433223322347229835214867)
            ·
              refine ⟨21649834983520844752822301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14433223322347229835214867 21649834983520844752822301)
              ·
                refine ⟨8118688118820316782308363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21649834983520844752822301 8118688118820316782308363)
                ·
                  refine ⟨12178032178230475173462545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118688118820316782308363 12178032178230475173462545)
                  ·
                    refine ⟨9133524133672856380096909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12178032178230475173462545 9133524133672856380096909)
                    ·
                      refine ⟨3425071550127321142536341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133524133672856380096909 3425071550127321142536341)
                      ·
                        rfl

theorem cell23_6670303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_6670303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670303 prefixEnd_6670303 := by exact prefixLift 6670303
  have htrace : WordTrace (prefixWord ++ tailWord_6670303) baseStart_6670303 baseEnd_6670303 := by
    simpa [prefixWord, tailWord_6670303, baseEnd_6670303] using wordTrace_append hprefix tailTrace_6670303
  have hstable : (prefixWord ++ tailWord_6670303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670303).length < 2 ^ (prefixWord ++ tailWord_6670303).sum := by decide
  have hdescent : baseEnd_6670303 < baseStart_6670303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670333 : List Nat := [1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 3]
def baseStart_6670333 : Nat := 118140960795 + 6670333 * 2 ^ 59
def prefixEnd_6670333 : Nat := 4983230072969 + 3 ^ 40 * 6670333 * 2
def baseEnd_6670333 : Nat := 3425086954546956025161203

theorem tailTrace_6670333 : CollatzResearch.WordTrace tailWord_6670333 prefixEnd_6670333 3425086954546956025161203 := by
  unfold tailWord_6670333
  simp only [CollatzResearch.WordTrace]
  refine ⟨243287031343530218024991653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162191354229020145349994435 243287031343530218024991653)
  ·
    refine ⟨45616318376911915879685935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243287031343530218024991653 45616318376911915879685935)
    ·
      refine ⟨68424477565367873819528903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45616318376911915879685935 68424477565367873819528903)
      ·
        refine ⟨102636716348051810729293355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68424477565367873819528903 102636716348051810729293355)
        ·
          refine ⟨153955074522077716093940033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102636716348051810729293355 153955074522077716093940033)
          ·
            refine ⟨115466305891558287070455025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153955074522077716093940033 115466305891558287070455025)
            ·
              refine ⟨86599729418668715302841269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115466305891558287070455025 86599729418668715302841269)
              ·
                refine ⟨8118724633000192059641369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86599729418668715302841269 8118724633000192059641369)
                ·
                  refine ⟨6089043474750144044731027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8118724633000192059641369 6089043474750144044731027)
                  ·
                    refine ⟨9133565212125216067096541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089043474750144044731027 9133565212125216067096541)
                    ·
                      refine ⟨3425086954546956025161203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133565212125216067096541 3425086954546956025161203)
                      ·
                        rfl

theorem cell23_6670333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 5, 2, 1, 3].length) (baseStart_6670333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670333 prefixEnd_6670333 := by exact prefixLift 6670333
  have htrace : WordTrace (prefixWord ++ tailWord_6670333) baseStart_6670333 baseEnd_6670333 := by
    simpa [prefixWord, tailWord_6670333, baseEnd_6670333] using wordTrace_append hprefix tailTrace_6670333
  have hstable : (prefixWord ++ tailWord_6670333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670333).length < 2 ^ (prefixWord ++ tailWord_6670333).sum := by decide
  have hdescent : baseEnd_6670333 < baseStart_6670333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670339 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4]
def baseStart_6670339 : Nat := 118140960795 + 6670339 * 2 ^ 59
def prefixEnd_6670339 : Nat := 4983230072969 + 3 ^ 40 * 6670339 * 2
def baseEnd_6670339 : Nat := 3425090035430883001686175

theorem tailTrace_6670339 : CollatzResearch.WordTrace tailWord_6670339 prefixEnd_6670339 3425090035430883001686175 := by
  unfold tailWord_6670339
  simp only [CollatzResearch.WordTrace]
  refine ⟨243287250181508481049710071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162191500121005654033140047 243287250181508481049710071)
  ·
    refine ⟨364930875272262721574565107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243287250181508481049710071 364930875272262721574565107)
    ·
      refine ⟨547396312908394082361847661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364930875272262721574565107 547396312908394082361847661)
      ·
        refine ⟨205273617340647780885692873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 547396312908394082361847661 205273617340647780885692873)
        ·
          refine ⟨153955213005485835664269655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205273617340647780885692873 153955213005485835664269655)
          ·
            refine ⟨230932819508228753496404483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153955213005485835664269655 230932819508228753496404483)
            ·
              refine ⟨346399229262343130244606725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230932819508228753496404483 346399229262343130244606725)
              ·
                refine ⟨64949855486689336920863761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346399229262343130244606725 64949855486689336920863761)
                ·
                  refine ⟨48712391615017002690647821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64949855486689336920863761 48712391615017002690647821)
                  ·
                    refine ⟨18267146855631376008992933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48712391615017002690647821 18267146855631376008992933)
                    ·
                      refine ⟨3425090035430883001686175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18267146855631376008992933 3425090035430883001686175)
                      ·
                        rfl

theorem cell23_6670339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_6670339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670339 prefixEnd_6670339 := by exact prefixLift 6670339
  have htrace : WordTrace (prefixWord ++ tailWord_6670339) baseStart_6670339 baseEnd_6670339 := by
    simpa [prefixWord, tailWord_6670339, baseEnd_6670339] using wordTrace_append hprefix tailTrace_6670339
  have hstable : (prefixWord ++ tailWord_6670339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670339).length < 2 ^ (prefixWord ++ tailWord_6670339).sum := by decide
  have hdescent : baseEnd_6670339 < baseStart_6670339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670340 : List Nat := [2, 3, 2, 4, 1, 2, 2, 7]
def baseStart_6670340 : Nat := 118140960795 + 6670340 * 2 ^ 59
def prefixEnd_6670340 : Nat := 4983230072969 + 3 ^ 40 * 6670340 * 2
def baseEnd_6670340 : Nat := 126855205515242129547173

theorem tailTrace_6670340 : CollatzResearch.WordTrace tailWord_6670340 prefixEnd_6670340 126855205515242129547173 := by
  unfold tailWord_6670340
  simp only [CollatzResearch.WordTrace]
  refine ⟨121643643327252429110248237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162191524436336572146997649 121643643327252429110248237)
  ·
    refine ⟨45616366247719660916343089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121643643327252429110248237 45616366247719660916343089)
    ·
      refine ⟨34212274685789745687257317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45616366247719660916343089 34212274685789745687257317)
      ·
        refine ⟨6414801503585577316360747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34212274685789745687257317 6414801503585577316360747)
        ·
          refine ⟨9622202255378365974541121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414801503585577316360747 9622202255378365974541121)
          ·
            refine ⟨7216651691533774480905841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622202255378365974541121 7216651691533774480905841)
            ·
              refine ⟨5412488768650330860679381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216651691533774480905841 5412488768650330860679381)
              ·
                refine ⟨126855205515242129547173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5412488768650330860679381 126855205515242129547173)
                ·
                  rfl

theorem cell23_6670340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 7].length) (baseStart_6670340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670340 prefixEnd_6670340 := by exact prefixLift 6670340
  have htrace : WordTrace (prefixWord ++ tailWord_6670340) baseStart_6670340 baseEnd_6670340 := by
    simpa [prefixWord, tailWord_6670340, baseEnd_6670340] using wordTrace_append hprefix tailTrace_6670340
  have hstable : (prefixWord ++ tailWord_6670340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670340).length < 2 ^ (prefixWord ++ tailWord_6670340).sum := by decide
  have hdescent : baseEnd_6670340 < baseStart_6670340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670379 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 7]
def baseStart_6670379 : Nat := 118140960795 + 6670379 * 2 ^ 59
def prefixEnd_6670379 : Nat := 4983230072969 + 3 ^ 40 * 6670379 * 2
def baseEnd_6670379 : Nat := 380567841628562538353999

theorem tailTrace_6670379 : CollatzResearch.WordTrace tailWord_6670379 prefixEnd_6670379 380567841628562538353999 := by
  unfold tailWord_6670379
  simp only [CollatzResearch.WordTrace]
  refine ⟨243288709101363567881166191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162192472734242378587444127 243288709101363567881166191)
  ·
    refine ⟨364933063652045351821749287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243288709101363567881166191 364933063652045351821749287)
    ·
      refine ⟨547399595478068027732623931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364933063652045351821749287 547399595478068027732623931)
      ·
        refine ⟨821099393217102041598935897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547399595478068027732623931 821099393217102041598935897)
        ·
          refine ⟨615824544912826531199201923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821099393217102041598935897 615824544912826531199201923)
          ·
            refine ⟨923736817369239796798802885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615824544912826531199201923 923736817369239796798802885)
            ·
              refine ⟨173200653256732461899775541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 923736817369239796798802885 173200653256732461899775541)
              ·
                refine ⟨16237561242818668303103957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173200653256732461899775541 16237561242818668303103957)
                ·
                  refine ⟨380567841628562538353999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16237561242818668303103957 380567841628562538353999)
                  ·
                    rfl

theorem cell23_6670379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 7].length) (baseStart_6670379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670379 prefixEnd_6670379 := by exact prefixLift 6670379
  have htrace : WordTrace (prefixWord ++ tailWord_6670379) baseStart_6670379 baseEnd_6670379 := by
    simpa [prefixWord, tailWord_6670379, baseEnd_6670379] using wordTrace_append hprefix tailTrace_6670379
  have hstable : (prefixWord ++ tailWord_6670379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670379).length < 2 ^ (prefixWord ++ tailWord_6670379).sum := by decide
  have hdescent : baseEnd_6670379 < baseStart_6670379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670390 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_6670390 : Nat := 118140960795 + 6670390 * 2 ^ 59
def prefixEnd_6670390 : Nat := 4983230072969 + 3 ^ 40 * 6670390 * 2
def baseEnd_6670390 : Nat := 3425116222944262302148441

theorem tailTrace_6670390 : CollatzResearch.WordTrace tailWord_6670390 prefixEnd_6670390 3425116222944262302148441 := by
  unfold tailWord_6670390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205569394020232297488539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162192740202882477839877749 15205569394020232297488539)
  ·
    refine ⟨22808354091030348446232809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15205569394020232297488539 22808354091030348446232809)
    ·
      refine ⟨17106265568272761334674607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22808354091030348446232809 17106265568272761334674607)
      ·
        refine ⟨25659398352409142002011911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17106265568272761334674607 25659398352409142002011911)
        ·
          refine ⟨38489097528613713003017867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25659398352409142002011911 38489097528613713003017867)
          ·
            refine ⟨57733646292920569504526801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38489097528613713003017867 57733646292920569504526801)
            ·
              refine ⟨43300234719690427128395101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57733646292920569504526801 43300234719690427128395101)
              ·
                refine ⟨16237588019883910173148163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43300234719690427128395101 16237588019883910173148163)
                ·
                  refine ⟨24356382029825865259722245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16237588019883910173148163 24356382029825865259722245)
                  ·
                    refine ⟨4566821630592349736197921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24356382029825865259722245 4566821630592349736197921)
                    ·
                      refine ⟨3425116222944262302148441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566821630592349736197921 3425116222944262302148441)
                      ·
                        rfl

theorem cell23_6670390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_6670390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670390 prefixEnd_6670390 := by exact prefixLift 6670390
  have htrace : WordTrace (prefixWord ++ tailWord_6670390) baseStart_6670390 baseEnd_6670390 := by
    simpa [prefixWord, tailWord_6670390, baseEnd_6670390] using wordTrace_append hprefix tailTrace_6670390
  have hstable : (prefixWord ++ tailWord_6670390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670390).length < 2 ^ (prefixWord ++ tailWord_6670390).sum := by decide
  have hdescent : baseEnd_6670390 < baseStart_6670390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670426 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_6670426 : Nat := 118140960795 + 6670426 * 2 ^ 59
def prefixEnd_6670426 : Nat := 4983230072969 + 3 ^ 40 * 6670426 * 2
def baseEnd_6670426 : Nat := 1141711569415941387099425

theorem tailTrace_6670426 : CollatzResearch.WordTrace tailWord_6670426 prefixEnd_6670426 1141711569415941387099425 := by
  unfold tailWord_6670426
  simp only [CollatzResearch.WordTrace]
  refine ⟨60822605833048323727031783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162193615554795529938751421 60822605833048323727031783)
  ·
    refine ⟨91233908749572485590547675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60822605833048323727031783 91233908749572485590547675)
    ·
      refine ⟨136850863124358728385821513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91233908749572485590547675 136850863124358728385821513)
      ·
        refine ⟨102638147343269046289366135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136850863124358728385821513 102638147343269046289366135)
        ·
          refine ⟨153957221014903569434049203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102638147343269046289366135 153957221014903569434049203)
          ·
            refine ⟨230935831522355354151073805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153957221014903569434049203 230935831522355354151073805)
            ·
              refine ⟨86600936820883257806652677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230935831522355354151073805 86600936820883257806652677)
              ·
                refine ⟨16237675653915610838747377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86600936820883257806652677 16237675653915610838747377)
                ·
                  refine ⟨12178256740436708129060533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16237675653915610838747377 12178256740436708129060533)
                  ·
                    refine ⟨1141711569415941387099425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12178256740436708129060533 1141711569415941387099425)
                    ·
                      rfl

theorem cell23_6670426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_6670426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670426 prefixEnd_6670426 := by exact prefixLift 6670426
  have htrace : WordTrace (prefixWord ++ tailWord_6670426) baseStart_6670426 baseEnd_6670426 := by
    simpa [prefixWord, tailWord_6670426, baseEnd_6670426] using wordTrace_append hprefix tailTrace_6670426
  have hstable : (prefixWord ++ tailWord_6670426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670426).length < 2 ^ (prefixWord ++ tailWord_6670426).sum := by decide
  have hdescent : baseEnd_6670426 < baseStart_6670426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670436 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_6670436 : Nat := 118140960795 + 6670436 * 2 ^ 59
def prefixEnd_6670436 : Nat := 4983230072969 + 3 ^ 40 * 6670436 * 2
def baseEnd_6670436 : Nat := 3425139843054369122173229

theorem tailTrace_6670436 : CollatzResearch.WordTrace tailWord_6670436 prefixEnd_6670436 3425139843054369122173229 := by
  unfold tailWord_6670436
  simp only [CollatzResearch.WordTrace]
  refine ⟨121645394031078533307995581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162193858708104711077327441 121645394031078533307995581)
  ·
    refine ⟨45617022761654449990498343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121645394031078533307995581 45617022761654449990498343)
    ·
      refine ⟨68425534142481674985747515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45617022761654449990498343 68425534142481674985747515)
      ·
        refine ⟨102638301213722512478621273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68425534142481674985747515 102638301213722512478621273)
        ·
          refine ⟨76978725910291884358965955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102638301213722512478621273 76978725910291884358965955)
          ·
            refine ⟨115468088865437826538448933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76978725910291884358965955 115468088865437826538448933)
            ·
              refine ⟨21650266662269592475959175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115468088865437826538448933 21650266662269592475959175)
              ·
                refine ⟨32475399993404388713938763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21650266662269592475959175 32475399993404388713938763)
                ·
                  refine ⟨48713099990106583070908145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32475399993404388713938763 48713099990106583070908145)
                  ·
                    refine ⟨36534824992579937303181109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48713099990106583070908145 36534824992579937303181109)
                    ·
                      refine ⟨3425139843054369122173229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36534824992579937303181109 3425139843054369122173229)
                      ·
                        rfl

theorem cell23_6670436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_6670436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670436 prefixEnd_6670436 := by exact prefixLift 6670436
  have htrace : WordTrace (prefixWord ++ tailWord_6670436) baseStart_6670436 baseEnd_6670436 := by
    simpa [prefixWord, tailWord_6670436, baseEnd_6670436] using wordTrace_append hprefix tailTrace_6670436
  have hstable : (prefixWord ++ tailWord_6670436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670436).length < 2 ^ (prefixWord ++ tailWord_6670436).sum := by decide
  have hdescent : baseEnd_6670436 < baseStart_6670436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670523 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 1, 5, 2]
def baseStart_6670523 : Nat := 118140960795 + 6670523 * 2 ^ 59
def prefixEnd_6670523 : Nat := 4983230072969 + 3 ^ 40 * 6670523 * 2
def baseEnd_6670523 : Nat := 3425184515871310281785329

theorem tailTrace_6670523 : CollatzResearch.WordTrace tailWord_6670523 prefixEnd_6670523 3425184515871310281785329 := by
  unfold tailWord_6670523
  simp only [CollatzResearch.WordTrace]
  refine ⟨243293961212841880474408223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162195974141894586982938815 243293961212841880474408223)
  ·
    refine ⟨364940941819262820711612335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243293961212841880474408223 364940941819262820711612335)
    ·
      refine ⟨547411412728894231067418503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364940941819262820711612335 547411412728894231067418503)
      ·
        refine ⟨821117119093341346601127755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547411412728894231067418503 821117119093341346601127755)
        ·
          refine ⟨1231675678640012019901691633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821117119093341346601127755 1231675678640012019901691633)
          ·
            refine ⟨923756758980009014926268725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231675678640012019901691633 923756758980009014926268725)
            ·
              refine ⟨86602196154375845149337693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 923756758980009014926268725 86602196154375845149337693)
              ·
                refine ⟨32475823557890941931001635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86602196154375845149337693 32475823557890941931001635)
                ·
                  refine ⟨48713735336836412896502453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32475823557890941931001635 48713735336836412896502453)
                  ·
                    refine ⟨4566912687828413709047105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48713735336836412896502453 4566912687828413709047105)
                    ·
                      refine ⟨3425184515871310281785329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566912687828413709047105 3425184515871310281785329)
                      ·
                        rfl

theorem cell23_6670523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5, 2].length) (baseStart_6670523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670523 prefixEnd_6670523 := by exact prefixLift 6670523
  have htrace : WordTrace (prefixWord ++ tailWord_6670523) baseStart_6670523 baseEnd_6670523 := by
    simpa [prefixWord, tailWord_6670523, baseEnd_6670523] using wordTrace_append hprefix tailTrace_6670523
  have hstable : (prefixWord ++ tailWord_6670523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670523).length < 2 ^ (prefixWord ++ tailWord_6670523).sum := by decide
  have hdescent : baseEnd_6670523 < baseStart_6670523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670524 : List Nat := [2, 2, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_6670524 : Nat := 118140960795 + 6670524 * 2 ^ 59
def prefixEnd_6670524 : Nat := 4983230072969 + 3 ^ 40 * 6670524 * 2
def baseEnd_6670524 : Nat := 1141728343117321592624275

theorem tailTrace_6670524 : CollatzResearch.WordTrace tailWord_6670524 prefixEnd_6670524 1141728343117321592624275 := by
  unfold tailWord_6670524
  simp only [CollatzResearch.WordTrace]
  refine ⟨121646998842919128822597313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162195998457225505096796417 121646998842919128822597313)
  ·
    refine ⟨91235249132189346616947985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121646998842919128822597313 91235249132189346616947985)
    ·
      refine ⟨68426436849142009962710989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91235249132189346616947985 68426436849142009962710989)
      ·
        refine ⟨25659913818428253736016621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68426436849142009962710989 25659913818428253736016621)
        ·
          refine ⟨9622467681910595151006233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25659913818428253736016621 9622467681910595151006233)
          ·
            refine ⟨7216850761432946363254675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622467681910595151006233 7216850761432946363254675)
            ·
              refine ⟨10825276142149419544882013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216850761432946363254675 10825276142149419544882013)
              ·
                refine ⟨4059478553306032329330755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10825276142149419544882013 4059478553306032329330755)
                ·
                  refine ⟨6089217829959048493996133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059478553306032329330755 6089217829959048493996133)
                  ·
                    refine ⟨1141728343117321592624275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6089217829959048493996133 1141728343117321592624275)
                    ·
                      rfl

theorem cell23_6670524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_6670524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670524 prefixEnd_6670524 := by exact prefixLift 6670524
  have htrace : WordTrace (prefixWord ++ tailWord_6670524) baseStart_6670524 baseEnd_6670524 := by
    simpa [prefixWord, tailWord_6670524, baseEnd_6670524] using wordTrace_append hprefix tailTrace_6670524
  have hstable : (prefixWord ++ tailWord_6670524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670524).length < 2 ^ (prefixWord ++ tailWord_6670524).sum := by decide
  have hdescent : baseEnd_6670524 < baseStart_6670524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670533 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_6670533 : Nat := 118140960795 + 6670533 * 2 ^ 59
def prefixEnd_6670533 : Nat := 4983230072969 + 3 ^ 40 * 6670533 * 2
def baseEnd_6670533 : Nat := 1141729883559285080886761

theorem tailTrace_6670533 : CollatzResearch.WordTrace tailWord_6670533 prefixEnd_6670533 1141729883559285080886761 := by
  unfold tailWord_6670533
  simp only [CollatzResearch.WordTrace]
  refine ⟨243294325942805652182272253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162196217295203768121514835 243294325942805652182272253)
  ·
    refine ⟨91235372228552119568352095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243294325942805652182272253 91235372228552119568352095)
    ·
      refine ⟨136853058342828179352528143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91235372228552119568352095 136853058342828179352528143)
      ·
        refine ⟨205279587514242269028792215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136853058342828179352528143 205279587514242269028792215)
        ·
          refine ⟨307919381271363403543188323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205279587514242269028792215 307919381271363403543188323)
          ·
            refine ⟨461879071907045105314782485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307919381271363403543188323 461879071907045105314782485)
            ·
              refine ⟨21650581495642739311630429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 461879071907045105314782485 21650581495642739311630429)
              ·
                refine ⟨8118968060866027241861411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21650581495642739311630429 8118968060866027241861411)
                ·
                  refine ⟨12178452091299040862792117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8118968060866027241861411 12178452091299040862792117)
                  ·
                    refine ⟨1141729883559285080886761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12178452091299040862792117 1141729883559285080886761)
                    ·
                      rfl

theorem cell23_6670533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_6670533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670533 prefixEnd_6670533 := by exact prefixLift 6670533
  have htrace : WordTrace (prefixWord ++ tailWord_6670533) baseStart_6670533 baseEnd_6670533 := by
    simpa [prefixWord, tailWord_6670533, baseEnd_6670533] using wordTrace_append hprefix tailTrace_6670533
  have hstable : (prefixWord ++ tailWord_6670533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670533).length < 2 ^ (prefixWord ++ tailWord_6670533).sum := by decide
  have hdescent : baseEnd_6670533 < baseStart_6670533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670567 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 1, 5]
def baseStart_6670567 : Nat := 118140960795 + 6670567 * 2 ^ 59
def prefixEnd_6670567 : Nat := 4983230072969 + 3 ^ 40 * 6670567 * 2
def baseEnd_6670567 : Nat := 1141735703006702703211709

theorem tailTrace_6670567 : CollatzResearch.WordTrace tailWord_6670567 prefixEnd_6670567 1141735703006702703211709 := by
  unfold tailWord_6670567
  simp only [CollatzResearch.WordTrace]
  refine ⟨243295566024682475989009955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162197044016454983992673303 243295566024682475989009955)
  ·
    refine ⟨364943349037023713983514933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243295566024682475989009955 364943349037023713983514933)
    ·
      refine ⟨34213438972220973185954525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 364943349037023713983514933 34213438972220973185954525)
      ·
        refine ⟨12830039614582864944732947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34213438972220973185954525 12830039614582864944732947)
        ·
          refine ⟨19245059421874297417099421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12830039614582864944732947 19245059421874297417099421)
          ·
            refine ⟨7216897283202861531412283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19245059421874297417099421 7216897283202861531412283)
            ·
              refine ⟨10825345924804292297118425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7216897283202861531412283 10825345924804292297118425)
              ·
                refine ⟨8119009443603219222838819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10825345924804292297118425 8119009443603219222838819)
                ·
                  refine ⟨12178514165404828834258229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8119009443603219222838819 12178514165404828834258229)
                  ·
                    refine ⟨1141735703006702703211709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12178514165404828834258229 1141735703006702703211709)
                    ·
                      rfl

theorem cell23_6670567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_6670567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670567 prefixEnd_6670567 := by exact prefixLift 6670567
  have htrace : WordTrace (prefixWord ++ tailWord_6670567) baseStart_6670567 baseEnd_6670567 := by
    simpa [prefixWord, tailWord_6670567, baseEnd_6670567] using wordTrace_append hprefix tailTrace_6670567
  have hstable : (prefixWord ++ tailWord_6670567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670567).length < 2 ^ (prefixWord ++ tailWord_6670567).sum := by decide
  have hdescent : baseEnd_6670567 < baseStart_6670567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670603 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 3]
def baseStart_6670603 : Nat := 118140960795 + 6670603 * 2 ^ 59
def prefixEnd_6670603 : Nat := 4983230072969 + 3 ^ 40 * 6670603 * 2
def baseEnd_6670603 : Nat := 3425225594323669968784961

theorem tailTrace_6670603 : CollatzResearch.WordTrace tailWord_6670603 prefixEnd_6670603 3425225594323669968784961 := by
  unfold tailWord_6670603
  simp only [CollatzResearch.WordTrace]
  refine ⟨243296879052552054137320463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162197919368368036091546975 243296879052552054137320463)
  ·
    refine ⟨364945318578828081205980695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243296879052552054137320463 364945318578828081205980695)
    ·
      refine ⟨547417977868242121808971043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364945318578828081205980695 547417977868242121808971043)
      ·
        refine ⟨821126966802363182713456565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547417977868242121808971043 821126966802363182713456565)
        ·
          refine ⟨76980653137721548379386553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 821126966802363182713456565 76980653137721548379386553)
          ·
            refine ⟨57735489853291161284539915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76980653137721548379386553 57735489853291161284539915)
            ·
              refine ⟨86603234779936741926809873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57735489853291161284539915 86603234779936741926809873)
              ·
                refine ⟨64952426084952556445107405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86603234779936741926809873 64952426084952556445107405)
                ·
                  refine ⟨24357159781857208666915277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64952426084952556445107405 24357159781857208666915277)
                  ·
                    refine ⟨9133934918196453250093229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24357159781857208666915277 9133934918196453250093229)
                    ·
                      refine ⟨3425225594323669968784961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133934918196453250093229 3425225594323669968784961)
                      ·
                        rfl

theorem cell23_6670603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 3].length) (baseStart_6670603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670603 prefixEnd_6670603 := by exact prefixLift 6670603
  have htrace : WordTrace (prefixWord ++ tailWord_6670603) baseStart_6670603 baseEnd_6670603 := by
    simpa [prefixWord, tailWord_6670603, baseEnd_6670603] using wordTrace_append hprefix tailTrace_6670603
  have hstable : (prefixWord ++ tailWord_6670603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670603).length < 2 ^ (prefixWord ++ tailWord_6670603).sum := by decide
  have hdescent : baseEnd_6670603 < baseStart_6670603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670604 : List Nat := [2, 2, 1, 2, 2, 2, 3, 4, 1, 2, 2]
def baseStart_6670604 : Nat := 118140960795 + 6670604 * 2 ^ 59
def prefixEnd_6670604 : Nat := 4983230072969 + 3 ^ 40 * 6670604 * 2
def baseEnd_6670604 : Nat := 3425226107804324464872457

theorem tailTrace_6670604 : CollatzResearch.WordTrace tailWord_6670604 prefixEnd_6670604 3425226107804324464872457 := by
  unfold tailWord_6670604
  simp only [CollatzResearch.WordTrace]
  refine ⟨121648457762774215654053433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162197943683698954205404577 121648457762774215654053433)
  ·
    refine ⟨91236343322080661740540075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121648457762774215654053433 91236343322080661740540075)
    ·
      refine ⟨136854514983120992610810113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91236343322080661740540075 136854514983120992610810113)
      ·
        refine ⟨102640886237340744458107585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136854514983120992610810113 102640886237340744458107585)
        ·
          refine ⟨76980664678005558343580689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102640886237340744458107585 76980664678005558343580689)
          ·
            refine ⟨57735498508504168757685517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76980664678005558343580689 57735498508504168757685517)
            ·
              refine ⟨21650811940689063284132069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57735498508504168757685517 21650811940689063284132069)
              ·
                refine ⟨4059527238879199365774763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21650811940689063284132069 4059527238879199365774763)
                ·
                  refine ⟨6089290858318799048662145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059527238879199365774763 6089290858318799048662145)
                  ·
                    refine ⟨4566968143739099286496609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6089290858318799048662145 4566968143739099286496609)
                    ·
                      refine ⟨3425226107804324464872457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4566968143739099286496609 3425226107804324464872457)
                      ·
                        rfl

theorem cell23_6670604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_6670604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670604 prefixEnd_6670604 := by exact prefixLift 6670604
  have htrace : WordTrace (prefixWord ++ tailWord_6670604) baseStart_6670604 baseEnd_6670604 := by
    simpa [prefixWord, tailWord_6670604, baseEnd_6670604] using wordTrace_append hprefix tailTrace_6670604
  have hstable : (prefixWord ++ tailWord_6670604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670604).length < 2 ^ (prefixWord ++ tailWord_6670604).sum := by decide
  have hdescent : baseEnd_6670604 < baseStart_6670604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670620 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_6670620 : Nat := 118140960795 + 6670620 * 2 ^ 59
def prefixEnd_6670620 : Nat := 4983230072969 + 3 ^ 40 * 6670620 * 2
def baseEnd_6670620 : Nat := 3425234323494796402272383

theorem tailTrace_6670620 : CollatzResearch.WordTrace tailWord_6670620 prefixEnd_6670620 3425234323494796402272383 := by
  unfold tailWord_6670620
  simp only [CollatzResearch.WordTrace]
  refine ⟨121648749546745233020344657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162198332728993644027126209 121648749546745233020344657)
  ·
    refine ⟨91236562160058924765258493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121648749546745233020344657 91236562160058924765258493)
    ·
      refine ⟨34213710810022096786971935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91236562160058924765258493 34213710810022096786971935)
      ·
        refine ⟨51320566215033145180457903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34213710810022096786971935 51320566215033145180457903)
        ·
          refine ⟨76980849322549717770686855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51320566215033145180457903 76980849322549717770686855)
          ·
            refine ⟨115471273983824576656030283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76980849322549717770686855 115471273983824576656030283)
            ·
              refine ⟨173206910975736864984045425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115471273983824576656030283 173206910975736864984045425)
              ·
                refine ⟨129905183231802648738034069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173206910975736864984045425 129905183231802648738034069)
                ·
                  refine ⟨6089305463990749159595347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129905183231802648738034069 6089305463990749159595347)
                  ·
                    refine ⟨9133958195986123739393021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089305463990749159595347 9133958195986123739393021)
                    ·
                      refine ⟨3425234323494796402272383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133958195986123739393021 3425234323494796402272383)
                      ·
                        rfl

theorem cell23_6670620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_6670620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670620 prefixEnd_6670620 := by exact prefixLift 6670620
  have htrace : WordTrace (prefixWord ++ tailWord_6670620) baseStart_6670620 baseEnd_6670620 := by
    simpa [prefixWord, tailWord_6670620, baseEnd_6670620] using wordTrace_append hprefix tailTrace_6670620
  have hstable : (prefixWord ++ tailWord_6670620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670620).length < 2 ^ (prefixWord ++ tailWord_6670620).sum := by decide
  have hdescent : baseEnd_6670620 < baseStart_6670620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670638 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6670638 : Nat := 118140960795 + 6670638 * 2 ^ 59
def prefixEnd_6670638 : Nat := 4983230072969 + 3 ^ 40 * 6670638 * 2
def baseEnd_6670638 : Nat := 3425243566146577331847301

theorem tailTrace_6670638 : CollatzResearch.WordTrace tailWord_6670638 prefixEnd_6670638 3425243566146577331847301 := by
  unfold tailWord_6670638
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412269450928156889355571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162198770404950170076563045 30412269450928156889355571)
  ·
    refine ⟨45618404176392235334033357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30412269450928156889355571 45618404176392235334033357)
    ·
      refine ⟨17106901566147088250262509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45618404176392235334033357 17106901566147088250262509)
      ·
        refine ⟨6415088087305158093848441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17106901566147088250262509 6415088087305158093848441)
        ·
          refine ⟨4811316065478868570386331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6415088087305158093848441 4811316065478868570386331)
          ·
            refine ⟨7216974098218302855579497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811316065478868570386331 7216974098218302855579497)
            ·
              refine ⟨5412730573663727141684623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216974098218302855579497 5412730573663727141684623)
              ·
                refine ⟨8119095860495590712526935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412730573663727141684623 8119095860495590712526935)
                ·
                  refine ⟨12178643790743386068790403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8119095860495590712526935 12178643790743386068790403)
                  ·
                    refine ⟨18267965686115079103185605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12178643790743386068790403 18267965686115079103185605)
                    ·
                      refine ⟨3425243566146577331847301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18267965686115079103185605 3425243566146577331847301)
                      ·
                        rfl

theorem cell23_6670638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6670638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670638 prefixEnd_6670638 := by exact prefixLift 6670638
  have htrace : WordTrace (prefixWord ++ tailWord_6670638) baseStart_6670638 baseEnd_6670638 := by
    simpa [prefixWord, tailWord_6670638, baseEnd_6670638] using wordTrace_append hprefix tailTrace_6670638
  have hstable : (prefixWord ++ tailWord_6670638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670638).length < 2 ^ (prefixWord ++ tailWord_6670638).sum := by decide
  have hdescent : baseEnd_6670638 < baseStart_6670638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670641 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 1, 2, 3]
def baseStart_6670641 : Nat := 118140960795 + 6670641 * 2 ^ 59
def prefixEnd_6670641 : Nat := 4983230072969 + 3 ^ 40 * 6670641 * 2
def baseEnd_6670641 : Nat := 3425245106588540820109787

theorem tailTrace_6670641 : CollatzResearch.WordTrace tailWord_6670641 prefixEnd_6670641 3425245106588540820109787 := by
  unfold tailWord_6670641
  simp only [CollatzResearch.WordTrace]
  refine ⟨243298265026414386627203777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162198843350942924418135851 243298265026414386627203777)
  ·
    refine ⟨182473698769810789970402833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243298265026414386627203777 182473698769810789970402833)
    ·
      refine ⟨136855274077358092477802125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182473698769810789970402833 136855274077358092477802125)
      ·
        refine ⟨51320727779009284679175797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136855274077358092477802125 51320727779009284679175797)
        ·
          refine ⟨4811318229282120438672731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51320727779009284679175797 4811318229282120438672731)
          ·
            refine ⟨7216977343923180658009097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811318229282120438672731 7216977343923180658009097)
            ·
              refine ⟨5412733007942385493506823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216977343923180658009097 5412733007942385493506823)
              ·
                refine ⟨8119099511913578240260235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412733007942385493506823 8119099511913578240260235)
                ·
                  refine ⟨12178649267870367360390353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8119099511913578240260235 12178649267870367360390353)
                  ·
                    refine ⟨9133986950902775520292765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12178649267870367360390353 9133986950902775520292765)
                    ·
                      refine ⟨3425245106588540820109787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9133986950902775520292765 3425245106588540820109787)
                      ·
                        rfl

theorem cell23_6670641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_6670641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670641 prefixEnd_6670641 := by exact prefixLift 6670641
  have htrace : WordTrace (prefixWord ++ tailWord_6670641) baseStart_6670641 baseEnd_6670641 := by
    simpa [prefixWord, tailWord_6670641, baseEnd_6670641] using wordTrace_append hprefix tailTrace_6670641
  have hstable : (prefixWord ++ tailWord_6670641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670641).length < 2 ^ (prefixWord ++ tailWord_6670641).sum := by decide
  have hdescent : baseEnd_6670641 < baseStart_6670641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670654 : List Nat := [4, 2, 1, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_6670654 : Nat := 118140960795 + 6670654 * 2 ^ 59
def prefixEnd_6670654 : Nat := 4983230072969 + 3 ^ 40 * 6670654 * 2
def baseEnd_6670654 : Nat := 3425251781837049269247227

theorem tailTrace_6670654 : CollatzResearch.WordTrace tailWord_6670654 prefixEnd_6670654 3425251781837049269247227 := by
  unfold tailWord_6670654
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412342396920911230928377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162199159450244859898284677 30412342396920911230928377)
  ·
    refine ⟨22809256797690683423196283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30412342396920911230928377 22809256797690683423196283)
    ·
      refine ⟨34213885196536025134794425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22809256797690683423196283 34213885196536025134794425)
      ·
        refine ⟨25660413897402018851095819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34213885196536025134794425 25660413897402018851095819)
        ·
          refine ⟨38490620846103028276643729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25660413897402018851095819 38490620846103028276643729)
          ·
            refine ⟨28867965634577271207482797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38490620846103028276643729 28867965634577271207482797)
            ·
              refine ⟨10825487112966476702806049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28867965634577271207482797 10825487112966476702806049)
              ·
                refine ⟨8119115334724857527104537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10825487112966476702806049 8119115334724857527104537)
                ·
                  refine ⟨6089336501043643145328403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8119115334724857527104537 6089336501043643145328403)
                  ·
                    refine ⟨9134004751565464717992605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089336501043643145328403 9134004751565464717992605)
                    ·
                      refine ⟨3425251781837049269247227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9134004751565464717992605 3425251781837049269247227)
                      ·
                        rfl

theorem cell23_6670654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_6670654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670654 prefixEnd_6670654 := by exact prefixLift 6670654
  have htrace : WordTrace (prefixWord ++ tailWord_6670654) baseStart_6670654 baseEnd_6670654 := by
    simpa [prefixWord, tailWord_6670654, baseEnd_6670654] using wordTrace_append hprefix tailTrace_6670654
  have hstable : (prefixWord ++ tailWord_6670654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670654).length < 2 ^ (prefixWord ++ tailWord_6670654).sum := by decide
  have hdescent : baseEnd_6670654 < baseStart_6670654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670743 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 8]
def baseStart_6670743 : Nat := 118140960795 + 6670743 * 2 ^ 59
def prefixEnd_6670743 : Nat := 4983230072969 + 3 ^ 40 * 6670743 * 2
def baseEnd_6670743 : Nat := 1141765827205099807011439

theorem tailTrace_6670743 : CollatzResearch.WordTrace tailWord_6670743 prefixEnd_6670743 1141765827205099807011439 := by
  unfold tailWord_6670743
  simp only [CollatzResearch.WordTrace]
  refine ⟨243301985272044858047416883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162201323514696572031611255 243301985272044858047416883)
  ·
    refine ⟨364952977908067287071125325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243301985272044858047416883 364952977908067287071125325)
    ·
      refine ⟨136857366715525232651671997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364952977908067287071125325 136857366715525232651671997)
      ·
        refine ⟨51321512518321962244376999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136857366715525232651671997 51321512518321962244376999)
        ·
          refine ⟨76982268777482943366565499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51321512518321962244376999 76982268777482943366565499)
          ·
            refine ⟨115473403166224415049848249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76982268777482943366565499 115473403166224415049848249)
            ·
              refine ⟨86605052374668311287386187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115473403166224415049848249 86605052374668311287386187)
              ·
                refine ⟨129907578562002466931079281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86605052374668311287386187 129907578562002466931079281)
                ·
                  refine ⟨97430683921501850198309461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129907578562002466931079281 97430683921501850198309461)
                  ·
                    refine ⟨1141765827205099807011439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97430683921501850198309461 1141765827205099807011439)
                    ·
                      rfl

theorem cell23_6670743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_6670743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670743 prefixEnd_6670743 := by exact prefixLift 6670743
  have htrace : WordTrace (prefixWord ++ tailWord_6670743) baseStart_6670743 baseEnd_6670743 := by
    simpa [prefixWord, tailWord_6670743, baseEnd_6670743] using wordTrace_append hprefix tailTrace_6670743
  have hstable : (prefixWord ++ tailWord_6670743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670743).length < 2 ^ (prefixWord ++ tailWord_6670743).sum := by decide
  have hdescent : baseEnd_6670743 < baseStart_6670743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670804 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_6670804 : Nat := 118140960795 + 6670804 * 2 ^ 59
def prefixEnd_6670804 : Nat := 4983230072969 + 3 ^ 40 * 6670804 * 2
def baseEnd_6670804 : Nat := 3425328803935223682371537

theorem tailTrace_6670804 : CollatzResearch.WordTrace tailWord_6670804 prefixEnd_6670804 3425328803935223682371537 := by
  unfold tailWord_6670804
  simp only [CollatzResearch.WordTrace]
  refine ⟨121652105062411932732693733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162202806749882576976924977 121652105062411932732693733)
  ·
    refine ⟨22809769699202237387380075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121652105062411932732693733 22809769699202237387380075)
    ·
      refine ⟨34214654548803356081070113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22809769699202237387380075 34214654548803356081070113)
      ·
        refine ⟨25660990911602517060802585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34214654548803356081070113 25660990911602517060802585)
        ·
          refine ⟨19245743183701887795601939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25660990911602517060802585 19245743183701887795601939)
          ·
            refine ⟨28868614775552831693402909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19245743183701887795601939 28868614775552831693402909)
            ·
              refine ⟨10825730540832311885026091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28868614775552831693402909 10825730540832311885026091)
              ·
                refine ⟨16238595811248467827539137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10825730540832311885026091 16238595811248467827539137)
                ·
                  refine ⟨12178946858436350870654353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16238595811248467827539137 12178946858436350870654353)
                  ·
                    refine ⟨9134210143827263152990765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12178946858436350870654353 9134210143827263152990765)
                    ·
                      refine ⟨3425328803935223682371537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9134210143827263152990765 3425328803935223682371537)
                      ·
                        rfl

theorem cell23_6670804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_6670804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670804 prefixEnd_6670804 := by exact prefixLift 6670804
  have htrace : WordTrace (prefixWord ++ tailWord_6670804) baseStart_6670804 baseEnd_6670804 := by
    simpa [prefixWord, tailWord_6670804, baseEnd_6670804] using wordTrace_append hprefix tailTrace_6670804
  have hstable : (prefixWord ++ tailWord_6670804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670804).length < 2 ^ (prefixWord ++ tailWord_6670804).sum := by decide
  have hdescent : baseEnd_6670804 < baseStart_6670804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670817 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 3]
def baseStart_6670817 : Nat := 118140960795 + 6670817 * 2 ^ 59
def prefixEnd_6670817 : Nat := 4983230072969 + 3 ^ 40 * 6670817 * 2
def baseEnd_6670817 : Nat := 3425335479183732131508977

theorem tailTrace_6670817 : CollatzResearch.WordTrace tailWord_6670817 prefixEnd_6670817 3425335479183732131508977 := by
  unfold tailWord_6670817
  simp only [CollatzResearch.WordTrace]
  refine ⟨243304684273776768685610705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162203122849184512457073803 243304684273776768685610705)
  ·
    refine ⟨182478513205332576514208029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243304684273776768685610705 182478513205332576514208029)
    ·
      refine ⟨68429442451999716192828011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182478513205332576514208029 68429442451999716192828011)
      ·
        refine ⟨102644163677999574289242017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68429442451999716192828011 102644163677999574289242017)
        ·
          refine ⟨76983122758499680716931513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102644163677999574289242017 76983122758499680716931513)
          ·
            refine ⟨57737342068874760537698635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76983122758499680716931513 57737342068874760537698635)
            ·
              refine ⟨86606013103312140806547953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57737342068874760537698635 86606013103312140806547953)
              ·
                refine ⟨64954509827484105604910965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86606013103312140806547953 64954509827484105604910965)
                ·
                  refine ⟨6089485296326634900460403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64954509827484105604910965 6089485296326634900460403)
                  ·
                    refine ⟨9134227944489952350690605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089485296326634900460403 9134227944489952350690605)
                    ·
                      refine ⟨3425335479183732131508977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9134227944489952350690605 3425335479183732131508977)
                      ·
                        rfl

theorem cell23_6670817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_6670817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670817 prefixEnd_6670817 := by exact prefixLift 6670817
  have htrace : WordTrace (prefixWord ++ tailWord_6670817) baseStart_6670817 baseEnd_6670817 := by
    simpa [prefixWord, tailWord_6670817, baseEnd_6670817] using wordTrace_append hprefix tailTrace_6670817
  have hstable : (prefixWord ++ tailWord_6670817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670817).length < 2 ^ (prefixWord ++ tailWord_6670817).sum := by decide
  have hdescent : baseEnd_6670817 < baseStart_6670817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670827 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 4, 3, 2]
def baseStart_6670827 : Nat := 118140960795 + 6670827 * 2 ^ 59
def prefixEnd_6670827 : Nat := 4983230072969 + 3 ^ 40 * 6670827 * 2
def baseEnd_6670827 : Nat := 3425340613990277092383931

theorem tailTrace_6670827 : CollatzResearch.WordTrace tailWord_6670827 prefixEnd_6670827 3425340613990277092383931 := by
  unfold tailWord_6670827
  simp only [CollatzResearch.WordTrace]
  refine ⟨243305049003740540393474735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162203366002493693595649823 243305049003740540393474735)
  ·
    refine ⟨364957573505610810590212103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243305049003740540393474735 364957573505610810590212103)
    ·
      refine ⟨547436360258416215885318155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364957573505610810590212103 547436360258416215885318155)
      ·
        refine ⟨821154540387624323827977233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547436360258416215885318155 821154540387624323827977233)
        ·
          refine ⟨615865905290718242870982925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821154540387624323827977233 615865905290718242870982925)
          ·
            refine ⟨230949714484019341076618597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 615865905290718242870982925 230949714484019341076618597)
            ·
              refine ⟨43303071465753626451865987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230949714484019341076618597 43303071465753626451865987)
              ·
                refine ⟨64954607198630439677798981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43303071465753626451865987 64954607198630439677798981)
                ·
                  refine ⟨12178988849743207439587309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64954607198630439677798981 12178988849743207439587309)
                  ·
                    refine ⟨4567120818653702789845241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12178988849743207439587309 4567120818653702789845241)
                    ·
                      refine ⟨3425340613990277092383931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567120818653702789845241 3425340613990277092383931)
                      ·
                        rfl

theorem cell23_6670827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 3, 2].length) (baseStart_6670827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670827 prefixEnd_6670827 := by exact prefixLift 6670827
  have htrace : WordTrace (prefixWord ++ tailWord_6670827) baseStart_6670827 baseEnd_6670827 := by
    simpa [prefixWord, tailWord_6670827, baseEnd_6670827] using wordTrace_append hprefix tailTrace_6670827
  have hstable : (prefixWord ++ tailWord_6670827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670827).length < 2 ^ (prefixWord ++ tailWord_6670827).sum := by decide
  have hdescent : baseEnd_6670827 < baseStart_6670827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670874 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2]
def baseStart_6670874 : Nat := 118140960795 + 6670874 * 2 ^ 59
def prefixEnd_6670874 : Nat := 4983230072969 + 3 ^ 40 * 6670874 * 2
def baseEnd_6670874 : Nat := 3425364747581038408496215

theorem tailTrace_6670874 : CollatzResearch.WordTrace tailWord_6670874 prefixEnd_6670874 3425364747581038408496215 := by
  unfold tailWord_6670874
  simp only [CollatzResearch.WordTrace]
  refine ⟨60826690808642566855108919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162204508823046844946957117 60826690808642566855108919)
  ·
    refine ⟨91240036212963850282663379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60826690808642566855108919 91240036212963850282663379)
    ·
      refine ⟨136860054319445775423995069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91240036212963850282663379 136860054319445775423995069)
      ·
        refine ⟨51322520369792165783998151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136860054319445775423995069 51322520369792165783998151)
        ·
          refine ⟨76983780554688248675997227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51322520369792165783998151 76983780554688248675997227)
          ·
            refine ⟨115475670832032373013995841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76983780554688248675997227 115475670832032373013995841)
            ·
              refine ⟨86606753124024279760496881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115475670832032373013995841 86606753124024279760496881)
              ·
                refine ⟨64955064843018209820372661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86606753124024279760496881 64955064843018209820372661)
                ·
                  refine ⟨6089537329032957170659937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64955064843018209820372661 6089537329032957170659937)
                  ·
                    refine ⟨4567152996774717877994953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6089537329032957170659937 4567152996774717877994953)
                    ·
                      refine ⟨3425364747581038408496215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567152996774717877994953 3425364747581038408496215)
                      ·
                        rfl

theorem cell23_6670874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_6670874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670874 prefixEnd_6670874 := by exact prefixLift 6670874
  have htrace : WordTrace (prefixWord ++ tailWord_6670874) baseStart_6670874 baseEnd_6670874 := by
    simpa [prefixWord, tailWord_6670874, baseEnd_6670874] using wordTrace_append hprefix tailTrace_6670874
  have hstable : (prefixWord ++ tailWord_6670874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670874).length < 2 ^ (prefixWord ++ tailWord_6670874).sum := by decide
  have hdescent : baseEnd_6670874 < baseStart_6670874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670877 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6670877 : Nat := 118140960795 + 6670877 * 2 ^ 59
def prefixEnd_6670877 : Nat := 4983230072969 + 3 ^ 40 * 6670877 * 2
def baseEnd_6670877 : Nat := 3425366288023001896758701

theorem tailTrace_6670877 : CollatzResearch.WordTrace tailWord_6670877 prefixEnd_6670877 3425366288023001896758701 := by
  unfold tailWord_6670877
  simp only [CollatzResearch.WordTrace]
  refine ⟨243306872653559398932794885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162204581769039599288529923 243306872653559398932794885)
  ·
    refine ⟨45620038622542387299899041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243306872653559398932794885 45620038622542387299899041)
    ·
      refine ⟨34215028966906790474924281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45620038622542387299899041 34215028966906790474924281)
      ·
        refine ⟨25661271725180092856193211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34215028966906790474924281 25661271725180092856193211)
        ·
          refine ⟨38491907587770139284289817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25661271725180092856193211 38491907587770139284289817)
          ·
            refine ⟨28868930690827604463217363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38491907587770139284289817 28868930690827604463217363)
            ·
              refine ⟨43303396036241406694826045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28868930690827604463217363 43303396036241406694826045)
              ·
                refine ⟨16238773513590527510559767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43303396036241406694826045 16238773513590527510559767)
                ·
                  refine ⟨24358160270385791265839651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16238773513590527510559767 24358160270385791265839651)
                  ·
                    refine ⟨36537240405578686898759477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24358160270385791265839651 36537240405578686898759477)
                    ·
                      refine ⟨3425366288023001896758701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36537240405578686898759477 3425366288023001896758701)
                      ·
                        rfl

theorem cell23_6670877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6670877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670877 prefixEnd_6670877 := by exact prefixLift 6670877
  have htrace : WordTrace (prefixWord ++ tailWord_6670877) baseStart_6670877 baseEnd_6670877 := by
    simpa [prefixWord, tailWord_6670877, baseEnd_6670877] using wordTrace_append hprefix tailTrace_6670877
  have hstable : (prefixWord ++ tailWord_6670877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670877).length < 2 ^ (prefixWord ++ tailWord_6670877).sum := by decide
  have hdescent : baseEnd_6670877 < baseStart_6670877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670891 : List Nat := [1, 1, 1, 1, 2, 1, 3, 8, 1, 2, 2]
def baseStart_6670891 : Nat := 118140960795 + 6670891 * 2 ^ 59
def prefixEnd_6670891 : Nat := 4983230072969 + 3 ^ 40 * 6670891 * 2
def baseEnd_6670891 : Nat := 3425373476752164841983637

theorem tailTrace_6670891 : CollatzResearch.WordTrace tailWord_6670891 prefixEnd_6670891 3425373476752164841983637 := by
  unfold tailWord_6670891
  simp only [CollatzResearch.WordTrace]
  refine ⟨243307383275508679323804527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162204922183672452882536351 243307383275508679323804527)
  ·
    refine ⟨364961074913263018985706791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243307383275508679323804527 364961074913263018985706791)
    ·
      refine ⟨547441612369894528478560187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364961074913263018985706791 547441612369894528478560187)
      ·
        refine ⟨821162418554841792717840281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547441612369894528478560187 821162418554841792717840281)
        ·
          refine ⟨615871813916131344538380211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821162418554841792717840281 615871813916131344538380211)
          ·
            refine ⟨923807720874197016807570317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615871813916131344538380211 923807720874197016807570317)
            ·
              refine ⟨346427895327823881302838869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 923807720874197016807570317 346427895327823881302838869)
              ·
                refine ⟨4059701898372936109017643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 346427895327823881302838869 4059701898372936109017643)
                ·
                  refine ⟨6089552847559404163526465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059701898372936109017643 6089552847559404163526465)
                  ·
                    refine ⟨4567164635669553122644849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6089552847559404163526465 4567164635669553122644849)
                    ·
                      refine ⟨3425373476752164841983637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567164635669553122644849 3425373476752164841983637)
                      ·
                        rfl

theorem cell23_6670891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 1, 2, 2].length) (baseStart_6670891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670891 prefixEnd_6670891 := by exact prefixLift 6670891
  have htrace : WordTrace (prefixWord ++ tailWord_6670891) baseStart_6670891 baseEnd_6670891 := by
    simpa [prefixWord, tailWord_6670891, baseEnd_6670891] using wordTrace_append hprefix tailTrace_6670891
  have hstable : (prefixWord ++ tailWord_6670891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670891).length < 2 ^ (prefixWord ++ tailWord_6670891).sum := by decide
  have hdescent : baseEnd_6670891 < baseStart_6670891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670920 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 1, 4, 5]
def baseStart_6670920 : Nat := 118140960795 + 6670920 * 2 ^ 59
def prefixEnd_6670920 : Nat := 4983230072969 + 3 ^ 40 * 6670920 * 2
def baseEnd_6670920 : Nat := 3425388367691145228521003

theorem tailTrace_6670920 : CollatzResearch.WordTrace tailWord_6670920 prefixEnd_6670920 3425388367691145228521003 := by
  unfold tailWord_6670920
  simp only [CollatzResearch.WordTrace]
  refine ⟨121654220496201808638305107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162205627328269078184406809 121654220496201808638305107)
  ·
    refine ⟨182481330744302712957457661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121654220496201808638305107 182481330744302712957457661)
    ·
      refine ⟨68430499029113517359046623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182481330744302712957457661 68430499029113517359046623)
      ·
        refine ⟨102645748543670276038569935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68430499029113517359046623 102645748543670276038569935)
        ·
          refine ⟨153968622815505414057854903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102645748543670276038569935 153968622815505414057854903)
          ·
            refine ⟨230952934223258121086782355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153968622815505414057854903 230952934223258121086782355)
            ·
              refine ⟨346429401334887181630173533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230952934223258121086782355 346429401334887181630173533)
              ·
                refine ⟨129911025500582693111315075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 346429401334887181630173533 129911025500582693111315075)
                ·
                  refine ⟨194866538250874039666972613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129911025500582693111315075 194866538250874039666972613)
                  ·
                    refine ⟨36537475922038882437557365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194866538250874039666972613 36537475922038882437557365)
                    ·
                      refine ⟨3425388367691145228521003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36537475922038882437557365 3425388367691145228521003)
                      ·
                        rfl

theorem cell23_6670920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_6670920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670920 prefixEnd_6670920 := by exact prefixLift 6670920
  have htrace : WordTrace (prefixWord ++ tailWord_6670920) baseStart_6670920 baseEnd_6670920 := by
    simpa [prefixWord, tailWord_6670920, baseEnd_6670920] using wordTrace_append hprefix tailTrace_6670920
  have hstable : (prefixWord ++ tailWord_6670920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670920).length < 2 ^ (prefixWord ++ tailWord_6670920).sum := by decide
  have hdescent : baseEnd_6670920 < baseStart_6670920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670957 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_6670957 : Nat := 118140960795 + 6670957 * 2 ^ 59
def prefixEnd_6670957 : Nat := 4983230072969 + 3 ^ 40 * 6670957 * 2
def baseEnd_6670957 : Nat := 1141802455491787194586111

theorem tailTrace_6670957 : CollatzResearch.WordTrace tailWord_6670957 prefixEnd_6670957 1141802455491787194586111 := by
  unfold tailWord_6670957
  simp only [CollatzResearch.WordTrace]
  refine ⟨243309790493269572595707125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162206526995513048397138083 243309790493269572595707125)
  ·
    refine ⟨22810292858744022430847543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243309790493269572595707125 22810292858744022430847543)
    ·
      refine ⟨34215439288116033646271315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22810292858744022430847543 34215439288116033646271315)
      ·
        refine ⟨51323158932174050469406973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34215439288116033646271315 51323158932174050469406973)
        ·
          refine ⟨19246184599565268926027615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51323158932174050469406973 19246184599565268926027615)
          ·
            refine ⟨28869276899347903389041423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19246184599565268926027615 28869276899347903389041423)
            ·
              refine ⟨43303915349021855083562135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28869276899347903389041423 43303915349021855083562135)
              ·
                refine ⟨64955873023532782625343203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43303915349021855083562135 64955873023532782625343203)
                ·
                  refine ⟨97433809535299173938014805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64955873023532782625343203 97433809535299173938014805)
                  ·
                    refine ⟨1141802455491787194586111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97433809535299173938014805 1141802455491787194586111)
                    ·
                      rfl

theorem cell23_6670957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_6670957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670957 prefixEnd_6670957 := by exact prefixLift 6670957
  have htrace : WordTrace (prefixWord ++ tailWord_6670957) baseStart_6670957 baseEnd_6670957 := by
    simpa [prefixWord, tailWord_6670957, baseEnd_6670957] using wordTrace_append hprefix tailTrace_6670957
  have hstable : (prefixWord ++ tailWord_6670957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670957).length < 2 ^ (prefixWord ++ tailWord_6670957).sum := by decide
  have hdescent : baseEnd_6670957 < baseStart_6670957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670977 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_6670977 : Nat := 118140960795 + 6670977 * 2 ^ 59
def prefixEnd_6670977 : Nat := 4983230072969 + 3 ^ 40 * 6670977 * 2
def baseEnd_6670977 : Nat := 3425417636088451505508241

theorem tailTrace_6670977 : CollatzResearch.WordTrace tailWord_6670977 prefixEnd_6670977 3425417636088451505508241 := by
  unfold tailWord_6670977
  simp only [CollatzResearch.WordTrace]
  refine ⟨243310519953197116011435185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162207013302131410674290123 243310519953197116011435185)
  ·
    refine ⟨182482889964897837008576389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243310519953197116011435185 182482889964897837008576389)
    ·
      refine ⟨34215541868418344439108073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182482889964897837008576389 34215541868418344439108073)
      ·
        refine ⟨25661656401313758329331055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34215541868418344439108073 25661656401313758329331055)
        ·
          refine ⟨38492484601970637493996583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25661656401313758329331055 38492484601970637493996583)
          ·
            refine ⟨57738726902955956240994875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38492484601970637493996583 57738726902955956240994875)
            ·
              refine ⟨86608090354433934361492313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57738726902955956240994875 86608090354433934361492313)
              ·
                refine ⟨64956067765825450771119235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86608090354433934361492313 64956067765825450771119235)
                ·
                  refine ⟨97434101648738176156678853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64956067765825450771119235 97434101648738176156678853)
                  ·
                    refine ⟨18268894059138408029377285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97434101648738176156678853 18268894059138408029377285)
                    ·
                      refine ⟨3425417636088451505508241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18268894059138408029377285 3425417636088451505508241)
                      ·
                        rfl

theorem cell23_6670977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_6670977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670977 prefixEnd_6670977 := by exact prefixLift 6670977
  have htrace : WordTrace (prefixWord ++ tailWord_6670977) baseStart_6670977 baseEnd_6670977 := by
    simpa [prefixWord, tailWord_6670977, baseEnd_6670977] using wordTrace_append hprefix tailTrace_6670977
  have hstable : (prefixWord ++ tailWord_6670977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670977).length < 2 ^ (prefixWord ++ tailWord_6670977).sum := by decide
  have hdescent : baseEnd_6670977 < baseStart_6670977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6670994 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6670994 : Nat := 118140960795 + 6670994 * 2 ^ 59
def prefixEnd_6670994 : Nat := 4983230072969 + 3 ^ 40 * 6670994 * 2
def baseEnd_6670994 : Nat := 3425426365259577938995663

theorem tailTrace_6670994 : CollatzResearch.WordTrace tailWord_6670994 prefixEnd_6670994 3425426365259577938995663 := by
  unfold tailWord_6670994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60827784998533881978701009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162207426662757018609869357 60827784998533881978701009)
  ·
    refine ⟨45620838748900411484025757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60827784998533881978701009 45620838748900411484025757)
    ·
      refine ⟨17107814530837654306509659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45620838748900411484025757 17107814530837654306509659)
      ·
        refine ⟨25661721796256481459764489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17107814530837654306509659 25661721796256481459764489)
        ·
          refine ⟨19246291347192361094823367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25661721796256481459764489 19246291347192361094823367)
          ·
            refine ⟨28869437020788541642235051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19246291347192361094823367 28869437020788541642235051)
            ·
              refine ⟨43304155531182812463352577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28869437020788541642235051 43304155531182812463352577)
              ·
                refine ⟨32478116648387109347514433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43304155531182812463352577 32478116648387109347514433)
                ·
                  refine ⟨24358587486290332010635825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32478116648387109347514433 24358587486290332010635825)
                  ·
                    refine ⟨18268940614717749007976869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24358587486290332010635825 18268940614717749007976869)
                    ·
                      refine ⟨3425426365259577938995663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18268940614717749007976869 3425426365259577938995663)
                      ·
                        rfl

theorem cell23_6670994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6670994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6670994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6670994 prefixEnd_6670994 := by exact prefixLift 6670994
  have htrace : WordTrace (prefixWord ++ tailWord_6670994) baseStart_6670994 baseEnd_6670994 := by
    simpa [prefixWord, tailWord_6670994, baseEnd_6670994] using wordTrace_append hprefix tailTrace_6670994
  have hstable : (prefixWord ++ tailWord_6670994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6670994).length < 2 ^ (prefixWord ++ tailWord_6670994).sum := by decide
  have hdescent : baseEnd_6670994 < baseStart_6670994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6670994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671004 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 7]
def baseStart_6671004 : Nat := 118140960795 + 6671004 * 2 ^ 59
def prefixEnd_6671004 : Nat := 4983230072969 + 3 ^ 40 * 6671004 * 2
def baseEnd_6671004 : Nat := 380603500007346988874513

theorem tailTrace_6671004 : CollatzResearch.WordTrace tailWord_6671004 prefixEnd_6671004 380603500007346988874513 := by
  unfold tailWord_6671004
  simp only [CollatzResearch.WordTrace]
  refine ⟨121655752362049649811334033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162207669816066199748445377 121655752362049649811334033)
  ·
    refine ⟨91241814271537237358500525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121655752362049649811334033 91241814271537237358500525)
    ·
      refine ⟨34215680351826464009437697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91241814271537237358500525 34215680351826464009437697)
      ·
        refine ⟨25661760263869848007078273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34215680351826464009437697 25661760263869848007078273)
        ·
          refine ⟨19246320197902386005308705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25661760263869848007078273 19246320197902386005308705)
          ·
            refine ⟨14434740148426789503981529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19246320197902386005308705 14434740148426789503981529)
            ·
              refine ⟨10826055111320092127986147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14434740148426789503981529 10826055111320092127986147)
              ·
                refine ⟨16239082666980138191979221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826055111320092127986147 16239082666980138191979221)
                ·
                  refine ⟨380603500007346988874513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16239082666980138191979221 380603500007346988874513)
                  ·
                    rfl

theorem cell23_6671004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 7].length) (baseStart_6671004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671004 prefixEnd_6671004 := by exact prefixLift 6671004
  have htrace : WordTrace (prefixWord ++ tailWord_6671004) baseStart_6671004 baseEnd_6671004 := by
    simpa [prefixWord, tailWord_6671004, baseEnd_6671004] using wordTrace_append hprefix tailTrace_6671004
  have hstable : (prefixWord ++ tailWord_6671004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671004).length < 2 ^ (prefixWord ++ tailWord_6671004).sum := by decide
  have hdescent : baseEnd_6671004 < baseStart_6671004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671015 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6671015 : Nat := 118140960795 + 6671015 * 2 ^ 59
def prefixEnd_6671015 : Nat := 4983230072969 + 3 ^ 40 * 6671015 * 2
def baseEnd_6671015 : Nat := 3425437148353322356833067

theorem tailTrace_6671015 : CollatzResearch.WordTrace tailWord_6671015 prefixEnd_6671015 3425437148353322356833067 := by
  unfold tailWord_6671015
  simp only [CollatzResearch.WordTrace]
  refine ⟨243311905927059448501318499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162207937284706299000878999 243311905927059448501318499)
  ·
    refine ⟨364967858890589172751977749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243311905927059448501318499 364967858890589172751977749)
    ·
      refine ⟨17107868385496367472748957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 364967858890589172751977749 17107868385496367472748957)
      ·
        refine ⟨6415450644561137802280859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17107868385496367472748957 6415450644561137802280859)
        ·
          refine ⟨9623175966841706703421289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415450644561137802280859 9623175966841706703421289)
          ·
            refine ⟨7217381975131280027565967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9623175966841706703421289 7217381975131280027565967)
            ·
              refine ⟨10826072962696920041348951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217381975131280027565967 10826072962696920041348951)
              ·
                refine ⟨16239109444045380062023427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826072962696920041348951 16239109444045380062023427)
                ·
                  refine ⟨24358664166068070093035141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16239109444045380062023427 24358664166068070093035141)
                  ·
                    refine ⟨4567249531137763142444089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24358664166068070093035141 4567249531137763142444089)
                    ·
                      refine ⟨3425437148353322356833067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567249531137763142444089 3425437148353322356833067)
                      ·
                        rfl

theorem cell23_6671015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6671015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671015 prefixEnd_6671015 := by exact prefixLift 6671015
  have htrace : WordTrace (prefixWord ++ tailWord_6671015) baseStart_6671015 baseEnd_6671015 := by
    simpa [prefixWord, tailWord_6671015, baseEnd_6671015] using wordTrace_append hprefix tailTrace_6671015
  have hstable : (prefixWord ++ tailWord_6671015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671015).length < 2 ^ (prefixWord ++ tailWord_6671015).sum := by decide
  have hdescent : baseEnd_6671015 < baseStart_6671015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671054 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6671054 : Nat := 118140960795 + 6671054 * 2 ^ 59
def prefixEnd_6671054 : Nat := 4983230072969 + 3 ^ 40 * 6671054 * 2
def baseEnd_6671054 : Nat := 3425457174098847704245387

theorem tailTrace_6671054 : CollatzResearch.WordTrace tailWord_6671054 prefixEnd_6671054 3425457174098847704245387 := by
  unfold tailWord_6671054
  simp only [CollatzResearch.WordTrace]
  refine ⟨30414166046739769770248527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162208885582612105441325477 30414166046739769770248527)
  ·
    refine ⟨45621249070109654655372791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30414166046739769770248527 45621249070109654655372791)
    ·
      refine ⟨68431873605164481983059187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45621249070109654655372791 68431873605164481983059187)
      ·
        refine ⟨102647810407746722974588781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68431873605164481983059187 102647810407746722974588781)
        ·
          refine ⟨38492928902905021115470793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102647810407746722974588781 38492928902905021115470793)
          ·
            refine ⟨28869696677178765836603095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38492928902905021115470793 28869696677178765836603095)
            ·
              refine ⟨43304545015768148754904643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28869696677178765836603095 43304545015768148754904643)
              ·
                refine ⟨64956817523652223132356965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43304545015768148754904643 64956817523652223132356965)
                ·
                  refine ⟨12179403285684791837316931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64956817523652223132356965 12179403285684791837316931)
                  ·
                    refine ⟨18269104928527187755975397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12179403285684791837316931 18269104928527187755975397)
                    ·
                      refine ⟨3425457174098847704245387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18269104928527187755975397 3425457174098847704245387)
                      ·
                        rfl

theorem cell23_6671054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6671054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671054 prefixEnd_6671054 := by exact prefixLift 6671054
  have htrace : WordTrace (prefixWord ++ tailWord_6671054) baseStart_6671054 baseEnd_6671054 := by
    simpa [prefixWord, tailWord_6671054, baseEnd_6671054] using wordTrace_append hprefix tailTrace_6671054
  have hstable : (prefixWord ++ tailWord_6671054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671054).length < 2 ^ (prefixWord ++ tailWord_6671054).sum := by decide
  have hdescent : baseEnd_6671054 < baseStart_6671054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671061 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6671061 : Nat := 118140960795 + 6671061 * 2 ^ 59
def prefixEnd_6671061 : Nat := 4983230072969 + 3 ^ 40 * 6671061 * 2
def baseEnd_6671061 : Nat := 3425460768463429176857855

theorem tailTrace_6671061 : CollatzResearch.WordTrace tailWord_6671061 prefixEnd_6671061 3425460768463429176857855 := by
  unfold tailWord_6671061
  simp only [CollatzResearch.WordTrace]
  refine ⟨243313583684892798357493037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162209055789928532238328691 243313583684892798357493037)
  ·
    refine ⟨91242593881834799384059889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243313583684892798357493037 91242593881834799384059889)
    ·
      refine ⟨68431945411376099538044917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91242593881834799384059889 68431945411376099538044917)
      ·
        refine ⟨6415494882316509331691711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68431945411376099538044917 6415494882316509331691711)
        ·
          refine ⟨9623242323474763997537567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415494882316509331691711 9623242323474763997537567)
          ·
            refine ⟨14434863485212145996306351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623242323474763997537567 14434863485212145996306351)
            ·
              refine ⟨21652295227818218994459527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14434863485212145996306351 21652295227818218994459527)
              ·
                refine ⟨32478442841727328491689291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21652295227818218994459527 32478442841727328491689291)
                ·
                  refine ⟨48717664262590992737533937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32478442841727328491689291 48717664262590992737533937)
                  ·
                    refine ⟨36538248196943244553150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48717664262590992737533937 36538248196943244553150453)
                    ·
                      refine ⟨3425460768463429176857855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36538248196943244553150453 3425460768463429176857855)
                      ·
                        rfl

theorem cell23_6671061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6671061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671061 prefixEnd_6671061 := by exact prefixLift 6671061
  have htrace : WordTrace (prefixWord ++ tailWord_6671061) baseStart_6671061 baseEnd_6671061 := by
    simpa [prefixWord, tailWord_6671061, baseEnd_6671061] using wordTrace_append hprefix tailTrace_6671061
  have hstable : (prefixWord ++ tailWord_6671061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671061).length < 2 ^ (prefixWord ++ tailWord_6671061).sum := by decide
  have hdescent : baseEnd_6671061 < baseStart_6671061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671111 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 6]
def baseStart_6671111 : Nat := 118140960795 + 6671111 * 2 ^ 59
def prefixEnd_6671111 : Nat := 4983230072969 + 3 ^ 40 * 6671111 * 2
def baseEnd_6671111 : Nat := 380609604721794886803625

theorem tailTrace_6671111 : CollatzResearch.WordTrace tailWord_6671111 prefixEnd_6671111 380609604721794886803625 := by
  unfold tailWord_6671111
  simp only [CollatzResearch.WordTrace]
  refine ⟨243315407334711656896813187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162210271556474437931208791 243315407334711656896813187)
  ·
    refine ⟨364973111002067485345219781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243315407334711656896813187 364973111002067485345219781)
    ·
      refine ⟨68432458312887653502228709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364973111002067485345219781 68432458312887653502228709)
      ·
        refine ⟨12831085933666435031667883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68432458312887653502228709 12831085933666435031667883)
        ·
          refine ⟨19246628900499652547501825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12831085933666435031667883 19246628900499652547501825)
          ·
            refine ⟨14434971675374739410626369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19246628900499652547501825 14434971675374739410626369)
            ·
              refine ⟨10826228756531054557969777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14434971675374739410626369 10826228756531054557969777)
              ·
                refine ⟨8119671567398290918477333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10826228756531054557969777 8119671567398290918477333)
                ·
                  refine ⟨380609604721794886803625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8119671567398290918477333 380609604721794886803625)
                  ·
                    rfl

theorem cell23_6671111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 6].length) (baseStart_6671111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671111 prefixEnd_6671111 := by exact prefixLift 6671111
  have htrace : WordTrace (prefixWord ++ tailWord_6671111) baseStart_6671111 baseEnd_6671111 := by
    simpa [prefixWord, tailWord_6671111, baseEnd_6671111] using wordTrace_append hprefix tailTrace_6671111
  have hstable : (prefixWord ++ tailWord_6671111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671111).length < 2 ^ (prefixWord ++ tailWord_6671111).sum := by decide
  have hdescent : baseEnd_6671111 < baseStart_6671111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671138 : List Nat := [3, 3, 1, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_6671138 : Nat := 118140960795 + 6671138 * 2 ^ 59
def prefixEnd_6671138 : Nat := 4983230072969 + 3 ^ 40 * 6671138 * 2
def baseEnd_6671138 : Nat := 3425500306473825375595001

theorem tailTrace_6671138 : CollatzResearch.WordTrace tailWord_6671138 prefixEnd_6671138 3425500306473825375595001 := by
  unfold tailWord_6671138
  simp only [CollatzResearch.WordTrace]
  refine ⟨60829098026403460127011517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162210928070409227005364045 60829098026403460127011517)
  ·
    refine ⟨22810911759901297547629319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60829098026403460127011517 22810911759901297547629319)
    ·
      refine ⟨34216367639851946321443979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22810911759901297547629319 34216367639851946321443979)
      ·
        refine ⟨51324551459777919482165969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34216367639851946321443979 51324551459777919482165969)
        ·
          refine ⟨38493413594833439611624477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51324551459777919482165969 38493413594833439611624477)
          ·
            refine ⟨14435030098062539854359179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38493413594833439611624477 14435030098062539854359179)
            ·
              refine ⟨21652545147093809781538769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435030098062539854359179 21652545147093809781538769)
              ·
                refine ⟨16239408860320357336154077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21652545147093809781538769 16239408860320357336154077)
                ·
                  refine ⟨6089778322620134001057779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16239408860320357336154077 6089778322620134001057779)
                  ·
                    refine ⟨9134667483930201001586669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089778322620134001057779 9134667483930201001586669)
                    ·
                      refine ⟨3425500306473825375595001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9134667483930201001586669 3425500306473825375595001)
                      ·
                        rfl

theorem cell23_6671138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_6671138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671138 prefixEnd_6671138 := by exact prefixLift 6671138
  have htrace : WordTrace (prefixWord ++ tailWord_6671138) baseStart_6671138 baseEnd_6671138 := by
    simpa [prefixWord, tailWord_6671138, baseEnd_6671138] using wordTrace_append hprefix tailTrace_6671138
  have hstable : (prefixWord ++ tailWord_6671138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671138).length < 2 ^ (prefixWord ++ tailWord_6671138).sum := by decide
  have hdescent : baseEnd_6671138 < baseStart_6671138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671154 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_6671154 : Nat := 118140960795 + 6671154 * 2 ^ 59
def prefixEnd_6671154 : Nat := 4983230072969 + 3 ^ 40 * 6671154 * 2
def baseEnd_6671154 : Nat := 1141836174054765770998309

theorem tailTrace_6671154 : CollatzResearch.WordTrace tailWord_6671154 prefixEnd_6671154 1141836174054765770998309 := by
  unfold tailWord_6671154
  simp only [CollatzResearch.WordTrace]
  refine ⟨60829243918388968810157129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162211317115703916827085677 60829243918388968810157129)
  ·
    refine ⟨45621932938791726607617847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60829243918388968810157129 45621932938791726607617847)
    ·
      refine ⟨68432899408187589911426771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45621932938791726607617847 68432899408187589911426771)
      ·
        refine ⟨102649349112281384867140157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68432899408187589911426771 102649349112281384867140157)
        ·
          refine ⟨38493505917105519325177559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102649349112281384867140157 38493505917105519325177559)
          ·
            refine ⟨57740258875658278987766339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38493505917105519325177559 57740258875658278987766339)
            ·
              refine ⟨86610388313487418481649509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57740258875658278987766339 86610388313487418481649509)
              ·
                refine ⟨16239447808778890965309283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86610388313487418481649509 16239447808778890965309283)
                ·
                  refine ⟨24359171713168336447963925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16239447808778890965309283 24359171713168336447963925)
                  ·
                    refine ⟨1141836174054765770998309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24359171713168336447963925 1141836174054765770998309)
                    ·
                      rfl

theorem cell23_6671154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_6671154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671154 prefixEnd_6671154 := by exact prefixLift 6671154
  have htrace : WordTrace (prefixWord ++ tailWord_6671154) baseStart_6671154 baseEnd_6671154 := by
    simpa [prefixWord, tailWord_6671154, baseEnd_6671154] using wordTrace_append hprefix tailTrace_6671154
  have hstable : (prefixWord ++ tailWord_6671154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671154).length < 2 ^ (prefixWord ++ tailWord_6671154).sum := by decide
  have hdescent : baseEnd_6671154 < baseStart_6671154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671155 : List Nat := [1, 1, 1, 2, 6, 2, 2, 3, 1, 1, 3]
def baseStart_6671155 : Nat := 118140960795 + 6671155 * 2 ^ 59
def prefixEnd_6671155 : Nat := 4983230072969 + 3 ^ 40 * 6671155 * 2
def baseEnd_6671155 : Nat := 3425509035644951809082423

theorem tailTrace_6671155 : CollatzResearch.WordTrace tailWord_6671155 prefixEnd_6671155 3425509035644951809082423 := by
  unfold tailWord_6671155
  simp only [CollatzResearch.WordTrace]
  refine ⟨243317012146552252411414919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162211341431034834940943279 243317012146552252411414919)
  ·
    refine ⟨364975518219828378617122379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243317012146552252411414919 364975518219828378617122379)
    ·
      refine ⟨547463277329742567925683569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364975518219828378617122379 547463277329742567925683569)
      ·
        refine ⟨410597457997306925944262677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547463277329742567925683569 410597457997306925944262677)
        ·
          refine ⟨19246755843623762153637313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 410597457997306925944262677 19246755843623762153637313)
          ·
            refine ⟨14435066882717821615227985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19246755843623762153637313 14435066882717821615227985)
            ·
              refine ⟨10826300162038366211420989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435066882717821615227985 10826300162038366211420989)
              ·
                refine ⟨4059862560764387329282871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10826300162038366211420989 4059862560764387329282871)
                ·
                  refine ⟨6089793841146580993924307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059862560764387329282871 6089793841146580993924307)
                  ·
                    refine ⟨9134690761719871490886461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089793841146580993924307 9134690761719871490886461)
                    ·
                      refine ⟨3425509035644951809082423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9134690761719871490886461 3425509035644951809082423)
                      ·
                        rfl

theorem cell23_6671155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 3, 1, 1, 3].length) (baseStart_6671155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671155 prefixEnd_6671155 := by exact prefixLift 6671155
  have htrace : WordTrace (prefixWord ++ tailWord_6671155) baseStart_6671155 baseEnd_6671155 := by
    simpa [prefixWord, tailWord_6671155, baseEnd_6671155] using wordTrace_append hprefix tailTrace_6671155
  have hstable : (prefixWord ++ tailWord_6671155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671155).length < 2 ^ (prefixWord ++ tailWord_6671155).sum := by decide
  have hdescent : baseEnd_6671155 < baseStart_6671155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671164 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_6671164 : Nat := 118140960795 + 6671164 * 2 ^ 59
def prefixEnd_6671164 : Nat := 4983230072969 + 3 ^ 40 * 6671164 * 2
def baseEnd_6671164 : Nat := 3425513656970842273869881

theorem tailTrace_6671164 : CollatzResearch.WordTrace tailWord_6671164 prefixEnd_6671164 3425513656970842273869881 := by
  unfold tailWord_6671164
  simp only [CollatzResearch.WordTrace]
  refine ⟨121658670201759823474246273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162211560269013097965661697 121658670201759823474246273)
  ·
    refine ⟨91244002651319867605684705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121658670201759823474246273 91244002651319867605684705)
    ·
      refine ⟨68433001988489900704263529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91244002651319867605684705 68433001988489900704263529)
      ·
        refine ⟨51324751491367425528197647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68433001988489900704263529 51324751491367425528197647)
        ·
          refine ⟨76987127237051138292296471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51324751491367425528197647 76987127237051138292296471)
          ·
            refine ⟨115480690855576707438444707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76987127237051138292296471 115480690855576707438444707)
            ·
              refine ⟨173221036283365061157667061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115480690855576707438444707 173221036283365061157667061)
              ·
                refine ⟨16239472151565474483531287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 173221036283365061157667061 16239472151565474483531287)
                ·
                  refine ⟨24359208227348211725296931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16239472151565474483531287 24359208227348211725296931)
                  ·
                    refine ⟨36538812341022317587945397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24359208227348211725296931 36538812341022317587945397)
                    ·
                      refine ⟨3425513656970842273869881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36538812341022317587945397 3425513656970842273869881)
                      ·
                        rfl

theorem cell23_6671164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_6671164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671164 prefixEnd_6671164 := by exact prefixLift 6671164
  have htrace : WordTrace (prefixWord ++ tailWord_6671164) baseStart_6671164 baseEnd_6671164 := by
    simpa [prefixWord, tailWord_6671164, baseEnd_6671164] using wordTrace_append hprefix tailTrace_6671164
  have hstable : (prefixWord ++ tailWord_6671164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671164).length < 2 ^ (prefixWord ++ tailWord_6671164).sum := by decide
  have hdescent : baseEnd_6671164 < baseStart_6671164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671172 : List Nat := [2, 3, 4, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6671172 : Nat := 118140960795 + 6671172 * 2 ^ 59
def prefixEnd_6671172 : Nat := 4983230072969 + 3 ^ 40 * 6671172 * 2
def baseEnd_6671172 : Nat := 3425517764816078242569845

theorem tailTrace_6671172 : CollatzResearch.WordTrace tailWord_6671172 prefixEnd_6671172 3425517764816078242569845 := by
  unfold tailWord_6671172
  simp only [CollatzResearch.WordTrace]
  refine ⟨121658816093745332157391885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162211754791660442876522513 121658816093745332157391885)
  ·
    refine ⟨45622056035154499559021957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121658816093745332157391885 45622056035154499559021957)
    ·
      refine ⟨8554135506591468667316617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45622056035154499559021957 8554135506591468667316617)
      ·
        refine ⟨6415601629943601500487463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8554135506591468667316617 6415601629943601500487463)
        ·
          refine ⟨9623402444915402250731195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415601629943601500487463 9623402444915402250731195)
          ·
            refine ⟨14435103667373103376096793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623402444915402250731195 14435103667373103376096793)
            ·
              refine ⟨10826327750529827532072595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435103667373103376096793 10826327750529827532072595)
              ·
                refine ⟨16239491625794741298108893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826327750529827532072595 16239491625794741298108893)
                ·
                  refine ⟨6089809359673027986790835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16239491625794741298108893 6089809359673027986790835)
                  ·
                    refine ⟨9134714039509541980186253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089809359673027986790835 9134714039509541980186253)
                    ·
                      refine ⟨3425517764816078242569845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9134714039509541980186253 3425517764816078242569845)
                      ·
                        rfl

theorem cell23_6671172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6671172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671172 prefixEnd_6671172 := by exact prefixLift 6671172
  have htrace : WordTrace (prefixWord ++ tailWord_6671172) baseStart_6671172 baseEnd_6671172 := by
    simpa [prefixWord, tailWord_6671172, baseEnd_6671172] using wordTrace_append hprefix tailTrace_6671172
  have hstable : (prefixWord ++ tailWord_6671172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671172).length < 2 ^ (prefixWord ++ tailWord_6671172).sum := by decide
  have hdescent : baseEnd_6671172 < baseStart_6671172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671188 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_6671188 : Nat := 118140960795 + 6671188 * 2 ^ 59
def prefixEnd_6671188 : Nat := 4983230072969 + 3 ^ 40 * 6671188 * 2
def baseEnd_6671188 : Nat := 1141841993502183393323257

theorem tailTrace_6671188 : CollatzResearch.WordTrace tailWord_6671188 prefixEnd_6671188 1141841993502183393323257 := by
  unfold tailWord_6671188
  simp only [CollatzResearch.WordTrace]
  refine ⟨121659107877716349523683109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162212143836955132698244145 121659107877716349523683109)
  ·
    refine ⟨22811082727071815535690583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121659107877716349523683109 22811082727071815535690583)
    ·
      refine ⟨34216624090607723303535875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22811082727071815535690583 34216624090607723303535875)
      ·
        refine ⟨51324936135911584955303813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34216624090607723303535875 51324936135911584955303813)
        ·
          refine ⟨9623425525483422179119465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51324936135911584955303813 9623425525483422179119465)
          ·
            refine ⟨7217569144112566634339599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9623425525483422179119465 7217569144112566634339599)
            ·
              refine ⟨10826353716168849951509399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217569144112566634339599 10826353716168849951509399)
              ·
                refine ⟨16239530574253274927264099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826353716168849951509399 16239530574253274927264099)
                ·
                  refine ⟨24359295861379912390896149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16239530574253274927264099 24359295861379912390896149)
                  ·
                    refine ⟨1141841993502183393323257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24359295861379912390896149 1141841993502183393323257)
                    ·
                      rfl

theorem cell23_6671188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_6671188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671188 prefixEnd_6671188 := by exact prefixLift 6671188
  have htrace : WordTrace (prefixWord ++ tailWord_6671188) baseStart_6671188 baseEnd_6671188 := by
    simpa [prefixWord, tailWord_6671188, baseEnd_6671188] using wordTrace_append hprefix tailTrace_6671188
  have hstable : (prefixWord ++ tailWord_6671188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671188).length < 2 ^ (prefixWord ++ tailWord_6671188).sum := by decide
  have hdescent : baseEnd_6671188 < baseStart_6671188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671191 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_6671191 : Nat := 118140960795 + 6671191 * 2 ^ 59
def prefixEnd_6671191 : Nat := 4983230072969 + 3 ^ 40 * 6671191 * 2
def baseEnd_6671191 : Nat := 3425527520948513668232257

theorem tailTrace_6671191 : CollatzResearch.WordTrace tailWord_6671191 prefixEnd_6671191 3425527520948513668232257 := by
  unfold tailWord_6671191
  simp only [CollatzResearch.WordTrace]
  refine ⟨243318325174421830559725427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162212216782947887039816951 243318325174421830559725427)
  ·
    refine ⟨364977487761632745839588141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243318325174421830559725427 364977487761632745839588141)
    ·
      refine ⟨136866557910612279689845553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364977487761632745839588141 136866557910612279689845553)
      ·
        refine ⟨102649918432959209767384165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136866557910612279689845553 102649918432959209767384165)
        ·
          refine ⟨19246859706179851831384531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102649918432959209767384165 19246859706179851831384531)
          ·
            refine ⟨28870289559269777747076797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19246859706179851831384531 28870289559269777747076797)
            ·
              refine ⟨10826358584726166655153799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28870289559269777747076797 10826358584726166655153799)
              ·
                refine ⟨16239537877089249982730699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826358584726166655153799 16239537877089249982730699)
                ·
                  refine ⟨24359306815633874974096049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16239537877089249982730699 24359306815633874974096049)
                  ·
                    refine ⟨18269480111725406230572037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24359306815633874974096049 18269480111725406230572037)
                    ·
                      refine ⟨3425527520948513668232257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18269480111725406230572037 3425527520948513668232257)
                      ·
                        rfl

theorem cell23_6671191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_6671191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671191 prefixEnd_6671191 := by exact prefixLift 6671191
  have htrace : WordTrace (prefixWord ++ tailWord_6671191) baseStart_6671191 baseEnd_6671191 := by
    simpa [prefixWord, tailWord_6671191, baseEnd_6671191] using wordTrace_append hprefix tailTrace_6671191
  have hstable : (prefixWord ++ tailWord_6671191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671191).length < 2 ^ (prefixWord ++ tailWord_6671191).sum := by decide
  have hdescent : baseEnd_6671191 < baseStart_6671191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671211 : List Nat := [1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 3]
def baseStart_6671211 : Nat := 118140960795 + 6671211 * 2 ^ 59
def prefixEnd_6671211 : Nat := 4983230072969 + 3 ^ 40 * 6671211 * 2
def baseEnd_6671211 : Nat := 3425537790561603589982165

theorem tailTrace_6671211 : CollatzResearch.WordTrace tailWord_6671211 prefixEnd_6671211 3425537790561603589982165 := by
  unfold tailWord_6671211
  simp only [CollatzResearch.WordTrace]
  refine ⟨243319054634349373975453487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162212703089566249316968991 243319054634349373975453487)
  ·
    refine ⟨364978581951524060963180231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243319054634349373975453487 364978581951524060963180231)
    ·
      refine ⟨547467872927286091444770347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364978581951524060963180231 547467872927286091444770347)
      ·
        refine ⟨821201809390929137167155521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547467872927286091444770347 821201809390929137167155521)
        ·
          refine ⟨615901357043196852875366641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821201809390929137167155521 615901357043196852875366641)
          ·
            refine ⟨461926017782397639656524981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 615901357043196852875366641 461926017782397639656524981)
            ·
              refine ⟨43305564167099778717799217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 461926017782397639656524981 43305564167099778717799217)
              ·
                refine ⟨32479173125324834038349413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43305564167099778717799217 32479173125324834038349413)
                ·
                  refine ⟨6089844960998406382190515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32479173125324834038349413 6089844960998406382190515)
                  ·
                    refine ⟨9134767441497609573285773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6089844960998406382190515 9134767441497609573285773)
                    ·
                      refine ⟨3425537790561603589982165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9134767441497609573285773 3425537790561603589982165)
                      ·
                        rfl

theorem cell23_6671211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 3].length) (baseStart_6671211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671211 prefixEnd_6671211 := by exact prefixLift 6671211
  have htrace : WordTrace (prefixWord ++ tailWord_6671211) baseStart_6671211 baseEnd_6671211 := by
    simpa [prefixWord, tailWord_6671211, baseEnd_6671211] using wordTrace_append hprefix tailTrace_6671211
  have hstable : (prefixWord ++ tailWord_6671211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671211).length < 2 ^ (prefixWord ++ tailWord_6671211).sum := by decide
  have hdescent : baseEnd_6671211 < baseStart_6671211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671244 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_6671244 : Nat := 118140960795 + 6671244 * 2 ^ 59
def prefixEnd_6671244 : Nat := 4983230072969 + 3 ^ 40 * 6671244 * 2
def baseEnd_6671244 : Nat := 1141851578474400653623171

theorem tailTrace_6671244 : CollatzResearch.WordTrace tailWord_6671244 prefixEnd_6671244 1141851578474400653623171 := by
  unfold tailWord_6671244
  simp only [CollatzResearch.WordTrace]
  refine ⟨121660129121614910305702393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162213505495486547074269857 121660129121614910305702393)
  ·
    refine ⟨91245096841211182729276795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121660129121614910305702393 91245096841211182729276795)
    ·
      refine ⟨136867645261816774093915193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91245096841211182729276795 136867645261816774093915193)
      ·
        refine ⟨102650733946362580570436395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136867645261816774093915193 102650733946362580570436395)
        ·
          refine ⟨153976100919543870855654593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102650733946362580570436395 153976100919543870855654593)
          ·
            refine ⟨115482075689657903141740945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153976100919543870855654593 115482075689657903141740945)
            ·
              refine ⟨86611556767243427356305709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115482075689657903141740945 86611556767243427356305709)
              ·
                refine ⟨32479333787716285258614641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86611556767243427356305709 32479333787716285258614641)
                ·
                  refine ⟨24359500340787213943960981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32479333787716285258614641 24359500340787213943960981)
                  ·
                    refine ⟨1141851578474400653623171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24359500340787213943960981 1141851578474400653623171)
                    ·
                      rfl

theorem cell23_6671244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_6671244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671244 prefixEnd_6671244 := by exact prefixLift 6671244
  have htrace : WordTrace (prefixWord ++ tailWord_6671244) baseStart_6671244 baseEnd_6671244 := by
    simpa [prefixWord, tailWord_6671244, baseEnd_6671244] using wordTrace_append hprefix tailTrace_6671244
  have hstable : (prefixWord ++ tailWord_6671244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671244).length < 2 ^ (prefixWord ++ tailWord_6671244).sum := by decide
  have hdescent : baseEnd_6671244 < baseStart_6671244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671268 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_6671268 : Nat := 118140960795 + 6671268 * 2 ^ 59
def prefixEnd_6671268 : Nat := 4983230072969 + 3 ^ 40 * 6671268 * 2
def baseEnd_6671268 : Nat := 3425567058958909866969403

theorem tailTrace_6671268 : CollatzResearch.WordTrace tailWord_6671268 prefixEnd_6671268 3425567058958909866969403 := by
  unfold tailWord_6671268
  simp only [CollatzResearch.WordTrace]
  refine ⟨121660566797571436355139229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162214089063428581806852305 121660566797571436355139229)
  ·
    refine ⟨45622712549089288633177211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121660566797571436355139229 45622712549089288633177211)
    ·
      refine ⟨68434068823633932949765817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45622712549089288633177211 68434068823633932949765817)
      ·
        refine ⟨51325551617725449712324363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68434068823633932949765817 51325551617725449712324363)
        ·
          refine ⟨76988327426588174568486545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51325551617725449712324363 76988327426588174568486545)
          ·
            refine ⟨57741245569941130926364909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76988327426588174568486545 57741245569941130926364909)
            ·
              refine ⟨21652967088727924097386841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57741245569941130926364909 21652967088727924097386841)
              ·
                refine ⟨16239725316545943073040131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21652967088727924097386841 16239725316545943073040131)
                ·
                  refine ⟨24359587974818914609560197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16239725316545943073040131 24359587974818914609560197)
                  ·
                    refine ⟨4567422745278546489292537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24359587974818914609560197 4567422745278546489292537)
                    ·
                      refine ⟨3425567058958909866969403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567422745278546489292537 3425567058958909866969403)
                      ·
                        rfl

theorem cell23_6671268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_6671268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671268 prefixEnd_6671268 := by exact prefixLift 6671268
  have htrace : WordTrace (prefixWord ++ tailWord_6671268) baseStart_6671268 baseEnd_6671268 := by
    simpa [prefixWord, tailWord_6671268, baseEnd_6671268] using wordTrace_append hprefix tailTrace_6671268
  have hstable : (prefixWord ++ tailWord_6671268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671268).length < 2 ^ (prefixWord ++ tailWord_6671268).sum := by decide
  have hdescent : baseEnd_6671268 < baseStart_6671268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671321 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 1, 7]
def baseStart_6671321 : Nat := 118140960795 + 6671321 * 2 ^ 59
def prefixEnd_6671321 : Nat := 4983230072969 + 3 ^ 40 * 6671321 * 2
def baseEnd_6671321 : Nat := 1141864757811199386535553

theorem tailTrace_6671321 : CollatzResearch.WordTrace tailWord_6671321 prefixEnd_6671321 1141864757811199386535553 := by
  unfold tailWord_6671321
  simp only [CollatzResearch.WordTrace]
  refine ⟨243323066663950862761957817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162215377775967241841305211 243323066663950862761957817)
  ·
    refine ⟨182492299997963147071468363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243323066663950862761957817 182492299997963147071468363)
    ·
      refine ⟨273738449996944720607202545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182492299997963147071468363 273738449996944720607202545)
      ·
        refine ⟨205303837497708540455401909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273738449996944720607202545 205303837497708540455401909)
        ·
          refine ⟨19247234765410175667693929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205303837497708540455401909 19247234765410175667693929)
          ·
            refine ⟨14435426074057631750770447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19247234765410175667693929 14435426074057631750770447)
            ·
              refine ⟨21653139111086447626155671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435426074057631750770447 21653139111086447626155671)
              ·
                refine ⟨32479708666629671439233507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21653139111086447626155671 32479708666629671439233507)
                ·
                  refine ⟨48719562999944507158850261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32479708666629671439233507 48719562999944507158850261)
                  ·
                    refine ⟨1141864757811199386535553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48719562999944507158850261 1141864757811199386535553)
                    ·
                      rfl

theorem cell23_6671321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 7].length) (baseStart_6671321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671321 prefixEnd_6671321 := by exact prefixLift 6671321
  have htrace : WordTrace (prefixWord ++ tailWord_6671321) baseStart_6671321 baseEnd_6671321 := by
    simpa [prefixWord, tailWord_6671321, baseEnd_6671321] using wordTrace_append hprefix tailTrace_6671321
  have hstable : (prefixWord ++ tailWord_6671321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671321).length < 2 ^ (prefixWord ++ tailWord_6671321).sum := by decide
  have hdescent : baseEnd_6671321 < baseStart_6671321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671325 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 5]
def baseStart_6671325 : Nat := 118140960795 + 6671325 * 2 ^ 59
def prefixEnd_6671325 : Nat := 4983230072969 + 3 ^ 40 * 6671325 * 2
def baseEnd_6671325 : Nat := 380621814150690682661849

theorem tailTrace_6671325 : CollatzResearch.WordTrace tailWord_6671325 prefixEnd_6671325 380621814150690682661849 := by
  unfold tailWord_6671325
  simp only [CollatzResearch.WordTrace]
  refine ⟨243323212555936371445103429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162215475037290914296735619 243323212555936371445103429)
  ·
    refine ⟨45623102354238069645956893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243323212555936371445103429 45623102354238069645956893)
    ·
      refine ⟨17108663382839276117233835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45623102354238069645956893 17108663382839276117233835)
      ·
        refine ⟨25662995074258914175850753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17108663382839276117233835 25662995074258914175850753)
        ·
          refine ⟨19247246305694185631888065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25662995074258914175850753 19247246305694185631888065)
          ·
            refine ⟨14435434729270639223916049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19247246305694185631888065 14435434729270639223916049)
            ·
              refine ⟨10826576046952979417937037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14435434729270639223916049 10826576046952979417937037)
              ·
                refine ⟨4059966017607367281726389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10826576046952979417937037 4059966017607367281726389)
                ·
                  refine ⟨380621814150690682661849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4059966017607367281726389 380621814150690682661849)
                  ·
                    rfl

theorem cell23_6671325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_6671325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671325 prefixEnd_6671325 := by exact prefixLift 6671325
  have htrace : WordTrace (prefixWord ++ tailWord_6671325) baseStart_6671325 baseEnd_6671325 := by
    simpa [prefixWord, tailWord_6671325, baseEnd_6671325] using wordTrace_append hprefix tailTrace_6671325
  have hstable : (prefixWord ++ tailWord_6671325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671325).length < 2 ^ (prefixWord ++ tailWord_6671325).sum := by decide
  have hdescent : baseEnd_6671325 < baseStart_6671325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671368 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 3, 4]
def baseStart_6671368 : Nat := 118140960795 + 6671368 * 2 ^ 59
def prefixEnd_6671368 : Nat := 4983230072969 + 3 ^ 40 * 6671368 * 2
def baseEnd_6671368 : Nat := 1141872802341453158572981

theorem tailTrace_6671368 : CollatzResearch.WordTrace tailWord_6671368 prefixEnd_6671368 1141872802341453158572981 := by
  unfold tailWord_6671368
  simp only [CollatzResearch.WordTrace]
  refine ⟨121662390447390294894459379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162216520596520393192612505 121662390447390294894459379)
  ·
    refine ⟨182493585671085442341689069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121662390447390294894459379 182493585671085442341689069)
    ·
      refine ⟨68435094626657040878133401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182493585671085442341689069 68435094626657040878133401)
      ·
        refine ⟨51326320969992780658600051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68435094626657040878133401 51326320969992780658600051)
        ·
          refine ⟨76989481454989170987900077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51326320969992780658600051 76989481454989170987900077)
          ·
            refine ⟨28871055545620939120462529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76989481454989170987900077 28871055545620939120462529)
            ·
              refine ⟨21653291659215704340346897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28871055545620939120462529 21653291659215704340346897)
              ·
                refine ⟨16239968744411778255260173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21653291659215704340346897 16239968744411778255260173)
                ·
                  refine ⟨6089988279154416845722565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16239968744411778255260173 6089988279154416845722565)
                  ·
                    refine ⟨1141872802341453158572981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6089988279154416845722565 1141872802341453158572981)
                    ·
                      rfl

theorem cell23_6671368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_6671368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671368 prefixEnd_6671368 := by exact prefixLift 6671368
  have htrace : WordTrace (prefixWord ++ tailWord_6671368) baseStart_6671368 baseEnd_6671368 := by
    simpa [prefixWord, tailWord_6671368, baseEnd_6671368] using wordTrace_append hprefix tailTrace_6671368
  have hstable : (prefixWord ++ tailWord_6671368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671368).length < 2 ^ (prefixWord ++ tailWord_6671368).sum := by decide
  have hdescent : baseEnd_6671368 < baseStart_6671368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671381 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 8]
def baseStart_6671381 : Nat := 118140960795 + 6671381 * 2 ^ 59
def prefixEnd_6671381 : Nat := 4983230072969 + 3 ^ 40 * 6671381 * 2
def baseEnd_6671381 : Nat := 380625009141429769428487

theorem tailTrace_6671381 : CollatzResearch.WordTrace tailWord_6671381 prefixEnd_6671381 380625009141429769428487 := by
  unfold tailWord_6671381
  simp only [CollatzResearch.WordTrace]
  refine ⟨243325255043733493009141997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162216836695822328672761331 243325255043733493009141997)
  ·
    refine ⟨91246970641400059878428249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243325255043733493009141997 91246970641400059878428249)
    ·
      refine ⟨68435227981050044908821187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91246970641400059878428249 68435227981050044908821187)
      ·
        refine ⟨102652841971575067363231781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68435227981050044908821187 102652841971575067363231781)
        ·
          refine ⟨19247407869670325130605959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102652841971575067363231781 19247407869670325130605959)
          ·
            refine ⟨28871111804505487695908939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19247407869670325130605959 28871111804505487695908939)
            ·
              refine ⟨43306667706758231543863409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28871111804505487695908939 43306667706758231543863409)
              ·
                refine ⟨32480000780068673657897557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43306667706758231543863409 32480000780068673657897557)
                ·
                  refine ⟨380625009141429769428487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32480000780068673657897557 380625009141429769428487)
                  ·
                    rfl

theorem cell23_6671381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_6671381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671381 prefixEnd_6671381 := by exact prefixLift 6671381
  have htrace : WordTrace (prefixWord ++ tailWord_6671381) baseStart_6671381 baseEnd_6671381 := by
    simpa [prefixWord, tailWord_6671381, baseEnd_6671381] using wordTrace_append hprefix tailTrace_6671381
  have hstable : (prefixWord ++ tailWord_6671381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671381).length < 2 ^ (prefixWord ++ tailWord_6671381).sum := by decide
  have hdescent : baseEnd_6671381 < baseStart_6671381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671385 : List Nat := [1, 2, 1, 2, 1, 1, 7, 3, 1, 4]
def baseStart_6671385 : Nat := 118140960795 + 6671385 * 2 ^ 59
def prefixEnd_6671385 : Nat := 4983230072969 + 3 ^ 40 * 6671385 * 2
def baseEnd_6671385 : Nat := 1141875712065161969735455

theorem tailTrace_6671385 : CollatzResearch.WordTrace tailWord_6671385 prefixEnd_6671385 1141875712065161969735455 := by
  unfold tailWord_6671385
  simp only [CollatzResearch.WordTrace]
  refine ⟨243325400935719001692287609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162216933957146001128191739 243325400935719001692287609)
  ·
    refine ⟨182494050701789251269215707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243325400935719001692287609 182494050701789251269215707)
    ·
      refine ⟨273741076052683876903823561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182494050701789251269215707 273741076052683876903823561)
      ·
        refine ⟨205305807039512907677867671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273741076052683876903823561 205305807039512907677867671)
        ·
          refine ⟨307958710559269361516801507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205305807039512907677867671 307958710559269361516801507)
          ·
            refine ⟨461938065838904042275202261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307958710559269361516801507 461938065838904042275202261)
            ·
              refine ⟨10826673418099313490825053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 461938065838904042275202261 10826673418099313490825053)
              ·
                refine ⟨4060002531787242559059395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10826673418099313490825053 4060002531787242559059395)
                ·
                  refine ⟨6090003797680863838589093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4060002531787242559059395 6090003797680863838589093)
                  ·
                    refine ⟨1141875712065161969735455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6090003797680863838589093 1141875712065161969735455)
                    ·
                      rfl

theorem cell23_6671385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 1, 4].length) (baseStart_6671385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671385 prefixEnd_6671385 := by exact prefixLift 6671385
  have htrace : WordTrace (prefixWord ++ tailWord_6671385) baseStart_6671385 baseEnd_6671385 := by
    simpa [prefixWord, tailWord_6671385, baseEnd_6671385] using wordTrace_append hprefix tailTrace_6671385
  have hstable : (prefixWord ++ tailWord_6671385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671385).length < 2 ^ (prefixWord ++ tailWord_6671385).sum := by decide
  have hdescent : baseEnd_6671385 < baseStart_6671385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671402 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_6671402 : Nat := 118140960795 + 6671402 * 2 ^ 59
def prefixEnd_6671402 : Nat := 4983230072969 + 3 ^ 40 * 6671402 * 2
def baseEnd_6671402 : Nat := 1141878621788870780897929

theorem tailTrace_6671402 : CollatzResearch.WordTrace tailWord_6671402 prefixEnd_6671402 1141878621788870780897929 := by
  unfold tailWord_6671402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60831505244164353398914115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162217347317771609063770973 60831505244164353398914115)
  ·
    refine ⟨91247257866246530098371173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60831505244164353398914115 91247257866246530098371173)
    ·
      refine ⟨17108860849921224393444595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91247257866246530098371173 17108860849921224393444595)
      ·
        refine ⟨25663291274881836590166893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17108860849921224393444595 25663291274881836590166893)
        ·
          refine ⟨9623734228080688721312585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25663291274881836590166893 9623734228080688721312585)
          ·
            refine ⟨7217800671060516540984439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9623734228080688721312585 7217800671060516540984439)
            ·
              refine ⟨10826701006590774811476659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7217800671060516540984439 10826701006590774811476659)
              ·
                refine ⟨16240051509886162217214989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10826701006590774811476659 16240051509886162217214989)
                ·
                  refine ⟨6090019316207310831455621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16240051509886162217214989 6090019316207310831455621)
                  ·
                    refine ⟨1141878621788870780897929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6090019316207310831455621 1141878621788870780897929)
                    ·
                      rfl

theorem cell23_6671402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_6671402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671402 prefixEnd_6671402 := by exact prefixLift 6671402
  have htrace : WordTrace (prefixWord ++ tailWord_6671402) baseStart_6671402 baseEnd_6671402 := by
    simpa [prefixWord, tailWord_6671402, baseEnd_6671402] using wordTrace_append hprefix tailTrace_6671402
  have hstable : (prefixWord ++ tailWord_6671402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671402).length < 2 ^ (prefixWord ++ tailWord_6671402).sum := by decide
  have hdescent : baseEnd_6671402 < baseStart_6671402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671411 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 3, 5]
def baseStart_6671411 : Nat := 118140960795 + 6671411 * 2 ^ 59
def prefixEnd_6671411 : Nat := 4983230072969 + 3 ^ 40 * 6671411 * 2
def baseEnd_6671411 : Nat := 1141880162230834269160415

theorem tailTrace_6671411 : CollatzResearch.WordTrace tailWord_6671411 prefixEnd_6671411 1141880162230834269160415 := by
  unfold tailWord_6671411
  simp only [CollatzResearch.WordTrace]
  refine ⟨243326349233624808132734087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162217566155749872088489391 243326349233624808132734087)
  ·
    refine ⟨364989523850437212199101131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243326349233624808132734087 364989523850437212199101131)
    ·
      refine ⟨547484285775655818298651697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364989523850437212199101131 547484285775655818298651697)
      ·
        refine ⟨410613214331741863723988773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547484285775655818298651697 410613214331741863723988773)
        ·
          refine ⟨76989977687201599448247895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410613214331741863723988773 76989977687201599448247895)
          ·
            refine ⟨115484966530802399172371843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76989977687201599448247895 115484966530802399172371843)
            ·
              refine ⟨173227449796203598758557765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115484966530802399172371843 173227449796203598758557765)
              ·
                refine ⟨32480146836788174767229581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173227449796203598758557765 32480146836788174767229581)
                ·
                  refine ⟨12180055063795565537711093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32480146836788174767229581 12180055063795565537711093)
                  ·
                    refine ⟨1141880162230834269160415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12180055063795565537711093 1141880162230834269160415)
                    ·
                      rfl

theorem cell23_6671411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 5].length) (baseStart_6671411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671411 prefixEnd_6671411 := by exact prefixLift 6671411
  have htrace : WordTrace (prefixWord ++ tailWord_6671411) baseStart_6671411 baseEnd_6671411 := by
    simpa [prefixWord, tailWord_6671411, baseEnd_6671411] using wordTrace_append hprefix tailTrace_6671411
  have hstable : (prefixWord ++ tailWord_6671411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671411).length < 2 ^ (prefixWord ++ tailWord_6671411).sum := by decide
  have hdescent : baseEnd_6671411 < baseStart_6671411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671418 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2]
def baseStart_6671418 : Nat := 118140960795 + 6671418 * 2 ^ 59
def prefixEnd_6671418 : Nat := 4983230072969 + 3 ^ 40 * 6671418 * 2
def baseEnd_6671418 : Nat := 3425644081057084280093713

theorem tailTrace_6671418 : CollatzResearch.WordTrace tailWord_6671418 prefixEnd_6671418 3425644081057084280093713 := by
  unfold tailWord_6671418
  simp only [CollatzResearch.WordTrace]
  refine ⟨60831651136149862082059727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162217736363066298885492605 60831651136149862082059727)
  ·
    refine ⟨91247476704224793123089591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60831651136149862082059727 91247476704224793123089591)
    ·
      refine ⟨136871215056337189684634387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91247476704224793123089591 136871215056337189684634387)
      ·
        refine ⟨205306822584505784526951581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136871215056337189684634387 205306822584505784526951581)
        ·
          refine ⟨76990058469189669197606843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205306822584505784526951581 76990058469189669197606843)
          ·
            refine ⟨115485087703784503796410265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76990058469189669197606843 115485087703784503796410265)
            ·
              refine ⟨86613815777838377847307699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115485087703784503796410265 86613815777838377847307699)
              ·
                refine ⟨129920723666757566770961549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86613815777838377847307699 129920723666757566770961549)
                ·
                  refine ⟨48720271375034087539110581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129920723666757566770961549 48720271375034087539110581)
                  ·
                    refine ⟨4567525441409445706791617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48720271375034087539110581 4567525441409445706791617)
                    ·
                      refine ⟨3425644081057084280093713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567525441409445706791617 3425644081057084280093713)
                      ·
                        rfl

theorem cell23_6671418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_6671418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671418 prefixEnd_6671418 := by exact prefixLift 6671418
  have htrace : WordTrace (prefixWord ++ tailWord_6671418) baseStart_6671418 baseEnd_6671418 := by
    simpa [prefixWord, tailWord_6671418, baseEnd_6671418] using wordTrace_append hprefix tailTrace_6671418
  have hstable : (prefixWord ++ tailWord_6671418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671418).length < 2 ^ (prefixWord ++ tailWord_6671418).sum := by decide
  have hdescent : baseEnd_6671418 < baseStart_6671418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671441 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 3, 6]
def baseStart_6671441 : Nat := 118140960795 + 6671441 * 2 ^ 59
def prefixEnd_6671441 : Nat := 4983230072969 + 3 ^ 40 * 6671441 * 2
def baseEnd_6671441 : Nat := 1141885297037379230035369

theorem tailTrace_6671441 : CollatzResearch.WordTrace tailWord_6671441 prefixEnd_6671441 1141885297037379230035369 := by
  unfold tailWord_6671441
  simp only [CollatzResearch.WordTrace]
  refine ⟨243327443423516123256326177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162218295615677415504217451 243327443423516123256326177)
  ·
    refine ⟨182495582567637092442244633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243327443423516123256326177 182495582567637092442244633)
    ·
      refine ⟨136871686925727819331683475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182495582567637092442244633 136871686925727819331683475)
      ·
        refine ⟨205307530388591728997525213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136871686925727819331683475 205307530388591728997525213)
        ·
          refine ⟨76990323895721898374071955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205307530388591728997525213 76990323895721898374071955)
          ·
            refine ⟨115485485843582847561107933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76990323895721898374071955 115485485843582847561107933)
            ·
              refine ⟨43307057191343567835415475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115485485843582847561107933 43307057191343567835415475)
              ·
                refine ⟨64960585787015351753123213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43307057191343567835415475 64960585787015351753123213)
                ·
                  refine ⟨24360219670130756907421205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64960585787015351753123213 24360219670130756907421205)
                  ·
                    refine ⟨1141885297037379230035369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24360219670130756907421205 1141885297037379230035369)
                    ·
                      rfl

theorem cell23_6671441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 6].length) (baseStart_6671441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671441 prefixEnd_6671441 := by exact prefixLift 6671441
  have htrace : WordTrace (prefixWord ++ tailWord_6671441) baseStart_6671441 baseEnd_6671441 := by
    simpa [prefixWord, tailWord_6671441, baseEnd_6671441] using wordTrace_append hprefix tailTrace_6671441
  have hstable : (prefixWord ++ tailWord_6671441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671441).length < 2 ^ (prefixWord ++ tailWord_6671441).sum := by decide
  have hdescent : baseEnd_6671441 < baseStart_6671441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671445 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_6671445 : Nat := 118140960795 + 6671445 * 2 ^ 59
def prefixEnd_6671445 : Nat := 4983230072969 + 3 ^ 40 * 6671445 * 2
def baseEnd_6671445 : Nat := 1141885981678251891485363

theorem tailTrace_6671445 : CollatzResearch.WordTrace tailWord_6671445 prefixEnd_6671445 1141885981678251891485363 := by
  unfold tailWord_6671445
  simp only [CollatzResearch.WordTrace]
  refine ⟨243327589315501631939471789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162218392877001087959647859 243327589315501631939471789)
  ·
    refine ⟨91247845993313111977301921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243327589315501631939471789 91247845993313111977301921)
    ·
      refine ⟨68435884494984833982976441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91247845993313111977301921 68435884494984833982976441)
      ·
        refine ⟨51326913371238625487232331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68435884494984833982976441 51326913371238625487232331)
        ·
          refine ⟨76990370056857938230848497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51326913371238625487232331 76990370056857938230848497)
          ·
            refine ⟨57742777542643453673136373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76990370056857938230848497 57742777542643453673136373)
            ·
              refine ⟨5413385394622823781856535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57742777542643453673136373 5413385394622823781856535)
              ·
                refine ⟨8120078091934235672784803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5413385394622823781856535 8120078091934235672784803)
                ·
                  refine ⟨12180117137901353509177205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120078091934235672784803 12180117137901353509177205)
                  ·
                    refine ⟨1141885981678251891485363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12180117137901353509177205 1141885981678251891485363)
                    ·
                      rfl

theorem cell23_6671445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_6671445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671445 prefixEnd_6671445 := by exact prefixLift 6671445
  have htrace : WordTrace (prefixWord ++ tailWord_6671445) baseStart_6671445 baseEnd_6671445 := by
    simpa [prefixWord, tailWord_6671445, baseEnd_6671445] using wordTrace_append hprefix tailTrace_6671445
  have hstable : (prefixWord ++ tailWord_6671445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671445).length < 2 ^ (prefixWord ++ tailWord_6671445).sum := by decide
  have hdescent : baseEnd_6671445 < baseStart_6671445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671453 : List Nat := [1, 4, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6671453 : Nat := 118140960795 + 6671453 * 2 ^ 59
def prefixEnd_6671453 : Nat := 4983230072969 + 3 ^ 40 * 6671453 * 2
def baseEnd_6671453 : Nat := 1141887350959997214385351

theorem tailTrace_6671453 : CollatzResearch.WordTrace tailWord_6671453 prefixEnd_6671453 1141887350959997214385351 := by
  unfold tailWord_6671453
  simp only [CollatzResearch.WordTrace]
  refine ⟨243327881099472649305763013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162218587399648432870508675 243327881099472649305763013)
  ·
    refine ⟨45623977706151121744830565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243327881099472649305763013 45623977706151121744830565)
    ·
      refine ⟨8554495819903335327155731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45623977706151121744830565 8554495819903335327155731)
      ·
        refine ⟨12831743729855002990733597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8554495819903335327155731 12831743729855002990733597)
        ·
          refine ⟨4811903898695626121525099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12831743729855002990733597 4811903898695626121525099)
          ·
            refine ⟨7217855848043439182287649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811903898695626121525099 7217855848043439182287649)
            ·
              refine ⟨5413391886032579386715737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7217855848043439182287649 5413391886032579386715737)
              ·
                refine ⟨4060043914524434540036803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5413391886032579386715737 4060043914524434540036803)
                ·
                  refine ⟨6090065871786651810055205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4060043914524434540036803 6090065871786651810055205)
                  ·
                    refine ⟨1141887350959997214385351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6090065871786651810055205 1141887350959997214385351)
                    ·
                      rfl

theorem cell23_6671453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6671453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671453 prefixEnd_6671453 := by exact prefixLift 6671453
  have htrace : WordTrace (prefixWord ++ tailWord_6671453) baseStart_6671453 baseEnd_6671453 := by
    simpa [prefixWord, tailWord_6671453, baseEnd_6671453] using wordTrace_append hprefix tailTrace_6671453
  have hstable : (prefixWord ++ tailWord_6671453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671453).length < 2 ^ (prefixWord ++ tailWord_6671453).sum := by decide
  have hdescent : baseEnd_6671453 < baseStart_6671453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671468 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_6671468 : Nat := 118140960795 + 6671468 * 2 ^ 59
def prefixEnd_6671468 : Nat := 4983230072969 + 3 ^ 40 * 6671468 * 2
def baseEnd_6671468 : Nat := 3425669755089809084468483

theorem tailTrace_6671468 : CollatzResearch.WordTrace tailWord_6671468 prefixEnd_6671468 3425669755089809084468483 := by
  unfold tailWord_6671468
  simp only [CollatzResearch.WordTrace]
  refine ⟨121664214097209153433779529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162218952129612204578372705 121664214097209153433779529)
  ·
    refine ⟨91248160572906865075334647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121664214097209153433779529 91248160572906865075334647)
    ·
      refine ⟨136872240859360297613001971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91248160572906865075334647 136872240859360297613001971)
      ·
        refine ⟨205308361289040446419502957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136872240859360297613001971 205308361289040446419502957)
        ·
          refine ⟨76990635483390167407313609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205308361289040446419502957 76990635483390167407313609)
          ·
            refine ⟨57742976612542625555485207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76990635483390167407313609 57742976612542625555485207)
            ·
              refine ⟨86614464918813938333227811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57742976612542625555485207 86614464918813938333227811)
              ·
                refine ⟨129921697378220907499841717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86614464918813938333227811 129921697378220907499841717)
                ·
                  refine ⟨12180159129208210078110161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129921697378220907499841717 12180159129208210078110161)
                  ·
                    refine ⟨9135119346906157558582621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12180159129208210078110161 9135119346906157558582621)
                    ·
                      refine ⟨3425669755089809084468483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135119346906157558582621 3425669755089809084468483)
                      ·
                        rfl

theorem cell23_6671468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_6671468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671468 prefixEnd_6671468 := by exact prefixLift 6671468
  have htrace : WordTrace (prefixWord ++ tailWord_6671468) baseStart_6671468 baseEnd_6671468 := by
    simpa [prefixWord, tailWord_6671468, baseEnd_6671468] using wordTrace_append hprefix tailTrace_6671468
  have hstable : (prefixWord ++ tailWord_6671468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671468).length < 2 ^ (prefixWord ++ tailWord_6671468).sum := by decide
  have hdescent : baseEnd_6671468 < baseStart_6671468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671485 : List Nat := [1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_6671485 : Nat := 118140960795 + 6671485 * 2 ^ 59
def prefixEnd_6671485 : Nat := 4983230072969 + 3 ^ 40 * 6671485 * 2
def baseEnd_6671485 : Nat := 3425678484260935517955905

theorem tailTrace_6671485 : CollatzResearch.WordTrace tailWord_6671485 prefixEnd_6671485 3425678484260935517955905 := by
  unfold tailWord_6671485
  simp only [CollatzResearch.WordTrace]
  refine ⟨243329048235356718770927909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162219365490237812513951939 243329048235356718770927909)
  ·
    refine ⟨45624196544129384769548983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243329048235356718770927909 45624196544129384769548983)
    ·
      refine ⟨68436294816194077154323475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45624196544129384769548983 68436294816194077154323475)
      ·
        refine ⟨102654442224291115731485213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68436294816194077154323475 102654442224291115731485213)
        ·
          refine ⟨38495415834109168399306955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102654442224291115731485213 38495415834109168399306955)
          ·
            refine ⟨57743123751163752598960433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38495415834109168399306955 57743123751163752598960433)
            ·
              refine ⟨43307342813372814449220325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57743123751163752598960433 43307342813372814449220325)
              ·
                refine ⟨8120126777507402709228811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43307342813372814449220325 8120126777507402709228811)
                ·
                  refine ⟨12180190166261104063843217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120126777507402709228811 12180190166261104063843217)
                  ·
                    refine ⟨9135142624695828047882413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12180190166261104063843217 9135142624695828047882413)
                    ·
                      refine ⟨3425678484260935517955905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135142624695828047882413 3425678484260935517955905)
                      ·
                        rfl

theorem cell23_6671485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_6671485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671485 prefixEnd_6671485 := by exact prefixLift 6671485
  have htrace : WordTrace (prefixWord ++ tailWord_6671485) baseStart_6671485 baseEnd_6671485 := by
    simpa [prefixWord, tailWord_6671485, baseEnd_6671485] using wordTrace_append hprefix tailTrace_6671485
  have hstable : (prefixWord ++ tailWord_6671485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671485).length < 2 ^ (prefixWord ++ tailWord_6671485).sum := by decide
  have hdescent : baseEnd_6671485 < baseStart_6671485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671486 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6671486 : Nat := 118140960795 + 6671486 * 2 ^ 59
def prefixEnd_6671486 : Nat := 4983230072969 + 3 ^ 40 * 6671486 * 2
def baseEnd_6671486 : Nat := 3425678997741590014043401

theorem tailTrace_6671486 : CollatzResearch.WordTrace tailWord_6671486 prefixEnd_6671486 3425678997741590014043401 := by
  unfold tailWord_6671486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30416135588544136992714289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162219389805568730627809541 30416135588544136992714289)
  ·
    refine ⟨22812101691408102744535717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30416135588544136992714289 22812101691408102744535717)
    ·
      refine ⟨4277269067139019264600447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22812101691408102744535717 4277269067139019264600447)
      ·
        refine ⟨6415903600708528896900671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4277269067139019264600447 6415903600708528896900671)
        ·
          refine ⟨9623855401062793345351007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415903600708528896900671 9623855401062793345351007)
          ·
            refine ⟨14435783101594190018026511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623855401062793345351007 14435783101594190018026511)
            ·
              refine ⟨21653674652391285027039767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435783101594190018026511 21653674652391285027039767)
              ·
                refine ⟨32480511978586927540559651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21653674652391285027039767 32480511978586927540559651)
                ·
                  refine ⟨48720767967880391310839477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32480511978586927540559651 48720767967880391310839477)
                  ·
                    refine ⟨4567571996988786685391201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48720767967880391310839477 4567571996988786685391201)
                    ·
                      refine ⟨3425678997741590014043401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567571996988786685391201 3425678997741590014043401)
                      ·
                        rfl

theorem cell23_6671486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6671486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671486 prefixEnd_6671486 := by exact prefixLift 6671486
  have htrace : WordTrace (prefixWord ++ tailWord_6671486) baseStart_6671486 baseEnd_6671486 := by
    simpa [prefixWord, tailWord_6671486, baseEnd_6671486] using wordTrace_append hprefix tailTrace_6671486
  have hstable : (prefixWord ++ tailWord_6671486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671486).length < 2 ^ (prefixWord ++ tailWord_6671486).sum := by decide
  have hdescent : baseEnd_6671486 < baseStart_6671486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671502 : List Nat := [4, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6671502 : Nat := 118140960795 + 6671502 * 2 ^ 59
def prefixEnd_6671502 : Nat := 4983230072969 + 3 ^ 40 * 6671502 * 2
def baseEnd_6671502 : Nat := 3425687213432061951443327

theorem tailTrace_6671502 : CollatzResearch.WordTrace tailWord_6671502 prefixEnd_6671502 3425687213432061951443327 := by
  unfold tailWord_6671502
  simp only [CollatzResearch.WordTrace]
  refine ⟨30416208534536891334287095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162219778850863420449531173 30416208534536891334287095)
  ·
    refine ⟨45624312801805337001430643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30416208534536891334287095 45624312801805337001430643)
    ·
      refine ⟨68436469202708005502145965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45624312801805337001430643 68436469202708005502145965)
      ·
        refine ⟨25663675951015502063304737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68436469202708005502145965 25663675951015502063304737)
        ·
          refine ⟨19247756963261626547478553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25663675951015502063304737 19247756963261626547478553)
          ·
            refine ⟨14435817722446219910608915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19247756963261626547478553 14435817722446219910608915)
            ·
              refine ⟨21653726583669329865913373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14435817722446219910608915 21653726583669329865913373)
              ·
                refine ⟨8120147468875998699717515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21653726583669329865913373 8120147468875998699717515)
                ·
                  refine ⟨12180221203313998049576273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120147468875998699717515 12180221203313998049576273)
                  ·
                    refine ⟨9135165902485498537182205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12180221203313998049576273 9135165902485498537182205)
                    ·
                      refine ⟨3425687213432061951443327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135165902485498537182205 3425687213432061951443327)
                      ·
                        rfl

theorem cell23_6671502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6671502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671502 prefixEnd_6671502 := by exact prefixLift 6671502
  have htrace : WordTrace (prefixWord ++ tailWord_6671502) baseStart_6671502 baseEnd_6671502 := by
    simpa [prefixWord, tailWord_6671502, baseEnd_6671502] using wordTrace_append hprefix tailTrace_6671502
  have hstable : (prefixWord ++ tailWord_6671502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671502).length < 2 ^ (prefixWord ++ tailWord_6671502).sum := by decide
  have hdescent : baseEnd_6671502 < baseStart_6671502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671755 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5]
def baseStart_6671755 : Nat := 118140960795 + 6671755 * 2 ^ 59
def prefixEnd_6671755 : Nat := 4983230072969 + 3 ^ 40 * 6671755 * 2
def baseEnd_6671755 : Nat := 3425817124037649461579663

theorem tailTrace_6671755 : CollatzResearch.WordTrace tailWord_6671755 prefixEnd_6671755 3425817124037649461579663 := by
  unfold tailWord_6671755
  simp only [CollatzResearch.WordTrace]
  refine ⟨243338895944378554883256719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162225930629585703255504479 243338895944378554883256719)
  ·
    refine ⟨365008343916567832324885079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243338895944378554883256719 365008343916567832324885079)
    ·
      refine ⟨547512515874851748487327619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365008343916567832324885079 547512515874851748487327619)
      ·
        refine ⟨821268773812277622730991429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547512515874851748487327619 821268773812277622730991429)
        ·
          refine ⟨153987895089802054262060893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 821268773812277622730991429 153987895089802054262060893)
          ·
            refine ⟨57745460658675770348272835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153987895089802054262060893 57745460658675770348272835)
            ·
              refine ⟨86618190988013655522409253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57745460658675770348272835 86618190988013655522409253)
              ·
                refine ⟨16240910810252560410451735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86618190988013655522409253 16240910810252560410451735)
                ·
                  refine ⟨24361366215378840615677603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16240910810252560410451735 24361366215378840615677603)
                  ·
                    refine ⟨36542049323068260923516405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24361366215378840615677603 36542049323068260923516405)
                    ·
                      refine ⟨3425817124037649461579663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36542049323068260923516405 3425817124037649461579663)
                      ·
                        rfl

theorem cell23_6671755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].length) (baseStart_6671755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671755 prefixEnd_6671755 := by exact prefixLift 6671755
  have htrace : WordTrace (prefixWord ++ tailWord_6671755) baseStart_6671755 baseEnd_6671755 := by
    simpa [prefixWord, tailWord_6671755, baseEnd_6671755] using wordTrace_append hprefix tailTrace_6671755
  have hstable : (prefixWord ++ tailWord_6671755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671755).length < 2 ^ (prefixWord ++ tailWord_6671755).sum := by decide
  have hdescent : baseEnd_6671755 < baseStart_6671755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671765 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_6671765 : Nat := 118140960795 + 6671765 * 2 ^ 59
def prefixEnd_6671765 : Nat := 4983230072969 + 3 ^ 40 * 6671765 * 2
def baseEnd_6671765 : Nat := 3425822258844194422454617

theorem tailTrace_6671765 : CollatzResearch.WordTrace tailWord_6671765 prefixEnd_6671765 3425822258844194422454617 := by
  unfold tailWord_6671765
  simp only [CollatzResearch.WordTrace]
  refine ⟨243339260674342326591120749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162226173782894884394080499 243339260674342326591120749)
  ·
    refine ⟨91252222752878372471670281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243339260674342326591120749 91252222752878372471670281)
    ·
      refine ⟨68439167064658779353752711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91252222752878372471670281 68439167064658779353752711)
      ·
        refine ⟨102658750596988169030629067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68439167064658779353752711 102658750596988169030629067)
        ·
          refine ⟨153988125895482253545943601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102658750596988169030629067 153988125895482253545943601)
          ·
            refine ⟨115491094421611690159457701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153988125895482253545943601 115491094421611690159457701)
            ·
              refine ⟨21654580204052191904898319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115491094421611690159457701 21654580204052191904898319)
              ·
                refine ⟨32481870306078287857347479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21654580204052191904898319 32481870306078287857347479)
                ·
                  refine ⟨48722805459117431786021219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32481870306078287857347479 48722805459117431786021219)
                  ·
                    refine ⟨73084208188676147679031829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48722805459117431786021219 73084208188676147679031829)
                    ·
                      refine ⟨3425822258844194422454617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73084208188676147679031829 3425822258844194422454617)
                      ·
                        rfl

theorem cell23_6671765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_6671765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671765 prefixEnd_6671765 := by exact prefixLift 6671765
  have htrace : WordTrace (prefixWord ++ tailWord_6671765) baseStart_6671765 baseEnd_6671765 := by
    simpa [prefixWord, tailWord_6671765, baseEnd_6671765] using wordTrace_append hprefix tailTrace_6671765
  have hstable : (prefixWord ++ tailWord_6671765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671765).length < 2 ^ (prefixWord ++ tailWord_6671765).sum := by decide
  have hdescent : baseEnd_6671765 < baseStart_6671765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671769 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 4]
def baseStart_6671769 : Nat := 118140960795 + 6671769 * 2 ^ 59
def prefixEnd_6671769 : Nat := 4983230072969 + 3 ^ 40 * 6671769 * 2
def baseEnd_6671769 : Nat := 3425824312766812406804599

theorem tailTrace_6671769 : CollatzResearch.WordTrace tailWord_6671769 prefixEnd_6671769 3425824312766812406804599 := by
  unfold tailWord_6671769
  simp only [CollatzResearch.WordTrace]
  refine ⟨243339406566327835274266361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162226271044218556849510907 243339406566327835274266361)
  ·
    refine ⟨182504554924745876455699771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243339406566327835274266361 182504554924745876455699771)
    ·
      refine ⟨273756832387118814683549657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182504554924745876455699771 273756832387118814683549657)
      ·
        refine ⟨205317624290339111012662243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273756832387118814683549657 205317624290339111012662243)
        ·
          refine ⟨307976436435508666518993365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205317624290339111012662243 307976436435508666518993365)
          ·
            refine ⟨7218197728957234371538907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 307976436435508666518993365 7218197728957234371538907)
            ·
              refine ⟨10827296593435851557308361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218197728957234371538907 10827296593435851557308361)
              ·
                refine ⟨8120472445076888667981271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10827296593435851557308361 8120472445076888667981271)
                ·
                  refine ⟨12180708667615333001971907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120472445076888667981271 12180708667615333001971907)
                  ·
                    refine ⟨18271063001422999502957861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12180708667615333001971907 18271063001422999502957861)
                    ·
                      refine ⟨3425824312766812406804599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18271063001422999502957861 3425824312766812406804599)
                      ·
                        rfl

theorem cell23_6671769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_6671769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671769 prefixEnd_6671769 := by exact prefixLift 6671769
  have htrace : WordTrace (prefixWord ++ tailWord_6671769) baseStart_6671769 baseEnd_6671769 := by
    simpa [prefixWord, tailWord_6671769, baseEnd_6671769] using wordTrace_append hprefix tailTrace_6671769
  have hstable : (prefixWord ++ tailWord_6671769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671769).length < 2 ^ (prefixWord ++ tailWord_6671769).sum := by decide
  have hdescent : baseEnd_6671769 < baseStart_6671769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671775 : List Nat := [1, 1, 2, 5, 1, 2, 2, 9]
def baseStart_6671775 : Nat := 118140960795 + 6671775 * 2 ^ 59
def prefixEnd_6671775 : Nat := 4983230072969 + 3 ^ 40 * 6671775 * 2
def baseEnd_6671775 : Nat := 126882496061138495678873

theorem tailTrace_6671775 : CollatzResearch.WordTrace tailWord_6671775 prefixEnd_6671775 126882496061138495678873 := by
  unfold tailWord_6671775
  simp only [CollatzResearch.WordTrace]
  refine ⟨243339625404306098298984779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162226416936204065532656519 243339625404306098298984779)
  ·
    refine ⟨365009438106459147448477169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243339625404306098298984779 365009438106459147448477169)
    ·
      refine ⟨273757078579844360586357877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365009438106459147448477169 273757078579844360586357877)
      ·
        refine ⟨25664726116860408804971051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273757078579844360586357877 25664726116860408804971051)
        ·
          refine ⟨38497089175290613207456577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25664726116860408804971051 38497089175290613207456577)
          ·
            refine ⟨28872816881467959905592433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38497089175290613207456577 28872816881467959905592433)
            ·
              refine ⟨21654612661100969929194325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28872816881467959905592433 21654612661100969929194325)
              ·
                refine ⟨126882496061138495678873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21654612661100969929194325 126882496061138495678873)
                ·
                  rfl

theorem cell23_6671775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 9].length) (baseStart_6671775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671775 prefixEnd_6671775 := by exact prefixLift 6671775
  have htrace : WordTrace (prefixWord ++ tailWord_6671775) baseStart_6671775 baseEnd_6671775 := by
    simpa [prefixWord, tailWord_6671775, baseEnd_6671775] using wordTrace_append hprefix tailTrace_6671775
  have hstable : (prefixWord ++ tailWord_6671775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671775).length < 2 ^ (prefixWord ++ tailWord_6671775).sum := by decide
  have hdescent : baseEnd_6671775 < baseStart_6671775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671789 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6671789 : Nat := 118140960795 + 6671789 * 2 ^ 59
def prefixEnd_6671789 : Nat := 4983230072969 + 3 ^ 40 * 6671789 * 2
def baseEnd_6671789 : Nat := 3425834582379902328554507

theorem tailTrace_6671789 : CollatzResearch.WordTrace tailWord_6671789 prefixEnd_6671789 3425834582379902328554507 := by
  unfold tailWord_6671789
  simp only [CollatzResearch.WordTrace]
  refine ⟨243340136026255378689994421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162226757350836919126662947 243340136026255378689994421)
  ·
    refine ⟨22813137752461441752186977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243340136026255378689994421 22813137752461441752186977)
    ·
      refine ⟨17109853314346081314140233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22813137752461441752186977 17109853314346081314140233)
      ·
        refine ⟨12832389985759560985605175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17109853314346081314140233 12832389985759560985605175)
        ·
          refine ⟨19248584978639341478407763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832389985759560985605175 19248584978639341478407763)
          ·
            refine ⟨28872877467959012217611645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19248584978639341478407763 28872877467959012217611645)
            ·
              refine ⟨10827329050484629581604367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28872877467959012217611645 10827329050484629581604367)
              ·
                refine ⟨16240993575726944372406551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10827329050484629581604367 16240993575726944372406551)
                ·
                  refine ⟨24361490363590416558609827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16240993575726944372406551 24361490363590416558609827)
                  ·
                    refine ⟨36542235545385624837914741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24361490363590416558609827 36542235545385624837914741)
                    ·
                      refine ⟨3425834582379902328554507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36542235545385624837914741 3425834582379902328554507)
                      ·
                        rfl

theorem cell23_6671789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6671789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671789 prefixEnd_6671789 := by exact prefixLift 6671789
  have htrace : WordTrace (prefixWord ++ tailWord_6671789) baseStart_6671789 baseEnd_6671789 := by
    simpa [prefixWord, tailWord_6671789, baseEnd_6671789] using wordTrace_append hprefix tailTrace_6671789
  have hstable : (prefixWord ++ tailWord_6671789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671789).length < 2 ^ (prefixWord ++ tailWord_6671789).sum := by decide
  have hdescent : baseEnd_6671789 < baseStart_6671789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671805 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_6671805 : Nat := 118140960795 + 6671805 * 2 ^ 59
def prefixEnd_6671805 : Nat := 4983230072969 + 3 ^ 40 * 6671805 * 2
def baseEnd_6671805 : Nat := 1141947599356791421984811

theorem tailTrace_6671805 : CollatzResearch.WordTrace tailWord_6671805 prefixEnd_6671805 1141947599356791421984811 := by
  unfold tailWord_6671805
  simp only [CollatzResearch.WordTrace]
  refine ⟨243340719594197413422576869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162227146396131608948384579 243340719594197413422576869)
  ·
    refine ⟨45626384923912015016733163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243340719594197413422576869 45626384923912015016733163)
    ·
      refine ⟨68439577385868022525099745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45626384923912015016733163 68439577385868022525099745)
      ·
        refine ⟨51329683039401016893824809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68439577385868022525099745 51329683039401016893824809)
        ·
          refine ⟨38497262279550762670368607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51329683039401016893824809 38497262279550762670368607)
          ·
            refine ⟨57745893419326144005552911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38497262279550762670368607 57745893419326144005552911)
            ·
              refine ⟨86618840128989216008329367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57745893419326144005552911 86618840128989216008329367)
              ·
                refine ⟨129928260193483824012494051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86618840128989216008329367 129928260193483824012494051)
                ·
                  refine ⟨194892390290225736018741077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129928260193483824012494051 194892390290225736018741077)
                  ·
                    refine ⟨1141947599356791421984811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194892390290225736018741077 1141947599356791421984811)
                    ·
                      rfl

theorem cell23_6671805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_6671805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671805 prefixEnd_6671805 := by exact prefixLift 6671805
  have htrace : WordTrace (prefixWord ++ tailWord_6671805) baseStart_6671805 baseEnd_6671805 := by
    simpa [prefixWord, tailWord_6671805, baseEnd_6671805] using wordTrace_append hprefix tailTrace_6671805
  have hstable : (prefixWord ++ tailWord_6671805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671805).length < 2 ^ (prefixWord ++ tailWord_6671805).sum := by decide
  have hdescent : baseEnd_6671805 < baseStart_6671805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671819 : List Nat := [1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 3]
def baseStart_6671819 : Nat := 118140960795 + 6671819 * 2 ^ 59
def prefixEnd_6671819 : Nat := 4983230072969 + 3 ^ 40 * 6671819 * 2
def baseEnd_6671819 : Nat := 3425849986799537211179369

theorem tailTrace_6671819 : CollatzResearch.WordTrace tailWord_6671819 prefixEnd_6671819 3425849986799537211179369 := by
  unfold tailWord_6671819
  simp only [CollatzResearch.WordTrace]
  refine ⟨243341230216146693813586511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162227486810764462542391007 243341230216146693813586511)
  ·
    refine ⟨365011845324220040720379767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243341230216146693813586511 365011845324220040720379767)
    ·
      refine ⟨547517767986330061080569651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365011845324220040720379767 547517767986330061080569651)
      ·
        refine ⟨821276651979495091620854477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547517767986330061080569651 821276651979495091620854477)
        ·
          refine ⟨307978744492310659357820429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 821276651979495091620854477 307978744492310659357820429)
          ·
            refine ⟨115492029184616497259182661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307978744492310659357820429 115492029184616497259182661)
            ·
              refine ⟨21654755472115593236096749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115492029184616497259182661 21654755472115593236096749)
              ·
                refine ⟨8120533302043347463536281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21654755472115593236096749 8120533302043347463536281)
                ·
                  refine ⟨6090399976532510597652211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8120533302043347463536281 6090399976532510597652211)
                  ·
                    refine ⟨9135599964798765896478317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6090399976532510597652211 9135599964798765896478317)
                    ·
                      refine ⟨3425849986799537211179369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135599964798765896478317 3425849986799537211179369)
                      ·
                        rfl

theorem cell23_6671819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 3].length) (baseStart_6671819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671819 prefixEnd_6671819 := by exact prefixLift 6671819
  have htrace : WordTrace (prefixWord ++ tailWord_6671819) baseStart_6671819 baseEnd_6671819 := by
    simpa [prefixWord, tailWord_6671819, baseEnd_6671819] using wordTrace_append hprefix tailTrace_6671819
  have hstable : (prefixWord ++ tailWord_6671819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671819).length < 2 ^ (prefixWord ++ tailWord_6671819).sum := by decide
  have hdescent : baseEnd_6671819 < baseStart_6671819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671829 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6671829 : Nat := 118140960795 + 6671829 * 2 ^ 59
def prefixEnd_6671829 : Nat := 4983230072969 + 3 ^ 40 * 6671829 * 2
def baseEnd_6671829 : Nat := 3425855121606082172054323

theorem tailTrace_6671829 : CollatzResearch.WordTrace tailWord_6671829 prefixEnd_6671829 3425855121606082172054323 := by
  unfold tailWord_6671829
  simp only [CollatzResearch.WordTrace]
  refine ⟨243341594946110465521450541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162227729964073643680967027 243341594946110465521450541)
  ·
    refine ⟨91253098104791424570543953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243341594946110465521450541 91253098104791424570543953)
    ·
      refine ⟨68439823578593568427907965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91253098104791424570543953 68439823578593568427907965)
      ·
        refine ⟨25664933841972588160465487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68439823578593568427907965 25664933841972588160465487)
        ·
          refine ⟨38497400762958882240698231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25664933841972588160465487 38497400762958882240698231)
          ·
            refine ⟨57746101144438323361047347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38497400762958882240698231 57746101144438323361047347)
            ·
              refine ⟨86619151716657485041571021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57746101144438323361047347 86619151716657485041571021)
              ·
                refine ⟨32482181893746556890589133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86619151716657485041571021 32482181893746556890589133)
                ·
                  refine ⟨12180818210154958833970925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32482181893746556890589133 12180818210154958833970925)
                  ·
                    refine ⟨4567806828808109562739097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12180818210154958833970925 4567806828808109562739097)
                    ·
                      refine ⟨3425855121606082172054323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567806828808109562739097 3425855121606082172054323)
                      ·
                        rfl

theorem cell23_6671829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6671829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671829 prefixEnd_6671829 := by exact prefixLift 6671829
  have htrace : WordTrace (prefixWord ++ tailWord_6671829) baseStart_6671829 baseEnd_6671829 := by
    simpa [prefixWord, tailWord_6671829, baseEnd_6671829] using wordTrace_append hprefix tailTrace_6671829
  have hstable : (prefixWord ++ tailWord_6671829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671829).length < 2 ^ (prefixWord ++ tailWord_6671829).sum := by decide
  have hdescent : baseEnd_6671829 < baseStart_6671829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671870 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6671870 : Nat := 118140960795 + 6671870 * 2 ^ 59
def prefixEnd_6671870 : Nat := 4983230072969 + 3 ^ 40 * 6671870 * 2
def baseEnd_6671870 : Nat := 3425876174312916511641635

theorem tailTrace_6671870 : CollatzResearch.WordTrace tailWord_6671870 prefixEnd_6671870 3425876174312916511641635 := by
  unfold tailWord_6671870
  simp only [CollatzResearch.WordTrace]
  refine ⟨30417886292370241190461633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162228726892641286349128709 30417886292370241190461633)
  ·
    refine ⟨22813414719277680892846225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30417886292370241190461633 22813414719277680892846225)
    ·
      refine ⟨17110061039458260669634669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22813414719277680892846225 17110061039458260669634669)
      ·
        refine ⟨6416272889796847751113001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17110061039458260669634669 6416272889796847751113001)
        ·
          refine ⟨4812204667347635813334751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6416272889796847751113001 4812204667347635813334751)
          ·
            refine ⟨7218307001021453720002127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812204667347635813334751 7218307001021453720002127)
            ·
              refine ⟨10827460501532180580003191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218307001021453720002127 10827460501532180580003191)
              ·
                refine ⟨16241190752298270870004787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10827460501532180580003191 16241190752298270870004787)
                ·
                  refine ⟨24361786128447406305007181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16241190752298270870004787 24361786128447406305007181)
                  ·
                    refine ⟨9135669798167777364377693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24361786128447406305007181 9135669798167777364377693)
                    ·
                      refine ⟨3425876174312916511641635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135669798167777364377693 3425876174312916511641635)
                      ·
                        rfl

theorem cell23_6671870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6671870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671870 prefixEnd_6671870 := by exact prefixLift 6671870
  have htrace : WordTrace (prefixWord ++ tailWord_6671870) baseStart_6671870 baseEnd_6671870 := by
    simpa [prefixWord, tailWord_6671870, baseEnd_6671870] using wordTrace_append hprefix tailTrace_6671870
  have hstable : (prefixWord ++ tailWord_6671870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671870).length < 2 ^ (prefixWord ++ tailWord_6671870).sum := by decide
  have hdescent : baseEnd_6671870 < baseStart_6671870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671882 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_6671882 : Nat := 118140960795 + 6671882 * 2 ^ 59
def prefixEnd_6671882 : Nat := 4983230072969 + 3 ^ 40 * 6671882 * 2
def baseEnd_6671882 : Nat := 380653592897863384965731

theorem tailTrace_6671882 : CollatzResearch.WordTrace tailWord_6671882 prefixEnd_6671882 380653592897863384965731 := by
  unfold tailWord_6671882
  simp only [CollatzResearch.WordTrace]
  refine ⟨60835882003729613893282475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162229018676612303715419933 60835882003729613893282475)
  ·
    refine ⟨91253823005594420839923713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60835882003729613893282475 91253823005594420839923713)
    ·
      refine ⟨68440367254195815629942785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91253823005594420839923713 68440367254195815629942785)
      ·
        refine ⟨51330275440646861722457089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68440367254195815629942785 51330275440646861722457089)
        ·
          refine ⟨38497706580485146291842817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51330275440646861722457089 38497706580485146291842817)
          ·
            refine ⟨28873279935363859718882113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38497706580485146291842817 28873279935363859718882113)
            ·
              refine ⟨21654959951522894789161585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28873279935363859718882113 21654959951522894789161585)
              ·
                refine ⟨16241219963642171091871189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21654959951522894789161585 16241219963642171091871189)
                ·
                  refine ⟨380653592897863384965731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16241219963642171091871189 380653592897863384965731)
                  ·
                    rfl

theorem cell23_6671882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_6671882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671882 prefixEnd_6671882 := by exact prefixLift 6671882
  have htrace : WordTrace (prefixWord ++ tailWord_6671882) baseStart_6671882 baseEnd_6671882 := by
    simpa [prefixWord, tailWord_6671882, baseEnd_6671882] using wordTrace_append hprefix tailTrace_6671882
  have hstable : (prefixWord ++ tailWord_6671882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671882).length < 2 ^ (prefixWord ++ tailWord_6671882).sum := by decide
  have hdescent : baseEnd_6671882 < baseStart_6671882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671915 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_6671915 : Nat := 118140960795 + 6671915 * 2 ^ 59
def prefixEnd_6671915 : Nat := 4983230072969 + 3 ^ 40 * 6671915 * 2
def baseEnd_6671915 : Nat := 3425899280942368835578927

theorem tailTrace_6671915 : CollatzResearch.WordTrace tailWord_6671915 prefixEnd_6671915 3425899280942368835578927 := by
  unfold tailWord_6671915
  simp only [CollatzResearch.WordTrace]
  refine ⟨243344731623798902209081199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162229821082532601472720799 243344731623798902209081199)
  ·
    refine ⟨365017097435698353313621799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243344731623798902209081199 365017097435698353313621799)
    ·
      refine ⟨547525646153547529970432699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365017097435698353313621799 547525646153547529970432699)
      ·
        refine ⟨821288469230321294955649049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547525646153547529970432699 821288469230321294955649049)
        ·
          refine ⟨615966351922740971216736787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821288469230321294955649049 615966351922740971216736787)
          ·
            refine ⟨923949527884111456825105181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615966351922740971216736787 923949527884111456825105181)
            ·
              refine ⟨346481072956541796309414443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 923949527884111456825105181 346481072956541796309414443)
              ·
                refine ⟨519721609434812694464121665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346481072956541796309414443 519721609434812694464121665)
                ·
                  refine ⟨389791207076109520848091249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519721609434812694464121665 389791207076109520848091249)
                  ·
                    refine ⟨292343405307082140636068437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389791207076109520848091249 292343405307082140636068437)
                    ·
                      refine ⟨3425899280942368835578927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 292343405307082140636068437 3425899280942368835578927)
                      ·
                        rfl

theorem cell23_6671915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_6671915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671915 prefixEnd_6671915 := by exact prefixLift 6671915
  have htrace : WordTrace (prefixWord ++ tailWord_6671915) baseStart_6671915 baseEnd_6671915 := by
    simpa [prefixWord, tailWord_6671915, baseEnd_6671915] using wordTrace_append hprefix tailTrace_6671915
  have hstable : (prefixWord ++ tailWord_6671915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671915).length < 2 ^ (prefixWord ++ tailWord_6671915).sum := by decide
  have hdescent : baseEnd_6671915 < baseStart_6671915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6671969 : List Nat := [1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 3]
def baseStart_6671969 : Nat := 118140960795 + 6671969 * 2 ^ 59
def prefixEnd_6671969 : Nat := 4983230072969 + 3 ^ 40 * 6671969 * 2
def baseEnd_6671969 : Nat := 3425927008897711624303679

theorem tailTrace_6671969 : CollatzResearch.WordTrace tailWord_6671969 prefixEnd_6671969 3425927008897711624303679 := by
  unfold tailWord_6671969
  simp only [CollatzResearch.WordTrace]
  refine ⟨243346701165603269431546961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162231134110402179621031307 243346701165603269431546961)
  ·
    refine ⟨182510025874202452073660221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243346701165603269431546961 182510025874202452073660221)
    ·
      refine ⟨68441259702825919527622583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182510025874202452073660221 68441259702825919527622583)
      ·
        refine ⟨102661889554238879291433875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68441259702825919527622583 102661889554238879291433875)
        ·
          refine ⟨153992834331358318937150813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102661889554238879291433875 153992834331358318937150813)
          ·
            refine ⟨57747312874259369601431555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153992834331358318937150813 57747312874259369601431555)
            ·
              refine ⟨86620969311389054402147333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57747312874259369601431555 86620969311389054402147333)
              ·
                refine ⟨16241431745885447700402625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86620969311389054402147333 16241431745885447700402625)
                ·
                  refine ⟨12181073809414085775301969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16241431745885447700402625 12181073809414085775301969)
                  ·
                    refine ⟨9135805357060564331476477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12181073809414085775301969 9135805357060564331476477)
                    ·
                      refine ⟨3425927008897711624303679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135805357060564331476477 3425927008897711624303679)
                      ·
                        rfl

theorem cell23_6671969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_6671969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6671969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6671969 prefixEnd_6671969 := by exact prefixLift 6671969
  have htrace : WordTrace (prefixWord ++ tailWord_6671969) baseStart_6671969 baseEnd_6671969 := by
    simpa [prefixWord, tailWord_6671969, baseEnd_6671969] using wordTrace_append hprefix tailTrace_6671969
  have hstable : (prefixWord ++ tailWord_6671969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6671969).length < 2 ^ (prefixWord ++ tailWord_6671969).sum := by decide
  have hdescent : baseEnd_6671969 < baseStart_6671969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6671969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672033 : List Nat := [1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 3]
def baseStart_6672033 : Nat := 118140960795 + 6672033 * 2 ^ 59
def prefixEnd_6672033 : Nat := 4983230072969 + 3 ^ 40 * 6672033 * 2
def baseEnd_6672033 : Nat := 3425959871659599373903385

theorem tailTrace_6672033 : CollatzResearch.WordTrace tailWord_6672033 prefixEnd_6672033 3425959871659599373903385 := by
  unfold tailWord_6672033
  simp only [CollatzResearch.WordTrace]
  refine ⟨243349035437371408361876753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162232690291580938907917835 243349035437371408361876753)
  ·
    refine ⟨182511776578028556271407565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243349035437371408361876753 182511776578028556271407565)
    ·
      refine ⟨68441916216760708601777837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182511776578028556271407565 68441916216760708601777837)
      ·
        refine ⟨25665718581285265725666689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68441916216760708601777837 25665718581285265725666689)
        ·
          refine ⟨19249288935963949294250017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25665718581285265725666689 19249288935963949294250017)
          ·
            refine ⟨14436966701972961970687513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19249288935963949294250017 14436966701972961970687513)
            ·
              refine ⟨10827725026479721478015635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14436966701972961970687513 10827725026479721478015635)
              ·
                refine ⟨16241587539719582217023453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10827725026479721478015635 16241587539719582217023453)
                ·
                  refine ⟨6090595327394843331383795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16241587539719582217023453 6090595327394843331383795)
                  ·
                    refine ⟨9135892991092264997075693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6090595327394843331383795 9135892991092264997075693)
                    ·
                      refine ⟨3425959871659599373903385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135892991092264997075693 3425959871659599373903385)
                      ·
                        rfl

theorem cell23_6672033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_6672033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672033 prefixEnd_6672033 := by exact prefixLift 6672033
  have htrace : WordTrace (prefixWord ++ tailWord_6672033) baseStart_6672033 baseEnd_6672033 := by
    simpa [prefixWord, tailWord_6672033, baseEnd_6672033] using wordTrace_append hprefix tailTrace_6672033
  have hstable : (prefixWord ++ tailWord_6672033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672033).length < 2 ^ (prefixWord ++ tailWord_6672033).sum := by decide
  have hdescent : baseEnd_6672033 < baseStart_6672033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672053 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_6672053 : Nat := 118140960795 + 6672053 * 2 ^ 59
def prefixEnd_6672053 : Nat := 4983230072969 + 3 ^ 40 * 6672053 * 2
def baseEnd_6672053 : Nat := 1141990047090896431884431

theorem tailTrace_6672053 : CollatzResearch.WordTrace tailWord_6672053 prefixEnd_6672053 1141990047090896431884431 := by
  unfold tailWord_6672053
  simp only [CollatzResearch.WordTrace]
  refine ⟨243349764897298951777604813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162233176598199301185069875 243349764897298951777604813)
  ·
    refine ⟨91256161836487106916601805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243349764897298951777604813 91256161836487106916601805)
    ·
      refine ⟨34221060688682665093725677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91256161836487106916601805 34221060688682665093725677)
      ·
        refine ⟨12832897758255999410147129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34221060688682665093725677 12832897758255999410147129)
        ·
          refine ⟨9624673318691999557610347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12832897758255999410147129 9624673318691999557610347)
          ·
            refine ⟨14437009978037999336415521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624673318691999557610347 14437009978037999336415521)
            ·
              refine ⟨10827757483528499502311641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14437009978037999336415521 10827757483528499502311641)
              ·
                refine ⟨8120818112646374626733731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10827757483528499502311641 8120818112646374626733731)
                ·
                  refine ⟨12181227168969561940100597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120818112646374626733731 12181227168969561940100597)
                  ·
                    refine ⟨1141990047090896431884431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12181227168969561940100597 1141990047090896431884431)
                    ·
                      rfl

theorem cell23_6672053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_6672053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672053 prefixEnd_6672053 := by exact prefixLift 6672053
  have htrace : WordTrace (prefixWord ++ tailWord_6672053) baseStart_6672053 baseEnd_6672053 := by
    simpa [prefixWord, tailWord_6672053, baseEnd_6672053] using wordTrace_append hprefix tailTrace_6672053
  have hstable : (prefixWord ++ tailWord_6672053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672053).length < 2 ^ (prefixWord ++ tailWord_6672053).sum := by decide
  have hdescent : baseEnd_6672053 < baseStart_6672053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672059 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 3]
def baseStart_6672059 : Nat := 118140960795 + 6672059 * 2 ^ 59
def prefixEnd_6672059 : Nat := 4983230072969 + 3 ^ 40 * 6672059 * 2
def baseEnd_6672059 : Nat := 3425973222156616272178265

theorem tailTrace_6672059 : CollatzResearch.WordTrace tailWord_6672059 prefixEnd_6672059 3425973222156616272178265 := by
  unfold tailWord_6672059
  simp only [CollatzResearch.WordTrace]
  refine ⟨243349983735277214802323231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162233322490184809868215487 243349983735277214802323231)
  ·
    refine ⟨365024975602915822203484847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243349983735277214802323231 365024975602915822203484847)
    ·
      refine ⟨547537463404373733305227271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365024975602915822203484847 547537463404373733305227271)
      ·
        refine ⟨821306195106560599957840907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547537463404373733305227271 821306195106560599957840907)
        ·
          refine ⟨1231959292659840899936761361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821306195106560599957840907 1231959292659840899936761361)
          ·
            refine ⟨923969469494880674952571021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231959292659840899936761361 923969469494880674952571021)
            ·
              refine ⟨346488551060580253107214133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 923969469494880674952571021 346488551060580253107214133)
              ·
                refine ⟨32483301661929398728801325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346488551060580253107214133 32483301661929398728801325)
                ·
                  refine ⟨12181238123223524523300497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32483301661929398728801325 12181238123223524523300497)
                  ·
                    refine ⟨9135928592417643392475373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12181238123223524523300497 9135928592417643392475373)
                    ·
                      refine ⟨3425973222156616272178265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9135928592417643392475373 3425973222156616272178265)
                      ·
                        rfl

theorem cell23_6672059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 3].length) (baseStart_6672059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672059 prefixEnd_6672059 := by exact prefixLift 6672059
  have htrace : WordTrace (prefixWord ++ tailWord_6672059) baseStart_6672059 baseEnd_6672059 := by
    simpa [prefixWord, tailWord_6672059, baseEnd_6672059] using wordTrace_append hprefix tailTrace_6672059
  have hstable : (prefixWord ++ tailWord_6672059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672059).length < 2 ^ (prefixWord ++ tailWord_6672059).sum := by decide
  have hdescent : baseEnd_6672059 < baseStart_6672059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672070 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6672070 : Nat := 118140960795 + 6672070 * 2 ^ 59
def prefixEnd_6672070 : Nat := 4983230072969 + 3 ^ 40 * 6672070 * 2
def baseEnd_6672070 : Nat := 1141992956814605243046905

theorem tailTrace_6672070 : CollatzResearch.WordTrace tailWord_6672070 prefixEnd_6672070 1141992956814605243046905 := by
  unfold tailWord_6672070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604699529319917615030427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162233589958824909120649109 7604699529319917615030427)
  ·
    refine ⟨11407049293979876422545641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7604699529319917615030427 11407049293979876422545641)
    ·
      refine ⟨8555286970484907316909231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11407049293979876422545641 8555286970484907316909231)
      ·
        refine ⟨12832930455727360975363847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555286970484907316909231 12832930455727360975363847)
        ·
          refine ⟨19249395683591041463045771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832930455727360975363847 19249395683591041463045771)
          ·
            refine ⟨28874093525386562194568657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19249395683591041463045771 28874093525386562194568657)
            ·
              refine ⟨21655570144039921645926493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28874093525386562194568657 21655570144039921645926493)
              ·
                refine ⟨8120838804014970617222435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21655570144039921645926493 8120838804014970617222435)
                ·
                  refine ⟨12181258206022455925833653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8120838804014970617222435 12181258206022455925833653)
                  ·
                    refine ⟨1141992956814605243046905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12181258206022455925833653 1141992956814605243046905)
                    ·
                      rfl

theorem cell23_6672070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6672070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672070 prefixEnd_6672070 := by exact prefixLift 6672070
  have htrace : WordTrace (prefixWord ++ tailWord_6672070) baseStart_6672070 baseEnd_6672070 := by
    simpa [prefixWord, tailWord_6672070, baseEnd_6672070] using wordTrace_append hprefix tailTrace_6672070
  have hstable : (prefixWord ++ tailWord_6672070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672070).length < 2 ^ (prefixWord ++ tailWord_6672070).sum := by decide
  have hdescent : baseEnd_6672070 < baseStart_6672070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672090 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2]
def baseStart_6672090 : Nat := 118140960795 + 6672090 * 2 ^ 59
def prefixEnd_6672090 : Nat := 4983230072969 + 3 ^ 40 * 6672090 * 2
def baseEnd_6672090 : Nat := 3425989140056905650890623

theorem tailTrace_6672090 : CollatzResearch.WordTrace tailWord_6672090 prefixEnd_6672090 3425989140056905650890623 := by
  unfold tailWord_6672090
  simp only [CollatzResearch.WordTrace]
  refine ⟨60837778599541226774175431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162234076265443271397801149 60837778599541226774175431)
  ·
    refine ⟨91256667899311840161263147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60837778599541226774175431 91256667899311840161263147)
    ·
      refine ⟨136885001848967760241894721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91256667899311840161263147 136885001848967760241894721)
      ·
        refine ⟨102663751386725820181421041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136885001848967760241894721 102663751386725820181421041)
        ·
          refine ⟨76997813540044365136065781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102663751386725820181421041 76997813540044365136065781)
          ·
            refine ⟨7218545019379159231506167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76997813540044365136065781 7218545019379159231506167)
            ·
              refine ⟨10827817529068738847259251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7218545019379159231506167 10827817529068738847259251)
              ·
                refine ⟨16241726293603108270888877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10827817529068738847259251 16241726293603108270888877)
                ·
                  refine ⟨6090647360101165601583329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16241726293603108270888877 6090647360101165601583329)
                  ·
                    refine ⟨4567985520075874201187497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6090647360101165601583329 4567985520075874201187497)
                    ·
                      refine ⟨3425989140056905650890623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4567985520075874201187497 3425989140056905650890623)
                      ·
                        rfl

theorem cell23_6672090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_6672090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672090 prefixEnd_6672090 := by exact prefixLift 6672090
  have htrace : WordTrace (prefixWord ++ tailWord_6672090) baseStart_6672090 baseEnd_6672090 := by
    simpa [prefixWord, tailWord_6672090, baseEnd_6672090] using wordTrace_append hprefix tailTrace_6672090
  have hstable : (prefixWord ++ tailWord_6672090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672090).length < 2 ^ (prefixWord ++ tailWord_6672090).sum := by decide
  have hdescent : baseEnd_6672090 < baseStart_6672090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672180 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_6672180 : Nat := 118140960795 + 6672180 * 2 ^ 59
def prefixEnd_6672180 : Nat := 4983230072969 + 3 ^ 40 * 6672180 * 2
def baseEnd_6672180 : Nat := 3426035353315810298765209

theorem tailTrace_6672180 : CollatzResearch.WordTrace tailWord_6672180 prefixEnd_6672180 3426035353315810298765209 := by
  unfold tailWord_6672180
  simp only [CollatzResearch.WordTrace]
  refine ⟨121677198483919426233738997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162236264645225901644985329 121677198483919426233738997)
  ·
    refine ⟨11407237357867446209413031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121677198483919426233738997 11407237357867446209413031)
    ·
      refine ⟨17110856036801169314119547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11407237357867446209413031 17110856036801169314119547)
      ·
        refine ⟨25666284055201753971179321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17110856036801169314119547 25666284055201753971179321)
        ·
          refine ⟨19249713041401315478384491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25666284055201753971179321 19249713041401315478384491)
          ·
            refine ⟨28874569562101973217576737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19249713041401315478384491 28874569562101973217576737)
            ·
              refine ⟨21655927171576479913182553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28874569562101973217576737 21655927171576479913182553)
              ·
                refine ⟨16241945378682359934886915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21655927171576479913182553 16241945378682359934886915)
                ·
                  refine ⟨24362918068023539902330373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16241945378682359934886915 24362918068023539902330373)
                  ·
                    refine ⟨4568047137754413731686945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24362918068023539902330373 4568047137754413731686945)
                    ·
                      refine ⟨3426035353315810298765209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568047137754413731686945 3426035353315810298765209)
                      ·
                        rfl

theorem cell23_6672180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_6672180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672180 prefixEnd_6672180 := by exact prefixLift 6672180
  have htrace : WordTrace (prefixWord ++ tailWord_6672180) baseStart_6672180 baseEnd_6672180 := by
    simpa [prefixWord, tailWord_6672180, baseEnd_6672180] using wordTrace_append hprefix tailTrace_6672180
  have hstable : (prefixWord ++ tailWord_6672180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672180).length < 2 ^ (prefixWord ++ tailWord_6672180).sum := by decide
  have hdescent : baseEnd_6672180 < baseStart_6672180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672229 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_6672229 : Nat := 118140960795 + 6672229 * 2 ^ 59
def prefixEnd_6672229 : Nat := 4983230072969 + 3 ^ 40 * 6672229 * 2
def baseEnd_6672229 : Nat := 1142020171289293535684161

theorem tailTrace_6672229 : CollatzResearch.WordTrace tailWord_6672229 prefixEnd_6672229 1142020171289293535684161 := by
  unfold tailWord_6672229
  simp only [CollatzResearch.WordTrace]
  refine ⟨243356184144661333836011741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162237456096440889224007827 243356184144661333836011741)
  ·
    refine ⟨91258569054248000188504403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243356184144661333836011741 91258569054248000188504403)
    ·
      refine ⟨136887853581372000282756605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91258569054248000188504403 136887853581372000282756605)
      ·
        refine ⟨51332945093014500106033727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136887853581372000282756605 51332945093014500106033727)
        ·
          refine ⟨76999417639521750159050591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51332945093014500106033727 76999417639521750159050591)
          ·
            refine ⟨115499126459282625238575887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76999417639521750159050591 115499126459282625238575887)
            ·
              refine ⟨173248689688923937857863831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115499126459282625238575887 173248689688923937857863831)
              ·
                refine ⟨259873034533385906786795747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173248689688923937857863831 259873034533385906786795747)
                ·
                  refine ⟨389809551800078860180193621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259873034533385906786795747 389809551800078860180193621)
                  ·
                    refine ⟨1142020171289293535684161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 389809551800078860180193621 1142020171289293535684161)
                    ·
                      rfl

theorem cell23_6672229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_6672229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672229 prefixEnd_6672229 := by exact prefixLift 6672229
  have htrace : WordTrace (prefixWord ++ tailWord_6672229) baseStart_6672229 baseEnd_6672229 := by
    simpa [prefixWord, tailWord_6672229, baseEnd_6672229] using wordTrace_append hprefix tailTrace_6672229
  have hstable : (prefixWord ++ tailWord_6672229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672229).length < 2 ^ (prefixWord ++ tailWord_6672229).sum := by decide
  have hdescent : baseEnd_6672229 < baseStart_6672229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672236 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_6672236 : Nat := 118140960795 + 6672236 * 2 ^ 59
def prefixEnd_6672236 : Nat := 4983230072969 + 3 ^ 40 * 6672236 * 2
def baseEnd_6672236 : Nat := 3426064108232462079664951

theorem tailTrace_6672236 : CollatzResearch.WordTrace tailWord_6672236 prefixEnd_6672236 3426064108232462079664951 := by
  unfold tailWord_6672236
  simp only [CollatzResearch.WordTrace]
  refine ⟨121678219727817987015758281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162237626303757316021011041 121678219727817987015758281)
  ·
    refine ⟨91258664795863490261818711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121678219727817987015758281 91258664795863490261818711)
    ·
      refine ⟨136887997193795235392728067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91258664795863490261818711 136887997193795235392728067)
      ·
        refine ⟨205331995790692853089092101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136887997193795235392728067 205331995790692853089092101)
        ·
          refine ⟨38499749210754909954204769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205331995790692853089092101 38499749210754909954204769)
          ·
            refine ⟨28874811908066182465653577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38499749210754909954204769 28874811908066182465653577)
            ·
              refine ⟨21656108931049636849240183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28874811908066182465653577 21656108931049636849240183)
              ·
                refine ⟨32484163396574455273860275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21656108931049636849240183 32484163396574455273860275)
                ·
                  refine ⟨48726245094861682910790413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32484163396574455273860275 48726245094861682910790413)
                  ·
                    refine ⟨18272341910573131091546405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48726245094861682910790413 18272341910573131091546405)
                    ·
                      refine ⟨3426064108232462079664951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18272341910573131091546405 3426064108232462079664951)
                      ·
                        rfl

theorem cell23_6672236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_6672236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672236 prefixEnd_6672236 := by exact prefixLift 6672236
  have htrace : WordTrace (prefixWord ++ tailWord_6672236) baseStart_6672236 baseEnd_6672236 := by
    simpa [prefixWord, tailWord_6672236, baseEnd_6672236] using wordTrace_append hprefix tailTrace_6672236
  have hstable : (prefixWord ++ tailWord_6672236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672236).length < 2 ^ (prefixWord ++ tailWord_6672236).sum := by decide
  have hdescent : baseEnd_6672236 < baseStart_6672236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672239 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_6672239 : Nat := 118140960795 + 6672239 * 2 ^ 59
def prefixEnd_6672239 : Nat := 4983230072969 + 3 ^ 40 * 6672239 * 2
def baseEnd_6672239 : Nat := 3426065648674425567927437

theorem tailTrace_6672239 : CollatzResearch.WordTrace tailWord_6672239 prefixEnd_6672239 3426065648674425567927437 := by
  unfold tailWord_6672239
  simp only [CollatzResearch.WordTrace]
  refine ⟨243356548874625105543875771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162237699249750070362583847 243356548874625105543875771)
  ·
    refine ⟨365034823311937658315813657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243356548874625105543875771 365034823311937658315813657)
    ·
      refine ⟨273776117483953243736860243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365034823311937658315813657 273776117483953243736860243)
      ·
        refine ⟨410664176225929865605290365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273776117483953243736860243 410664176225929865605290365)
        ·
          refine ⟨153999066084723699601983887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410664176225929865605290365 153999066084723699601983887)
          ·
            refine ⟨230998599127085549402975831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153999066084723699601983887 230998599127085549402975831)
            ·
              refine ⟨346497898690628324104463747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230998599127085549402975831 346497898690628324104463747)
              ·
                refine ⟨519746848035942486156695621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346497898690628324104463747 519746848035942486156695621)
                ·
                  refine ⟨97452534006739216154380429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 519746848035942486156695621 97452534006739216154380429)
                  ·
                    refine ⟨36544700252527206057892661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97452534006739216154380429 36544700252527206057892661)
                    ·
                      refine ⟨3426065648674425567927437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36544700252527206057892661 3426065648674425567927437)
                      ·
                        rfl

theorem cell23_6672239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_6672239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672239 prefixEnd_6672239 := by exact prefixLift 6672239
  have htrace : WordTrace (prefixWord ++ tailWord_6672239) baseStart_6672239 baseEnd_6672239 := by
    simpa [prefixWord, tailWord_6672239, baseEnd_6672239] using wordTrace_append hprefix tailTrace_6672239
  have hstable : (prefixWord ++ tailWord_6672239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672239).length < 2 ^ (prefixWord ++ tailWord_6672239).sum := by decide
  have hdescent : baseEnd_6672239 < baseStart_6672239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672336 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_6672336 : Nat := 118140960795 + 6672336 * 2 ^ 59
def prefixEnd_6672336 : Nat := 4983230072969 + 3 ^ 40 * 6672336 * 2
def baseEnd_6672336 : Nat := 1142038485432637229471497

theorem tailTrace_6672336 : CollatzResearch.WordTrace tailWord_6672336 prefixEnd_6672336 1142038485432637229471497 := by
  unfold tailWord_6672336
  simp only [CollatzResearch.WordTrace]
  refine ⟨121680043377636845555078431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162240057836849127406771241 121680043377636845555078431)
  ·
    refine ⟨182520065066455268332617647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121680043377636845555078431 182520065066455268332617647)
    ·
      refine ⟨273780097599682902498926471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182520065066455268332617647 273780097599682902498926471)
      ·
        refine ⟨410670146399524353748389707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273780097599682902498926471 410670146399524353748389707)
        ·
          refine ⟨616005219599286530622584561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410670146399524353748389707 616005219599286530622584561)
          ·
            refine ⟨462003914699464897966938421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616005219599286530622584561 462003914699464897966938421)
            ·
              refine ⟨43312867003074834184400477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 462003914699464897966938421 43312867003074834184400477)
              ·
                refine ⟨16242325126153062819150179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43312867003074834184400477 16242325126153062819150179)
                ·
                  refine ⟨24363487689229594228725269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16242325126153062819150179 24363487689229594228725269)
                  ·
                    refine ⟨1142038485432637229471497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24363487689229594228725269 1142038485432637229471497)
                    ·
                      rfl

theorem cell23_6672336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_6672336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672336 prefixEnd_6672336 := by exact prefixLift 6672336
  have htrace : WordTrace (prefixWord ++ tailWord_6672336) baseStart_6672336 baseEnd_6672336 := by
    simpa [prefixWord, tailWord_6672336, baseEnd_6672336] using wordTrace_append hprefix tailTrace_6672336
  have hstable : (prefixWord ++ tailWord_6672336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672336).length < 2 ^ (prefixWord ++ tailWord_6672336).sum := by decide
  have hdescent : baseEnd_6672336 < baseStart_6672336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672343 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_6672343 : Nat := 118140960795 + 6672343 * 2 ^ 59
def prefixEnd_6672343 : Nat := 4983230072969 + 3 ^ 40 * 6672343 * 2
def baseEnd_6672343 : Nat := 3426119050662493161026959

theorem tailTrace_6672343 : CollatzResearch.WordTrace tailWord_6672343 prefixEnd_6672343 3426119050662493161026959 := by
  unfold tailWord_6672343
  simp only [CollatzResearch.WordTrace]
  refine ⟨243360342066248331305661683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162240228044165554203774455 243360342066248331305661683)
  ·
    refine ⟨365040513099372496958492525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243360342066248331305661683 365040513099372496958492525)
    ·
      refine ⟨136890192412264686359434697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365040513099372496958492525 136890192412264686359434697)
      ·
        refine ⟨102667644309198514769576023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136890192412264686359434697 102667644309198514769576023)
        ·
          refine ⟨154001466463797772154364035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102667644309198514769576023 154001466463797772154364035)
          ·
            refine ⟨231002199695696658231546053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154001466463797772154364035 231002199695696658231546053)
            ·
              refine ⟨43312912442943123418414885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231002199695696658231546053 43312912442943123418414885)
              ·
                refine ⟨8121171083051835640952791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43312912442943123418414885 8121171083051835640952791)
                ·
                  refine ⟨12181756624577753461429187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8121171083051835640952791 12181756624577753461429187)
                  ·
                    refine ⟨18272634936866630192143781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12181756624577753461429187 18272634936866630192143781)
                    ·
                      refine ⟨3426119050662493161026959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18272634936866630192143781 3426119050662493161026959)
                      ·
                        rfl

theorem cell23_6672343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_6672343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672343 prefixEnd_6672343 := by exact prefixLift 6672343
  have htrace : WordTrace (prefixWord ++ tailWord_6672343) baseStart_6672343 baseEnd_6672343 := by
    simpa [prefixWord, tailWord_6672343, baseEnd_6672343] using wordTrace_append hprefix tailTrace_6672343
  have hstable : (prefixWord ++ tailWord_6672343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672343).length < 2 ^ (prefixWord ++ tailWord_6672343).sum := by decide
  have hdescent : baseEnd_6672343 < baseStart_6672343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672360 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6672360 : Nat := 118140960795 + 6672360 * 2 ^ 59
def prefixEnd_6672360 : Nat := 4983230072969 + 3 ^ 40 * 6672360 * 2
def baseEnd_6672360 : Nat := 3426127779833619594514381

theorem tailTrace_6672360 : CollatzResearch.WordTrace tailWord_6672360 prefixEnd_6672360 3426127779833619594514381 := by
  unfold tailWord_6672360
  simp only [CollatzResearch.WordTrace]
  refine ⟨121680481053593371604515267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162240641404791162139353689 121680481053593371604515267)
  ·
    refine ⟨182520721580390057406772901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121680481053593371604515267 182520721580390057406772901)
    ·
      refine ⟨34222635296323135763769919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182520721580390057406772901 34222635296323135763769919)
      ·
        refine ⟨51333952944484703645654879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34222635296323135763769919 51333952944484703645654879)
        ·
          refine ⟨77000929416727055468482319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51333952944484703645654879 77000929416727055468482319)
          ·
            refine ⟨115501394125090583202723479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77000929416727055468482319 115501394125090583202723479)
            ·
              refine ⟨173252091187635874804085219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115501394125090583202723479 173252091187635874804085219)
              ·
                refine ⟨259878136781453812206127829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173252091187635874804085219 259878136781453812206127829)
                ·
                  refine ⟨6090893830815323723581121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259878136781453812206127829 6090893830815323723581121)
                  ·
                    refine ⟨4568170373111492792685841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6090893830815323723581121 4568170373111492792685841)
                    ·
                      refine ⟨3426127779833619594514381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568170373111492792685841 3426127779833619594514381)
                      ·
                        rfl

theorem cell23_6672360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6672360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672360 prefixEnd_6672360 := by exact prefixLift 6672360
  have htrace : WordTrace (prefixWord ++ tailWord_6672360) baseStart_6672360 baseEnd_6672360 := by
    simpa [prefixWord, tailWord_6672360, baseEnd_6672360] using wordTrace_append hprefix tailTrace_6672360
  have hstable : (prefixWord ++ tailWord_6672360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672360).length < 2 ^ (prefixWord ++ tailWord_6672360).sum := by decide
  have hdescent : baseEnd_6672360 < baseStart_6672360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672377 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 3, 2, 2]
def baseStart_6672377 : Nat := 118140960795 + 6672377 * 2 ^ 59
def prefixEnd_6672377 : Nat := 4983230072969 + 3 ^ 40 * 6672377 * 2
def baseEnd_6672377 : Nat := 3426136509004746028001803

theorem tailTrace_6672377 : CollatzResearch.WordTrace tailWord_6672377 prefixEnd_6672377 3426136509004746028001803 := by
  unfold tailWord_6672377
  simp only [CollatzResearch.WordTrace]
  refine ⟨243361582148125155112399385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162241054765416770074932923 243361582148125155112399385)
  ·
    refine ⟨182521186611093866334299539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243361582148125155112399385 182521186611093866334299539)
    ·
      refine ⟨273781779916640799501449309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182521186611093866334299539 273781779916640799501449309)
      ·
        refine ⟨102668167468740299813043491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273781779916640799501449309 102668167468740299813043491)
        ·
          refine ⟨154002251203110449719565237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102668167468740299813043491 154002251203110449719565237)
          ·
            refine ⟨14437711050291604661209241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154002251203110449719565237 14437711050291604661209241)
            ·
              refine ⟨10828283287718703495906931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14437711050291604661209241 10828283287718703495906931)
              ·
                refine ⟨16242424931578055243860397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10828283287718703495906931 16242424931578055243860397)
                ·
                  refine ⟨6090909349341770716447649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16242424931578055243860397 6090909349341770716447649)
                  ·
                    refine ⟨4568182012006328037335737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6090909349341770716447649 4568182012006328037335737)
                    ·
                      refine ⟨3426136509004746028001803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568182012006328037335737 3426136509004746028001803)
                      ·
                        rfl

theorem cell23_6672377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_6672377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672377 prefixEnd_6672377 := by exact prefixLift 6672377
  have htrace : WordTrace (prefixWord ++ tailWord_6672377) baseStart_6672377 baseEnd_6672377 := by
    simpa [prefixWord, tailWord_6672377, baseEnd_6672377] using wordTrace_append hprefix tailTrace_6672377
  have hstable : (prefixWord ++ tailWord_6672377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672377).length < 2 ^ (prefixWord ++ tailWord_6672377).sum := by decide
  have hdescent : baseEnd_6672377 < baseStart_6672377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672410 : List Nat := [3, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_6672410 : Nat := 118140960795 + 6672410 * 2 ^ 59
def prefixEnd_6672410 : Nat := 4983230072969 + 3 ^ 40 * 6672410 * 2
def baseEnd_6672410 : Nat := 3426153453866344398889151

theorem tailTrace_6672410 : CollatzResearch.WordTrace tailWord_6672410 prefixEnd_6672410 3426153453866344398889151 := by
  unfold tailWord_6672410
  simp only [CollatzResearch.WordTrace]
  refine ⟨60840696439251400437087671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162241857171337067832233789 60840696439251400437087671)
  ·
    refine ⟨91261044658877100655631507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60840696439251400437087671 91261044658877100655631507)
    ·
      refine ⟨136891566988315650983447261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91261044658877100655631507 136891566988315650983447261)
      ·
        refine ⟨51334337620618369118792723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136891566988315650983447261 51334337620618369118792723)
        ·
          refine ⟨77001506430927553678189085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51334337620618369118792723 77001506430927553678189085)
          ·
            refine ⟨28875564911597832629320907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77001506430927553678189085 28875564911597832629320907)
            ·
              refine ⟨43313347367396748943981361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28875564911597832629320907 43313347367396748943981361)
              ·
                refine ⟨32485010525547561707986021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43313347367396748943981361 32485010525547561707986021)
                ·
                  refine ⟨6090939473540167820247379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32485010525547561707986021 6090939473540167820247379)
                  ·
                    refine ⟨9136409210310251730371069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6090939473540167820247379 9136409210310251730371069)
                    ·
                      refine ⟨3426153453866344398889151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9136409210310251730371069 3426153453866344398889151)
                      ·
                        rfl

theorem cell23_6672410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_6672410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672410 prefixEnd_6672410 := by exact prefixLift 6672410
  have htrace : WordTrace (prefixWord ++ tailWord_6672410) baseStart_6672410 baseEnd_6672410 := by
    simpa [prefixWord, tailWord_6672410, baseEnd_6672410] using wordTrace_append hprefix tailTrace_6672410
  have hstable : (prefixWord ++ tailWord_6672410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672410).length < 2 ^ (prefixWord ++ tailWord_6672410).sum := by decide
  have hdescent : baseEnd_6672410 < baseStart_6672410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672454 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6672454 : Nat := 118140960795 + 6672454 * 2 ^ 59
def prefixEnd_6672454 : Nat := 4983230072969 + 3 ^ 40 * 6672454 * 2
def baseEnd_6672454 : Nat := 3426176047015142226738949

theorem tailTrace_6672454 : CollatzResearch.WordTrace tailWord_6672454 prefixEnd_6672454 3426176047015142226738949 := by
  unfold tailWord_6672454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605137205276443664467263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162242927045897464841968277 7605137205276443664467263)
  ·
    refine ⟨11407705807914665496700895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7605137205276443664467263 11407705807914665496700895)
    ·
      refine ⟨17111558711871998245051343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11407705807914665496700895 17111558711871998245051343)
      ·
        refine ⟨25667338067807997367577015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17111558711871998245051343 25667338067807997367577015)
        ·
          refine ⟨38501007101711996051365523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25667338067807997367577015 38501007101711996051365523)
          ·
            refine ⟨57751510652567994077048285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38501007101711996051365523 57751510652567994077048285)
            ·
              refine ⟨21656816494712997778893107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57751510652567994077048285 21656816494712997778893107)
              ·
                refine ⟨32485224742069496668339661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21656816494712997778893107 32485224742069496668339661)
                ·
                  refine ⟨12181959278276061250627373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32485224742069496668339661 12181959278276061250627373)
                  ·
                    refine ⟨4568234729353522968985265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12181959278276061250627373 4568234729353522968985265)
                    ·
                      refine ⟨3426176047015142226738949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568234729353522968985265 3426176047015142226738949)
                      ·
                        rfl

theorem cell23_6672454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6672454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672454 prefixEnd_6672454 := by exact prefixLift 6672454
  have htrace : WordTrace (prefixWord ++ tailWord_6672454) baseStart_6672454 baseEnd_6672454 := by
    simpa [prefixWord, tailWord_6672454, baseEnd_6672454] using wordTrace_append hprefix tailTrace_6672454
  have hstable : (prefixWord ++ tailWord_6672454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672454).length < 2 ^ (prefixWord ++ tailWord_6672454).sum := by decide
  have hdescent : baseEnd_6672454 < baseStart_6672454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672478 : List Nat := [4, 4, 1, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_6672478 : Nat := 118140960795 + 6672478 * 2 ^ 59
def prefixEnd_6672478 : Nat := 4983230072969 + 3 ^ 40 * 6672478 * 2
def baseEnd_6672478 : Nat := 3426188370550850132838839

theorem tailTrace_6672478 : CollatzResearch.WordTrace tailWord_6672478 prefixEnd_6672478 3426188370550850132838839 := by
  unfold tailWord_6672478
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420658240094906170228261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162243510613839499574550725 30420658240094906170228261)
  ·
    refine ⟨5703873420017794906917799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30420658240094906170228261 5703873420017794906917799)
    ·
      refine ⟨8555810130026692360376699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703873420017794906917799 8555810130026692360376699)
      ·
        refine ⟨12833715195040038540565049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555810130026692360376699 12833715195040038540565049)
        ·
          refine ⟨9625286396280028905423787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12833715195040038540565049 9625286396280028905423787)
          ·
            refine ⟨14437929594420043358135681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9625286396280028905423787 14437929594420043358135681)
            ·
              refine ⟨10828447195815032518601761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14437929594420043358135681 10828447195815032518601761)
              ·
                refine ⟨8121335396861274388951321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828447195815032518601761 8121335396861274388951321)
                ·
                  refine ⟨6091001547645955791713491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121335396861274388951321 6091001547645955791713491)
                  ·
                    refine ⟨9136502321468933687570237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6091001547645955791713491 9136502321468933687570237)
                    ·
                      refine ⟨3426188370550850132838839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9136502321468933687570237 3426188370550850132838839)
                      ·
                        rfl

theorem cell23_6672478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_6672478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672478 prefixEnd_6672478 := by exact prefixLift 6672478
  have htrace : WordTrace (prefixWord ++ tailWord_6672478) baseStart_6672478 baseEnd_6672478 := by
    simpa [prefixWord, tailWord_6672478, baseEnd_6672478] using wordTrace_append hprefix tailTrace_6672478
  have hstable : (prefixWord ++ tailWord_6672478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672478).length < 2 ^ (prefixWord ++ tailWord_6672478).sum := by decide
  have hdescent : baseEnd_6672478 < baseStart_6672478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672520 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_6672520 : Nat := 118140960795 + 6672520 * 2 ^ 59
def prefixEnd_6672520 : Nat := 4983230072969 + 3 ^ 40 * 6672520 * 2
def baseEnd_6672520 : Nat := 1142069978912779656171215

theorem tailTrace_6672520 : CollatzResearch.WordTrace tailWord_6672520 prefixEnd_6672520 1142069978912779656171215 := by
  unfold tailWord_6672520
  simp only [CollatzResearch.WordTrace]
  refine ⟨121683398893303545267427507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162244531857738060356570009 121683398893303545267427507)
  ·
    refine ⟨182525098339955317901141261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121683398893303545267427507 182525098339955317901141261)
    ·
      refine ⟨68446911877483244212927973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182525098339955317901141261 68446911877483244212927973)
      ·
        refine ⟨12833795977028108289923995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68446911877483244212927973 12833795977028108289923995)
        ·
          refine ⟨19250693965542162434885993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12833795977028108289923995 19250693965542162434885993)
          ·
            refine ⟨14438020474156621826164495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19250693965542162434885993 14438020474156621826164495)
            ·
              refine ⟨21657030711234932739246743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14438020474156621826164495 21657030711234932739246743)
              ·
                refine ⟨32485546066852399108870115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21657030711234932739246743 32485546066852399108870115)
                ·
                  refine ⟨48728319100278598663305173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32485546066852399108870115 48728319100278598663305173)
                  ·
                    refine ⟨1142069978912779656171215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48728319100278598663305173 1142069978912779656171215)
                    ·
                      rfl

theorem cell23_6672520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_6672520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672520 prefixEnd_6672520 := by exact prefixLift 6672520
  have htrace : WordTrace (prefixWord ++ tailWord_6672520) baseStart_6672520 baseEnd_6672520 := by
    simpa [prefixWord, tailWord_6672520, baseEnd_6672520] using wordTrace_append hprefix tailTrace_6672520
  have hstable : (prefixWord ++ tailWord_6672520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672520).length < 2 ^ (prefixWord ++ tailWord_6672520).sum := by decide
  have hdescent : baseEnd_6672520 < baseStart_6672520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672540 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6672540 : Nat := 118140960795 + 6672540 * 2 ^ 59
def prefixEnd_6672540 : Nat := 4983230072969 + 3 ^ 40 * 6672540 * 2
def baseEnd_6672540 : Nat := 3426220206351428890263553

theorem tailTrace_6672540 : CollatzResearch.WordTrace tailWord_6672540 prefixEnd_6672540 3426220206351428890263553 := by
  unfold tailWord_6672540
  simp only [CollatzResearch.WordTrace]
  refine ⟨121683763623267316975291537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162245018164356422633722049 121683763623267316975291537)
  ·
    refine ⟨91262822717450487731468653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121683763623267316975291537 91262822717450487731468653)
    ·
      refine ⟨34223558519043932899300745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91262822717450487731468653 34223558519043932899300745)
      ·
        refine ⟨25667668889282949674475559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34223558519043932899300745 25667668889282949674475559)
        ·
          refine ⟨38501503333924424511713339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25667668889282949674475559 38501503333924424511713339)
          ·
            refine ⟨57752255000886636767570009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38501503333924424511713339 57752255000886636767570009)
            ·
              refine ⟨43314191250664977575677507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57752255000886636767570009 43314191250664977575677507)
              ·
                refine ⟨64971286875997466363516261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43314191250664977575677507 64971286875997466363516261)
                ·
                  refine ⟨12182116289249524943159299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64971286875997466363516261 12182116289249524943159299)
                  ·
                    refine ⟨18273174433874287414738949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12182116289249524943159299 18273174433874287414738949)
                    ·
                      refine ⟨3426220206351428890263553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18273174433874287414738949 3426220206351428890263553)
                      ·
                        rfl

theorem cell23_6672540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6672540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672540 prefixEnd_6672540 := by exact prefixLift 6672540
  have htrace : WordTrace (prefixWord ++ tailWord_6672540) baseStart_6672540 baseEnd_6672540 := by
    simpa [prefixWord, tailWord_6672540, baseEnd_6672540] using wordTrace_append hprefix tailTrace_6672540
  have hstable : (prefixWord ++ tailWord_6672540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672540).length < 2 ^ (prefixWord ++ tailWord_6672540).sum := by decide
  have hdescent : baseEnd_6672540 < baseStart_6672540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672580 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 8]
def baseStart_6672580 : Nat := 118140960795 + 6672580 * 2 ^ 59
def prefixEnd_6672580 : Nat := 4983230072969 + 3 ^ 40 * 6672580 * 2
def baseEnd_6672580 : Nat := 380693416175289859307041

theorem tailTrace_6672580 : CollatzResearch.WordTrace tailWord_6672580 prefixEnd_6672580 380693416175289859307041 := by
  unfold tailWord_6672580
  simp only [CollatzResearch.WordTrace]
  refine ⟨121684493083194860391019597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162245990777593147188026129 121684493083194860391019597)
  ·
    refine ⟨45631684906198072646632349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121684493083194860391019597 45631684906198072646632349)
    ·
      refine ⟨17111881839824277242487131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45631684906198072646632349 17111881839824277242487131)
      ·
        refine ⟨25667822759736415863730697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17111881839824277242487131 25667822759736415863730697)
        ·
          refine ⟨19250867069802311897798023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25667822759736415863730697 19250867069802311897798023)
          ·
            refine ⟨28876300604703467846697035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19250867069802311897798023 28876300604703467846697035)
            ·
              refine ⟨43314450907055201770045553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28876300604703467846697035 43314450907055201770045553)
              ·
                refine ⟨32485838180291401327534165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43314450907055201770045553 32485838180291401327534165)
                ·
                  refine ⟨380693416175289859307041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32485838180291401327534165 380693416175289859307041)
                  ·
                    rfl

theorem cell23_6672580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_6672580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672580 prefixEnd_6672580 := by exact prefixLift 6672580
  have htrace : WordTrace (prefixWord ++ tailWord_6672580) baseStart_6672580 baseEnd_6672580 := by
    simpa [prefixWord, tailWord_6672580, baseEnd_6672580] using wordTrace_append hprefix tailTrace_6672580
  have hstable : (prefixWord ++ tailWord_6672580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672580).length < 2 ^ (prefixWord ++ tailWord_6672580).sum := by decide
  have hdescent : baseEnd_6672580 < baseStart_6672580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672634 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2]
def baseStart_6672634 : Nat := 118140960795 + 6672634 * 2 ^ 59
def prefixEnd_6672634 : Nat := 4983230072969 + 3 ^ 40 * 6672634 * 2
def baseEnd_6672634 : Nat := 3426268473532951522488121

theorem tailTrace_6672634 : CollatzResearch.WordTrace tailWord_6672634 prefixEnd_6672634 3426268473532951522488121 := by
  unfold tailWord_6672634
  simp only [CollatzResearch.WordTrace]
  refine ⟨60842738927048522001126239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162247303805462725336336637 60842738927048522001126239)
  ·
    refine ⟨91264108390572783001689359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60842738927048522001126239 91264108390572783001689359)
    ·
      refine ⟨136896162585859174502534039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91264108390572783001689359 136896162585859174502534039)
      ·
        refine ⟨205344243878788761753801059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136896162585859174502534039 205344243878788761753801059)
        ·
          refine ⟨308016365818183142630701589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205344243878788761753801059 308016365818183142630701589)
          ·
            refine ⟨14438267147727334810814137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 308016365818183142630701589 14438267147727334810814137)
            ·
              refine ⟨10828700360795501108110603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14438267147727334810814137 10828700360795501108110603)
              ·
                refine ⟨16243050541193251662165905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10828700360795501108110603 16243050541193251662165905)
                ·
                  refine ⟨12182287905894938746624429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16243050541193251662165905 12182287905894938746624429)
                  ·
                    refine ⟨4568357964710602029984161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12182287905894938746624429 4568357964710602029984161)
                    ·
                      refine ⟨3426268473532951522488121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568357964710602029984161 3426268473532951522488121)
                      ·
                        rfl

theorem cell23_6672634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_6672634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672634 prefixEnd_6672634 := by exact prefixLift 6672634
  have htrace : WordTrace (prefixWord ++ tailWord_6672634) baseStart_6672634 baseEnd_6672634 := by
    simpa [prefixWord, tailWord_6672634, baseEnd_6672634] using wordTrace_append hprefix tailTrace_6672634
  have hstable : (prefixWord ++ tailWord_6672634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672634).length < 2 ^ (prefixWord ++ tailWord_6672634).sum := by decide
  have hdescent : baseEnd_6672634 < baseStart_6672634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672640 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 6, 4]
def baseStart_6672640 : Nat := 118140960795 + 6672640 * 2 ^ 59
def prefixEnd_6672640 : Nat := 4983230072969 + 3 ^ 40 * 6672640 * 2
def baseEnd_6672640 : Nat := 1142090518138959499671031

theorem tailTrace_6672640 : CollatzResearch.WordTrace tailWord_6672640 prefixEnd_6672640 1142090518138959499671031 := by
  unfold tailWord_6672640
  simp only [CollatzResearch.WordTrace]
  refine ⟨121685587273086175514611687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162247449697448234019482249 121685587273086175514611687)
  ·
    refine ⟨182528380909629263271917531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121685587273086175514611687 182528380909629263271917531)
    ·
      refine ⟨273792571364443894907876297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182528380909629263271917531 273792571364443894907876297)
      ·
        refine ⟨205344428523332921180907223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273792571364443894907876297 205344428523332921180907223)
        ·
          refine ⟨308016642784999381771360835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205344428523332921180907223 308016642784999381771360835)
          ·
            refine ⟨462024964177499072657041253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308016642784999381771360835 462024964177499072657041253)
            ·
              refine ⟨86629680783281076123195235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 462024964177499072657041253 86629680783281076123195235)
              ·
                refine ⟨129944521174921614184792853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86629680783281076123195235 129944521174921614184792853)
                ·
                  refine ⟨6091149430074450664912165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129944521174921614184792853 6091149430074450664912165)
                  ·
                    refine ⟨1142090518138959499671031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091149430074450664912165 1142090518138959499671031)
                    ·
                      rfl

theorem cell23_6672640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_6672640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672640 prefixEnd_6672640 := by exact prefixLift 6672640
  have htrace : WordTrace (prefixWord ++ tailWord_6672640) baseStart_6672640 baseEnd_6672640 := by
    simpa [prefixWord, tailWord_6672640, baseEnd_6672640] using wordTrace_append hprefix tailTrace_6672640
  have hstable : (prefixWord ++ tailWord_6672640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672640).length < 2 ^ (prefixWord ++ tailWord_6672640).sum := by decide
  have hdescent : baseEnd_6672640 < baseStart_6672640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672657 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 2, 4]
def baseStart_6672657 : Nat := 118140960795 + 6672657 * 2 ^ 59
def prefixEnd_6672657 : Nat := 4983230072969 + 3 ^ 40 * 6672657 * 2
def baseEnd_6672657 : Nat := 1142093427862668310833505

theorem tailTrace_6672657 : CollatzResearch.WordTrace tailWord_6672657 prefixEnd_6672657 1142093427862668310833505 := by
  unfold tailWord_6672657
  simp only [CollatzResearch.WordTrace]
  refine ⟨243371794587110762932592225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162247863058073841955061483 243371794587110762932592225)
  ·
    refine ⟨182528845940333072199444169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243371794587110762932592225 182528845940333072199444169)
    ·
      refine ⟨136896634455249804149583127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182528845940333072199444169 136896634455249804149583127)
      ·
        refine ⟨205344951682874706224374691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136896634455249804149583127 205344951682874706224374691)
        ·
          refine ⟨308017427524312059336562037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205344951682874706224374691 308017427524312059336562037)
          ·
            refine ⟨28876633830404255562802691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308017427524312059336562037 28876633830404255562802691)
            ·
              refine ⟨43314950745606383344204037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28876633830404255562802691 43314950745606383344204037)
              ·
                refine ⟨8121553264801196877038257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43314950745606383344204037 8121553264801196877038257)
                ·
                  refine ⟨6091164948600897657778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121553264801196877038257 6091164948600897657778693)
                  ·
                    refine ⟨1142093427862668310833505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091164948600897657778693 1142093427862668310833505)
                    ·
                      rfl

theorem cell23_6672657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 4].length) (baseStart_6672657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672657 prefixEnd_6672657 := by exact prefixLift 6672657
  have htrace : WordTrace (prefixWord ++ tailWord_6672657) baseStart_6672657 baseEnd_6672657 := by
    simpa [prefixWord, tailWord_6672657, baseEnd_6672657] using wordTrace_append hprefix tailTrace_6672657
  have hstable : (prefixWord ++ tailWord_6672657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672657).length < 2 ^ (prefixWord ++ tailWord_6672657).sum := by decide
  have hdescent : baseEnd_6672657 < baseStart_6672657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672664 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2]
def baseStart_6672664 : Nat := 118140960795 + 6672664 * 2 ^ 59
def prefixEnd_6672664 : Nat := 4983230072969 + 3 ^ 40 * 6672664 * 2
def baseEnd_6672664 : Nat := 3426283877952586405112983

theorem tailTrace_6672664 : CollatzResearch.WordTrace tailWord_6672664 prefixEnd_6672664 3426283877952586405112983 := by
  unfold tailWord_6672664
  simp only [CollatzResearch.WordTrace]
  refine ⟨121686024949042701564048523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162248033265390268752064697 121686024949042701564048523)
  ·
    refine ⟨182529037423564052346072785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121686024949042701564048523 182529037423564052346072785)
    ·
      refine ⟨136896778067673039259554589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182529037423564052346072785 136896778067673039259554589)
      ·
        refine ⟨51336291775377389722332971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136896778067673039259554589 51336291775377389722332971)
        ·
          refine ⟨77004437663066084583499457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51336291775377389722332971 77004437663066084583499457)
          ·
            refine ⟨57753328247299563437624593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77004437663066084583499457 57753328247299563437624593)
            ·
              refine ⟨43314996185474672578218445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57753328247299563437624593 43314996185474672578218445)
              ·
                refine ⟨16243123569553002216831917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43314996185474672578218445 16243123569553002216831917)
                ·
                  refine ⟨6091171338582375831311969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16243123569553002216831917 6091171338582375831311969)
                  ·
                    refine ⟨4568378503936781873483977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6091171338582375831311969 4568378503936781873483977)
                    ·
                      refine ⟨3426283877952586405112983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568378503936781873483977 3426283877952586405112983)
                      ·
                        rfl

theorem cell23_6672664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_6672664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672664 prefixEnd_6672664 := by exact prefixLift 6672664
  have htrace : WordTrace (prefixWord ++ tailWord_6672664) baseStart_6672664 baseEnd_6672664 := by
    simpa [prefixWord, tailWord_6672664, baseEnd_6672664] using wordTrace_append hprefix tailTrace_6672664
  have hstable : (prefixWord ++ tailWord_6672664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672664).length < 2 ^ (prefixWord ++ tailWord_6672664).sum := by decide
  have hdescent : baseEnd_6672664 < baseStart_6672664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672674 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6672674 : Nat := 118140960795 + 6672674 * 2 ^ 59
def prefixEnd_6672674 : Nat := 4983230072969 + 3 ^ 40 * 6672674 * 2
def baseEnd_6672674 : Nat := 1142096337586377121995979

theorem tailTrace_6672674 : CollatzResearch.WordTrace tailWord_6672674 prefixEnd_6672674 1142096337586377121995979 := by
  unfold tailWord_6672674
  simp only [CollatzResearch.WordTrace]
  refine ⟨60843103657012293708990269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162248276418699449890640717 60843103657012293708990269)
  ·
    refine ⟨22816163871379610140871351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60843103657012293708990269 22816163871379610140871351)
    ·
      refine ⟨34224245807069415211307027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22816163871379610140871351 34224245807069415211307027)
      ·
        refine ⟨51336368710604122816960541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34224245807069415211307027 51336368710604122816960541)
        ·
          refine ⟨19251138266476546056360203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51336368710604122816960541 19251138266476546056360203)
          ·
            refine ⟨28876707399714819084540305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19251138266476546056360203 28876707399714819084540305)
            ·
              refine ⟨21657530549786114313405229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28876707399714819084540305 21657530549786114313405229)
              ·
                refine ⟨8121573956169792867526961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21657530549786114313405229 8121573956169792867526961)
                ·
                  refine ⟨6091180467127344650645221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121573956169792867526961 6091180467127344650645221)
                  ·
                    refine ⟨1142096337586377121995979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091180467127344650645221 1142096337586377121995979)
                    ·
                      rfl

theorem cell23_6672674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6672674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672674 prefixEnd_6672674 := by exact prefixLift 6672674
  have htrace : WordTrace (prefixWord ++ tailWord_6672674) baseStart_6672674 baseEnd_6672674 := by
    simpa [prefixWord, tailWord_6672674, baseEnd_6672674] using wordTrace_append hprefix tailTrace_6672674
  have hstable : (prefixWord ++ tailWord_6672674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672674).length < 2 ^ (prefixWord ++ tailWord_6672674).sum := by decide
  have hdescent : baseEnd_6672674 < baseStart_6672674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672685 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_6672685 : Nat := 118140960795 + 6672685 * 2 ^ 59
def prefixEnd_6672685 : Nat := 4983230072969 + 3 ^ 40 * 6672685 * 2
def baseEnd_6672685 : Nat := 3426294661046330822950387

theorem tailTrace_6672685 : CollatzResearch.WordTrace tailWord_6672685 prefixEnd_6672685 3426294661046330822950387 := by
  unfold tailWord_6672685
  simp only [CollatzResearch.WordTrace]
  refine ⟨243372815831009323714611509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162248543887339549143074339 243372815831009323714611509)
  ·
    refine ⟨22816201484157124098244829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 243372815831009323714611509 22816201484157124098244829)
    ·
      refine ⟨8556075556558921536841811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22816201484157124098244829 8556075556558921536841811)
      ·
        refine ⟨12834113334838382305262717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556075556558921536841811 12834113334838382305262717)
        ·
          refine ⟨4812792500564393364473519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12834113334838382305262717 4812792500564393364473519)
          ·
            refine ⟨7219188750846590046710279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812792500564393364473519 7219188750846590046710279)
            ·
              refine ⟨10828783126269885070065419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219188750846590046710279 10828783126269885070065419)
              ·
                refine ⟨16243174689404827605098129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10828783126269885070065419 16243174689404827605098129)
                ·
                  refine ⟨12182381017053620703823597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16243174689404827605098129 12182381017053620703823597)
                  ·
                    refine ⟨4568392881395107763933849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12182381017053620703823597 4568392881395107763933849)
                    ·
                      refine ⟨3426294661046330822950387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568392881395107763933849 3426294661046330822950387)
                      ·
                        rfl

theorem cell23_6672685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_6672685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672685 prefixEnd_6672685 := by exact prefixLift 6672685
  have htrace : WordTrace (prefixWord ++ tailWord_6672685) baseStart_6672685 baseEnd_6672685 := by
    simpa [prefixWord, tailWord_6672685, baseEnd_6672685] using wordTrace_append hprefix tailTrace_6672685
  have hstable : (prefixWord ++ tailWord_6672685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672685).length < 2 ^ (prefixWord ++ tailWord_6672685).sum := by decide
  have hdescent : baseEnd_6672685 < baseStart_6672685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672698 : List Nat := [3, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2]
def baseStart_6672698 : Nat := 118140960795 + 6672698 * 2 ^ 59
def prefixEnd_6672698 : Nat := 4983230072969 + 3 ^ 40 * 6672698 * 2
def baseEnd_6672698 : Nat := 3426301336294839272087827

theorem tailTrace_6672698 : CollatzResearch.WordTrace tailWord_6672698 prefixEnd_6672698 3426301336294839272087827 := by
  unfold tailWord_6672698
  simp only [CollatzResearch.WordTrace]
  refine ⟨60843322494990556733708687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162248859986641484623223165 60843322494990556733708687)
  ·
    refine ⟨91264983742485835100563031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60843322494990556733708687 91264983742485835100563031)
    ·
      refine ⟨136897475613728752650844547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91264983742485835100563031 136897475613728752650844547)
      ·
        refine ⟨205346213420593128976266821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136897475613728752650844547 205346213420593128976266821)
        ·
          refine ⟨38502415016361211683050029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205346213420593128976266821 38502415016361211683050029)
          ·
            refine ⟨14438405631135454381143761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38502415016361211683050029 14438405631135454381143761)
            ·
              refine ⟨10828804223351590785857821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14438405631135454381143761 10828804223351590785857821)
              ·
                refine ⟨4060801583756846544696683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10828804223351590785857821 4060801583756846544696683)
                ·
                  refine ⟨6091202375635269817045025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4060801583756846544696683 6091202375635269817045025)
                  ·
                    refine ⟨4568401781726452362783769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6091202375635269817045025 4568401781726452362783769)
                    ·
                      refine ⟨3426301336294839272087827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568401781726452362783769 3426301336294839272087827)
                      ·
                        rfl

theorem cell23_6672698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_6672698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672698 prefixEnd_6672698 := by exact prefixLift 6672698
  have htrace : WordTrace (prefixWord ++ tailWord_6672698) baseStart_6672698 baseEnd_6672698 := by
    simpa [prefixWord, tailWord_6672698, baseEnd_6672698] using wordTrace_append hprefix tailTrace_6672698
  have hstable : (prefixWord ++ tailWord_6672698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672698).length < 2 ^ (prefixWord ++ tailWord_6672698).sum := by decide
  have hdescent : baseEnd_6672698 < baseStart_6672698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672708 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_6672708 : Nat := 118140960795 + 6672708 * 2 ^ 59
def prefixEnd_6672708 : Nat := 4983230072969 + 3 ^ 40 * 6672708 * 2
def baseEnd_6672708 : Nat := 1142102157033794744320927

theorem tailTrace_6672708 : CollatzResearch.WordTrace tailWord_6672708 prefixEnd_6672708 1142102157033794744320927 := by
  unfold tailWord_6672708
  simp only [CollatzResearch.WordTrace]
  refine ⟨121686827354962999321349389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162249103139950665761799185 121686827354962999321349389)
  ·
    refine ⟨45632560258111124745506021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121686827354962999321349389 45632560258111124745506021)
    ·
      refine ⟨8556105048395835889782379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45632560258111124745506021 8556105048395835889782379)
      ·
        refine ⟨12834157572593753834673569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556105048395835889782379 12834157572593753834673569)
        ·
          refine ⟨9625618179445315376005177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12834157572593753834673569 9625618179445315376005177)
          ·
            refine ⟨7219213634583986532003883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9625618179445315376005177 7219213634583986532003883)
            ·
              refine ⟨10828820451875979798005825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219213634583986532003883 10828820451875979798005825)
              ·
                refine ⟨8121615338906984848504369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828820451875979798005825 8121615338906984848504369)
                ·
                  refine ⟨6091211504180238636378277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121615338906984848504369 6091211504180238636378277)
                  ·
                    refine ⟨1142102157033794744320927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091211504180238636378277 1142102157033794744320927)
                    ·
                      rfl

theorem cell23_6672708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_6672708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672708 prefixEnd_6672708 := by exact prefixLift 6672708
  have htrace : WordTrace (prefixWord ++ tailWord_6672708) baseStart_6672708 baseEnd_6672708 := by
    simpa [prefixWord, tailWord_6672708, baseEnd_6672708] using wordTrace_append hprefix tailTrace_6672708
  have hstable : (prefixWord ++ tailWord_6672708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672708).length < 2 ^ (prefixWord ++ tailWord_6672708).sum := by decide
  have hdescent : baseEnd_6672708 < baseStart_6672708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672741 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 1, 3, 2]
def baseStart_6672741 : Nat := 118140960795 + 6672741 * 2 ^ 59
def prefixEnd_6672741 : Nat := 4983230072969 + 3 ^ 40 * 6672741 * 2
def baseEnd_6672741 : Nat := 3426323415962982603850129

theorem tailTrace_6672741 : CollatzResearch.WordTrace tailWord_6672741 prefixEnd_6672741 3426323415962982603850129 := by
  unfold tailWord_6672741
  simp only [CollatzResearch.WordTrace]
  refine ⟨243374858318806445278650077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162249905545870963519100051 243374858318806445278650077)
  ·
    refine ⟨91265571869552416979493779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243374858318806445278650077 91265571869552416979493779)
    ·
      refine ⟨136898357804328625469240669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91265571869552416979493779 136898357804328625469240669)
      ·
        refine ⟨51336884176623234550965251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136898357804328625469240669 51336884176623234550965251)
        ·
          refine ⟨77005326264934851826447877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51336884176623234550965251 77005326264934851826447877)
          ·
            refine ⟨14438498674675284717458977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77005326264934851826447877 14438498674675284717458977)
            ·
              refine ⟨10828874006006463538094233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14438498674675284717458977 10828874006006463538094233)
              ·
                refine ⟨8121655504504847653570675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828874006006463538094233 8121655504504847653570675)
                ·
                  refine ⟨12182483256757271480356013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8121655504504847653570675 12182483256757271480356013)
                  ·
                    refine ⟨4568431221283976805133505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12182483256757271480356013 4568431221283976805133505)
                    ·
                      refine ⟨3426323415962982603850129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568431221283976805133505 3426323415962982603850129)
                      ·
                        rfl

theorem cell23_6672741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_6672741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672741 prefixEnd_6672741 := by exact prefixLift 6672741
  have htrace : WordTrace (prefixWord ++ tailWord_6672741) baseStart_6672741 baseEnd_6672741 := by
    simpa [prefixWord, tailWord_6672741, baseEnd_6672741] using wordTrace_append hprefix tailTrace_6672741
  have hstable : (prefixWord ++ tailWord_6672741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672741).length < 2 ^ (prefixWord ++ tailWord_6672741).sum := by decide
  have hdescent : baseEnd_6672741 < baseStart_6672741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672757 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6672757 : Nat := 118140960795 + 6672757 * 2 ^ 59
def prefixEnd_6672757 : Nat := 4983230072969 + 3 ^ 40 * 6672757 * 2
def baseEnd_6672757 : Nat := 3426331631653454541250055

theorem tailTrace_6672757 : CollatzResearch.WordTrace tailWord_6672757 prefixEnd_6672757 3426331631653454541250055 := by
  unfold tailWord_6672757
  simp only [CollatzResearch.WordTrace]
  refine ⟨243375441886748480011232525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162250294591165653340821683 243375441886748480011232525)
  ·
    refine ⟨91265790707530680004212197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243375441886748480011232525 91265790707530680004212197)
    ·
      refine ⟨17112335757662002500789787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91265790707530680004212197 17112335757662002500789787)
      ·
        refine ⟨25668503636493003751184681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17112335757662002500789787 25668503636493003751184681)
        ·
          refine ⟨19251377727369752813388511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25668503636493003751184681 19251377727369752813388511)
          ·
            refine ⟨28877066591054629220082767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19251377727369752813388511 28877066591054629220082767)
            ·
              refine ⟨43315599886581943830124151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28877066591054629220082767 43315599886581943830124151)
              ·
                refine ⟨64973399829872915745186227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43315599886581943830124151 64973399829872915745186227)
                ·
                  refine ⟨97460099744809373617779341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64973399829872915745186227 97460099744809373617779341)
                  ·
                    refine ⟨36547537404303515106667253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97460099744809373617779341 36547537404303515106667253)
                    ·
                      refine ⟨3426331631653454541250055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36547537404303515106667253 3426331631653454541250055)
                      ·
                        rfl

theorem cell23_6672757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6672757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672757 prefixEnd_6672757 := by exact prefixLift 6672757
  have htrace : WordTrace (prefixWord ++ tailWord_6672757) baseStart_6672757 baseEnd_6672757 := by
    simpa [prefixWord, tailWord_6672757, baseEnd_6672757] using wordTrace_append hprefix tailTrace_6672757
  have hstable : (prefixWord ++ tailWord_6672757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672757).length < 2 ^ (prefixWord ++ tailWord_6672757).sum := by decide
  have hdescent : baseEnd_6672757 < baseStart_6672757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672777 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 7]
def baseStart_6672777 : Nat := 118140960795 + 6672777 * 2 ^ 59
def prefixEnd_6672777 : Nat := 4983230072969 + 3 ^ 40 * 6672777 * 2
def baseEnd_6672777 : Nat := 380704655696282718111107

theorem tailTrace_6672777 : CollatzResearch.WordTrace tailWord_6672777 prefixEnd_6672777 380704655696282718111107 := by
  unfold tailWord_6672777
  simp only [CollatzResearch.WordTrace]
  refine ⟨243376171346676023426960585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162250780897784015617973723 243376171346676023426960585)
  ·
    refine ⟨182532128510007017570220439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243376171346676023426960585 182532128510007017570220439)
    ·
      refine ⟨273798192765010526355330659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182532128510007017570220439 273798192765010526355330659)
      ·
        refine ⟨410697289147515789532995989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273798192765010526355330659 410697289147515789532995989)
        ·
          refine ⟨19251435428789802634359187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 410697289147515789532995989 19251435428789802634359187)
          ·
            refine ⟨28877153143184703951538781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19251435428789802634359187 28877153143184703951538781)
            ·
              refine ⟨10828932428694263981827043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28877153143184703951538781 10828932428694263981827043)
              ·
                refine ⟨16243398643041395972740565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10828932428694263981827043 16243398643041395972740565)
                ·
                  refine ⟨380704655696282718111107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16243398643041395972740565 380704655696282718111107)
                  ·
                    rfl

theorem cell23_6672777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 7].length) (baseStart_6672777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672777 prefixEnd_6672777 := by exact prefixLift 6672777
  have htrace : WordTrace (prefixWord ++ tailWord_6672777) baseStart_6672777 baseEnd_6672777 := by
    simpa [prefixWord, tailWord_6672777, baseEnd_6672777] using wordTrace_append hprefix tailTrace_6672777
  have hstable : (prefixWord ++ tailWord_6672777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672777).length < 2 ^ (prefixWord ++ tailWord_6672777).sum := by decide
  have hdescent : baseEnd_6672777 < baseStart_6672777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672817 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 5]
def baseStart_6672817 : Nat := 118140960795 + 6672817 * 2 ^ 59
def prefixEnd_6672817 : Nat := 4983230072969 + 3 ^ 40 * 6672817 * 2
def baseEnd_6672817 : Nat := 3426362440492724306499779

theorem tailTrace_6672817 : CollatzResearch.WordTrace tailWord_6672817 prefixEnd_6672817 3426362440492724306499779 := by
  unfold tailWord_6672817
  simp only [CollatzResearch.WordTrace]
  refine ⟨243377630266531110258416705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162251753511020740172277803 243377630266531110258416705)
  ·
    refine ⟨182533222699898332693812529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243377630266531110258416705 182533222699898332693812529)
    ·
      refine ⟨136899917024923749520359397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182533222699898332693812529 136899917024923749520359397)
      ·
        refine ⟨25668734442173203035067387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136899917024923749520359397 25668734442173203035067387)
        ·
          refine ⟨38503101663259804552601081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25668734442173203035067387 38503101663259804552601081)
          ·
            refine ⟨28877326247444853414450811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38503101663259804552601081 28877326247444853414450811)
            ·
              refine ⟨43315989371167280121676217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28877326247444853414450811 43315989371167280121676217)
              ·
                refine ⟨32486992028375460091257163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43315989371167280121676217 32486992028375460091257163)
                ·
                  refine ⟨48730488042563190136885745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32486992028375460091257163 48730488042563190136885745)
                  ·
                    refine ⟨36547866031922392602664309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48730488042563190136885745 36547866031922392602664309)
                    ·
                      refine ⟨3426362440492724306499779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36547866031922392602664309 3426362440492724306499779)
                      ·
                        rfl

theorem cell23_6672817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_6672817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672817 prefixEnd_6672817 := by exact prefixLift 6672817
  have htrace : WordTrace (prefixWord ++ tailWord_6672817) baseStart_6672817 baseEnd_6672817 := by
    simpa [prefixWord, tailWord_6672817, baseEnd_6672817] using wordTrace_append hprefix tailTrace_6672817
  have hstable : (prefixWord ++ tailWord_6672817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672817).length < 2 ^ (prefixWord ++ tailWord_6672817).sum := by decide
  have hdescent : baseEnd_6672817 < baseStart_6672817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672828 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 5]
def baseStart_6672828 : Nat := 118140960795 + 6672828 * 2 ^ 59
def prefixEnd_6672828 : Nat := 4983230072969 + 3 ^ 40 * 6672828 * 2
def baseEnd_6672828 : Nat := 380707565419991529273581

theorem tailTrace_6672828 : CollatzResearch.WordTrace tailWord_6672828 prefixEnd_6672828 380707565419991529273581 := by
  unfold tailWord_6672828
  simp only [CollatzResearch.WordTrace]
  refine ⟨121689015734745629568533569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162252020979660839424711425 121689015734745629568533569)
  ·
    refine ⟨91266761801059222176400177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121689015734745629568533569 91266761801059222176400177)
    ·
      refine ⟨68450071350794416632300133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91266761801059222176400177 68450071350794416632300133)
      ·
        refine ⟨12834388378273953118556275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68450071350794416632300133 12834388378273953118556275)
        ·
          refine ⟨19251582567410929677834413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12834388378273953118556275 19251582567410929677834413)
          ·
            refine ⟨7219343462779098629187905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19251582567410929677834413 7219343462779098629187905)
            ·
              refine ⟨5414507597084323971890929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7219343462779098629187905 5414507597084323971890929)
              ·
                refine ⟨4060880697813242978918197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5414507597084323971890929 4060880697813242978918197)
                ·
                  refine ⟨380707565419991529273581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4060880697813242978918197 380707565419991529273581)
                  ·
                    rfl

theorem cell23_6672828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_6672828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672828 prefixEnd_6672828 := by exact prefixLift 6672828
  have htrace : WordTrace (prefixWord ++ tailWord_6672828) baseStart_6672828 baseEnd_6672828 := by
    simpa [prefixWord, tailWord_6672828, baseEnd_6672828] using wordTrace_append hprefix tailTrace_6672828
  have hstable : (prefixWord ++ tailWord_6672828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672828).length < 2 ^ (prefixWord ++ tailWord_6672828).sum := by decide
  have hdescent : baseEnd_6672828 < baseStart_6672828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672837 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_6672837 : Nat := 118140960795 + 6672837 * 2 ^ 59
def prefixEnd_6672837 : Nat := 4983230072969 + 3 ^ 40 * 6672837 * 2
def baseEnd_6672837 : Nat := 1142124236701938076083229

theorem tailTrace_6672837 : CollatzResearch.WordTrace tailWord_6672837 prefixEnd_6672837 1142124236701938076083229 := by
  unfold tailWord_6672837
  simp only [CollatzResearch.WordTrace]
  refine ⟨243378359726458653674144765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162252239817639102449429843 243378359726458653674144765)
  ·
    refine ⟨91266884897421995127804287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243378359726458653674144765 91266884897421995127804287)
    ·
      refine ⟨136900327346132992691706431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91266884897421995127804287 136900327346132992691706431)
      ·
        refine ⟨205350491019199489037559647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136900327346132992691706431 205350491019199489037559647)
        ·
          refine ⟨308025736528799233556339471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205350491019199489037559647 308025736528799233556339471)
          ·
            refine ⟨462038604793198850334509207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308025736528799233556339471 462038604793198850334509207)
            ·
              refine ⟨693057907189798275501763811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462038604793198850334509207 693057907189798275501763811)
              ·
                refine ⟨1039586860784697413252645717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693057907189798275501763811 1039586860784697413252645717)
                ·
                  refine ⟨6091329262410336405777221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1039586860784697413252645717 6091329262410336405777221)
                  ·
                    refine ⟨1142124236701938076083229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091329262410336405777221 1142124236701938076083229)
                    ·
                      rfl

theorem cell23_6672837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_6672837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672837 prefixEnd_6672837 := by exact prefixLift 6672837
  have htrace : WordTrace (prefixWord ++ tailWord_6672837) baseStart_6672837 baseEnd_6672837 := by
    simpa [prefixWord, tailWord_6672837, baseEnd_6672837] using wordTrace_append hprefix tailTrace_6672837
  have hstable : (prefixWord ++ tailWord_6672837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672837).length < 2 ^ (prefixWord ++ tailWord_6672837).sum := by decide
  have hdescent : baseEnd_6672837 < baseStart_6672837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672847 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_6672847 : Nat := 118140960795 + 6672847 * 2 ^ 59
def prefixEnd_6672847 : Nat := 4983230072969 + 3 ^ 40 * 6672847 * 2
def baseEnd_6672847 : Nat := 3426377844912359189124641

theorem tailTrace_6672847 : CollatzResearch.WordTrace tailWord_6672847 prefixEnd_6672847 3426377844912359189124641 := by
  unfold tailWord_6672847
  simp only [CollatzResearch.WordTrace]
  refine ⟨243378724456422425382008795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162252482970948283588005863 243378724456422425382008795)
  ·
    refine ⟨365068086684633638073013193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243378724456422425382008795 365068086684633638073013193)
    ·
      refine ⟨273801065013475228554759895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365068086684633638073013193 273801065013475228554759895)
      ·
        refine ⟨410701597520212842832139843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273801065013475228554759895 410701597520212842832139843)
        ·
          refine ⟨616052396280319264248209765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410701597520212842832139843 616052396280319264248209765)
          ·
            refine ⟨115509824302559862046539331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 616052396280319264248209765 115509824302559862046539331)
            ·
              refine ⟨173264736453839793069808997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115509824302559862046539331 173264736453839793069808997)
              ·
                refine ⟨32487138085094961200589187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173264736453839793069808997 32487138085094961200589187)
                ·
                  refine ⟨48730707127642441800883781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32487138085094961200589187 48730707127642441800883781)
                  ·
                    refine ⟨9137007586432957837665709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48730707127642441800883781 9137007586432957837665709)
                    ·
                      refine ⟨3426377844912359189124641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9137007586432957837665709 3426377844912359189124641)
                      ·
                        rfl

theorem cell23_6672847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_6672847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672847 prefixEnd_6672847 := by exact prefixLift 6672847
  have htrace : WordTrace (prefixWord ++ tailWord_6672847) baseStart_6672847 baseEnd_6672847 := by
    simpa [prefixWord, tailWord_6672847, baseEnd_6672847] using wordTrace_append hprefix tailTrace_6672847
  have hstable : (prefixWord ++ tailWord_6672847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672847).length < 2 ^ (prefixWord ++ tailWord_6672847).sum := by decide
  have hdescent : baseEnd_6672847 < baseStart_6672847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672927 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 3, 6]
def baseStart_6672927 : Nat := 118140960795 + 6672927 * 2 ^ 59
def prefixEnd_6672927 : Nat := 4983230072969 + 3 ^ 40 * 6672927 * 2
def baseEnd_6672927 : Nat := 1142139641121572958708091

theorem tailTrace_6672927 : CollatzResearch.WordTrace tailWord_6672927 prefixEnd_6672927 1142139641121572958708091 := by
  unfold tailWord_6672927
  simp only [CollatzResearch.WordTrace]
  refine ⟨243381642296132599044921035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162254428197421732696614023 243381642296132599044921035)
  ·
    refine ⟨365072463444198898567381553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243381642296132599044921035 365072463444198898567381553)
    ·
      refine ⟨273804347583149173925536165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365072463444198898567381553 273804347583149173925536165)
      ·
        refine ⟨51338315171840470111038031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273804347583149173925536165 51338315171840470111038031)
        ·
          refine ⟨77007472757760705166557047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51338315171840470111038031 77007472757760705166557047)
          ·
            refine ⟨115511209136641057749835571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77007472757760705166557047 115511209136641057749835571)
            ·
              refine ⟨173266813704961586624753357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115511209136641057749835571 173266813704961586624753357)
              ·
                refine ⟨64975055139360594984282509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173266813704961586624753357 64975055139360594984282509)
                ·
                  refine ⟨24365645677260223119105941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64975055139360594984282509 24365645677260223119105941)
                  ·
                    refine ⟨1142139641121572958708091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24365645677260223119105941 1142139641121572958708091)
                    ·
                      rfl

theorem cell23_6672927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_6672927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672927 prefixEnd_6672927 := by exact prefixLift 6672927
  have htrace : WordTrace (prefixWord ++ tailWord_6672927) baseStart_6672927 baseEnd_6672927 := by
    simpa [prefixWord, tailWord_6672927, baseEnd_6672927] using wordTrace_append hprefix tailTrace_6672927
  have hstable : (prefixWord ++ tailWord_6672927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672927).length < 2 ^ (prefixWord ++ tailWord_6672927).sum := by decide
  have hdescent : baseEnd_6672927 < baseStart_6672927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672938 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_6672938 : Nat := 118140960795 + 6672938 * 2 ^ 59
def prefixEnd_6672938 : Nat := 4983230072969 + 3 ^ 40 * 6672938 * 2
def baseEnd_6672938 : Nat := 3426424571651918333086723

theorem tailTrace_6672938 : CollatzResearch.WordTrace tailWord_6672938 prefixEnd_6672938 3426424571651918333086723 := by
  unfold tailWord_6672938
  simp only [CollatzResearch.WordTrace]
  refine ⟨60845510874773186980892867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162254695666061831949047645 60845510874773186980892867)
  ·
    refine ⟨91268266312159780471339301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60845510874773186980892867 91268266312159780471339301)
    ·
      refine ⟨17112799933529958838376119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91268266312159780471339301 17112799933529958838376119)
      ·
        refine ⟨25669199900294938257564179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17112799933529958838376119 25669199900294938257564179)
        ·
          refine ⟨38503799850442407386346269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25669199900294938257564179 38503799850442407386346269)
          ·
            refine ⟨14438924943915902769879851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38503799850442407386346269 14438924943915902769879851)
            ·
              refine ⟨21658387415873854154819777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14438924943915902769879851 21658387415873854154819777)
              ·
                refine ⟨16243790561905390616114833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21658387415873854154819777 16243790561905390616114833)
                ·
                  refine ⟨12182842921429042962086125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16243790561905390616114833 12182842921429042962086125)
                  ·
                    refine ⟨4568566095535891110782297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12182842921429042962086125 4568566095535891110782297)
                    ·
                      refine ⟨3426424571651918333086723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568566095535891110782297 3426424571651918333086723)
                      ·
                        rfl

theorem cell23_6672938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_6672938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672938 prefixEnd_6672938 := by exact prefixLift 6672938
  have htrace : WordTrace (prefixWord ++ tailWord_6672938) baseStart_6672938 baseEnd_6672938 := by
    simpa [prefixWord, tailWord_6672938, baseEnd_6672938] using wordTrace_append hprefix tailTrace_6672938
  have hstable : (prefixWord ++ tailWord_6672938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672938).length < 2 ^ (prefixWord ++ tailWord_6672938).sum := by decide
  have hdescent : baseEnd_6672938 < baseStart_6672938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672944 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 4, 4]
def baseStart_6672944 : Nat := 118140960795 + 6672944 * 2 ^ 59
def prefixEnd_6672944 : Nat := 4983230072969 + 3 ^ 40 * 6672944 * 2
def baseEnd_6672944 : Nat := 1142142550845281769870565

theorem tailTrace_6672944 : CollatzResearch.WordTrace tailWord_6672944 prefixEnd_6672944 1142142550845281769870565 := by
  unfold tailWord_6672944
  simp only [CollatzResearch.WordTrace]
  refine ⟨121691131168535505474144943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162254841558047340632193257 121691131168535505474144943)
  ·
    refine ⟨182536696752803258211217415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121691131168535505474144943 182536696752803258211217415)
    ·
      refine ⟨273805045129204887316826123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182536696752803258211217415 273805045129204887316826123)
      ·
        refine ⟨410707567693807330975239185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273805045129204887316826123 410707567693807330975239185)
        ·
          refine ⟨308030675770355498231429389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410707567693807330975239185 308030675770355498231429389)
          ·
            refine ⟨115511503413883311836786021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308030675770355498231429389 115511503413883311836786021)
            ·
              refine ⟨21658406890103120969397379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115511503413883311836786021 21658406890103120969397379)
              ·
                refine ⟨32487610335154681454096069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21658406890103120969397379 32487610335154681454096069)
                ·
                  refine ⟨6091426937841502772643013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32487610335154681454096069 6091426937841502772643013)
                  ·
                    refine ⟨1142142550845281769870565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6091426937841502772643013 1142142550845281769870565)
                    ·
                      rfl

theorem cell23_6672944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_6672944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672944 prefixEnd_6672944 := by exact prefixLift 6672944
  have htrace : WordTrace (prefixWord ++ tailWord_6672944) baseStart_6672944 baseEnd_6672944 := by
    simpa [prefixWord, tailWord_6672944, baseEnd_6672944] using wordTrace_append hprefix tailTrace_6672944
  have hstable : (prefixWord ++ tailWord_6672944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672944).length < 2 ^ (prefixWord ++ tailWord_6672944).sum := by decide
  have hdescent : baseEnd_6672944 < baseStart_6672944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672947 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_6672947 : Nat := 118140960795 + 6672947 * 2 ^ 59
def prefixEnd_6672947 : Nat := 4983230072969 + 3 ^ 40 * 6672947 * 2
def baseEnd_6672947 : Nat := 3426429192977808797874181

theorem tailTrace_6672947 : CollatzResearch.WordTrace tailWord_6672947 prefixEnd_6672947 3426429192977808797874181 := by
  unfold tailWord_6672947
  simp only [CollatzResearch.WordTrace]
  refine ⟨243382371756060142460649095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162254914504040094973766063 243382371756060142460649095)
  ·
    refine ⟨365073557634090213690973643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243382371756060142460649095 365073557634090213690973643)
    ·
      refine ⟨547610336451135320536460465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365073557634090213690973643 547610336451135320536460465)
      ·
        refine ⟨410707752338351490402345349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547610336451135320536460465 410707752338351490402345349)
        ·
          refine ⟨77007703563440904450439753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410707752338351490402345349 77007703563440904450439753)
          ·
            refine ⟨57755777672580678337829815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77007703563440904450439753 57755777672580678337829815)
            ·
              refine ⟨86633666508871017506744723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57755777672580678337829815 86633666508871017506744723)
              ·
                refine ⟨129950499763306526260117085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86633666508871017506744723 129950499763306526260117085)
                ·
                  refine ⟨48731437411239947347543907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129950499763306526260117085 48731437411239947347543907)
                  ·
                    refine ⟨73097156116859921021315861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48731437411239947347543907 73097156116859921021315861)
                    ·
                      refine ⟨3426429192977808797874181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73097156116859921021315861 3426429192977808797874181)
                      ·
                        rfl

theorem cell23_6672947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_6672947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672947 prefixEnd_6672947 := by exact prefixLift 6672947
  have htrace : WordTrace (prefixWord ++ tailWord_6672947) baseStart_6672947 baseEnd_6672947 := by
    simpa [prefixWord, tailWord_6672947, baseEnd_6672947] using wordTrace_append hprefix tailTrace_6672947
  have hstable : (prefixWord ++ tailWord_6672947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672947).length < 2 ^ (prefixWord ++ tailWord_6672947).sum := by decide
  have hdescent : baseEnd_6672947 < baseStart_6672947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672954 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_6672954 : Nat := 118140960795 + 6672954 * 2 ^ 59
def prefixEnd_6672954 : Nat := 4983230072969 + 3 ^ 40 * 6672954 * 2
def baseEnd_6672954 : Nat := 3426432787342390270486649

theorem tailTrace_6672954 : CollatzResearch.WordTrace tailWord_6672954 prefixEnd_6672954 3426432787342390270486649 := by
  unfold tailWord_6672954
  simp only [CollatzResearch.WordTrace]
  refine ⟨60845656766758695664038479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162255084711356521770769277 60845656766758695664038479)
  ·
    refine ⟨91268485150138043496057719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60845656766758695664038479 91268485150138043496057719)
    ·
      refine ⟨136902727725207065244086579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91268485150138043496057719 136902727725207065244086579)
      ·
        refine ⟨205354091587810597866129869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136902727725207065244086579 205354091587810597866129869)
        ·
          refine ⟨77007784345428974199798701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205354091587810597866129869 77007784345428974199798701)
          ·
            refine ⟨28877919129535865324924513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77007784345428974199798701 28877919129535865324924513)
            ·
              refine ⟨21658439347151898993693385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28877919129535865324924513 21658439347151898993693385)
              ·
                refine ⟨16243829510363924245270039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21658439347151898993693385 16243829510363924245270039)
                ·
                  refine ⟨24365744265545886367905059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16243829510363924245270039 24365744265545886367905059)
                  ·
                    refine ⟨36548616398318829551857589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24365744265545886367905059 36548616398318829551857589)
                    ·
                      refine ⟨3426432787342390270486649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36548616398318829551857589 3426432787342390270486649)
                      ·
                        rfl

theorem cell23_6672954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_6672954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672954 prefixEnd_6672954 := by exact prefixLift 6672954
  have htrace : WordTrace (prefixWord ++ tailWord_6672954) baseStart_6672954 baseEnd_6672954 := by
    simpa [prefixWord, tailWord_6672954, baseEnd_6672954] using wordTrace_append hprefix tailTrace_6672954
  have hstable : (prefixWord ++ tailWord_6672954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672954).length < 2 ^ (prefixWord ++ tailWord_6672954).sum := by decide
  have hdescent : baseEnd_6672954 < baseStart_6672954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672971 : List Nat := [1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 3]
def baseStart_6672971 : Nat := 118140960795 + 6672971 * 2 ^ 59
def prefixEnd_6672971 : Nat := 4983230072969 + 3 ^ 40 * 6672971 * 2
def baseEnd_6672971 : Nat := 3426441516513516703974071

theorem tailTrace_6672971 : CollatzResearch.WordTrace tailWord_6672971 prefixEnd_6672971 3426441516513516703974071 := by
  unfold tailWord_6672971
  simp only [CollatzResearch.WordTrace]
  refine ⟨243383247107973194559522767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162255498071982129706348511 243383247107973194559522767)
  ·
    refine ⟨365074870661959791839284151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243383247107973194559522767 365074870661959791839284151)
    ·
      refine ⟨547612305992939687758926227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365074870661959791839284151 547612305992939687758926227)
      ·
        refine ⟨821418458989409531638389341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547612305992939687758926227 821418458989409531638389341)
        ·
          refine ⟨308031922121028574364396003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 821418458989409531638389341 308031922121028574364396003)
          ·
            refine ⟨462047883181542861546594005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308031922121028574364396003 462047883181542861546594005)
            ·
              refine ⟨10829247262067410817498297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 462047883181542861546594005 10829247262067410817498297)
              ·
                refine ⟨8121935446550558113123723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829247262067410817498297 8121935446550558113123723)
                ·
                  refine ⟨12182903169825837169685585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8121935446550558113123723 12182903169825837169685585)
                  ·
                    refine ⟨9137177377369377877264189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12182903169825837169685585 9137177377369377877264189)
                    ·
                      refine ⟨3426441516513516703974071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9137177377369377877264189 3426441516513516703974071)
                      ·
                        rfl

theorem cell23_6672971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 2, 3].length) (baseStart_6672971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672971 prefixEnd_6672971 := by exact prefixLift 6672971
  have htrace : WordTrace (prefixWord ++ tailWord_6672971) baseStart_6672971 baseEnd_6672971 := by
    simpa [prefixWord, tailWord_6672971, baseEnd_6672971] using wordTrace_append hprefix tailTrace_6672971
  have hstable : (prefixWord ++ tailWord_6672971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672971).length < 2 ^ (prefixWord ++ tailWord_6672971).sum := by decide
  have hdescent : baseEnd_6672971 < baseStart_6672971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672984 : List Nat := [2, 1, 2, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_6672984 : Nat := 118140960795 + 6672984 * 2 ^ 59
def prefixEnd_6672984 : Nat := 4983230072969 + 3 ^ 40 * 6672984 * 2
def baseEnd_6672984 : Nat := 3426448191762025153111511

theorem tailTrace_6672984 : CollatzResearch.WordTrace tailWord_6672984 prefixEnd_6672984 3426448191762025153111511 := by
  unfold tailWord_6672984
  simp only [CollatzResearch.WordTrace]
  refine ⟨121691860628463048889873003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162255814171284065186497337 121691860628463048889873003)
  ·
    refine ⟨182537790942694573334809505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121691860628463048889873003 182537790942694573334809505)
    ·
      refine ⟨136903343207020930001107129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182537790942694573334809505 136903343207020930001107129)
      ·
        refine ⟨102677507405265697500830347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136903343207020930001107129 102677507405265697500830347)
        ·
          refine ⟨154016261107898546251245521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102677507405265697500830347 154016261107898546251245521)
          ·
            refine ⟨115512195830923909688434141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154016261107898546251245521 115512195830923909688434141)
            ·
              refine ⟨43317073436596466133162803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115512195830923909688434141 43317073436596466133162803)
              ·
                refine ⟨64975610154894699199744205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43317073436596466133162803 64975610154894699199744205)
                ·
                  refine ⟨24365853808085512199904077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64975610154894699199744205 24365853808085512199904077)
                  ·
                    refine ⟨9137195178032067074964029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24365853808085512199904077 9137195178032067074964029)
                    ·
                      refine ⟨3426448191762025153111511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9137195178032067074964029 3426448191762025153111511)
                      ·
                        rfl

theorem cell23_6672984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_6672984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672984 prefixEnd_6672984 := by exact prefixLift 6672984
  have htrace : WordTrace (prefixWord ++ tailWord_6672984) baseStart_6672984 baseEnd_6672984 := by
    simpa [prefixWord, tailWord_6672984, baseEnd_6672984] using wordTrace_append hprefix tailTrace_6672984
  have hstable : (prefixWord ++ tailWord_6672984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672984).length < 2 ^ (prefixWord ++ tailWord_6672984).sum := by decide
  have hdescent : baseEnd_6672984 < baseStart_6672984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6672988 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_6672988 : Nat := 118140960795 + 6672988 * 2 ^ 59
def prefixEnd_6672988 : Nat := 4983230072969 + 3 ^ 40 * 6672988 * 2
def baseEnd_6672988 : Nat := 3426450245684643137461493

theorem tailTrace_6672988 : CollatzResearch.WordTrace tailWord_6672988 prefixEnd_6672988 3426450245684643137461493 := by
  unfold tailWord_6672988
  simp only [CollatzResearch.WordTrace]
  refine ⟨121691933574455803231445809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162255911432607737641927745 121691933574455803231445809)
  ·
    refine ⟨91268950180841852423584357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121691933574455803231445809 91268950180841852423584357)
    ·
      refine ⟨17112928158907847329422067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91268950180841852423584357 17112928158907847329422067)
      ·
        refine ⟨25669392238361770994133101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17112928158907847329422067 25669392238361770994133101)
        ·
          refine ⟨9626022089385664122799913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25669392238361770994133101 9626022089385664122799913)
          ·
            refine ⟨7219516567039248092099935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9626022089385664122799913 7219516567039248092099935)
            ·
              refine ⟨10829274850558872138149903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219516567039248092099935 10829274850558872138149903)
              ·
                refine ⟨16243912275838308207224855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10829274850558872138149903 16243912275838308207224855)
                ·
                  refine ⟨24365868413757462310837283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16243912275838308207224855 24365868413757462310837283)
                  ·
                    refine ⟨36548802620636193466255925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24365868413757462310837283 36548802620636193466255925)
                    ·
                      refine ⟨3426450245684643137461493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36548802620636193466255925 3426450245684643137461493)
                      ·
                        rfl

theorem cell23_6672988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_6672988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6672988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6672988 prefixEnd_6672988 := by exact prefixLift 6672988
  have htrace : WordTrace (prefixWord ++ tailWord_6672988) baseStart_6672988 baseEnd_6672988 := by
    simpa [prefixWord, tailWord_6672988, baseEnd_6672988] using wordTrace_append hprefix tailTrace_6672988
  have hstable : (prefixWord ++ tailWord_6672988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6672988).length < 2 ^ (prefixWord ++ tailWord_6672988).sum := by decide
  have hdescent : baseEnd_6672988 < baseStart_6672988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6672988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673028 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_6673028 : Nat := 118140960795 + 6673028 * 2 ^ 59
def prefixEnd_6673028 : Nat := 4983230072969 + 3 ^ 40 * 6673028 * 2
def baseEnd_6673028 : Nat := 3426470784910822980961309

theorem tailTrace_6673028 : CollatzResearch.WordTrace tailWord_6673028 prefixEnd_6673028 3426470784910822980961309 := by
  unfold tailWord_6673028
  simp only [CollatzResearch.WordTrace]
  refine ⟨121692663034383346647173869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162256884045844462196231825 121692663034383346647173869)
  ·
    refine ⟨45634748637893754992690201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121692663034383346647173869 45634748637893754992690201)
    ·
      refine ⟨34226061478420316244517651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45634748637893754992690201 34226061478420316244517651)
      ·
        refine ⟨51339092217630474366776477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34226061478420316244517651 51339092217630474366776477)
        ·
          refine ⟨19252159581611427887541179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51339092217630474366776477 19252159581611427887541179)
          ·
            refine ⟨28878239372417141831311769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19252159581611427887541179 28878239372417141831311769)
            ·
              refine ⟨21658679529312856373483827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28878239372417141831311769 21658679529312856373483827)
              ·
                refine ⟨32488019293969284560225741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21658679529312856373483827 32488019293969284560225741)
                ·
                  refine ⟨12183007235238481710084653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32488019293969284560225741 12183007235238481710084653)
                  ·
                    refine ⟨4568627713214430641281745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12183007235238481710084653 4568627713214430641281745)
                    ·
                      refine ⟨3426470784910822980961309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568627713214430641281745 3426470784910822980961309)
                      ·
                        rfl

theorem cell23_6673028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_6673028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673028 prefixEnd_6673028 := by exact prefixLift 6673028
  have htrace : WordTrace (prefixWord ++ tailWord_6673028) baseStart_6673028 baseEnd_6673028 := by
    simpa [prefixWord, tailWord_6673028, baseEnd_6673028] using wordTrace_append hprefix tailTrace_6673028
  have hstable : (prefixWord ++ tailWord_6673028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673028).length < 2 ^ (prefixWord ++ tailWord_6673028).sum := by decide
  have hdescent : baseEnd_6673028 < baseStart_6673028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673098 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_6673098 : Nat := 118140960795 + 6673098 * 2 ^ 59
def prefixEnd_6673098 : Nat := 4983230072969 + 3 ^ 40 * 6673098 * 2
def baseEnd_6673098 : Nat := 380722969839626411898443

theorem tailTrace_6673098 : CollatzResearch.WordTrace tailWord_6673098 prefixEnd_6673098 380722969839626411898443 := by
  unfold tailWord_6673098
  simp only [CollatzResearch.WordTrace]
  refine ⟨60846969794628273812348987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162258586119008730166263965 60846969794628273812348987)
  ·
    refine ⟨91270454691942410718523481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60846969794628273812348987 91270454691942410718523481)
    ·
      refine ⟨68452841018956808038892611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91270454691942410718523481 68452841018956808038892611)
      ·
        refine ⟨102679261528435212058338917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68452841018956808038892611 102679261528435212058338917)
        ·
          refine ⟨19252361536581602260938547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102679261528435212058338917 19252361536581602260938547)
          ·
            refine ⟨28878542304872403391407821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19252361536581602260938547 28878542304872403391407821)
            ·
              refine ⟨10829453364327151271777933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28878542304872403391407821 10829453364327151271777933)
              ·
                refine ⟨4061045011622681726916725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10829453364327151271777933 4061045011622681726916725)
                ·
                  refine ⟨380722969839626411898443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4061045011622681726916725 380722969839626411898443)
                  ·
                    rfl

theorem cell23_6673098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_6673098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673098 prefixEnd_6673098 := by exact prefixLift 6673098
  have htrace : WordTrace (prefixWord ++ tailWord_6673098) baseStart_6673098 baseEnd_6673098 := by
    simpa [prefixWord, tailWord_6673098, baseEnd_6673098] using wordTrace_append hprefix tailTrace_6673098
  have hstable : (prefixWord ++ tailWord_6673098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673098).length < 2 ^ (prefixWord ++ tailWord_6673098).sum := by decide
  have hdescent : baseEnd_6673098 < baseStart_6673098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673111 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 2, 5]
def baseStart_6673111 : Nat := 118140960795 + 6673111 * 2 ^ 59
def prefixEnd_6673111 : Nat := 4983230072969 + 3 ^ 40 * 6673111 * 2
def baseEnd_6673111 : Nat := 1142171134601715385407809

theorem tailTrace_6673111 : CollatzResearch.WordTrace tailWord_6673111 prefixEnd_6673111 1142171134601715385407809 := by
  unfold tailWord_6673111
  simp only [CollatzResearch.WordTrace]
  refine ⟨243388353327465998469619187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162258902218310665646412791 243388353327465998469619187)
  ·
    refine ⟨365082529991198997704428781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243388353327465998469619187 365082529991198997704428781)
    ·
      refine ⟨136905948746699624139160793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365082529991198997704428781 136905948746699624139160793)
      ·
        refine ⟨102679461560024718104370595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136905948746699624139160793 102679461560024718104370595)
        ·
          refine ⟨154019192340037077156555893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102679461560024718104370595 154019192340037077156555893)
          ·
            refine ⟨14439299281878475983427115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154019192340037077156555893 14439299281878475983427115)
            ·
              refine ⟨21658948922817713975140673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14439299281878475983427115 21658948922817713975140673)
              ·
                refine ⟨16244211692113285481355505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21658948922817713975140673 16244211692113285481355505)
                ·
                  refine ⟨12183158769084964111016629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16244211692113285481355505 12183158769084964111016629)
                  ·
                    refine ⟨1142171134601715385407809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12183158769084964111016629 1142171134601715385407809)
                    ·
                      rfl

theorem cell23_6673111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_6673111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673111 prefixEnd_6673111 := by exact prefixLift 6673111
  have htrace : WordTrace (prefixWord ++ tailWord_6673111) baseStart_6673111 baseEnd_6673111 := by
    simpa [prefixWord, tailWord_6673111, baseEnd_6673111] using wordTrace_append hprefix tailTrace_6673111
  have hstable : (prefixWord ++ tailWord_6673111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673111).length < 2 ^ (prefixWord ++ tailWord_6673111).sum := by decide
  have hdescent : baseEnd_6673111 < baseStart_6673111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673121 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6673121 : Nat := 118140960795 + 6673121 * 2 ^ 59
def prefixEnd_6673121 : Nat := 4983230072969 + 3 ^ 40 * 6673121 * 2
def baseEnd_6673121 : Nat := 3426518538611691117098381

theorem tailTrace_6673121 : CollatzResearch.WordTrace tailWord_6673121 prefixEnd_6673121 3426518538611691117098381 := by
  unfold tailWord_6673121
  simp only [CollatzResearch.WordTrace]
  refine ⟨243388718057429770177483217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162259145371619846784988811 243388718057429770177483217)
  ·
    refine ⟨182541538543072327633112413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243388718057429770177483217 182541538543072327633112413)
    ·
      refine ⟨68453076953652122862417155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182541538543072327633112413 68453076953652122862417155)
      ·
        refine ⟨102679615430478184293625733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68453076953652122862417155 102679615430478184293625733)
        ·
          refine ⟨19252427893214659555054825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102679615430478184293625733 19252427893214659555054825)
          ·
            refine ⟨14439320919910994666291119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19252427893214659555054825 14439320919910994666291119)
            ·
              refine ⟨21658981379866491999436679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14439320919910994666291119 21658981379866491999436679)
              ·
                refine ⟨32488472069799737999155019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21658981379866491999436679 32488472069799737999155019)
                ·
                  refine ⟨48732708104699606998732529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32488472069799737999155019 48732708104699606998732529)
                  ·
                    refine ⟨36549531078524705249049397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48732708104699606998732529 36549531078524705249049397)
                    ·
                      refine ⟨3426518538611691117098381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36549531078524705249049397 3426518538611691117098381)
                      ·
                        rfl

theorem cell23_6673121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6673121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673121 prefixEnd_6673121 := by exact prefixLift 6673121
  have htrace : WordTrace (prefixWord ++ tailWord_6673121) baseStart_6673121 baseEnd_6673121 := by
    simpa [prefixWord, tailWord_6673121, baseEnd_6673121] using wordTrace_append hprefix tailTrace_6673121
  have hstable : (prefixWord ++ tailWord_6673121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673121).length < 2 ^ (prefixWord ++ tailWord_6673121).sum := by decide
  have hdescent : baseEnd_6673121 < baseStart_6673121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673131 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 1, 6, 2]
def baseStart_6673131 : Nat := 118140960795 + 6673131 * 2 ^ 59
def prefixEnd_6673131 : Nat := 4983230072969 + 3 ^ 40 * 6673131 * 2
def baseEnd_6673131 : Nat := 3426523673418236077973335

theorem tailTrace_6673131 : CollatzResearch.WordTrace tailWord_6673131 prefixEnd_6673131 3426523673418236077973335 := by
  unfold tailWord_6673131
  simp only [CollatzResearch.WordTrace]
  refine ⟨243389082787393541885347247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162259388524929027923564831 243389082787393541885347247)
  ·
    refine ⟨365083624181090312828020871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243389082787393541885347247 365083624181090312828020871)
    ·
      refine ⟨547625436271635469242031307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365083624181090312828020871 547625436271635469242031307)
      ·
        refine ⟨821438154407453203863046961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547625436271635469242031307 821438154407453203863046961)
        ·
          refine ⟨616078615805589902897285221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821438154407453203863046961 616078615805589902897285221)
          ·
            refine ⟨115514740463548106793240979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 616078615805589902897285221 115514740463548106793240979)
            ·
              refine ⟨173272110695322160189861469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115514740463548106793240979 173272110695322160189861469)
              ·
                refine ⟨64977041510745810071198051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173272110695322160189861469 64977041510745810071198051)
                ·
                  refine ⟨97465562266118715106797077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64977041510745810071198051 97465562266118715106797077)
                  ·
                    refine ⟨4568698231224314770631113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97465562266118715106797077 4568698231224314770631113)
                    ·
                      refine ⟨3426523673418236077973335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568698231224314770631113 3426523673418236077973335)
                      ·
                        rfl

theorem cell23_6673131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 6, 2].length) (baseStart_6673131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673131 prefixEnd_6673131 := by exact prefixLift 6673131
  have htrace : WordTrace (prefixWord ++ tailWord_6673131) baseStart_6673131 baseEnd_6673131 := by
    simpa [prefixWord, tailWord_6673131, baseEnd_6673131] using wordTrace_append hprefix tailTrace_6673131
  have hstable : (prefixWord ++ tailWord_6673131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673131).length < 2 ^ (prefixWord ++ tailWord_6673131).sum := by decide
  have hdescent : baseEnd_6673131 < baseStart_6673131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673148 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_6673148 : Nat := 118140960795 + 6673148 * 2 ^ 59
def prefixEnd_6673148 : Nat := 4983230072969 + 3 ^ 40 * 6673148 * 2
def baseEnd_6673148 : Nat := 3426532402589362511460757

theorem tailTrace_6673148 : CollatzResearch.WordTrace tailWord_6673148 prefixEnd_6673148 3426532402589362511460757 := by
  unfold tailWord_6673148
  simp only [CollatzResearch.WordTrace]
  refine ⟨121694851414165976894358049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162259801885554635859144065 121694851414165976894358049)
  ·
    refine ⟨91271138560624482670768537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121694851414165976894358049 91271138560624482670768537)
    ·
      refine ⟨68453353920468362003076403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91271138560624482670768537 68453353920468362003076403)
      ·
        refine ⟨102680030880702543004614605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68453353920468362003076403 102680030880702543004614605)
        ·
          refine ⟨38505011580263453626730477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102680030880702543004614605 38505011580263453626730477)
          ·
            refine ⟨14439379342598795110023929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38505011580263453626730477 14439379342598795110023929)
            ·
              refine ⟨10829534506949096332517947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14439379342598795110023929 10829534506949096332517947)
              ·
                refine ⟨16244301760423644498776921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10829534506949096332517947 16244301760423644498776921)
                ·
                  refine ⟨12183226320317733374082691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16244301760423644498776921 12183226320317733374082691)
                  ·
                    refine ⟨18274839480476600061124037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12183226320317733374082691 18274839480476600061124037)
                    ·
                      refine ⟨3426532402589362511460757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18274839480476600061124037 3426532402589362511460757)
                      ·
                        rfl

theorem cell23_6673148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_6673148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673148 prefixEnd_6673148 := by exact prefixLift 6673148
  have htrace : WordTrace (prefixWord ++ tailWord_6673148) baseStart_6673148 baseEnd_6673148 := by
    simpa [prefixWord, tailWord_6673148, baseEnd_6673148] using wordTrace_append hprefix tailTrace_6673148
  have hstable : (prefixWord ++ tailWord_6673148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673148).length < 2 ^ (prefixWord ++ tailWord_6673148).sum := by decide
  have hdescent : baseEnd_6673148 < baseStart_6673148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673171 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 6]
def baseStart_6673171 : Nat := 118140960795 + 6673171 * 2 ^ 59
def prefixEnd_6673171 : Nat := 4983230072969 + 3 ^ 40 * 6673171 * 2
def baseEnd_6673171 : Nat := 380727134738268435719239

theorem tailTrace_6673171 : CollatzResearch.WordTrace tailWord_6673171 prefixEnd_6673171 380727134738268435719239 := by
  unfold tailWord_6673171
  simp only [CollatzResearch.WordTrace]
  refine ⟨243390541707248628716803367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162260361138165752477868911 243390541707248628716803367)
  ·
    refine ⟨365085812560872943075205051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243390541707248628716803367 365085812560872943075205051)
    ·
      refine ⟨547628718841309414612807577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365085812560872943075205051 547628718841309414612807577)
      ·
        refine ⟨410721539130982060959605683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547628718841309414612807577 410721539130982060959605683)
        ·
          refine ⟨616082308696473091439408525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410721539130982060959605683 616082308696473091439408525)
          ·
            refine ⟨231030865761177409289778197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 616082308696473091439408525 231030865761177409289778197)
            ·
              refine ⟨10829571832555191060458353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 231030865761177409289778197 10829571832555191060458353)
              ·
                refine ⟨8122178874416393295343765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829571832555191060458353 8122178874416393295343765)
                ·
                  refine ⟨380727134738268435719239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8122178874416393295343765 380727134738268435719239)
                  ·
                    rfl

theorem cell23_6673171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 6].length) (baseStart_6673171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673171 prefixEnd_6673171 := by exact prefixLift 6673171
  have htrace : WordTrace (prefixWord ++ tailWord_6673171) baseStart_6673171 baseEnd_6673171 := by
    simpa [prefixWord, tailWord_6673171, baseEnd_6673171] using wordTrace_append hprefix tailTrace_6673171
  have hstable : (prefixWord ++ tailWord_6673171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673171).length < 2 ^ (prefixWord ++ tailWord_6673171).sum := by decide
  have hdescent : baseEnd_6673171 < baseStart_6673171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673201 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 3, 5]
def baseStart_6673201 : Nat := 118140960795 + 6673201 * 2 ^ 59
def prefixEnd_6673201 : Nat := 4983230072969 + 3 ^ 40 * 6673201 * 2
def baseEnd_6673201 : Nat := 1142186539021350268032671

theorem tailTrace_6673201 : CollatzResearch.WordTrace tailWord_6673201 prefixEnd_6673201 1142186539021350268032671 := by
  unfold tailWord_6673201
  simp only [CollatzResearch.WordTrace]
  refine ⟨243391635897139943840395457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162261090598093295893596971 243391635897139943840395457)
  ·
    refine ⟨182543726922854957880296593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243391635897139943840395457 182543726922854957880296593)
    ·
      refine ⟨136907795192141218410222445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182543726922854957880296593 136907795192141218410222445)
      ·
        refine ⟨51340423197052956903833417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136907795192141218410222445 51340423197052956903833417)
        ·
          refine ⟨38505317397789717677875063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51340423197052956903833417 38505317397789717677875063)
          ·
            refine ⟨57757976096684576516812595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38505317397789717677875063 57757976096684576516812595)
            ·
              refine ⟨86636964145026864775218893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57757976096684576516812595 86636964145026864775218893)
              ·
                refine ⟨32488861554385074290707085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86636964145026864775218893 32488861554385074290707085)
                ·
                  refine ⟨12183323082894402859015157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32488861554385074290707085 12183323082894402859015157)
                  ·
                    refine ⟨1142186539021350268032671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12183323082894402859015157 1142186539021350268032671)
                    ·
                      rfl

theorem cell23_6673201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 5].length) (baseStart_6673201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673201 prefixEnd_6673201 := by exact prefixLift 6673201
  have htrace : WordTrace (prefixWord ++ tailWord_6673201) baseStart_6673201 baseEnd_6673201 := by
    simpa [prefixWord, tailWord_6673201, baseEnd_6673201] using wordTrace_append hprefix tailTrace_6673201
  have hstable : (prefixWord ++ tailWord_6673201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673201).length < 2 ^ (prefixWord ++ tailWord_6673201).sum := by decide
  have hdescent : baseEnd_6673201 < baseStart_6673201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673208 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 1, 5, 2]
def baseStart_6673208 : Nat := 118140960795 + 6673208 * 2 ^ 59
def prefixEnd_6673208 : Nat := 4983230072969 + 3 ^ 40 * 6673208 * 2
def baseEnd_6673208 : Nat := 3426563211428632276710481

theorem tailTrace_6673208 : CollatzResearch.WordTrace tailWord_6673208 prefixEnd_6673208 3426563211428632276710481 := by
  unfold tailWord_6673208
  simp only [CollatzResearch.WordTrace]
  refine ⟨121695945604057292017950139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162261260805409722690600185 121695945604057292017950139)
  ·
    refine ⟨182543918406085938026925209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121695945604057292017950139 182543918406085938026925209)
    ·
      refine ⟨136907938804564453520193907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182543918406085938026925209 136907938804564453520193907)
      ·
        refine ⟨205361908206846680280290861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136907938804564453520193907 205361908206846680280290861)
        ·
          refine ⟨77010715577567505105109073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205361908206846680280290861 77010715577567505105109073)
          ·
            refine ⟨57758036683175628828831805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77010715577567505105109073 57758036683175628828831805)
            ·
              refine ⟨21659263756190860810811927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57758036683175628828831805 21659263756190860810811927)
              ·
                refine ⟨32488895634286291216217891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21659263756190860810811927 32488895634286291216217891)
                ·
                  refine ⟨48733343451429436824326837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32488895634286291216217891 48733343451429436824326837)
                  ·
                    refine ⟨4568750948571509702280641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48733343451429436824326837 4568750948571509702280641)
                    ·
                      refine ⟨3426563211428632276710481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568750948571509702280641 3426563211428632276710481)
                      ·
                        rfl

theorem cell23_6673208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_6673208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673208 prefixEnd_6673208 := by exact prefixLift 6673208
  have htrace : WordTrace (prefixWord ++ tailWord_6673208) baseStart_6673208 baseEnd_6673208 := by
    simpa [prefixWord, tailWord_6673208, baseEnd_6673208] using wordTrace_append hprefix tailTrace_6673208
  have hstable : (prefixWord ++ tailWord_6673208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673208).length < 2 ^ (prefixWord ++ tailWord_6673208).sum := by decide
  have hdescent : baseEnd_6673208 < baseStart_6673208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673221 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_6673221 : Nat := 118140960795 + 6673221 * 2 ^ 59
def prefixEnd_6673221 : Nat := 4983230072969 + 3 ^ 40 * 6673221 * 2
def baseEnd_6673221 : Nat := 3426569886677140725847921

theorem tailTrace_6673221 : CollatzResearch.WordTrace tailWord_6673221 prefixEnd_6673221 3426569886677140725847921 := by
  unfold tailWord_6673221
  simp only [CollatzResearch.WordTrace]
  refine ⟨243392365357067487256123517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162261576904711658170749011 243392365357067487256123517)
  ·
    refine ⟨91272137008900307721046319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243392365357067487256123517 91272137008900307721046319)
    ·
      refine ⟨136908205513350461581569479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91272137008900307721046319 136908205513350461581569479)
      ·
        refine ⟨205362308270025692372354219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136908205513350461581569479 205362308270025692372354219)
        ·
          refine ⟨308043462405038538558531329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205362308270025692372354219 308043462405038538558531329)
          ·
            refine ⟨231032596803778903918898497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308043462405038538558531329 231032596803778903918898497)
            ·
              refine ⟨173274447602834177939173873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231032596803778903918898497 173274447602834177939173873)
              ·
                refine ⟨129955835702125633454380405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173274447602834177939173873 129955835702125633454380405)
                ·
                  refine ⟨12183359597074278136348163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129955835702125633454380405 12183359597074278136348163)
                  ·
                    refine ⟨18275039395611417204522245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12183359597074278136348163 18275039395611417204522245)
                    ·
                      refine ⟨3426569886677140725847921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18275039395611417204522245 3426569886677140725847921)
                      ·
                        rfl

theorem cell23_6673221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_6673221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673221 prefixEnd_6673221 := by exact prefixLift 6673221
  have htrace : WordTrace (prefixWord ++ tailWord_6673221) baseStart_6673221 baseEnd_6673221 := by
    simpa [prefixWord, tailWord_6673221, baseEnd_6673221] using wordTrace_append hprefix tailTrace_6673221
  have hstable : (prefixWord ++ tailWord_6673221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673221).length < 2 ^ (prefixWord ++ tailWord_6673221).sum := by decide
  have hdescent : baseEnd_6673221 < baseStart_6673221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673241 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 5]
def baseStart_6673241 : Nat := 118140960795 + 6673241 * 2 ^ 59
def prefixEnd_6673241 : Nat := 4983230072969 + 3 ^ 40 * 6673241 * 2
def baseEnd_6673241 : Nat := 3426580156290230647597829

theorem tailTrace_6673241 : CollatzResearch.WordTrace tailWord_6673241 prefixEnd_6673241 3426580156290230647597829 := by
  unfold tailWord_6673241
  simp only [CollatzResearch.WordTrace]
  refine ⟨243393094816995030671851577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162262063211330020447901051 243393094816995030671851577)
  ·
    refine ⟨182544821112746273003888683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243393094816995030671851577 182544821112746273003888683)
    ·
      refine ⟨273817231669119409505833025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182544821112746273003888683 273817231669119409505833025)
      ·
        refine ⟨205362923751839557129374769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273817231669119409505833025 205362923751839557129374769)
        ·
          refine ⟨154022192813879667847031077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205362923751839557129374769 154022192813879667847031077)
          ·
            refine ⟨28879161152602437721318327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154022192813879667847031077 28879161152602437721318327)
            ·
              refine ⟨43318741728903656581977491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28879161152602437721318327 43318741728903656581977491)
              ·
                refine ⟨64978112593355484872966237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43318741728903656581977491 64978112593355484872966237)
                ·
                  refine ⟨24366792222508306827362339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64978112593355484872966237 24366792222508306827362339)
                  ·
                    refine ⟨36550188333762460241043509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24366792222508306827362339 36550188333762460241043509)
                    ·
                      refine ⟨3426580156290230647597829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36550188333762460241043509 3426580156290230647597829)
                      ·
                        rfl

theorem cell23_6673241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_6673241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673241 prefixEnd_6673241 := by exact prefixLift 6673241
  have htrace : WordTrace (prefixWord ++ tailWord_6673241) baseStart_6673241 baseEnd_6673241 := by
    simpa [prefixWord, tailWord_6673241, baseEnd_6673241] using wordTrace_append hprefix tailTrace_6673241
  have hstable : (prefixWord ++ tailWord_6673241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673241).length < 2 ^ (prefixWord ++ tailWord_6673241).sum := by decide
  have hdescent : baseEnd_6673241 < baseStart_6673241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673255 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_6673255 : Nat := 118140960795 + 6673255 * 2 ^ 59
def prefixEnd_6673255 : Nat := 4983230072969 + 3 ^ 40 * 6673255 * 2
def baseEnd_6673255 : Nat := 3426587345019393592822765

theorem tailTrace_6673255 : CollatzResearch.WordTrace tailWord_6673255 prefixEnd_6673255 3426587345019393592822765 := by
  unfold tailWord_6673255
  simp only [CollatzResearch.WordTrace]
  refine ⟨243393605438944311062861219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162262403625962874041907479 243393605438944311062861219)
  ·
    refine ⟨365090408158416466594291829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243393605438944311062861219 365090408158416466594291829)
    ·
      refine ⟨34227225764851543743214859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365090408158416466594291829 34227225764851543743214859)
      ·
        refine ⟨51340838647277315614822289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34227225764851543743214859 51340838647277315614822289)
        ·
          refine ⟨38505628985457986711116717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51340838647277315614822289 38505628985457986711116717)
          ·
            refine ⟨14439610869546745016668769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38505628985457986711116717 14439610869546745016668769)
            ·
              refine ⟨10829708152160058762501577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14439610869546745016668769 10829708152160058762501577)
              ·
                refine ⟨8122281114120044071876183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829708152160058762501577 8122281114120044071876183)
                ·
                  refine ⟨12183421671180066107814275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122281114120044071876183 12183421671180066107814275)
                  ·
                    refine ⟨18275132506770099161721413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12183421671180066107814275 18275132506770099161721413)
                    ·
                      refine ⟨3426587345019393592822765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18275132506770099161721413 3426587345019393592822765)
                      ·
                        rfl

theorem cell23_6673255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_6673255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673255 prefixEnd_6673255 := by exact prefixLift 6673255
  have htrace : WordTrace (prefixWord ++ tailWord_6673255) baseStart_6673255 baseEnd_6673255 := by
    simpa [prefixWord, tailWord_6673255, baseEnd_6673255] using wordTrace_append hprefix tailTrace_6673255
  have hstable : (prefixWord ++ tailWord_6673255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673255).length < 2 ^ (prefixWord ++ tailWord_6673255).sum := by decide
  have hdescent : baseEnd_6673255 < baseStart_6673255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673272 : List Nat := [2, 1, 2, 1, 1, 1, 1, 9, 1, 2, 2]
def baseStart_6673272 : Nat := 118140960795 + 6673272 * 2 ^ 59
def prefixEnd_6673272 : Nat := 4983230072969 + 3 ^ 40 * 6673272 * 2
def baseEnd_6673272 : Nat := 3426596074190520026310187

theorem tailTrace_6673272 : CollatzResearch.WordTrace tailWord_6673272 prefixEnd_6673272 3426596074190520026310187 := by
  unfold tailWord_6673272
  simp only [CollatzResearch.WordTrace]
  refine ⟨121697112739941361483115035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162262816986588481977486713 121697112739941361483115035)
  ·
    refine ⟨182545669109912042224672553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121697112739941361483115035 182545669109912042224672553)
    ·
      refine ⟨136909251832434031668504415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182545669109912042224672553 136909251832434031668504415)
      ·
        refine ⟨205363877748651047502756623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136909251832434031668504415 205363877748651047502756623)
        ·
          refine ⟨308045816622976571254134935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205363877748651047502756623 308045816622976571254134935)
          ·
            refine ⟨462068724934464856881202403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308045816622976571254134935 462068724934464856881202403)
            ·
              refine ⟨693103087401697285321803605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462068724934464856881202403 693103087401697285321803605)
              ·
                refine ⟨4061150902744320031182443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 693103087401697285321803605 4061150902744320031182443)
                ·
                  refine ⟨6091726354116480046773665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061150902744320031182443 6091726354116480046773665)
                  ·
                    refine ⟨4568794765587360035080249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6091726354116480046773665 4568794765587360035080249)
                    ·
                      refine ⟨3426596074190520026310187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568794765587360035080249 3426596074190520026310187)
                      ·
                        rfl

theorem cell23_6673272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_6673272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673272 prefixEnd_6673272 := by exact prefixLift 6673272
  have htrace : WordTrace (prefixWord ++ tailWord_6673272) baseStart_6673272 baseEnd_6673272 := by
    simpa [prefixWord, tailWord_6673272, baseEnd_6673272] using wordTrace_append hprefix tailTrace_6673272
  have hstable : (prefixWord ++ tailWord_6673272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673272).length < 2 ^ (prefixWord ++ tailWord_6673272).sum := by decide
  have hdescent : baseEnd_6673272 < baseStart_6673272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673302 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6673302 : Nat := 118140960795 + 6673302 * 2 ^ 59
def prefixEnd_6673302 : Nat := 4983230072969 + 3 ^ 40 * 6673302 * 2
def baseEnd_6673302 : Nat := 3426611478610154908935049

theorem tailTrace_6673302 : CollatzResearch.WordTrace tailWord_6673302 prefixEnd_6673302 3426611478610154908935049 := by
  unfold tailWord_6673302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212207479360877380613885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 162263546446516025393214773 15212207479360877380613885)
  ·
    refine ⟨5704577804760329017730207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15212207479360877380613885 5704577804760329017730207)
    ·
      refine ⟨8556866707140493526595311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704577804760329017730207 8556866707140493526595311)
      ·
        refine ⟨12835300060710740289892967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556866707140493526595311 12835300060710740289892967)
        ·
          refine ⟨19252950091066110434839451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12835300060710740289892967 19252950091066110434839451)
          ·
            refine ⟨28879425136599165652259177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19252950091066110434839451 28879425136599165652259177)
            ·
              refine ⟨21659568852449374239194383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28879425136599165652259177 21659568852449374239194383)
              ·
                refine ⟨32489353278674061358791575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21659568852449374239194383 32489353278674061358791575)
                ·
                  refine ⟨48734029918011092038187363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32489353278674061358791575 48734029918011092038187363)
                  ·
                    refine ⟨73101044877016638057281045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48734029918011092038187363 73101044877016638057281045)
                    ·
                      refine ⟨3426611478610154908935049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73101044877016638057281045 3426611478610154908935049)
                      ·
                        rfl

theorem cell23_6673302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6673302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673302 prefixEnd_6673302 := by exact prefixLift 6673302
  have htrace : WordTrace (prefixWord ++ tailWord_6673302) baseStart_6673302 baseEnd_6673302 := by
    simpa [prefixWord, tailWord_6673302, baseEnd_6673302] using wordTrace_append hprefix tailTrace_6673302
  have hstable : (prefixWord ++ tailWord_6673302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673302).length < 2 ^ (prefixWord ++ tailWord_6673302).sum := by decide
  have hdescent : baseEnd_6673302 < baseStart_6673302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673331 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_6673331 : Nat := 118140960795 + 6673331 * 2 ^ 59
def prefixEnd_6673331 : Nat := 4983230072969 + 3 ^ 40 * 6673331 * 2
def baseEnd_6673331 : Nat := 3426626369549135295472415

theorem tailTrace_6673331 : CollatzResearch.WordTrace tailWord_6673331 prefixEnd_6673331 3426626369549135295472415 := by
  unfold tailWord_6673331
  simp only [CollatzResearch.WordTrace]
  refine ⟨243396377386668976042627847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162264251591112650695085231 243396377386668976042627847)
  ·
    refine ⟨365094566080003464063941771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243396377386668976042627847 365094566080003464063941771)
    ·
      refine ⟨547641849120005196095912657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365094566080003464063941771 547641849120005196095912657)
      ·
        refine ⟨410731386840003897071934493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547641849120005196095912657 410731386840003897071934493)
        ·
          refine ⟨154024270065001461401975435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410731386840003897071934493 154024270065001461401975435)
          ·
            refine ⟨231036405097502192102963153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154024270065001461401975435 231036405097502192102963153)
            ·
              refine ⟨173277303823126644077222365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231036405097502192102963153 173277303823126644077222365)
              ·
                refine ⟨64978988933672491528958387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173277303823126644077222365 64978988933672491528958387)
                ·
                  refine ⟨97468483400508737293437581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64978988933672491528958387 97468483400508737293437581)
                  ·
                    refine ⟨36550681275190776485039093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97468483400508737293437581 36550681275190776485039093)
                    ·
                      refine ⟨3426626369549135295472415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36550681275190776485039093 3426626369549135295472415)
                      ·
                        rfl

theorem cell23_6673331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_6673331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673331 prefixEnd_6673331 := by exact prefixLift 6673331
  have htrace : WordTrace (prefixWord ++ tailWord_6673331) baseStart_6673331 baseEnd_6673331 := by
    simpa [prefixWord, tailWord_6673331, baseEnd_6673331] using wordTrace_append hprefix tailTrace_6673331
  have hstable : (prefixWord ++ tailWord_6673331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673331).length < 2 ^ (prefixWord ++ tailWord_6673331).sum := by decide
  have hdescent : baseEnd_6673331 < baseStart_6673331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673358 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6673358 : Nat := 118140960795 + 6673358 * 2 ^ 59
def prefixEnd_6673358 : Nat := 4983230072969 + 3 ^ 40 * 6673358 * 2
def baseEnd_6673358 : Nat := 3426640233526806689834791

theorem tailTrace_6673358 : CollatzResearch.WordTrace tailWord_6673358 prefixEnd_6673358 3426640233526806689834791 := by
  unfold tailWord_6673358
  simp only [CollatzResearch.WordTrace]
  refine ⟨30424670269696394956732591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162264908105047439769240485 30424670269696394956732591)
  ·
    refine ⟨45637005404544592435098887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30424670269696394956732591 45637005404544592435098887)
    ·
      refine ⟨68455508106816888652648331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45637005404544592435098887 68455508106816888652648331)
      ·
        refine ⟨102683262160225332978972497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68455508106816888652648331 102683262160225332978972497)
        ·
          refine ⟨77012446620168999734229373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102683262160225332978972497 77012446620168999734229373)
          ·
            refine ⟨28879667482563374900336015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77012446620168999734229373 28879667482563374900336015)
            ·
              refine ⟨43319501223845062350504023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28879667482563374900336015 43319501223845062350504023)
              ·
                refine ⟨64979251835767593525756035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43319501223845062350504023 64979251835767593525756035)
                ·
                  refine ⟨97468877753651390288634053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64979251835767593525756035 97468877753651390288634053)
                  ·
                    refine ⟨18275414578809635679118885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97468877753651390288634053 18275414578809635679118885)
                    ·
                      refine ⟨3426640233526806689834791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18275414578809635679118885 3426640233526806689834791)
                      ·
                        rfl

theorem cell23_6673358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6673358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673358 prefixEnd_6673358 := by exact prefixLift 6673358
  have htrace : WordTrace (prefixWord ++ tailWord_6673358) baseStart_6673358 baseEnd_6673358 := by
    simpa [prefixWord, tailWord_6673358, baseEnd_6673358] using wordTrace_append hprefix tailTrace_6673358
  have hstable : (prefixWord ++ tailWord_6673358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673358).length < 2 ^ (prefixWord ++ tailWord_6673358).sum := by decide
  have hdescent : baseEnd_6673358 < baseStart_6673358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673362 : List Nat := [3, 2, 2, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6673362 : Nat := 118140960795 + 6673362 * 2 ^ 59
def prefixEnd_6673362 : Nat := 4983230072969 + 3 ^ 40 * 6673362 * 2
def baseEnd_6673362 : Nat := 3426642287449424674184773

theorem tailTrace_6673362 : CollatzResearch.WordTrace tailWord_6673362 prefixEnd_6673362 3426642287449424674184773 := by
  unfold tailWord_6673362
  simp only [CollatzResearch.WordTrace]
  refine ⟨60849377012389167084251585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162265005366371112224670893 60849377012389167084251585)
  ·
    refine ⟨45637032759291875313188689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60849377012389167084251585 45637032759291875313188689)
    ·
      refine ⟨34227774569468906484891517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45637032759291875313188689 34227774569468906484891517)
      ·
        refine ⟨12835415463550839931834319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34227774569468906484891517 12835415463550839931834319)
        ·
          refine ⟨19253123195326259897751479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12835415463550839931834319 19253123195326259897751479)
          ·
            refine ⟨28879684792989389846627219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19253123195326259897751479 28879684792989389846627219)
            ·
              refine ⟨43319527189484084769940829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28879684792989389846627219 43319527189484084769940829)
              ·
                refine ⟨16244822696056531788727811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43319527189484084769940829 16244822696056531788727811)
                ·
                  refine ⟨24367234044084797683091717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16244822696056531788727811 24367234044084797683091717)
                  ·
                    refine ⟨4568856383265899565579697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24367234044084797683091717 4568856383265899565579697)
                    ·
                      refine ⟨3426642287449424674184773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4568856383265899565579697 3426642287449424674184773)
                      ·
                        rfl

theorem cell23_6673362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6673362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673362 prefixEnd_6673362 := by exact prefixLift 6673362
  have htrace : WordTrace (prefixWord ++ tailWord_6673362) baseStart_6673362 baseEnd_6673362 := by
    simpa [prefixWord, tailWord_6673362, baseEnd_6673362] using wordTrace_append hprefix tailTrace_6673362
  have hstable : (prefixWord ++ tailWord_6673362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673362).length < 2 ^ (prefixWord ++ tailWord_6673362).sum := by decide
  have hdescent : baseEnd_6673362 < baseStart_6673362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673368 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 7]
def baseStart_6673368 : Nat := 118140960795 + 6673368 * 2 ^ 59
def prefixEnd_6673368 : Nat := 4983230072969 + 3 ^ 40 * 6673368 * 2
def baseEnd_6673368 : Nat := 380738374259261294523305

theorem tailTrace_6673368 : CollatzResearch.WordTrace tailWord_6673368 prefixEnd_6673368 380738374259261294523305 := by
  unfold tailWord_6673368
  simp only [CollatzResearch.WordTrace]
  refine ⟨121698863443767465680862379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162265151258356620907816505 121698863443767465680862379)
  ·
    refine ⟨182548295165651198521293569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121698863443767465680862379 182548295165651198521293569)
    ·
      refine ⟨136911221374238398890970177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182548295165651198521293569 136911221374238398890970177)
      ·
        refine ⟨102683416030678799168227633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136911221374238398890970177 102683416030678799168227633)
        ·
          refine ⟨77012562023009099376170725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102683416030678799168227633 77012562023009099376170725)
          ·
            refine ⟨14439855379314206133032011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77012562023009099376170725 14439855379314206133032011)
            ·
              refine ⟨21659783068971309199548017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14439855379314206133032011 21659783068971309199548017)
              ·
                refine ⟨16244837301728481899661013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21659783068971309199548017 16244837301728481899661013)
                ·
                  refine ⟨380738374259261294523305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16244837301728481899661013 380738374259261294523305)
                  ·
                    rfl

theorem cell23_6673368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_6673368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673368 prefixEnd_6673368 := by exact prefixLift 6673368
  have htrace : WordTrace (prefixWord ++ tailWord_6673368) baseStart_6673368 baseEnd_6673368 := by
    simpa [prefixWord, tailWord_6673368, baseEnd_6673368] using wordTrace_append hprefix tailTrace_6673368
  have hstable : (prefixWord ++ tailWord_6673368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673368).length < 2 ^ (prefixWord ++ tailWord_6673368).sum := by decide
  have hdescent : baseEnd_6673368 < baseStart_6673368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673458 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_6673458 : Nat := 118140960795 + 6673458 * 2 ^ 59
def prefixEnd_6673458 : Nat := 4983230072969 + 3 ^ 40 * 6673458 * 2
def baseEnd_6673458 : Nat := 380743509065806255398259

theorem tailTrace_6673458 : CollatzResearch.WordTrace tailWord_6673458 prefixEnd_6673458 380743509065806255398259 := by
  unfold tailWord_6673458
  simp only [CollatzResearch.WordTrace]
  refine ⟨60850252364302219183125257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162267339638139251155000685 60850252364302219183125257)
  ·
    refine ⟨45637689273226664387343943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60850252364302219183125257 45637689273226664387343943)
    ·
      refine ⟨68456533909839996581015915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45637689273226664387343943 68456533909839996581015915)
      ·
        refine ⟨102684800864759994871523873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68456533909839996581015915 102684800864759994871523873)
        ·
          refine ⟨77013600648569996153642905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102684800864759994871523873 77013600648569996153642905)
          ·
            refine ⟨57760200486427497115232179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77013600648569996153642905 57760200486427497115232179)
            ·
              refine ⟨86640300729641245672848269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57760200486427497115232179 86640300729641245672848269)
              ·
                refine ⟨32490112773615467127318101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86640300729641245672848269 32490112773615467127318101)
                ·
                  refine ⟨380743509065806255398259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32490112773615467127318101 380743509065806255398259)
                  ·
                    rfl

theorem cell23_6673458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_6673458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673458 prefixEnd_6673458 := by exact prefixLift 6673458
  have htrace : WordTrace (prefixWord ++ tailWord_6673458) baseStart_6673458 baseEnd_6673458 := by
    simpa [prefixWord, tailWord_6673458, baseEnd_6673458] using wordTrace_append hprefix tailTrace_6673458
  have hstable : (prefixWord ++ tailWord_6673458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673458).length < 2 ^ (prefixWord ++ tailWord_6673458).sum := by decide
  have hdescent : baseEnd_6673458 < baseStart_6673458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673498 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_6673498 : Nat := 118140960795 + 6673498 * 2 ^ 59
def prefixEnd_6673498 : Nat := 4983230072969 + 3 ^ 40 * 6673498 * 2
def baseEnd_6673498 : Nat := 3426712120818436142084147

theorem tailTrace_6673498 : CollatzResearch.WordTrace tailWord_6673498 prefixEnd_6673498 3426712120818436142084147 := by
  unfold tailWord_6673498
  simp only [CollatzResearch.WordTrace]
  refine ⟨60850617094265990890989287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162268312251375975709304765 60850617094265990890989287)
  ·
    refine ⟨91275925641398986336483931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60850617094265990890989287 91275925641398986336483931)
    ·
      refine ⟨136913888462098479504725897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91275925641398986336483931 136913888462098479504725897)
      ·
        refine ⟨102685416346573859628544423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136913888462098479504725897 102685416346573859628544423)
        ·
          refine ⟨154028124519860789442816635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102685416346573859628544423 154028124519860789442816635)
          ·
            refine ⟨231042186779791184164224953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154028124519860789442816635 231042186779791184164224953)
            ·
              refine ⟨173281640084843388123168715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231042186779791184164224953 173281640084843388123168715)
              ·
                refine ⟨259922460127265082184753073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173281640084843388123168715 259922460127265082184753073)
                ·
                  refine ⟨194941845095448811638564805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259922460127265082184753073 194941845095448811638564805)
                  ·
                    refine ⟨36551595955396652182230901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194941845095448811638564805 36551595955396652182230901)
                    ·
                      refine ⟨3426712120818436142084147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36551595955396652182230901 3426712120818436142084147)
                      ·
                        rfl

theorem cell23_6673498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_6673498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673498 prefixEnd_6673498 := by exact prefixLift 6673498
  have htrace : WordTrace (prefixWord ++ tailWord_6673498) baseStart_6673498 baseEnd_6673498 := by
    simpa [prefixWord, tailWord_6673498, baseEnd_6673498] using wordTrace_append hprefix tailTrace_6673498
  have hstable : (prefixWord ++ tailWord_6673498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673498).length < 2 ^ (prefixWord ++ tailWord_6673498).sum := by decide
  have hdescent : baseEnd_6673498 < baseStart_6673498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673505 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 1, 5]
def baseStart_6673505 : Nat := 118140960795 + 6673505 * 2 ^ 59
def prefixEnd_6673505 : Nat := 4983230072969 + 3 ^ 40 * 6673505 * 2
def baseEnd_6673505 : Nat := 1142238571727672538232205

theorem tailTrace_6673505 : CollatzResearch.WordTrace tailWord_6673505 prefixEnd_6673505 1142238571727672538232205 := by
  unfold tailWord_6673505
  simp only [CollatzResearch.WordTrace]
  refine ⟨243402723688038603759461969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162268482458692402506307979 243402723688038603759461969)
  ·
    refine ⟨182552042766028952819596477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243402723688038603759461969 182552042766028952819596477)
    ·
      refine ⟨68457016037260857307348679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182552042766028952819596477 68457016037260857307348679)
      ·
        refine ⟨102685524055891285961023019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68457016037260857307348679 102685524055891285961023019)
        ·
          refine ⟨154028286083836928941534529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102685524055891285961023019 154028286083836928941534529)
          ·
            refine ⟨115521214562877696706150897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154028286083836928941534529 115521214562877696706150897)
            ·
              refine ⟨86640910922158272529613173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115521214562877696706150897 86640910922158272529613173)
              ·
                refine ⟨8122585398952338049651235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86640910922158272529613173 8122585398952338049651235)
                ·
                  refine ⟨12183878098428507074476853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122585398952338049651235 12183878098428507074476853)
                  ·
                    refine ⟨1142238571727672538232205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12183878098428507074476853 1142238571727672538232205)
                    ·
                      rfl

theorem cell23_6673505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_6673505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673505 prefixEnd_6673505 := by exact prefixLift 6673505
  have htrace : WordTrace (prefixWord ++ tailWord_6673505) baseStart_6673505 baseEnd_6673505 := by
    simpa [prefixWord, tailWord_6673505, baseEnd_6673505] using wordTrace_append hprefix tailTrace_6673505
  have hstable : (prefixWord ++ tailWord_6673505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673505).length < 2 ^ (prefixWord ++ tailWord_6673505).sum := by decide
  have hdescent : baseEnd_6673505 < baseStart_6673505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673519 : List Nat := [1, 1, 2, 1, 3, 3, 3, 4, 1, 1, 3]
def baseStart_6673519 : Nat := 118140960795 + 6673519 * 2 ^ 59
def prefixEnd_6673519 : Nat := 4983230072969 + 3 ^ 40 * 6673519 * 2
def baseEnd_6673519 : Nat := 3426722903912180559921551

theorem tailTrace_6673519 : CollatzResearch.WordTrace tailWord_6673519 prefixEnd_6673519 3426722903912180559921551 := by
  unfold tailWord_6673519
  simp only [CollatzResearch.WordTrace]
  refine ⟨243403234309987884150471611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162268822873325256100314407 243403234309987884150471611)
  ·
    refine ⟨365104851464981826225707417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243403234309987884150471611 365104851464981826225707417)
    ·
      refine ⟨273828638598736369669280563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365104851464981826225707417 273828638598736369669280563)
      ·
        refine ⟨410742957898104554503920845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273828638598736369669280563 410742957898104554503920845)
        ·
          refine ⟨154028609211789207938970317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410742957898104554503920845 154028609211789207938970317)
          ·
            refine ⟨57760728454420952977113869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154028609211789207938970317 57760728454420952977113869)
            ·
              refine ⟨21660273170407857366417701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57760728454420952977113869 21660273170407857366417701)
              ·
                refine ⟨4061301219451473256203319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21660273170407857366417701 4061301219451473256203319)
                ·
                  refine ⟨6091951829177209884304979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4061301219451473256203319 6091951829177209884304979)
                  ·
                    refine ⟨9137927743765814826457469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6091951829177209884304979 9137927743765814826457469)
                    ·
                      refine ⟨3426722903912180559921551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9137927743765814826457469 3426722903912180559921551)
                      ·
                        rfl

theorem cell23_6673519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 4, 1, 1, 3].length) (baseStart_6673519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673519 prefixEnd_6673519 := by exact prefixLift 6673519
  have htrace : WordTrace (prefixWord ++ tailWord_6673519) baseStart_6673519 baseEnd_6673519 := by
    simpa [prefixWord, tailWord_6673519, baseEnd_6673519] using wordTrace_append hprefix tailTrace_6673519
  have hstable : (prefixWord ++ tailWord_6673519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673519).length < 2 ^ (prefixWord ++ tailWord_6673519).sum := by decide
  have hdescent : baseEnd_6673519 < baseStart_6673519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673548 : List Nat := [2, 2, 1, 2, 1, 1, 1, 13]
def baseStart_6673548 : Nat := 118140960795 + 6673548 * 2 ^ 59
def prefixEnd_6673548 : Nat := 4983230072969 + 3 ^ 40 * 6673548 * 2
def baseEnd_6673548 : Nat := 126916214624117072091071

theorem tailTrace_6673548 : CollatzResearch.WordTrace tailWord_6673548 prefixEnd_6673548 126916214624117072091071 := by
  unfold tailWord_6673548
  simp only [CollatzResearch.WordTrace]
  refine ⟨121702146013441411051638649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162269528017921881402184865 121702146013441411051638649)
  ·
    refine ⟨91276609510081058288728987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121702146013441411051638649 91276609510081058288728987)
    ·
      refine ⟨136914914265121587433093481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91276609510081058288728987 136914914265121587433093481)
      ·
        refine ⟨102686185698841190574820111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136914914265121587433093481 102686185698841190574820111)
        ·
          refine ⟨154029278548261785862230167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102686185698841190574820111 154029278548261785862230167)
          ·
            refine ⟨231043917822392678793345251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154029278548261785862230167 231043917822392678793345251)
            ·
              refine ⟨346565876733589018190017877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231043917822392678793345251 346565876733589018190017877)
              ·
                refine ⟨126916214624117072091071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 346565876733589018190017877 126916214624117072091071)
                ·
                  rfl

theorem cell23_6673548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 13].length) (baseStart_6673548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673548 prefixEnd_6673548 := by exact prefixLift 6673548
  have htrace : WordTrace (prefixWord ++ tailWord_6673548) baseStart_6673548 baseEnd_6673548 := by
    simpa [prefixWord, tailWord_6673548, baseEnd_6673548] using wordTrace_append hprefix tailTrace_6673548
  have hstable : (prefixWord ++ tailWord_6673548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673548).length < 2 ^ (prefixWord ++ tailWord_6673548).sum := by decide
  have hdescent : baseEnd_6673548 < baseStart_6673548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673555 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4]
def baseStart_6673555 : Nat := 118140960795 + 6673555 * 2 ^ 59
def prefixEnd_6673555 : Nat := 4983230072969 + 3 ^ 40 * 6673555 * 2
def baseEnd_6673555 : Nat := 3426741389215742419071385

theorem tailTrace_6673555 : CollatzResearch.WordTrace tailWord_6673555 prefixEnd_6673555 3426741389215742419071385 := by
  unfold tailWord_6673555
  simp only [CollatzResearch.WordTrace]
  refine ⟨243404547337857462298782119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162269698225238308199188079 243404547337857462298782119)
  ·
    refine ⟨365106821006786193448173179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243404547337857462298782119 365106821006786193448173179)
    ·
      refine ⟨547660231510179290172259769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365106821006786193448173179 547660231510179290172259769)
      ·
        refine ⟨410745173632634467629194827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547660231510179290172259769 410745173632634467629194827)
        ·
          refine ⟨616117760448951701443792241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410745173632634467629194827 616117760448951701443792241)
          ·
            refine ⟨462088320336713776082844181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616117760448951701443792241 462088320336713776082844181)
            ·
              refine ⟨21660390015783458253883321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 462088320336713776082844181 21660390015783458253883321)
              ·
                refine ⟨16245292511837593690412491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21660390015783458253883321 16245292511837593690412491)
                ·
                  refine ⟨24367938767756390535618737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16245292511837593690412491 24367938767756390535618737)
                  ·
                    refine ⟨18275954075817292901714053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24367938767756390535618737 18275954075817292901714053)
                    ·
                      refine ⟨3426741389215742419071385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18275954075817292901714053 3426741389215742419071385)
                      ·
                        rfl

theorem cell23_6673555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_6673555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673555 prefixEnd_6673555 := by exact prefixLift 6673555
  have htrace : WordTrace (prefixWord ++ tailWord_6673555) baseStart_6673555 baseEnd_6673555 := by
    simpa [prefixWord, tailWord_6673555, baseEnd_6673555] using wordTrace_append hprefix tailTrace_6673555
  have hstable : (prefixWord ++ tailWord_6673555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673555).length < 2 ^ (prefixWord ++ tailWord_6673555).sum := by decide
  have hdescent : baseEnd_6673555 < baseStart_6673555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673559 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 1, 1, 4]
def baseStart_6673559 : Nat := 118140960795 + 6673559 * 2 ^ 59
def prefixEnd_6673559 : Nat := 4983230072969 + 3 ^ 40 * 6673559 * 2
def baseEnd_6673559 : Nat := 3426743443138360403421367

theorem tailTrace_6673559 : CollatzResearch.WordTrace tailWord_6673559 prefixEnd_6673559 3426743443138360403421367 := by
  unfold tailWord_6673559
  simp only [CollatzResearch.WordTrace]
  refine ⟨243404693229842970981927731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162269795486561980654618487 243404693229842970981927731)
  ·
    refine ⟨365107039844764456472891597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243404693229842970981927731 365107039844764456472891597)
    ·
      refine ⟨136915139941786671177334349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365107039844764456472891597 136915139941786671177334349)
      ·
        refine ⟨51343177478170001691500381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136915139941786671177334349 51343177478170001691500381)
        ·
          refine ⟨19253691554313750634312643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51343177478170001691500381 19253691554313750634312643)
          ·
            refine ⟨28880537331470625951468965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19253691554313750634312643 28880537331470625951468965)
            ·
              refine ⟨5415100749650742365900431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28880537331470625951468965 5415100749650742365900431)
              ·
                refine ⟨8122651124476113548850647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415100749650742365900431 8122651124476113548850647)
                ·
                  refine ⟨12183976686714170323275971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122651124476113548850647 12183976686714170323275971)
                  ·
                    refine ⟨18275965030071255484913957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12183976686714170323275971 18275965030071255484913957)
                    ·
                      refine ⟨3426743443138360403421367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18275965030071255484913957 3426743443138360403421367)
                      ·
                        rfl

theorem cell23_6673559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_6673559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673559 prefixEnd_6673559 := by exact prefixLift 6673559
  have htrace : WordTrace (prefixWord ++ tailWord_6673559) baseStart_6673559 baseEnd_6673559 := by
    simpa [prefixWord, tailWord_6673559, baseEnd_6673559] using wordTrace_append hprefix tailTrace_6673559
  have hstable : (prefixWord ++ tailWord_6673559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673559).length < 2 ^ (prefixWord ++ tailWord_6673559).sum := by decide
  have hdescent : baseEnd_6673559 < baseStart_6673559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673685 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_6673685 : Nat := 118140960795 + 6673685 * 2 ^ 59
def prefixEnd_6673685 : Nat := 4983230072969 + 3 ^ 40 * 6673685 * 2
def baseEnd_6673685 : Nat := 1142269380566942303481929

theorem tailTrace_6673685 : CollatzResearch.WordTrace tailWord_6673685 prefixEnd_6673685 1142269380566942303481929 := by
  unfold tailWord_6673685
  simp only [CollatzResearch.WordTrace]
  refine ⟨243409288827386494501014509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162272859218257663000676339 243409288827386494501014509)
  ·
    refine ⟨91278483310269935437880441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243409288827386494501014509 91278483310269935437880441)
    ·
      refine ⟨68458862482702451578410331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91278483310269935437880441 68458862482702451578410331)
      ·
        refine ⟨102688293724053677367615497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68458862482702451578410331 102688293724053677367615497)
        ·
          refine ⟨77016220293040258025711623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102688293724053677367615497 77016220293040258025711623)
          ·
            refine ⟨115524330439560387038567435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77016220293040258025711623 115524330439560387038567435)
            ·
              refine ⟨173286495659340580557851153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115524330439560387038567435 173286495659340580557851153)
              ·
                refine ⟨129964871744505435418388365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173286495659340580557851153 129964871744505435418388365)
                ·
                  refine ⟨48736826904189538281895637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129964871744505435418388365 48736826904189538281895637)
                  ·
                    refine ⟨1142269380566942303481929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48736826904189538281895637 1142269380566942303481929)
                    ·
                      rfl

theorem cell23_6673685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_6673685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673685 prefixEnd_6673685 := by exact prefixLift 6673685
  have htrace : WordTrace (prefixWord ++ tailWord_6673685) baseStart_6673685 baseEnd_6673685 := by
    simpa [prefixWord, tailWord_6673685, baseEnd_6673685] using wordTrace_append hprefix tailTrace_6673685
  have hstable : (prefixWord ++ tailWord_6673685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673685).length < 2 ^ (prefixWord ++ tailWord_6673685).sum := by decide
  have hdescent : baseEnd_6673685 < baseStart_6673685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673705 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 4]
def baseStart_6673705 : Nat := 118140960795 + 6673705 * 2 ^ 59
def prefixEnd_6673705 : Nat := 4983230072969 + 3 ^ 40 * 6673705 * 2
def baseEnd_6673705 : Nat := 3426818411313916832195695

theorem tailTrace_6673705 : CollatzResearch.WordTrace tailWord_6673705 prefixEnd_6673705 3426818411313916832195695 := by
  unfold tailWord_6673705
  simp only [CollatzResearch.WordTrace]
  refine ⟨243410018287314037916742569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162273345524876025277828379 243410018287314037916742569)
  ·
    refine ⟨182557513715485528437556927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243410018287314037916742569 182557513715485528437556927)
    ·
      refine ⟨273836270573228292656335391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182557513715485528437556927 273836270573228292656335391)
      ·
        refine ⟨410754405859842438984503087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273836270573228292656335391 410754405859842438984503087)
        ·
          refine ⟨616131608789763658476754631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410754405859842438984503087 616131608789763658476754631)
          ·
            refine ⟨924197413184645487715131947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616131608789763658476754631 924197413184645487715131947)
            ·
              refine ⟨1386296119776968231572697921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924197413184645487715131947 1386296119776968231572697921)
              ·
                refine ⟨1039722089832726173679523441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1386296119776968231572697921 1039722089832726173679523441)
                ·
                  refine ⟨779791567374544630259642581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1039722089832726173679523441 779791567374544630259642581)
                  ·
                    refine ⟨18276364860340889771710373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 779791567374544630259642581 18276364860340889771710373)
                    ·
                      refine ⟨3426818411313916832195695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18276364860340889771710373 3426818411313916832195695)
                      ·
                        rfl

theorem cell23_6673705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_6673705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673705 prefixEnd_6673705 := by exact prefixLift 6673705
  have htrace : WordTrace (prefixWord ++ tailWord_6673705) baseStart_6673705 baseEnd_6673705 := by
    simpa [prefixWord, tailWord_6673705, baseEnd_6673705] using wordTrace_append hprefix tailTrace_6673705
  have hstable : (prefixWord ++ tailWord_6673705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673705).length < 2 ^ (prefixWord ++ tailWord_6673705).sum := by decide
  have hdescent : baseEnd_6673705 < baseStart_6673705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673722 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_6673722 : Nat := 118140960795 + 6673722 * 2 ^ 59
def prefixEnd_6673722 : Nat := 4983230072969 + 3 ^ 40 * 6673722 * 2
def baseEnd_6673722 : Nat := 3426827140485043265683117

theorem tailTrace_6673722 : CollatzResearch.WordTrace tailWord_6673722 prefixEnd_6673722 3426827140485043265683117 := by
  unfold tailWord_6673722
  simp only [CollatzResearch.WordTrace]
  refine ⟨60852659582063112455027855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162273758885501633213407613 60852659582063112455027855)
  ·
    refine ⟨91278989373094668682541783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60852659582063112455027855 91278989373094668682541783)
    ·
      refine ⟨136918484059642003023812675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91278989373094668682541783 136918484059642003023812675)
      ·
        refine ⟨205377726089463004535719013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136918484059642003023812675 205377726089463004535719013)
        ·
          refine ⟨38508323641774313350447315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205377726089463004535719013 38508323641774313350447315)
          ·
            refine ⟨57762485462661470025670973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38508323641774313350447315 57762485462661470025670973)
            ·
              refine ⟨21660932048498051259626615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57762485462661470025670973 21660932048498051259626615)
              ·
                refine ⟨32491398072747076889439923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21660932048498051259626615 32491398072747076889439923)
                ·
                  refine ⟨48737097109120615334159885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32491398072747076889439923 48737097109120615334159885)
                  ·
                    refine ⟨18276411415920230750309957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48737097109120615334159885 18276411415920230750309957)
                    ·
                      refine ⟨3426827140485043265683117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18276411415920230750309957 3426827140485043265683117)
                      ·
                        rfl

theorem cell23_6673722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_6673722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673722 prefixEnd_6673722 := by exact prefixLift 6673722
  have htrace : WordTrace (prefixWord ++ tailWord_6673722) baseStart_6673722 baseEnd_6673722 := by
    simpa [prefixWord, tailWord_6673722, baseEnd_6673722] using wordTrace_append hprefix tailTrace_6673722
  have hstable : (prefixWord ++ tailWord_6673722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673722).length < 2 ^ (prefixWord ++ tailWord_6673722).sum := by decide
  have hdescent : baseEnd_6673722 < baseStart_6673722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673734 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6673734 : Nat := 118140960795 + 6673734 * 2 ^ 59
def prefixEnd_6673734 : Nat := 4983230072969 + 3 ^ 40 * 6673734 * 2
def baseEnd_6673734 : Nat := 3426833302252897218733063

theorem tailTrace_6673734 : CollatzResearch.WordTrace tailWord_6673734 prefixEnd_6673734 3426833302252897218733063 := by
  unfold tailWord_6673734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7606596125131530495923383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 162274050669472650579698837 7606596125131530495923383)
  ·
    refine ⟨11409894187697295743885075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7606596125131530495923383 11409894187697295743885075)
    ·
      refine ⟨17114841281545943615827613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11409894187697295743885075 17114841281545943615827613)
      ·
        refine ⟨6418065480579728855935355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17114841281545943615827613 6418065480579728855935355)
        ·
          refine ⟨9627098220869593283903033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418065480579728855935355 9627098220869593283903033)
          ·
            refine ⟨7220323665652194962927275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9627098220869593283903033 7220323665652194962927275)
            ·
              refine ⟨10830485498478292444390913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220323665652194962927275 10830485498478292444390913)
              ·
                refine ⟨8122864123858719333293185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10830485498478292444390913 8122864123858719333293185)
                ·
                  refine ⟨6092148092894039499969889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8122864123858719333293185 6092148092894039499969889)
                  ·
                    refine ⟨4569111069670529624977417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6092148092894039499969889 4569111069670529624977417)
                    ·
                      refine ⟨3426833302252897218733063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569111069670529624977417 3426833302252897218733063)
                      ·
                        rfl

theorem cell23_6673734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6673734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673734 prefixEnd_6673734 := by exact prefixLift 6673734
  have htrace : WordTrace (prefixWord ++ tailWord_6673734) baseStart_6673734 baseEnd_6673734 := by
    simpa [prefixWord, tailWord_6673734, baseEnd_6673734] using wordTrace_append hprefix tailTrace_6673734
  have hstable : (prefixWord ++ tailWord_6673734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673734).length < 2 ^ (prefixWord ++ tailWord_6673734).sum := by decide
  have hdescent : baseEnd_6673734 < baseStart_6673734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673749 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_6673749 : Nat := 118140960795 + 6673749 * 2 ^ 59
def prefixEnd_6673749 : Nat := 4983230072969 + 3 ^ 40 * 6673749 * 2
def baseEnd_6673749 : Nat := 1142280334820904886681831

theorem tailTrace_6673749 : CollatzResearch.WordTrace tailWord_6673749 prefixEnd_6673749 1142280334820904886681831 := by
  unfold tailWord_6673749
  simp only [CollatzResearch.WordTrace]
  refine ⟨243411623099154633431344301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162274415399436422287562867 243411623099154633431344301)
  ·
    refine ⟨91279358662182987536754113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243411623099154633431344301 91279358662182987536754113)
    ·
      refine ⟨68459518996637240652565585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91279358662182987536754113 68459518996637240652565585)
      ·
        refine ⟨51344639247477930489424189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68459518996637240652565585 51344639247477930489424189)
        ·
          refine ⟨19254239717804223933534071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51344639247477930489424189 19254239717804223933534071)
          ·
            refine ⟨28881359576706335900301107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19254239717804223933534071 28881359576706335900301107)
            ·
              refine ⟨43322039365059503850451661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28881359576706335900301107 43322039365059503850451661)
              ·
                refine ⟨16245764761897313943919373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43322039365059503850451661 16245764761897313943919373)
                ·
                  refine ⟨6092161785711492728969765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16245764761897313943919373 6092161785711492728969765)
                  ·
                    refine ⟨1142280334820904886681831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6092161785711492728969765 1142280334820904886681831)
                    ·
                      rfl

theorem cell23_6673749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_6673749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673749 prefixEnd_6673749 := by exact prefixLift 6673749
  have htrace : WordTrace (prefixWord ++ tailWord_6673749) baseStart_6673749 baseEnd_6673749 := by
    simpa [prefixWord, tailWord_6673749, baseEnd_6673749] using wordTrace_append hprefix tailTrace_6673749
  have hstable : (prefixWord ++ tailWord_6673749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673749).length < 2 ^ (prefixWord ++ tailWord_6673749).sum := by decide
  have hdescent : baseEnd_6673749 < baseStart_6673749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673826 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6673826 : Nat := 118140960795 + 6673826 * 2 ^ 59
def prefixEnd_6673826 : Nat := 4983230072969 + 3 ^ 40 * 6673826 * 2
def baseEnd_6673826 : Nat := 1142293514157703619594213

theorem tailTrace_6673826 : CollatzResearch.WordTrace tailWord_6673826 prefixEnd_6673826 1142293514157703619594213 := by
  unfold tailWord_6673826
  simp only [CollatzResearch.WordTrace]
  refine ⟨60853607879968918895474333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162276287679917117054598221 60853607879968918895474333)
  ·
    refine ⟨22820102954988344585802875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60853607879968918895474333 22820102954988344585802875)
    ·
      refine ⟨34230154432482516878704313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22820102954988344585802875 34230154432482516878704313)
      ·
        refine ⟨25672615824361887659028235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34230154432482516878704313 25672615824361887659028235)
        ·
          refine ⟨38508923736542831488542353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25672615824361887659028235 38508923736542831488542353)
          ·
            refine ⟨28881692802407123616406765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38508923736542831488542353 28881692802407123616406765)
            ·
              refine ⟨10830634800902671356152537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28881692802407123616406765 10830634800902671356152537)
              ·
                refine ⟨8122976100677003517114403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10830634800902671356152537 8122976100677003517114403)
                ·
                  refine ⟨12184464151015505275671605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122976100677003517114403 12184464151015505275671605)
                  ·
                    refine ⟨1142293514157703619594213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12184464151015505275671605 1142293514157703619594213)
                    ·
                      rfl

theorem cell23_6673826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6673826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673826 prefixEnd_6673826 := by exact prefixLift 6673826
  have htrace : WordTrace (prefixWord ++ tailWord_6673826) baseStart_6673826 baseEnd_6673826 := by
    simpa [prefixWord, tailWord_6673826, baseEnd_6673826] using wordTrace_append hprefix tailTrace_6673826
  have hstable : (prefixWord ++ tailWord_6673826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673826).length < 2 ^ (prefixWord ++ tailWord_6673826).sum := by decide
  have hdescent : baseEnd_6673826 < baseStart_6673826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673829 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_6673829 : Nat := 118140960795 + 6673829 * 2 ^ 59
def prefixEnd_6673829 : Nat := 4983230072969 + 3 ^ 40 * 6673829 * 2
def baseEnd_6673829 : Nat := 3426882082915074347045125

theorem tailTrace_6673829 : CollatzResearch.WordTrace tailWord_6673829 prefixEnd_6673829 3426882082915074347045125 := by
  unfold tailWord_6673829
  simp only [CollatzResearch.WordTrace]
  refine ⟨243414540938864807094256541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162276360625909871396171027 243414540938864807094256541)
  ·
    refine ⟨91280452852074302660346203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243414540938864807094256541 91280452852074302660346203)
    ·
      refine ⟨136920679278111453990519305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91280452852074302660346203 136920679278111453990519305)
      ·
        refine ⟨102690509458583590492889479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136920679278111453990519305 102690509458583590492889479)
        ·
          refine ⟨154035764187875385739334219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102690509458583590492889479 154035764187875385739334219)
          ·
            refine ⟨231053646281813078609001329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154035764187875385739334219 231053646281813078609001329)
            ·
              refine ⟨173290234711359808956750997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231053646281813078609001329 173290234711359808956750997)
              ·
                refine ⟨8122979752094991044847703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173290234711359808956750997 8122979752094991044847703)
                ·
                  refine ⟨12184469628142486567271555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122979752094991044847703 12184469628142486567271555)
                  ·
                    refine ⟨18276704442213729850907333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12184469628142486567271555 18276704442213729850907333)
                    ·
                      refine ⟨3426882082915074347045125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18276704442213729850907333 3426882082915074347045125)
                      ·
                        rfl

theorem cell23_6673829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_6673829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673829 prefixEnd_6673829 := by exact prefixLift 6673829
  have htrace : WordTrace (prefixWord ++ tailWord_6673829) baseStart_6673829 baseEnd_6673829 := by
    simpa [prefixWord, tailWord_6673829, baseEnd_6673829] using wordTrace_append hprefix tailTrace_6673829
  have hstable : (prefixWord ++ tailWord_6673829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673829).length < 2 ^ (prefixWord ++ tailWord_6673829).sum := by decide
  have hdescent : baseEnd_6673829 < baseStart_6673829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673842 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_6673842 : Nat := 118140960795 + 6673842 * 2 ^ 59
def prefixEnd_6673842 : Nat := 4983230072969 + 3 ^ 40 * 6673842 * 2
def baseEnd_6673842 : Nat := 3426888758163582796182565

theorem tailTrace_6673842 : CollatzResearch.WordTrace tailWord_6673842 prefixEnd_6673842 3426888758163582796182565 := by
  unfold tailWord_6673842
  simp only [CollatzResearch.WordTrace]
  refine ⟨60853753771954427578619945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162276676725211806876319853 60853753771954427578619945)
  ·
    refine ⟨45640315328965820683964959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60853753771954427578619945 45640315328965820683964959)
    ·
      refine ⟨68460472993448731025947439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45640315328965820683964959 68460472993448731025947439)
      ·
        refine ⟨102690709490173096538921159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68460472993448731025947439 102690709490173096538921159)
        ·
          refine ⟨154036064235259644808381739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102690709490173096538921159 154036064235259644808381739)
          ·
            refine ⟨231054096352889467212572609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154036064235259644808381739 231054096352889467212572609)
            ·
              refine ⟨173290572264667100409429457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231054096352889467212572609 173290572264667100409429457)
              ·
                refine ⟨129967929198500325307072093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173290572264667100409429457 129967929198500325307072093)
                ·
                  refine ⟨48737973449437621990152035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129967929198500325307072093 48737973449437621990152035)
                  ·
                    refine ⟨73106960174156432985228053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48737973449437621990152035 73106960174156432985228053)
                    ·
                      refine ⟨3426888758163582796182565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73106960174156432985228053 3426888758163582796182565)
                      ·
                        rfl

theorem cell23_6673842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_6673842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673842 prefixEnd_6673842 := by exact prefixLift 6673842
  have htrace : WordTrace (prefixWord ++ tailWord_6673842) baseStart_6673842 baseEnd_6673842 := by
    simpa [prefixWord, tailWord_6673842, baseEnd_6673842] using wordTrace_append hprefix tailTrace_6673842
  have hstable : (prefixWord ++ tailWord_6673842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673842).length < 2 ^ (prefixWord ++ tailWord_6673842).sum := by decide
  have hdescent : baseEnd_6673842 < baseStart_6673842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673852 : List Nat := [2, 2, 2, 4, 13]
def baseStart_6673852 : Nat := 118140960795 + 6673852 * 2 ^ 59
def prefixEnd_6673852 : Nat := 4983230072969 + 3 ^ 40 * 6673852 * 2
def baseEnd_6673852 : Nat := 4700814667997431765511

theorem tailTrace_6673852 : CollatzResearch.WordTrace tailWord_6673852 prefixEnd_6673852 4700814667997431765511 := by
  unfold tailWord_6673852
  simp only [CollatzResearch.WordTrace]
  refine ⟨121707689908890741011171905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162276919878520988014895873 121707689908890741011171905)
  ·
    refine ⟨91280767431668055758378929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121707689908890741011171905 91280767431668055758378929)
    ·
      refine ⟨68460575573751041818784197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91280767431668055758378929 68460575573751041818784197)
      ·
        refine ⟨12836357920078320341022037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68460575573751041818784197 12836357920078320341022037)
        ·
          refine ⟨4700814667997431765511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12836357920078320341022037 4700814667997431765511)
          ·
            rfl

theorem cell23_6673852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 13].length) (baseStart_6673852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673852 prefixEnd_6673852 := by exact prefixLift 6673852
  have htrace : WordTrace (prefixWord ++ tailWord_6673852) baseStart_6673852 baseEnd_6673852 := by
    simpa [prefixWord, tailWord_6673852, baseEnd_6673852] using wordTrace_append hprefix tailTrace_6673852
  have hstable : (prefixWord ++ tailWord_6673852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673852).length < 2 ^ (prefixWord ++ tailWord_6673852).sum := by decide
  have hdescent : baseEnd_6673852 < baseStart_6673852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673896 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6673896 : Nat := 118140960795 + 6673896 * 2 ^ 59
def prefixEnd_6673896 : Nat := 4983230072969 + 3 ^ 40 * 6673896 * 2
def baseEnd_6673896 : Nat := 3426916486118925584907317

theorem tailTrace_6673896 : CollatzResearch.WordTrace tailWord_6673896 prefixEnd_6673896 3426916486118925584907317 := by
  unfold tailWord_6673896
  simp only [CollatzResearch.WordTrace]
  refine ⟨121708492314811038768472771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162277989753081385024630361 121708492314811038768472771)
  ·
    refine ⟨182562738472216558152709157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121708492314811038768472771 182562738472216558152709157)
    ·
      refine ⟨34230513463540604653632967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182562738472216558152709157 34230513463540604653632967)
      ·
        refine ⟨51345770195310906980449451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34230513463540604653632967 51345770195310906980449451)
        ·
          refine ⟨77018655292966360470674177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51345770195310906980449451 77018655292966360470674177)
          ·
            refine ⟨57763991469724770353005633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77018655292966360470674177 57763991469724770353005633)
            ·
              refine ⟨43322993602293577764754225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57763991469724770353005633 43322993602293577764754225)
              ·
                refine ⟨32492245201720183323565669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43322993602293577764754225 32492245201720183323565669)
                ·
                  refine ⟨6092295975322534373168563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32492245201720183323565669 6092295975322534373168563)
                  ·
                    refine ⟨9138443962983801559752845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6092295975322534373168563 9138443962983801559752845)
                    ·
                      refine ⟨3426916486118925584907317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9138443962983801559752845 3426916486118925584907317)
                      ·
                        rfl

theorem cell23_6673896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6673896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673896 prefixEnd_6673896 := by exact prefixLift 6673896
  have htrace : WordTrace (prefixWord ++ tailWord_6673896) baseStart_6673896 baseEnd_6673896 := by
    simpa [prefixWord, tailWord_6673896, baseEnd_6673896] using wordTrace_append hprefix tailTrace_6673896
  have hstable : (prefixWord ++ tailWord_6673896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673896).length < 2 ^ (prefixWord ++ tailWord_6673896).sum := by decide
  have hdescent : baseEnd_6673896 < baseStart_6673896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673930 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_6673930 : Nat := 118140960795 + 6673930 * 2 ^ 59
def prefixEnd_6673930 : Nat := 4983230072969 + 3 ^ 40 * 6673930 * 2
def baseEnd_6673930 : Nat := 3426933944461178451882161

theorem tailTrace_6673930 : CollatzResearch.WordTrace tailWord_6673930 prefixEnd_6673930 3426933944461178451882161 := by
  unfold tailWord_6673930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60854556177874725335920811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162278816474332600895788829 60854556177874725335920811)
  ·
    refine ⟨91281834266812088003881217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60854556177874725335920811 91281834266812088003881217)
    ·
      refine ⟨68461375700109066002910913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91281834266812088003881217 68461375700109066002910913)
      ·
        refine ⟨51346031775081799502183185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68461375700109066002910913 51346031775081799502183185)
        ·
          refine ⟨38509523831311349626637389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51346031775081799502183185 38509523831311349626637389)
          ·
            refine ⟨14441071436741756109989021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38509523831311349626637389 14441071436741756109989021)
            ·
              refine ⟨5415401788778158541245883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14441071436741756109989021 5415401788778158541245883)
              ·
                refine ⟨8123102683167237811868825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415401788778158541245883 8123102683167237811868825)
                ·
                  refine ⟨6092327012375428358901619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8123102683167237811868825 6092327012375428358901619)
                  ·
                    refine ⟨9138490518563142538352429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6092327012375428358901619 9138490518563142538352429)
                    ·
                      refine ⟨3426933944461178451882161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9138490518563142538352429 3426933944461178451882161)
                      ·
                        rfl

theorem cell23_6673930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_6673930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673930 prefixEnd_6673930 := by exact prefixLift 6673930
  have htrace : WordTrace (prefixWord ++ tailWord_6673930) baseStart_6673930 baseEnd_6673930 := by
    simpa [prefixWord, tailWord_6673930, baseEnd_6673930] using wordTrace_append hprefix tailTrace_6673930
  have hstable : (prefixWord ++ tailWord_6673930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673930).length < 2 ^ (prefixWord ++ tailWord_6673930).sum := by decide
  have hdescent : baseEnd_6673930 < baseStart_6673930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673953 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 4, 2, 2]
def baseStart_6673953 : Nat := 118140960795 + 6673953 * 2 ^ 59
def prefixEnd_6673953 : Nat := 4983230072969 + 3 ^ 40 * 6673953 * 2
def baseEnd_6673953 : Nat := 3426945754516231861894555

theorem tailTrace_6673953 : CollatzResearch.WordTrace tailWord_6673953 prefixEnd_6673953 3426945754516231861894555 := by
  unfold tailWord_6673953
  simp only [CollatzResearch.WordTrace]
  refine ⟨243419063590415576271770513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162279375726943717514513675 243419063590415576271770513)
  ·
    refine ⟨182564297692811682203827885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243419063590415576271770513 182564297692811682203827885)
    ·
      refine ⟨68461611634804380826435457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182564297692811682203827885 68461611634804380826435457)
      ·
        refine ⟨51346208726103285619826593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68461611634804380826435457 51346208726103285619826593)
        ·
          refine ⟨38509656544577464214869945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51346208726103285619826593 38509656544577464214869945)
          ·
            refine ⟨28882242408433098161152459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38509656544577464214869945 28882242408433098161152459)
            ·
              refine ⟨43323363612649647241728689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28882242408433098161152459 43323363612649647241728689)
              ·
                refine ⟨32492522709487235431296517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43323363612649647241728689 32492522709487235431296517)
                ·
                  refine ⟨6092348008028856643368097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32492522709487235431296517 6092348008028856643368097)
                  ·
                    refine ⟨4569261006021642482526073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6092348008028856643368097 4569261006021642482526073)
                    ·
                      refine ⟨3426945754516231861894555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569261006021642482526073 3426945754516231861894555)
                      ·
                        rfl

theorem cell23_6673953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_6673953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673953 prefixEnd_6673953 := by exact prefixLift 6673953
  have htrace : WordTrace (prefixWord ++ tailWord_6673953) baseStart_6673953 baseEnd_6673953 := by
    simpa [prefixWord, tailWord_6673953, baseEnd_6673953] using wordTrace_append hprefix tailTrace_6673953
  have hstable : (prefixWord ++ tailWord_6673953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673953).length < 2 ^ (prefixWord ++ tailWord_6673953).sum := by decide
  have hdescent : baseEnd_6673953 < baseStart_6673953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673976 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 7]
def baseStart_6673976 : Nat := 118140960795 + 6673976 * 2 ^ 59
def prefixEnd_6673976 : Nat := 4983230072969 + 3 ^ 40 * 6673976 * 2
def baseEnd_6673976 : Nat := 380773062730142807989661

theorem tailTrace_6673976 : CollatzResearch.WordTrace tailWord_6673976 prefixEnd_6673976 380773062730142807989661 := by
  unfold tailWord_6673976
  simp only [CollatzResearch.WordTrace]
  refine ⟨121709951234666125599928891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162279934979554834133238521 121709951234666125599928891)
  ·
    refine ⟨182564926851999188399893337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121709951234666125599928891 182564926851999188399893337)
    ·
      refine ⟨136923695138999391299920003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182564926851999188399893337 136923695138999391299920003)
      ·
        refine ⟨205385542708499086949880005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136923695138999391299920003 205385542708499086949880005)
        ·
          refine ⟨38509789257843578803102501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205385542708499086949880005 38509789257843578803102501)
          ·
            refine ⟨7220585485845671025581719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38509789257843578803102501 7220585485845671025581719)
            ·
              refine ⟨10830878228768506538372579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220585485845671025581719 10830878228768506538372579)
              ·
                refine ⟨16246317343152759807558869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10830878228768506538372579 16246317343152759807558869)
                ·
                  refine ⟨380773062730142807989661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16246317343152759807558869 380773062730142807989661)
                  ·
                    rfl

theorem cell23_6673976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 7].length) (baseStart_6673976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673976 prefixEnd_6673976 := by exact prefixLift 6673976
  have htrace : WordTrace (prefixWord ++ tailWord_6673976) baseStart_6673976 baseEnd_6673976 := by
    simpa [prefixWord, tailWord_6673976, baseEnd_6673976] using wordTrace_append hprefix tailTrace_6673976
  have hstable : (prefixWord ++ tailWord_6673976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673976).length < 2 ^ (prefixWord ++ tailWord_6673976).sum := by decide
  have hdescent : baseEnd_6673976 < baseStart_6673976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6673989 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_6673989 : Nat := 118140960795 + 6673989 * 2 ^ 59
def prefixEnd_6673989 : Nat := 4983230072969 + 3 ^ 40 * 6673989 * 2
def baseEnd_6673989 : Nat := 1142321413273264573681463

theorem tailTrace_6673989 : CollatzResearch.WordTrace tailWord_6673989 prefixEnd_6673989 1142321413273264573681463 := by
  unfold tailWord_6673989
  simp only [CollatzResearch.WordTrace]
  refine ⟨243420376618285154420081021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162280251078856769613387347 243420376618285154420081021)
  ·
    refine ⟨91282641231856932907530383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243420376618285154420081021 91282641231856932907530383)
    ·
      refine ⟨136923961847785399361295575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91282641231856932907530383 136923961847785399361295575)
      ·
        refine ⟨205385942771678099041943363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136923961847785399361295575 205385942771678099041943363)
        ·
          refine ⟨308078914157517148562915045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205385942771678099041943363 308078914157517148562915045)
          ·
            refine ⟨57764796404534465355546571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308078914157517148562915045 57764796404534465355546571)
            ·
              refine ⟨86647194606801698033319857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57764796404534465355546571 86647194606801698033319857)
              ·
                refine ⟨64985395955101273524989893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86647194606801698033319857 64985395955101273524989893)
                ·
                  refine ⟨12184761741581488785935605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64985395955101273524989893 12184761741581488785935605)
                  ·
                    refine ⟨1142321413273264573681463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12184761741581488785935605 1142321413273264573681463)
                    ·
                      rfl

theorem cell23_6673989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_6673989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6673989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6673989 prefixEnd_6673989 := by exact prefixLift 6673989
  have htrace : WordTrace (prefixWord ++ tailWord_6673989) baseStart_6673989 baseEnd_6673989 := by
    simpa [prefixWord, tailWord_6673989, baseEnd_6673989] using wordTrace_append hprefix tailTrace_6673989
  have hstable : (prefixWord ++ tailWord_6673989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6673989).length < 2 ^ (prefixWord ++ tailWord_6673989).sum := by decide
  have hdescent : baseEnd_6673989 < baseStart_6673989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6673989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674009 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 4]
def baseStart_6674009 : Nat := 118140960795 + 6674009 * 2 ^ 59
def prefixEnd_6674009 : Nat := 4983230072969 + 3 ^ 40 * 6674009 * 2
def baseEnd_6674009 : Nat := 3426974509432883642794297

theorem tailTrace_6674009 : CollatzResearch.WordTrace tailWord_6674009 prefixEnd_6674009 3426974509432883642794297 := by
  unfold tailWord_6674009
  simp only [CollatzResearch.WordTrace]
  refine ⟨243421106078212697835809081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162280737385475131890539387 243421106078212697835809081)
  ·
    refine ⟨182565829558659523376856811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243421106078212697835809081 182565829558659523376856811)
    ·
      refine ⟨273848744337989285065285217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182565829558659523376856811 273848744337989285065285217)
      ·
        refine ⟨205386558253491963798963913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273848744337989285065285217 205386558253491963798963913)
        ·
          refine ⟨154039918690118972849222935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205386558253491963798963913 154039918690118972849222935)
          ·
            refine ⟨231059878035178459273834403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154039918690118972849222935 231059878035178459273834403)
            ·
              refine ⟨346589817052767688910751605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231059878035178459273834403 346589817052767688910751605)
              ·
                refine ⟨32492795348696970835382963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 346589817052767688910751605 32492795348696970835382963)
                ·
                  refine ⟨48739193023045456253074445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32492795348696970835382963 48739193023045456253074445)
                  ·
                    refine ⟨18277197383642046094902917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48739193023045456253074445 18277197383642046094902917)
                    ·
                      refine ⟨3426974509432883642794297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18277197383642046094902917 3426974509432883642794297)
                      ·
                        rfl

theorem cell23_6674009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_6674009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674009 prefixEnd_6674009 := by exact prefixLift 6674009
  have htrace : WordTrace (prefixWord ++ tailWord_6674009) baseStart_6674009 baseEnd_6674009 := by
    simpa [prefixWord, tailWord_6674009, baseEnd_6674009] using wordTrace_append hprefix tailTrace_6674009
  have hstable : (prefixWord ++ tailWord_6674009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674009).length < 2 ^ (prefixWord ++ tailWord_6674009).sum := by decide
  have hdescent : baseEnd_6674009 < baseStart_6674009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674039 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_6674039 : Nat := 118140960795 + 6674039 * 2 ^ 59
def prefixEnd_6674039 : Nat := 4983230072969 + 3 ^ 40 * 6674039 * 2
def baseEnd_6674039 : Nat := 3426989913852518525419159

theorem tailTrace_6674039 : CollatzResearch.WordTrace tailWord_6674039 prefixEnd_6674039 3426989913852518525419159 := by
  unfold tailWord_6674039
  simp only [CollatzResearch.WordTrace]
  refine ⟨243422200268104012959401171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162281466845402675306267447 243422200268104012959401171)
  ·
    refine ⟨365133300402156019439101757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243422200268104012959401171 365133300402156019439101757)
    ·
      refine ⟨136924987650808507289663159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365133300402156019439101757 136924987650808507289663159)
      ·
        refine ⟨205387481476212760934494739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136924987650808507289663159 205387481476212760934494739)
        ·
          refine ⟨308081222214319141401742109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205387481476212760934494739 308081222214319141401742109)
          ·
            refine ⟨115530458330369678025653291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308081222214319141401742109 115530458330369678025653291)
            ·
              refine ⟨173295687495554517038479937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115530458330369678025653291 173295687495554517038479937)
              ·
                refine ⟨129971765621665887778859953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173295687495554517038479937 129971765621665887778859953)
                ·
                  refine ⟨97478824216249415834144965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129971765621665887778859953 97478824216249415834144965)
                  ·
                    refine ⟨18277279540546765468902181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97478824216249415834144965 18277279540546765468902181)
                    ·
                      refine ⟨3426989913852518525419159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18277279540546765468902181 3426989913852518525419159)
                      ·
                        rfl

theorem cell23_6674039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_6674039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674039 prefixEnd_6674039 := by exact prefixLift 6674039
  have htrace : WordTrace (prefixWord ++ tailWord_6674039) baseStart_6674039 baseEnd_6674039 := by
    simpa [prefixWord, tailWord_6674039, baseEnd_6674039] using wordTrace_append hprefix tailTrace_6674039
  have hstable : (prefixWord ++ tailWord_6674039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674039).length < 2 ^ (prefixWord ++ tailWord_6674039).sum := by decide
  have hdescent : baseEnd_6674039 < baseStart_6674039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674069 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_6674069 : Nat := 118140960795 + 6674069 * 2 ^ 59
def prefixEnd_6674069 : Nat := 4983230072969 + 3 ^ 40 * 6674069 * 2
def baseEnd_6674069 : Nat := 3427005318272153408044021

theorem tailTrace_6674069 : CollatzResearch.WordTrace tailWord_6674069 prefixEnd_6674069 3427005318272153408044021 := by
  unfold tailWord_6674069
  simp only [CollatzResearch.WordTrace]
  refine ⟨243423294457995328082993261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162282196305330218721995507 243423294457995328082993261)
  ·
    refine ⟨91283735421748248031122473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243423294457995328082993261 91283735421748248031122473)
    ·
      refine ⟨68462801566311186023341855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91283735421748248031122473 68462801566311186023341855)
      ·
        refine ⟨102694202349466779035012783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68462801566311186023341855 102694202349466779035012783)
        ·
          refine ⟨154041303524200168552519175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102694202349466779035012783 154041303524200168552519175)
          ·
            refine ⟨231061955286300252828778763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154041303524200168552519175 231061955286300252828778763)
            ·
              refine ⟨346592932929450379243168145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231061955286300252828778763 346592932929450379243168145)
              ·
                refine ⟨259944699697087784432376109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346592932929450379243168145 259944699697087784432376109)
                ·
                  refine ⟨97479262386407919162141041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259944699697087784432376109 97479262386407919162141041)
                  ·
                    refine ⟨73109446789805939371605781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97479262386407919162141041 73109446789805939371605781)
                    ·
                      refine ⟨3427005318272153408044021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 73109446789805939371605781 3427005318272153408044021)
                      ·
                        rfl

theorem cell23_6674069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_6674069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674069 prefixEnd_6674069 := by exact prefixLift 6674069
  have htrace : WordTrace (prefixWord ++ tailWord_6674069) baseStart_6674069 baseEnd_6674069 := by
    simpa [prefixWord, tailWord_6674069, baseEnd_6674069] using wordTrace_append hprefix tailTrace_6674069
  have hstable : (prefixWord ++ tailWord_6674069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674069).length < 2 ^ (prefixWord ++ tailWord_6674069).sum := by decide
  have hdescent : baseEnd_6674069 < baseStart_6674069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674103 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 1, 5, 2]
def baseStart_6674103 : Nat := 118140960795 + 6674103 * 2 ^ 59
def prefixEnd_6674103 : Nat := 4983230072969 + 3 ^ 40 * 6674103 * 2
def baseEnd_6674103 : Nat := 3427022776614406275018865

theorem tailTrace_6674103 : CollatzResearch.WordTrace tailWord_6674103 prefixEnd_6674103 3427022776614406275018865 := by
  unfold tailWord_6674103
  simp only [CollatzResearch.WordTrace]
  refine ⟨243424534539872151889730963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162283023026581434593153975 243424534539872151889730963)
  ·
    refine ⟨365136801809808227834596445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243424534539872151889730963 365136801809808227834596445)
    ·
      refine ⟨136926300678678085437973667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365136801809808227834596445 136926300678678085437973667)
      ·
        refine ⟨205389451018017128156960501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136926300678678085437973667 205389451018017128156960501)
        ·
          refine ⟨19255261032939105764715047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205389451018017128156960501 19255261032939105764715047)
          ·
            refine ⟨28882891549408658647072571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19255261032939105764715047 28882891549408658647072571)
            ·
              refine ⟨43324337324112987970608857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28882891549408658647072571 43324337324112987970608857)
              ·
                refine ⟨32493252993084740977956643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43324337324112987970608857 32493252993084740977956643)
                ·
                  refine ⟨48739879489627111466934965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32493252993084740977956643 48739879489627111466934965)
                  ·
                    refine ⟨4569363702152541700025153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48739879489627111466934965 4569363702152541700025153)
                    ·
                      refine ⟨3427022776614406275018865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569363702152541700025153 3427022776614406275018865)
                      ·
                        rfl

theorem cell23_6674103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_6674103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674103 prefixEnd_6674103 := by exact prefixLift 6674103
  have htrace : WordTrace (prefixWord ++ tailWord_6674103) baseStart_6674103 baseEnd_6674103 := by
    simpa [prefixWord, tailWord_6674103, baseEnd_6674103] using wordTrace_append hprefix tailTrace_6674103
  have hstable : (prefixWord ++ tailWord_6674103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674103).length < 2 ^ (prefixWord ++ tailWord_6674103).sum := by decide
  have hdescent : baseEnd_6674103 < baseStart_6674103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674110 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_6674110 : Nat := 118140960795 + 6674110 * 2 ^ 59
def prefixEnd_6674110 : Nat := 4983230072969 + 3 ^ 40 * 6674110 * 2
def baseEnd_6674110 : Nat := 3427026370978987747631333

theorem tailTrace_6674110 : CollatzResearch.WordTrace tailWord_6674110 prefixEnd_6674110 3427026370978987747631333 := by
  unfold tailWord_6674110
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428098731355849010654473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162283193233897861390157189 30428098731355849010654473)
  ·
    refine ⟨22821074048516886757990855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30428098731355849010654473 22821074048516886757990855)
    ·
      refine ⟨34231611072775330136986283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22821074048516886757990855 34231611072775330136986283)
      ·
        refine ⟨51347416609162995205479425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34231611072775330136986283 51347416609162995205479425)
        ·
          refine ⟨38510562456872246404109569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51347416609162995205479425 38510562456872246404109569)
          ·
            refine ⟨28882921842654184803082177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38510562456872246404109569 28882921842654184803082177)
            ·
              refine ⟨21662191381990638602311633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28882921842654184803082177 21662191381990638602311633)
              ·
                refine ⟨16246643536492978951733725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21662191381990638602311633 16246643536492978951733725)
                ·
                  refine ⟨6092491326184867106900147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16246643536492978951733725 6092491326184867106900147)
                  ·
                    refine ⟨9138736989277300660350221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6092491326184867106900147 9138736989277300660350221)
                    ·
                      refine ⟨3427026370978987747631333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9138736989277300660350221 3427026370978987747631333)
                      ·
                        rfl

theorem cell23_6674110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_6674110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674110 prefixEnd_6674110 := by exact prefixLift 6674110
  have htrace : WordTrace (prefixWord ++ tailWord_6674110) baseStart_6674110 baseEnd_6674110 := by
    simpa [prefixWord, tailWord_6674110, baseEnd_6674110] using wordTrace_append hprefix tailTrace_6674110
  have hstable : (prefixWord ++ tailWord_6674110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674110).length < 2 ^ (prefixWord ++ tailWord_6674110).sum := by decide
  have hdescent : baseEnd_6674110 < baseStart_6674110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674126 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 3, 6]
def baseStart_6674126 : Nat := 118140960795 + 6674126 * 2 ^ 59
def prefixEnd_6674126 : Nat := 4983230072969 + 3 ^ 40 * 6674126 * 2
def baseEnd_6674126 : Nat := 1142344862223153228343753

theorem tailTrace_6674126 : CollatzResearch.WordTrace tailWord_6674126 prefixEnd_6674126 1142344862223153228343753 := by
  unfold tailWord_6674126
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428171677348603352227279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162283582279192551211878821 30428171677348603352227279)
  ·
    refine ⟨45642257516022905028340919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30428171677348603352227279 45642257516022905028340919)
    ·
      refine ⟨68463386274034357542511379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45642257516022905028340919 68463386274034357542511379)
      ·
        refine ⟨102695079411051536313767069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68463386274034357542511379 102695079411051536313767069)
        ·
          refine ⟨38510654779144326117662651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102695079411051536313767069 38510654779144326117662651)
          ·
            refine ⟨57765982168716489176493977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38510654779144326117662651 57765982168716489176493977)
            ·
              refine ⟨43324486626537366882370483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57765982168716489176493977 43324486626537366882370483)
              ·
                refine ⟨64986729939806050323555725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43324486626537366882370483 64986729939806050323555725)
                ·
                  refine ⟨24370023727427268871333397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64986729939806050323555725 24370023727427268871333397)
                  ·
                    refine ⟨1142344862223153228343753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24370023727427268871333397 1142344862223153228343753)
                    ·
                      rfl

theorem cell23_6674126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_6674126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674126 prefixEnd_6674126 := by exact prefixLift 6674126
  have htrace : WordTrace (prefixWord ++ tailWord_6674126) baseStart_6674126 baseEnd_6674126 := by
    simpa [prefixWord, tailWord_6674126, baseEnd_6674126] using wordTrace_append hprefix tailTrace_6674126
  have hstable : (prefixWord ++ tailWord_6674126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674126).length < 2 ^ (prefixWord ++ tailWord_6674126).sum := by decide
  have hdescent : baseEnd_6674126 < baseStart_6674126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674143 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 2, 4]
def baseStart_6674143 : Nat := 118140960795 + 6674143 * 2 ^ 59
def prefixEnd_6674143 : Nat := 4983230072969 + 3 ^ 40 * 6674143 * 2
def baseEnd_6674143 : Nat := 1142347771946862039506227

theorem tailTrace_6674143 : CollatzResearch.WordTrace tailWord_6674143 prefixEnd_6674143 1142347771946862039506227 := by
  unfold tailWord_6674143
  simp only [CollatzResearch.WordTrace]
  refine ⟨243425993459727238721187083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162283995639818159147458055 243425993459727238721187083)
  ·
    refine ⟨365138990189590858081780625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243425993459727238721187083 365138990189590858081780625)
    ·
      refine ⟨273854242642193143561335469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365138990189590858081780625 273854242642193143561335469)
      ·
        refine ⟨102695340990822428835500801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273854242642193143561335469 102695340990822428835500801)
        ·
          refine ⟨77021505743116821626625601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102695340990822428835500801 77021505743116821626625601)
          ·
            refine ⟨57766129307337616219969201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77021505743116821626625601 57766129307337616219969201)
            ·
              refine ⟨43324596980503212164976901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57766129307337616219969201 43324596980503212164976901)
              ·
                refine ⟨8123361933844352280933169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43324596980503212164976901 8123361933844352280933169)
                ·
                  refine ⟨6092521450383264210699877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8123361933844352280933169 6092521450383264210699877)
                  ·
                    refine ⟨1142347771946862039506227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6092521450383264210699877 1142347771946862039506227)
                    ·
                      rfl

theorem cell23_6674143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_6674143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674143 prefixEnd_6674143 := by exact prefixLift 6674143
  have htrace : WordTrace (prefixWord ++ tailWord_6674143) baseStart_6674143 baseEnd_6674143 := by
    simpa [prefixWord, tailWord_6674143, baseEnd_6674143] using wordTrace_append hprefix tailTrace_6674143
  have hstable : (prefixWord ++ tailWord_6674143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674143).length < 2 ^ (prefixWord ++ tailWord_6674143).sum := by decide
  have hdescent : baseEnd_6674143 < baseStart_6674143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674164 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6674164 : Nat := 118140960795 + 6674164 * 2 ^ 59
def prefixEnd_6674164 : Nat := 4983230072969 + 3 ^ 40 * 6674164 * 2
def baseEnd_6674164 : Nat := 1142351366311443512118695

theorem tailTrace_6674164 : CollatzResearch.WordTrace tailWord_6674164 prefixEnd_6674164 1142351366311443512118695 := by
  unfold tailWord_6674164
  simp only [CollatzResearch.WordTrace]
  refine ⟨121713379696325579653850773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162284506261767439538467697 121713379696325579653850773)
  ·
    refine ⟨5705314673265261546274255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121713379696325579653850773 5705314673265261546274255)
    ·
      refine ⟨8557972009897892319411383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5705314673265261546274255 8557972009897892319411383)
      ·
        refine ⟨12836958014846838479117075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8557972009897892319411383 12836958014846838479117075)
        ·
          refine ⟨19255437022270257718675613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12836958014846838479117075 19255437022270257718675613)
          ·
            refine ⟨7220788883351346644503355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19255437022270257718675613 7220788883351346644503355)
            ·
              refine ⟨10831183325027019966755033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220788883351346644503355 10831183325027019966755033)
              ·
                refine ⟨8123387493770264975066275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10831183325027019966755033 8123387493770264975066275)
                ·
                  refine ⟨12185081240655397462599413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123387493770264975066275 12185081240655397462599413)
                  ·
                    refine ⟨1142351366311443512118695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12185081240655397462599413 1142351366311443512118695)
                    ·
                      rfl

theorem cell23_6674164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6674164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674164 prefixEnd_6674164 := by exact prefixLift 6674164
  have htrace : WordTrace (prefixWord ++ tailWord_6674164) baseStart_6674164 baseEnd_6674164 := by
    simpa [prefixWord, tailWord_6674164, baseEnd_6674164] using wordTrace_append hprefix tailTrace_6674164
  have hstable : (prefixWord ++ tailWord_6674164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674164).length < 2 ^ (prefixWord ++ tailWord_6674164).sum := by decide
  have hdescent : baseEnd_6674164 < baseStart_6674164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674200 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_6674200 : Nat := 118140960795 + 6674200 * 2 ^ 59
def prefixEnd_6674200 : Nat := 4983230072969 + 3 ^ 40 * 6674200 * 2
def baseEnd_6674200 : Nat := 3427072584237892395505919

theorem tailTrace_6674200 : CollatzResearch.WordTrace tailWord_6674200 prefixEnd_6674200 3427072584237892395505919 := by
  unfold tailWord_6674200
  simp only [CollatzResearch.WordTrace]
  refine ⟨121714036210260368728006027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162285381613680491637341369 121714036210260368728006027)
  ·
    refine ⟨182571054315390553092009041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121714036210260368728006027 182571054315390553092009041)
    ·
      refine ⟨136928290736542914819006781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182571054315390553092009041 136928290736542914819006781)
      ·
        refine ⟨51348109026203593057127543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136928290736542914819006781 51348109026203593057127543)
        ·
          refine ⟨77022163539305389585691315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51348109026203593057127543 77022163539305389585691315)
          ·
            refine ⟨115533245308958084378536973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77022163539305389585691315 115533245308958084378536973)
            ·
              refine ⟨43324966990859281641951365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115533245308958084378536973 43324966990859281641951365)
              ·
                refine ⟨8123431310786115307865881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43324966990859281641951365 8123431310786115307865881)
                ·
                  refine ⟨6092573483089586480899411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8123431310786115307865881 6092573483089586480899411)
                  ·
                    refine ⟨9138860224634379721349117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6092573483089586480899411 9138860224634379721349117)
                    ·
                      refine ⟨3427072584237892395505919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9138860224634379721349117 3427072584237892395505919)
                      ·
                        rfl

theorem cell23_6674200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_6674200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674200 prefixEnd_6674200 := by exact prefixLift 6674200
  have htrace : WordTrace (prefixWord ++ tailWord_6674200) baseStart_6674200 baseEnd_6674200 := by
    simpa [prefixWord, tailWord_6674200, baseEnd_6674200] using wordTrace_append hprefix tailTrace_6674200
  have hstable : (prefixWord ++ tailWord_6674200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674200).length < 2 ^ (prefixWord ++ tailWord_6674200).sum := by decide
  have hdescent : baseEnd_6674200 < baseStart_6674200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674210 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_6674210 : Nat := 118140960795 + 6674210 * 2 ^ 59
def prefixEnd_6674210 : Nat := 4983230072969 + 3 ^ 40 * 6674210 * 2
def baseEnd_6674210 : Nat := 3427077719044437356380873

theorem tailTrace_6674210 : CollatzResearch.WordTrace tailWord_6674210 prefixEnd_6674210 3427077719044437356380873 := by
  unfold tailWord_6674210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60857109287621127290969021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162285624766989672775917389 60857109287621127290969021)
  ·
    refine ⟨22821415982857922734113383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60857109287621127290969021 22821415982857922734113383)
    ·
      refine ⟨34232123974286884101170075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22821415982857922734113383 34232123974286884101170075)
      ·
        refine ⟨51348185961430326151755113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34232123974286884101170075 51348185961430326151755113)
        ·
          refine ⟨38511139471072744613816335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51348185961430326151755113 38511139471072744613816335)
          ·
            refine ⟨57766709206609116920724503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38511139471072744613816335 57766709206609116920724503)
            ·
              refine ⟨86650063809913675381086755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57766709206609116920724503 86650063809913675381086755)
              ·
                refine ⟨129975095714870513071630133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86650063809913675381086755 129975095714870513071630133)
                ·
                  refine ⟨12185165223269110600465325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129975095714870513071630133 12185165223269110600465325)
                  ·
                    refine ⟨4569436958725916475174497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12185165223269110600465325 4569436958725916475174497)
                    ·
                      refine ⟨3427077719044437356380873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569436958725916475174497 3427077719044437356380873)
                      ·
                        rfl

theorem cell23_6674210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_6674210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674210 prefixEnd_6674210 := by exact prefixLift 6674210
  have htrace : WordTrace (prefixWord ++ tailWord_6674210) baseStart_6674210 baseEnd_6674210 := by
    simpa [prefixWord, tailWord_6674210, baseEnd_6674210] using wordTrace_append hprefix tailTrace_6674210
  have hstable : (prefixWord ++ tailWord_6674210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674210).length < 2 ^ (prefixWord ++ tailWord_6674210).sum := by decide
  have hdescent : baseEnd_6674210 < baseStart_6674210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674223 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 5, 4, 2]
def baseStart_6674223 : Nat := 118140960795 + 6674223 * 2 ^ 59
def prefixEnd_6674223 : Nat := 4983230072969 + 3 ^ 40 * 6674223 * 2
def baseEnd_6674223 : Nat := 3427084394292945805518313

theorem tailTrace_6674223 : CollatzResearch.WordTrace tailWord_6674223 prefixEnd_6674223 3427084394292945805518313 := by
  unfold tailWord_6674223
  simp only [CollatzResearch.WordTrace]
  refine ⟨243428911299437412384099323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162285940866291608256066215 243428911299437412384099323)
  ·
    refine ⟨365143366949156118576148985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243428911299437412384099323 365143366949156118576148985)
    ·
      refine ⟨273857525211867088932111739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365143366949156118576148985 273857525211867088932111739)
      ·
        refine ⟨410786287817800633398167609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273857525211867088932111739 410786287817800633398167609)
        ·
          refine ⟨308089715863350475048625707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410786287817800633398167609 308089715863350475048625707)
          ·
            refine ⟨462134573795025712572938561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308089715863350475048625707 462134573795025712572938561)
            ·
              refine ⟨346600930346269284429703921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 462134573795025712572938561 346600930346269284429703921)
              ·
                refine ⟨259950697759701963322277941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346600930346269284429703921 259950697759701963322277941)
                ·
                  refine ⟨24370377914972059061463557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259950697759701963322277941 24370377914972059061463557)
                  ·
                    refine ⟨4569445859057261074024417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24370377914972059061463557 4569445859057261074024417)
                    ·
                      refine ⟨3427084394292945805518313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569445859057261074024417 3427084394292945805518313)
                      ·
                        rfl

theorem cell23_6674223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 4, 2].length) (baseStart_6674223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674223 prefixEnd_6674223 := by exact prefixLift 6674223
  have htrace : WordTrace (prefixWord ++ tailWord_6674223) baseStart_6674223 baseEnd_6674223 := by
    simpa [prefixWord, tailWord_6674223, baseEnd_6674223] using wordTrace_append hprefix tailTrace_6674223
  have hstable : (prefixWord ++ tailWord_6674223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674223).length < 2 ^ (prefixWord ++ tailWord_6674223).sum := by decide
  have hdescent : baseEnd_6674223 < baseStart_6674223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674257 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 4, 2, 2]
def baseStart_6674257 : Nat := 118140960795 + 6674257 * 2 ^ 59
def prefixEnd_6674257 : Nat := 4983230072969 + 3 ^ 40 * 6674257 * 2
def baseEnd_6674257 : Nat := 3427101852635198672493157

theorem tailTrace_6674257 : CollatzResearch.WordTrace tailWord_6674257 prefixEnd_6674257 3427101852635198672493157 := by
  unfold tailWord_6674257
  simp only [CollatzResearch.WordTrace]
  refine ⟨243430151381314236190837025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162286767587542824127224683 243430151381314236190837025)
  ·
    refine ⟨182572613535985677143127769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243430151381314236190837025 182572613535985677143127769)
    ·
      refine ⟨136929460151989257857345827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182572613535985677143127769 136929460151989257857345827)
      ·
        refine ⟨205394190227983886786018741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136929460151989257857345827 205394190227983886786018741)
        ·
          refine ⟨19255705333873489386189257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 205394190227983886786018741 19255705333873489386189257)
          ·
            refine ⟨14441779000405117039641943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19255705333873489386189257 14441779000405117039641943)
            ·
              refine ⟨21662668500607675559462915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14441779000405117039641943 21662668500607675559462915)
              ·
                refine ⟨32494002750911513339194373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21662668500607675559462915 32494002750911513339194373)
                ·
                  refine ⟨6092625515795908751098945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32494002750911513339194373 6092625515795908751098945)
                  ·
                    refine ⟨4569469136846931563324209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6092625515795908751098945 4569469136846931563324209)
                    ·
                      refine ⟨3427101852635198672493157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569469136846931563324209 3427101852635198672493157)
                      ·
                        rfl

theorem cell23_6674257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_6674257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674257 prefixEnd_6674257 := by exact prefixLift 6674257
  have htrace : WordTrace (prefixWord ++ tailWord_6674257) baseStart_6674257 baseEnd_6674257 := by
    simpa [prefixWord, tailWord_6674257, baseEnd_6674257] using wordTrace_append hprefix tailTrace_6674257
  have hstable : (prefixWord ++ tailWord_6674257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674257).length < 2 ^ (prefixWord ++ tailWord_6674257).sum := by decide
  have hdescent : baseEnd_6674257 < baseStart_6674257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674273 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_6674273 : Nat := 118140960795 + 6674273 * 2 ^ 59
def prefixEnd_6674273 : Nat := 4983230072969 + 3 ^ 40 * 6674273 * 2
def baseEnd_6674273 : Nat := 3427110068325670609893083

theorem tailTrace_6674273 : CollatzResearch.WordTrace tailWord_6674273 prefixEnd_6674273 3427110068325670609893083 := by
  unfold tailWord_6674273
  simp only [CollatzResearch.WordTrace]
  refine ⟨243430734949256270923419473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162287156632837513948946315 243430734949256270923419473)
  ·
    refine ⟨182573051211942203192564605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243430734949256270923419473 182573051211942203192564605)
    ·
      refine ⟨68464894204478326197211727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182573051211942203192564605 68464894204478326197211727)
      ·
        refine ⟨102697341306717489295817591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68464894204478326197211727 102697341306717489295817591)
        ·
          refine ⟨154046011960076233943726387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102697341306717489295817591 154046011960076233943726387)
          ·
            refine ⟨231069017940114350915589581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154046011960076233943726387 231069017940114350915589581)
            ·
              refine ⟨86650881727542881593346093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231069017940114350915589581 86650881727542881593346093)
              ·
                refine ⟨32494080647828580597504785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86650881727542881593346093 32494080647828580597504785)
                ·
                  refine ⟨24370560485871435448128589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32494080647828580597504785 24370560485871435448128589)
                  ·
                    refine ⟨9138960182201788293048221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24370560485871435448128589 9138960182201788293048221)
                    ·
                      refine ⟨3427110068325670609893083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9138960182201788293048221 3427110068325670609893083)
                      ·
                        rfl

theorem cell23_6674273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_6674273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674273 prefixEnd_6674273 := by exact prefixLift 6674273
  have htrace : WordTrace (prefixWord ++ tailWord_6674273) baseStart_6674273 baseEnd_6674273 := by
    simpa [prefixWord, tailWord_6674273, baseEnd_6674273] using wordTrace_append hprefix tailTrace_6674273
  have hstable : (prefixWord ++ tailWord_6674273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674273).length < 2 ^ (prefixWord ++ tailWord_6674273).sum := by decide
  have hdescent : baseEnd_6674273 < baseStart_6674273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674274 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6674274 : Nat := 118140960795 + 6674274 * 2 ^ 59
def prefixEnd_6674274 : Nat := 4983230072969 + 3 ^ 40 * 6674274 * 2
def baseEnd_6674274 : Nat := 3427110581806325105980579

theorem tailTrace_6674274 : CollatzResearch.WordTrace tailWord_6674274 prefixEnd_6674274 3427110581806325105980579 := by
  unfold tailWord_6674274
  simp only [CollatzResearch.WordTrace]
  refine ⟨60857692855563162023551469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162287180948168432062803917 60857692855563162023551469)
  ·
    refine ⟨22821634820836185758831801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60857692855563162023551469 22821634820836185758831801)
    ·
      refine ⟨17116226115627139319123851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22821634820836185758831801 17116226115627139319123851)
      ·
        refine ⟨25674339173440708978685777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17116226115627139319123851 25674339173440708978685777)
        ·
          refine ⟨19255754380080531734014333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25674339173440708978685777 19255754380080531734014333)
          ·
            refine ⟨7220907892530199400255375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19255754380080531734014333 7220907892530199400255375)
            ·
              refine ⟨10831361838795299100383063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220907892530199400255375 10831361838795299100383063)
              ·
                refine ⟨16247042758192948650574595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831361838795299100383063 16247042758192948650574595)
                ·
                  refine ⟨24370564137289422975861893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16247042758192948650574595 24370564137289422975861893)
                  ·
                    refine ⟨4569480775741766807974105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24370564137289422975861893 4569480775741766807974105)
                    ·
                      refine ⟨3427110581806325105980579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569480775741766807974105 3427110581806325105980579)
                      ·
                        rfl

theorem cell23_6674274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6674274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674274 prefixEnd_6674274 := by exact prefixLift 6674274
  have htrace : WordTrace (prefixWord ++ tailWord_6674274) baseStart_6674274 baseEnd_6674274 := by
    simpa [prefixWord, tailWord_6674274, baseEnd_6674274] using wordTrace_append hprefix tailTrace_6674274
  have hstable : (prefixWord ++ tailWord_6674274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674274).length < 2 ^ (prefixWord ++ tailWord_6674274).sum := by decide
  have hdescent : baseEnd_6674274 < baseStart_6674274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674293 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6674293 : Nat := 118140960795 + 6674293 * 2 ^ 59
def prefixEnd_6674293 : Nat := 4983230072969 + 3 ^ 40 * 6674293 * 2
def baseEnd_6674293 : Nat := 1142373445979586843880997

theorem tailTrace_6674293 : CollatzResearch.WordTrace tailWord_6674293 prefixEnd_6674293 1142373445979586843880997 := by
  unfold tailWord_6674293
  simp only [CollatzResearch.WordTrace]
  refine ⟨243431464409183814339147533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162287642939455876226098355 243431464409183814339147533)
  ·
    refine ⟨91286799153443930377180325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243431464409183814339147533 91286799153443930377180325)
    ·
      refine ⟨17116274841270736945721311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91286799153443930377180325 17116274841270736945721311)
      ·
        refine ⟨25674412261906105418581967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17116274841270736945721311 25674412261906105418581967)
        ·
          refine ⟨38511618392859158127872951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25674412261906105418581967 38511618392859158127872951)
          ·
            refine ⟨57767427589288737191809427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38511618392859158127872951 57767427589288737191809427)
            ·
              refine ⟨86651141383933105787714141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57767427589288737191809427 86651141383933105787714141)
              ·
                refine ⟨32494178018974914670392803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86651141383933105787714141 32494178018974914670392803)
                ·
                  refine ⟨48741267028462372005589205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32494178018974914670392803 48741267028462372005589205)
                  ·
                    refine ⟨1142373445979586843880997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48741267028462372005589205 1142373445979586843880997)
                    ·
                      rfl

theorem cell23_6674293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6674293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674293 prefixEnd_6674293 := by exact prefixLift 6674293
  have htrace : WordTrace (prefixWord ++ tailWord_6674293) baseStart_6674293 baseEnd_6674293 := by
    simpa [prefixWord, tailWord_6674293, baseEnd_6674293] using wordTrace_append hprefix tailTrace_6674293
  have hstable : (prefixWord ++ tailWord_6674293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674293).length < 2 ^ (prefixWord ++ tailWord_6674293).sum := by decide
  have hdescent : baseEnd_6674293 < baseStart_6674293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674296 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_6674296 : Nat := 118140960795 + 6674296 * 2 ^ 59
def prefixEnd_6674296 : Nat := 4983230072969 + 3 ^ 40 * 6674296 * 2
def baseEnd_6674296 : Nat := 3427121878380724019905477

theorem tailTrace_6674296 : CollatzResearch.WordTrace tailWord_6674296 prefixEnd_6674296 3427121878380724019905477 := by
  unfold tailWord_6674296
  simp only [CollatzResearch.WordTrace]
  refine ⟨121715786914086472925753371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162287715885448630567671161 121715786914086472925753371)
  ·
    refine ⟨182573680371129709388630057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121715786914086472925753371 182573680371129709388630057)
    ·
      refine ⟨136930260278347282041472543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182573680371129709388630057 136930260278347282041472543)
      ·
        refine ⟨205395390417520923062208815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136930260278347282041472543 205395390417520923062208815)
        ·
          refine ⟨308093085626281384593313223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205395390417520923062208815 308093085626281384593313223)
          ·
            refine ⟨462139628439422076889969835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308093085626281384593313223 462139628439422076889969835)
            ·
              refine ⟨693209442659133115334954753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462139628439422076889969835 693209442659133115334954753)
              ·
                refine ⟨519907081994349836501216065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693209442659133115334954753 519907081994349836501216065)
                ·
                  refine ⟨389930311495762377375912049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519907081994349836501216065 389930311495762377375912049)
                  ·
                    refine ⟨292447733621821783031934037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389930311495762377375912049 292447733621821783031934037)
                    ·
                      refine ⟨3427121878380724019905477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 292447733621821783031934037 3427121878380724019905477)
                      ·
                        rfl

theorem cell23_6674296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_6674296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674296 prefixEnd_6674296 := by exact prefixLift 6674296
  have htrace : WordTrace (prefixWord ++ tailWord_6674296) baseStart_6674296 baseEnd_6674296 := by
    simpa [prefixWord, tailWord_6674296, baseEnd_6674296] using wordTrace_append hprefix tailTrace_6674296
  have hstable : (prefixWord ++ tailWord_6674296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674296).length < 2 ^ (prefixWord ++ tailWord_6674296).sum := by decide
  have hdescent : baseEnd_6674296 < baseStart_6674296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674314 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_6674314 : Nat := 118140960795 + 6674314 * 2 ^ 59
def prefixEnd_6674314 : Nat := 4983230072969 + 3 ^ 40 * 6674314 * 2
def baseEnd_6674314 : Nat := 380792346781389438831155

theorem tailTrace_6674314 : CollatzResearch.WordTrace tailWord_6674314 prefixEnd_6674314 380792346781389438831155 := by
  unfold tailWord_6674314
  simp only [CollatzResearch.WordTrace]
  refine ⟨60858057585526933731415499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162288153561405156617107997 60858057585526933731415499)
  ·
    refine ⟨91287086378290400597123249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60858057585526933731415499 91287086378290400597123249)
    ·
      refine ⟨68465314783717800447842437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91287086378290400597123249 68465314783717800447842437)
      ·
        refine ⟨12837246521947087583970457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68465314783717800447842437 12837246521947087583970457)
        ·
          refine ⟨9627934891460315687977843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12837246521947087583970457 9627934891460315687977843)
          ·
            refine ⟨14441902337190473531966765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9627934891460315687977843 14441902337190473531966765)
            ·
              refine ⟨5415713376446427574487537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14441902337190473531966765 5415713376446427574487537)
              ·
                refine ⟨4061785032334820680865653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415713376446427574487537 4061785032334820680865653)
                ·
                  refine ⟨380792346781389438831155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4061785032334820680865653 380792346781389438831155)
                  ·
                    rfl

theorem cell23_6674314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_6674314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674314 prefixEnd_6674314 := by exact prefixLift 6674314
  have htrace : WordTrace (prefixWord ++ tailWord_6674314) baseStart_6674314 baseEnd_6674314 := by
    simpa [prefixWord, tailWord_6674314, baseEnd_6674314] using wordTrace_append hprefix tailTrace_6674314
  have hstable : (prefixWord ++ tailWord_6674314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674314).length < 2 ^ (prefixWord ++ tailWord_6674314).sum := by decide
  have hdescent : baseEnd_6674314 < baseStart_6674314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674344 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6674344 : Nat := 118140960795 + 6674344 * 2 ^ 59
def prefixEnd_6674344 : Nat := 4983230072969 + 3 ^ 40 * 6674344 * 2
def baseEnd_6674344 : Nat := 1142382175150713277368419

theorem tailTrace_6674344 : CollatzResearch.WordTrace tailWord_6674344 prefixEnd_6674344 1142382175150713277368419 := by
  unfold tailWord_6674344
  simp only [CollatzResearch.WordTrace]
  refine ⟨121716662265999525024627043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162288883021332700032836057 121716662265999525024627043)
  ·
    refine ⟨182574993398999287536940565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121716662265999525024627043 182574993398999287536940565)
    ·
      refine ⟨8558202815578091603294089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182574993398999287536940565 8558202815578091603294089)
      ·
        refine ⟨6418652111683568702470567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8558202815578091603294089 6418652111683568702470567)
        ·
          refine ⟨9627978167525353053705851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418652111683568702470567 9627978167525353053705851)
          ·
            refine ⟨14441967251288029580558777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9627978167525353053705851 14441967251288029580558777)
            ·
              refine ⟨10831475438466022185419083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14441967251288029580558777 10831475438466022185419083)
              ·
                refine ⟨16247213157699033278128625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831475438466022185419083 16247213157699033278128625)
                ·
                  refine ⟨12185409868274274958596469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16247213157699033278128625 12185409868274274958596469)
                  ·
                    refine ⟨1142382175150713277368419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12185409868274274958596469 1142382175150713277368419)
                    ·
                      rfl

theorem cell23_6674344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6674344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674344 prefixEnd_6674344 := by exact prefixLift 6674344
  have htrace : WordTrace (prefixWord ++ tailWord_6674344) baseStart_6674344 baseEnd_6674344 := by
    simpa [prefixWord, tailWord_6674344, baseEnd_6674344] using wordTrace_append hprefix tailTrace_6674344
  have hstable : (prefixWord ++ tailWord_6674344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674344).length < 2 ^ (prefixWord ++ tailWord_6674344).sum := by decide
  have hdescent : baseEnd_6674344 < baseStart_6674344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674383 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 5, 5]
def baseStart_6674383 : Nat := 118140960795 + 6674383 * 2 ^ 59
def prefixEnd_6674383 : Nat := 4983230072969 + 3 ^ 40 * 6674383 * 2
def baseEnd_6674383 : Nat := 1142388850399221726505859

theorem tailTrace_6674383 : CollatzResearch.WordTrace tailWord_6674383 prefixEnd_6674383 1142388850399221726505859 := by
  unfold tailWord_6674383
  simp only [CollatzResearch.WordTrace]
  refine ⟨243434746978857759709923803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162289831319238506473282535 243434746978857759709923803)
  ·
    refine ⟨365152120468286639564885705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243434746978857759709923803 365152120468286639564885705)
    ·
      refine ⟨273864090351214979673664279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365152120468286639564885705 273864090351214979673664279)
      ·
        refine ⟨410796135526822469510496419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273864090351214979673664279 410796135526822469510496419)
        ·
          refine ⟨616194203290233704265744629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410796135526822469510496419 616194203290233704265744629)
          ·
            refine ⟨57768206558459409774913559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 616194203290233704265744629 57768206558459409774913559)
            ·
              refine ⟨86652309837689114662370339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57768206558459409774913559 86652309837689114662370339)
              ·
                refine ⟨129978464756533671993555509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86652309837689114662370339 129978464756533671993555509)
                ·
                  refine ⟨12185481070925031749395829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129978464756533671993555509 12185481070925031749395829)
                  ·
                    refine ⟨1142388850399221726505859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12185481070925031749395829 1142388850399221726505859)
                    ·
                      rfl

theorem cell23_6674383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_6674383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674383 prefixEnd_6674383 := by exact prefixLift 6674383
  have htrace : WordTrace (prefixWord ++ tailWord_6674383) baseStart_6674383 baseEnd_6674383 := by
    simpa [prefixWord, tailWord_6674383, baseEnd_6674383] using wordTrace_append hprefix tailTrace_6674383
  have hstable : (prefixWord ++ tailWord_6674383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674383).length < 2 ^ (prefixWord ++ tailWord_6674383).sum := by decide
  have hdescent : baseEnd_6674383 < baseStart_6674383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674417 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 1, 5]
def baseStart_6674417 : Nat := 118140960795 + 6674417 * 2 ^ 59
def prefixEnd_6674417 : Nat := 4983230072969 + 3 ^ 40 * 6674417 * 2
def baseEnd_6674417 : Nat := 1142394669846639348830807

theorem tailTrace_6674417 : CollatzResearch.WordTrace tailWord_6674417 prefixEnd_6674417 1142394669846639348830807 := by
  unfold tailWord_6674417
  simp only [CollatzResearch.WordTrace]
  refine ⟨243435987060734583516661505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162290658040489722344441003 243435987060734583516661505)
  ·
    refine ⟨182576990295550937637496129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243435987060734583516661505 182576990295550937637496129)
    ·
      refine ⟨136932742721663203228122097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182576990295550937637496129 136932742721663203228122097)
      ·
        refine ⟨102699557041247402421091573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136932742721663203228122097 102699557041247402421091573)
        ·
          refine ⟨9628083472616943976977335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102699557041247402421091573 9628083472616943976977335)
          ·
            refine ⟨14442125208925415965466003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628083472616943976977335 14442125208925415965466003)
            ·
              refine ⟨21663187813388123948199005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442125208925415965466003 21663187813388123948199005)
              ·
                refine ⟨8123695430020546480574627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21663187813388123948199005 8123695430020546480574627)
                ·
                  refine ⟨12185543145030819720861941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123695430020546480574627 12185543145030819720861941)
                  ·
                    refine ⟨1142394669846639348830807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12185543145030819720861941 1142394669846639348830807)
                    ·
                      rfl

theorem cell23_6674417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_6674417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674417 prefixEnd_6674417 := by exact prefixLift 6674417
  have htrace : WordTrace (prefixWord ++ tailWord_6674417) baseStart_6674417 baseEnd_6674417 := by
    simpa [prefixWord, tailWord_6674417, baseEnd_6674417] using wordTrace_append hprefix tailTrace_6674417
  have hstable : (prefixWord ++ tailWord_6674417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674417).length < 2 ^ (prefixWord ++ tailWord_6674417).sum := by decide
  have hdescent : baseEnd_6674417 < baseStart_6674417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674423 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_6674423 : Nat := 118140960795 + 6674423 * 2 ^ 59
def prefixEnd_6674423 : Nat := 4983230072969 + 3 ^ 40 * 6674423 * 2
def baseEnd_6674423 : Nat := 3427187090423845023017393

theorem tailTrace_6674423 : CollatzResearch.WordTrace tailWord_6674423 prefixEnd_6674423 3427187090423845023017393 := by
  unfold tailWord_6674423
  simp only [CollatzResearch.WordTrace]
  refine ⟨243436205898712846541379923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162290803932475231027586615 243436205898712846541379923)
  ·
    refine ⟨365154308848069269812069885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243436205898712846541379923 365154308848069269812069885)
    ·
      refine ⟨136932865818025976179526207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365154308848069269812069885 136932865818025976179526207)
      ·
        refine ⟨205399298727038964269289311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136932865818025976179526207 205399298727038964269289311)
        ·
          refine ⟨308098948090558446403933967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205399298727038964269289311 308098948090558446403933967)
          ·
            refine ⟨462148422135837669605900951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308098948090558446403933967 462148422135837669605900951)
            ·
              refine ⟨693222633203756504408851427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462148422135837669605900951 693222633203756504408851427)
              ·
                refine ⟨1039833949805634756613277141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693222633203756504408851427 1039833949805634756613277141)
                ·
                  refine ⟨24371108198569564608123683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1039833949805634756613277141 24371108198569564608123683)
                  ·
                    refine ⟨36556662297854346912185525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24371108198569564608123683 36556662297854346912185525)
                    ·
                      refine ⟨3427187090423845023017393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36556662297854346912185525 3427187090423845023017393)
                      ·
                        rfl

theorem cell23_6674423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_6674423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674423 prefixEnd_6674423 := by exact prefixLift 6674423
  have htrace : WordTrace (prefixWord ++ tailWord_6674423) baseStart_6674423 baseEnd_6674423 := by
    simpa [prefixWord, tailWord_6674423, baseEnd_6674423] using wordTrace_append hprefix tailTrace_6674423
  have hstable : (prefixWord ++ tailWord_6674423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674423).length < 2 ^ (prefixWord ++ tailWord_6674423).sum := by decide
  have hdescent : baseEnd_6674423 < baseStart_6674423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674440 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_6674440 : Nat := 118140960795 + 6674440 * 2 ^ 59
def prefixEnd_6674440 : Nat := 4983230072969 + 3 ^ 40 * 6674440 * 2
def baseEnd_6674440 : Nat := 3427195819594971456504815

theorem tailTrace_6674440 : CollatzResearch.WordTrace tailWord_6674440 prefixEnd_6674440 3427195819594971456504815 := by
  unfold tailWord_6674440
  simp only [CollatzResearch.WordTrace]
  refine ⟨121718412969825629222374387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162291217293100838963165849 121718412969825629222374387)
  ·
    refine ⟨182577619454738443833561581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121718412969825629222374387 182577619454738443833561581)
    ·
      refine ⟨68466607295526916437585593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182577619454738443833561581 68466607295526916437585593)
      ·
        refine ⟨51349955471645187328189195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68466607295526916437585593 51349955471645187328189195)
        ·
          refine ⟨77024933207467780992283793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51349955471645187328189195 77024933207467780992283793)
          ·
            refine ⟨57768699905600835744212845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77024933207467780992283793 57768699905600835744212845)
            ·
              refine ⟨21663262464600313404079817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57768699905600835744212845 21663262464600313404079817)
              ·
                refine ⟨16247446848450235053059863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21663262464600313404079817 16247446848450235053059863)
                ·
                  refine ⟨24371170272675352579589795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16247446848450235053059863 24371170272675352579589795)
                  ·
                    refine ⟨36556755409013028869384693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24371170272675352579589795 36556755409013028869384693)
                    ·
                      refine ⟨3427195819594971456504815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36556755409013028869384693 3427195819594971456504815)
                      ·
                        rfl

theorem cell23_6674440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_6674440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674440 prefixEnd_6674440 := by exact prefixLift 6674440
  have htrace : WordTrace (prefixWord ++ tailWord_6674440) baseStart_6674440 baseEnd_6674440 := by
    simpa [prefixWord, tailWord_6674440, baseEnd_6674440] using wordTrace_append hprefix tailTrace_6674440
  have hstable : (prefixWord ++ tailWord_6674440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674440).length < 2 ^ (prefixWord ++ tailWord_6674440).sum := by decide
  have hdescent : baseEnd_6674440 < baseStart_6674440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674443 : List Nat := [1, 1, 1, 1, 6, 1, 2, 10]
def baseStart_6674443 : Nat := 118140960795 + 6674443 * 2 ^ 59
def prefixEnd_6674443 : Nat := 4983230072969 + 3 ^ 40 * 6674443 * 2
def baseEnd_6674443 : Nat := 126933235556923516472863

theorem tailTrace_6674443 : CollatzResearch.WordTrace tailWord_6674443 prefixEnd_6674443 126933235556923516472863 := by
  unfold tailWord_6674443
  simp only [CollatzResearch.WordTrace]
  refine ⟨243436935358640389957107983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162291290239093593304738655 243436935358640389957107983)
  ·
    refine ⟨365155403037960584935661975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243436935358640389957107983 365155403037960584935661975)
    ·
      refine ⟨547733104556940877403492963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365155403037960584935661975 547733104556940877403492963)
      ·
        refine ⟨821599656835411316105239445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547733104556940877403492963 821599656835411316105239445)
        ·
          refine ⟨38512483914159905442433099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 821599656835411316105239445 38512483914159905442433099)
          ·
            refine ⟨57768725871239858163649649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38512483914159905442433099 57768725871239858163649649)
            ·
              refine ⟨43326544403429893622737237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57768725871239858163649649 43326544403429893622737237)
              ·
                refine ⟨126933235556923516472863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43326544403429893622737237 126933235556923516472863)
                ·
                  rfl

theorem cell23_6674443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 10].length) (baseStart_6674443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674443 prefixEnd_6674443 := by exact prefixLift 6674443
  have htrace : WordTrace (prefixWord ++ tailWord_6674443) baseStart_6674443 baseEnd_6674443 := by
    simpa [prefixWord, tailWord_6674443, baseEnd_6674443] using wordTrace_append hprefix tailTrace_6674443
  have hstable : (prefixWord ++ tailWord_6674443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674443).length < 2 ^ (prefixWord ++ tailWord_6674443).sum := by decide
  have hdescent : baseEnd_6674443 < baseStart_6674443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674460 : List Nat := [2, 2, 3, 1, 3, 2, 1, 9]
def baseStart_6674460 : Nat := 118140960795 + 6674460 * 2 ^ 59
def prefixEnd_6674460 : Nat := 4983230072969 + 3 ^ 40 * 6674460 * 2
def baseEnd_6674460 : Nat := 126933558859557828824249

theorem tailTrace_6674460 : CollatzResearch.WordTrace tailWord_6674460 prefixEnd_6674460 126933558859557828824249 := by
  unfold tailWord_6674460
  simp only [CollatzResearch.WordTrace]
  refine ⟨121718777699789400930238417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162291703599719201240317889 121718777699789400930238417)
  ·
    refine ⟨91289083274842050697678813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121718777699789400930238417 91289083274842050697678813)
    ·
      refine ⟨34233406228065769011629555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91289083274842050697678813 34233406228065769011629555)
      ·
        refine ⟨51350109342098653517444333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34233406228065769011629555 51350109342098653517444333)
        ·
          refine ⟨19256291003286995069041625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51350109342098653517444333 19256291003286995069041625)
          ·
            refine ⟨14442218252465246301781219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19256291003286995069041625 14442218252465246301781219)
            ·
              refine ⟨21663327378697869452671829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442218252465246301781219 21663327378697869452671829)
              ·
                refine ⟨126933558859557828824249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21663327378697869452671829 126933558859557828824249)
                ·
                  rfl

theorem cell23_6674460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 9].length) (baseStart_6674460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674460 prefixEnd_6674460 := by exact prefixLift 6674460
  have htrace : WordTrace (prefixWord ++ tailWord_6674460) baseStart_6674460 baseEnd_6674460 := by
    simpa [prefixWord, tailWord_6674460, baseEnd_6674460] using wordTrace_append hprefix tailTrace_6674460
  have hstable : (prefixWord ++ tailWord_6674460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674460).length < 2 ^ (prefixWord ++ tailWord_6674460).sum := by decide
  have hdescent : baseEnd_6674460 < baseStart_6674460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674474 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_6674474 : Nat := 118140960795 + 6674474 * 2 ^ 59
def prefixEnd_6674474 : Nat := 4983230072969 + 3 ^ 40 * 6674474 * 2
def baseEnd_6674474 : Nat := 3427213277937224323479659

theorem tailTrace_6674474 : CollatzResearch.WordTrace tailWord_6674474 prefixEnd_6674474 3427213277937224323479659 := by
  unfold tailWord_6674474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60859516505382020562871619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162292044014352054834324317 60859516505382020562871619)
  ·
    refine ⟨91289274758073030844307429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60859516505382020562871619 91289274758073030844307429)
    ·
      refine ⟨17116739017138693283307643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91289274758073030844307429 17116739017138693283307643)
      ·
        refine ⟨25675108525708039924961465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17116739017138693283307643 25675108525708039924961465)
        ·
          refine ⟨19256331394281029943721099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25675108525708039924961465 19256331394281029943721099)
          ·
            refine ⟨28884497091421544915581649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19256331394281029943721099 28884497091421544915581649)
            ·
              refine ⟨21663372818566158686686237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28884497091421544915581649 21663372818566158686686237)
              ·
                refine ⟨8123764806962309507507339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21663372818566158686686237 8123764806962309507507339)
                ·
                  refine ⟨12185647210443464261261009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123764806962309507507339 12185647210443464261261009)
                  ·
                    refine ⟨9139235407832598195945757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12185647210443464261261009 9139235407832598195945757)
                    ·
                      refine ⟨3427213277937224323479659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9139235407832598195945757 3427213277937224323479659)
                      ·
                        rfl

theorem cell23_6674474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_6674474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674474 prefixEnd_6674474 := by exact prefixLift 6674474
  have htrace : WordTrace (prefixWord ++ tailWord_6674474) baseStart_6674474 baseEnd_6674474 := by
    simpa [prefixWord, tailWord_6674474, baseEnd_6674474] using wordTrace_append hprefix tailTrace_6674474
  have hstable : (prefixWord ++ tailWord_6674474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674474).length < 2 ^ (prefixWord ++ tailWord_6674474).sum := by decide
  have hdescent : baseEnd_6674474 < baseStart_6674474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674487 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_6674487 : Nat := 118140960795 + 6674487 * 2 ^ 59
def prefixEnd_6674487 : Nat := 4983230072969 + 3 ^ 40 * 6674487 * 2
def baseEnd_6674487 : Nat := 3427219953185732772617099

theorem tailTrace_6674487 : CollatzResearch.WordTrace tailWord_6674487 prefixEnd_6674487 3427219953185732772617099 := by
  unfold tailWord_6674487
  simp only [CollatzResearch.WordTrace]
  refine ⟨243438540170480985471709715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162292360113653990314473143 243438540170480985471709715)
  ·
    refine ⟨365157810255721478207564573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243438540170480985471709715 365157810255721478207564573)
    ·
      refine ⟨136934178845895554327836715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365157810255721478207564573 136934178845895554327836715)
      ·
        refine ⟨205401268268843331491755073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136934178845895554327836715 205401268268843331491755073)
        ·
          refine ⟨154050951201632498618816305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205401268268843331491755073 154050951201632498618816305)
          ·
            refine ⟨115538213401224373964112229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154050951201632498618816305 115538213401224373964112229)
            ·
              refine ⟨21663415012729570118271043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115538213401224373964112229 21663415012729570118271043)
              ·
                refine ⟨32495122519094355177406565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21663415012729570118271043 32495122519094355177406565)
                ·
                  refine ⟨6092835472330191595763731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32495122519094355177406565 6092835472330191595763731)
                  ·
                    refine ⟨9139253208495287393645597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6092835472330191595763731 9139253208495287393645597)
                    ·
                      refine ⟨3427219953185732772617099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9139253208495287393645597 3427219953185732772617099)
                      ·
                        rfl

theorem cell23_6674487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_6674487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674487 prefixEnd_6674487 := by exact prefixLift 6674487
  have htrace : WordTrace (prefixWord ++ tailWord_6674487) baseStart_6674487 baseEnd_6674487 := by
    simpa [prefixWord, tailWord_6674487, baseEnd_6674487] using wordTrace_append hprefix tailTrace_6674487
  have hstable : (prefixWord ++ tailWord_6674487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674487).length < 2 ^ (prefixWord ++ tailWord_6674487).sum := by decide
  have hdescent : baseEnd_6674487 < baseStart_6674487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674488 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 3, 2, 2]
def baseStart_6674488 : Nat := 118140960795 + 6674488 * 2 ^ 59
def prefixEnd_6674488 : Nat := 4983230072969 + 3 ^ 40 * 6674488 * 2
def baseEnd_6674488 : Nat := 3427220466666387268704595

theorem tailTrace_6674488 : CollatzResearch.WordTrace tailWord_6674488 prefixEnd_6674488 3427220466666387268704595 := by
  unfold tailWord_6674488
  simp only [CollatzResearch.WordTrace]
  refine ⟨121719288321738681321248059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162292384428984908428330745 121719288321738681321248059)
  ·
    refine ⟨182578932482608021981872089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121719288321738681321248059 182578932482608021981872089)
    ·
      refine ⟨136934199361956016486404067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182578932482608021981872089 136934199361956016486404067)
      ·
        refine ⟨205401299042934024729606101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136934199361956016486404067 205401299042934024729606101)
        ·
          refine ⟨4814092946318766204600143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 205401299042934024729606101 4814092946318766204600143)
          ·
            refine ⟨7221139419478149306900215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814092946318766204600143 7221139419478149306900215)
            ·
              refine ⟨10831709129217223960350323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221139419478149306900215 10831709129217223960350323)
              ·
                refine ⟨16247563693825835940525485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831709129217223960350323 16247563693825835940525485)
                ·
                  refine ⟨6092836385184688477697057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16247563693825835940525485 6092836385184688477697057)
                  ·
                    refine ⟨4569627288888516358272793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6092836385184688477697057 4569627288888516358272793)
                    ·
                      refine ⟨3427220466666387268704595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569627288888516358272793 3427220466666387268704595)
                      ·
                        rfl

theorem cell23_6674488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_6674488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674488 prefixEnd_6674488 := by exact prefixLift 6674488
  have htrace : WordTrace (prefixWord ++ tailWord_6674488) baseStart_6674488 baseEnd_6674488 := by
    simpa [prefixWord, tailWord_6674488, baseEnd_6674488] using wordTrace_append hprefix tailTrace_6674488
  have hstable : (prefixWord ++ tailWord_6674488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674488).length < 2 ^ (prefixWord ++ tailWord_6674488).sum := by decide
  have hdescent : baseEnd_6674488 < baseStart_6674488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674557 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_6674557 : Nat := 118140960795 + 6674557 * 2 ^ 59
def prefixEnd_6674557 : Nat := 4983230072969 + 3 ^ 40 * 6674557 * 2
def baseEnd_6674557 : Nat := 3427255896831547498741777

theorem tailTrace_6674557 : CollatzResearch.WordTrace tailWord_6674557 prefixEnd_6674557 3427255896831547498741777 := by
  unfold tailWord_6674557
  simp only [CollatzResearch.WordTrace]
  refine ⟨243441093280227387426757925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162294062186818258284505283 243441093280227387426757925)
  ·
    refine ⟨45645204990042635142517111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243441093280227387426757925 45645204990042635142517111)
    ·
      refine ⟨68467807485063952713775667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45645204990042635142517111 68467807485063952713775667)
      ·
        refine ⟨102701711227595929070663501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68467807485063952713775667 102701711227595929070663501)
        ·
          refine ⟨38513141710348473401498813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102701711227595929070663501 38513141710348473401498813)
          ·
            refine ⟨14442428141380677525562055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38513141710348473401498813 14442428141380677525562055)
            ·
              refine ⟨21663642212071016288343083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442428141380677525562055 21663642212071016288343083)
              ·
                refine ⟨32495463318106524432514625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21663642212071016288343083 32495463318106524432514625)
                ·
                  refine ⟨24371597488579893324385969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32495463318106524432514625 24371597488579893324385969)
                  ·
                    refine ⟨18278698116434919993289477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24371597488579893324385969 18278698116434919993289477)
                    ·
                      refine ⟨3427255896831547498741777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18278698116434919993289477 3427255896831547498741777)
                      ·
                        rfl

theorem cell23_6674557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_6674557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674557 prefixEnd_6674557 := by exact prefixLift 6674557
  have htrace : WordTrace (prefixWord ++ tailWord_6674557) baseStart_6674557 baseEnd_6674557 := by
    simpa [prefixWord, tailWord_6674557, baseEnd_6674557] using wordTrace_append hprefix tailTrace_6674557
  have hstable : (prefixWord ++ tailWord_6674557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674557).length < 2 ^ (prefixWord ++ tailWord_6674557).sum := by decide
  have hdescent : baseEnd_6674557 < baseStart_6674557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674561 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_6674561 : Nat := 118140960795 + 6674561 * 2 ^ 59
def prefixEnd_6674561 : Nat := 4983230072969 + 3 ^ 40 * 6674561 * 2
def baseEnd_6674561 : Nat := 3427257950754165483091759

theorem tailTrace_6674561 : CollatzResearch.WordTrace tailWord_6674561 prefixEnd_6674561 3427257950754165483091759 := by
  unfold tailWord_6674561
  simp only [CollatzResearch.WordTrace]
  refine ⟨243441239172212896109903537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162294159448141930739935691 243441239172212896109903537)
  ·
    refine ⟨182580929379159672082427653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243441239172212896109903537 182580929379159672082427653)
    ·
      refine ⟨34233924258592438515455185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182580929379159672082427653 34233924258592438515455185)
      ·
        refine ⟨25675443193944328886591389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34233924258592438515455185 25675443193944328886591389)
        ·
          refine ⟨9628291197729123332471771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25675443193944328886591389 9628291197729123332471771)
          ·
            refine ⟨14442436796593684998707657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628291197729123332471771 14442436796593684998707657)
            ·
              refine ⟨10831827597445263749030743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14442436796593684998707657 10831827597445263749030743)
              ·
                refine ⟨16247741396167895623546115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831827597445263749030743 16247741396167895623546115)
                ·
                  refine ⟨24371612094251843435319173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16247741396167895623546115 24371612094251843435319173)
                  ·
                    refine ⟨4569677267672220644122345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24371612094251843435319173 4569677267672220644122345)
                    ·
                      refine ⟨3427257950754165483091759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569677267672220644122345 3427257950754165483091759)
                      ·
                        rfl

theorem cell23_6674561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_6674561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674561 prefixEnd_6674561 := by exact prefixLift 6674561
  have htrace : WordTrace (prefixWord ++ tailWord_6674561) baseStart_6674561 baseEnd_6674561 := by
    simpa [prefixWord, tailWord_6674561, baseEnd_6674561] using wordTrace_append hprefix tailTrace_6674561
  have hstable : (prefixWord ++ tailWord_6674561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674561).length < 2 ^ (prefixWord ++ tailWord_6674561).sum := by decide
  have hdescent : baseEnd_6674561 < baseStart_6674561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674594 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6674594 : Nat := 118140960795 + 6674594 * 2 ^ 59
def prefixEnd_6674594 : Nat := 4983230072969 + 3 ^ 40 * 6674594 * 2
def baseEnd_6674594 : Nat := 3427274895615763853979107

theorem tailTrace_6674594 : CollatzResearch.WordTrace tailWord_6674594 prefixEnd_6674594 3427274895615763853979107 := by
  unfold tailWord_6674594
  simp only [CollatzResearch.WordTrace]
  refine ⟨60860610695273335686463709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162294961854062228497236557 60860610695273335686463709)
  ·
    refine ⟨22822729010727500882423891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60860610695273335686463709 22822729010727500882423891)
    ·
      refine ⟨34234093516091251323635837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22822729010727500882423891 34234093516091251323635837)
      ·
        refine ⟨12837785068534219246363439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34234093516091251323635837 12837785068534219246363439)
        ·
          refine ⟨19256677602801328869545159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12837785068534219246363439 19256677602801328869545159)
          ·
            refine ⟨28885016404201993304317739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19256677602801328869545159 28885016404201993304317739)
            ·
              refine ⟨43327524606302989956476609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28885016404201993304317739 43327524606302989956476609)
              ·
                refine ⟨32495643454727242467357457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43327524606302989956476609 32495643454727242467357457)
                ·
                  refine ⟨24371732591045431850518093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32495643454727242467357457 24371732591045431850518093)
                  ·
                    refine ⟨9139399721642036943944285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24371732591045431850518093 9139399721642036943944285)
                    ·
                      refine ⟨3427274895615763853979107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9139399721642036943944285 3427274895615763853979107)
                      ·
                        rfl

theorem cell23_6674594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6674594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674594 prefixEnd_6674594 := by exact prefixLift 6674594
  have htrace : WordTrace (prefixWord ++ tailWord_6674594) baseStart_6674594 baseEnd_6674594 := by
    simpa [prefixWord, tailWord_6674594, baseEnd_6674594] using wordTrace_append hprefix tailTrace_6674594
  have hstable : (prefixWord ++ tailWord_6674594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674594).length < 2 ^ (prefixWord ++ tailWord_6674594).sum := by decide
  have hdescent : baseEnd_6674594 < baseStart_6674594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674612 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_6674612 : Nat := 118140960795 + 6674612 * 2 ^ 59
def prefixEnd_6674612 : Nat := 4983230072969 + 3 ^ 40 * 6674612 * 2
def baseEnd_6674612 : Nat := 3427284138267544783554025

theorem tailTrace_6674612 : CollatzResearch.WordTrace tailWord_6674612 prefixEnd_6674612 3427284138267544783554025 := by
  unfold tailWord_6674612
  simp only [CollatzResearch.WordTrace]
  refine ⟨121721549647514065910005045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162295399530018754546673393 121721549647514065910005045)
  ·
    refine ⟨11411395279454443679062973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121721549647514065910005045 11411395279454443679062973)
    ·
      refine ⟨4279273229795416379648615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11411395279454443679062973 4279273229795416379648615)
      ·
        refine ⟨6418909844693124569472923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279273229795416379648615 6418909844693124569472923)
        ·
          refine ⟨9628364767039686854209385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418909844693124569472923 9628364767039686854209385)
          ·
            refine ⟨7221273575279765140657039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9628364767039686854209385 7221273575279765140657039)
            ·
              refine ⟨10831910362919647710985559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221273575279765140657039 10831910362919647710985559)
              ·
                refine ⟨16247865544379471566478339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831910362919647710985559 16247865544379471566478339)
                ·
                  refine ⟨24371798316569207349717509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16247865544379471566478339 24371798316569207349717509)
                  ·
                    refine ⟨4569712184356726378072033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24371798316569207349717509 4569712184356726378072033)
                    ·
                      refine ⟨3427284138267544783554025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569712184356726378072033 3427284138267544783554025)
                      ·
                        rfl

theorem cell23_6674612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_6674612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674612 prefixEnd_6674612 := by exact prefixLift 6674612
  have htrace : WordTrace (prefixWord ++ tailWord_6674612) baseStart_6674612 baseEnd_6674612 := by
    simpa [prefixWord, tailWord_6674612, baseEnd_6674612] using wordTrace_append hprefix tailTrace_6674612
  have hstable : (prefixWord ++ tailWord_6674612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674612).length < 2 ^ (prefixWord ++ tailWord_6674612).sum := by decide
  have hdescent : baseEnd_6674612 < baseStart_6674612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674657 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 6]
def baseStart_6674657 : Nat := 118140960795 + 6674657 * 2 ^ 59
def prefixEnd_6674657 : Nat := 4983230072969 + 3 ^ 40 * 6674657 * 2
def baseEnd_6674657 : Nat := 380811916099666345276813

theorem tailTrace_6674657 : CollatzResearch.WordTrace tailWord_6674657 prefixEnd_6674657 380811916099666345276813 := by
  unfold tailWord_6674657
  simp only [CollatzResearch.WordTrace]
  refine ⟨243444740579865104505398225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162296493719910069670265483 243444740579865104505398225)
  ·
    refine ⟨182583555434898828379048669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243444740579865104505398225 182583555434898828379048669)
    ·
      refine ⟨68468833288087060642143251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182583555434898828379048669 68468833288087060642143251)
      ·
        refine ⟨102703249932130590963214877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68468833288087060642143251 102703249932130590963214877)
        ·
          refine ⟨38513718724548971611205579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102703249932130590963214877 38513718724548971611205579)
          ·
            refine ⟨57770578086823457416808369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38513718724548971611205579 57770578086823457416808369)
            ·
              refine ⟨43327933565117593062606277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57770578086823457416808369 43327933565117593062606277)
              ·
                refine ⟨8123987543459548699238677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43327933565117593062606277 8123987543459548699238677)
                ·
                  refine ⟨380811916099666345276813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8123987543459548699238677 380811916099666345276813)
                  ·
                    rfl

theorem cell23_6674657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 6].length) (baseStart_6674657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674657 prefixEnd_6674657 := by exact prefixLift 6674657
  have htrace : WordTrace (prefixWord ++ tailWord_6674657) baseStart_6674657 baseEnd_6674657 := by
    simpa [prefixWord, tailWord_6674657, baseEnd_6674657] using wordTrace_append hprefix tailTrace_6674657
  have hstable : (prefixWord ++ tailWord_6674657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674657).length < 2 ^ (prefixWord ++ tailWord_6674657).sum := by decide
  have hdescent : baseEnd_6674657 < baseStart_6674657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674658 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6674658 : Nat := 118140960795 + 6674658 * 2 ^ 59
def prefixEnd_6674658 : Nat := 4983230072969 + 3 ^ 40 * 6674658 * 2
def baseEnd_6674658 : Nat := 3427307758377651603578813

theorem tailTrace_6674658 : CollatzResearch.WordTrace tailWord_6674658 prefixEnd_6674658 3427307758377651603578813 := by
  unfold tailWord_6674658
  simp only [CollatzResearch.WordTrace]
  refine ⟨60861194263215370419046157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162296518035240987784123085 60861194263215370419046157)
  ·
    refine ⟨22822947848705763907142309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60861194263215370419046157 22822947848705763907142309)
    ·
      refine ⟨4279302721632330732589183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22822947848705763907142309 4279302721632330732589183)
      ·
        refine ⟨6418954082448496098883775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279302721632330732589183 6418954082448496098883775)
        ·
          refine ⟨9628431123672744148325663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418954082448496098883775 9628431123672744148325663)
          ·
            refine ⟨14442646685509116222488495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628431123672744148325663 14442646685509116222488495)
            ·
              refine ⟨21663970028263674333732743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442646685509116222488495 21663970028263674333732743)
              ·
                refine ⟨32495955042395511500599115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21663970028263674333732743 32495955042395511500599115)
                ·
                  refine ⟨48743932563593267250898673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32495955042395511500599115 48743932563593267250898673)
                  ·
                    refine ⟨36557949422694950438174005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48743932563593267250898673 36557949422694950438174005)
                    ·
                      refine ⟨3427307758377651603578813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36557949422694950438174005 3427307758377651603578813)
                      ·
                        rfl

theorem cell23_6674658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6674658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674658 prefixEnd_6674658 := by exact prefixLift 6674658
  have htrace : WordTrace (prefixWord ++ tailWord_6674658) baseStart_6674658 baseEnd_6674658 := by
    simpa [prefixWord, tailWord_6674658, baseEnd_6674658] using wordTrace_append hprefix tailTrace_6674658
  have hstable : (prefixWord ++ tailWord_6674658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674658).length < 2 ^ (prefixWord ++ tailWord_6674658).sum := by decide
  have hdescent : baseEnd_6674658 < baseStart_6674658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674661 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_6674661 : Nat := 118140960795 + 6674661 * 2 ^ 59
def prefixEnd_6674661 : Nat := 4983230072969 + 3 ^ 40 * 6674661 * 2
def baseEnd_6674661 : Nat := 1142436432939871697280433

theorem tailTrace_6674661 : CollatzResearch.WordTrace tailWord_6674661 prefixEnd_6674661 1142436432939871697280433 := by
  unfold tailWord_6674661
  simp only [CollatzResearch.WordTrace]
  refine ⟨243444886471850613188543837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162296590981233742125695891 243444886471850613188543837)
  ·
    refine ⟨91291832426943979945703939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243444886471850613188543837 91291832426943979945703939)
    ·
      refine ⟨136937748640415969918555909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91291832426943979945703939 136937748640415969918555909)
      ·
        refine ⟨25675827870077994359729233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136937748640415969918555909 25675827870077994359729233)
        ·
          refine ⟨19256870902558495769796925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25675827870077994359729233 19256870902558495769796925)
          ·
            refine ⟨7221326588459435913673847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19256870902558495769796925 7221326588459435913673847)
            ·
              refine ⟨10831989882689153870510771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221326588459435913673847 10831989882689153870510771)
              ·
                refine ⟨16247984824033730805766157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10831989882689153870510771 16247984824033730805766157)
                ·
                  refine ⟨6092994309012649052162309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16247984824033730805766157 6092994309012649052162309)
                  ·
                    refine ⟨1142436432939871697280433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6092994309012649052162309 1142436432939871697280433)
                    ·
                      rfl

theorem cell23_6674661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_6674661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674661 prefixEnd_6674661 := by exact prefixLift 6674661
  have htrace : WordTrace (prefixWord ++ tailWord_6674661) baseStart_6674661 baseEnd_6674661 := by
    simpa [prefixWord, tailWord_6674661, baseEnd_6674661] using wordTrace_append hprefix tailTrace_6674661
  have hstable : (prefixWord ++ tailWord_6674661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674661).length < 2 ^ (prefixWord ++ tailWord_6674661).sum := by decide
  have hdescent : baseEnd_6674661 < baseStart_6674661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674674 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_6674674 : Nat := 118140960795 + 6674674 * 2 ^ 59
def prefixEnd_6674674 : Nat := 4983230072969 + 3 ^ 40 * 6674674 * 2
def baseEnd_6674674 : Nat := 380812886007569282330971

theorem tailTrace_6674674 : CollatzResearch.WordTrace tailWord_6674674 prefixEnd_6674674 380812886007569282330971 := by
  unfold tailWord_6674674
  simp only [CollatzResearch.WordTrace]
  refine ⟨60861340155200879102191769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162296907080535677605844717 60861340155200879102191769)
  ·
    refine ⟨45646005116400659326643827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60861340155200879102191769 45646005116400659326643827)
    ·
      refine ⟨68469007674600988989965741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45646005116400659326643827 68469007674600988989965741)
      ·
        refine ⟨25675877877975370871237153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68469007674600988989965741 25675877877975370871237153)
        ·
          refine ⟨19256908408481528153427865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25675877877975370871237153 19256908408481528153427865)
          ·
            refine ⟨14442681306361146115070899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19256908408481528153427865 14442681306361146115070899)
            ·
              refine ⟨21664021959541719172606349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14442681306361146115070899 21664021959541719172606349)
              ·
                refine ⟨8124008234828144689727381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21664021959541719172606349 8124008234828144689727381)
                ·
                  refine ⟨380812886007569282330971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8124008234828144689727381 380812886007569282330971)
                  ·
                    rfl

theorem cell23_6674674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_6674674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674674 prefixEnd_6674674 := by exact prefixLift 6674674
  have htrace : WordTrace (prefixWord ++ tailWord_6674674) baseStart_6674674 baseEnd_6674674 := by
    simpa [prefixWord, tailWord_6674674, baseEnd_6674674] using wordTrace_append hprefix tailTrace_6674674
  have hstable : (prefixWord ++ tailWord_6674674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674674).length < 2 ^ (prefixWord ++ tailWord_6674674).sum := by decide
  have hdescent : baseEnd_6674674 < baseStart_6674674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674687 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 3, 5]
def baseStart_6674687 : Nat := 118140960795 + 6674687 * 2 ^ 59
def prefixEnd_6674687 : Nat := 4983230072969 + 3 ^ 40 * 6674687 * 2
def baseEnd_6674687 : Nat := 1142440883105543996705393

theorem tailTrace_6674687 : CollatzResearch.WordTrace tailWord_6674687 prefixEnd_6674687 1142440883105543996705393 := by
  unfold tailWord_6674687
  simp only [CollatzResearch.WordTrace]
  refine ⟨243445834769756419628990315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162297223179837613085993543 243445834769756419628990315)
  ·
    refine ⟨365168752154634629443485473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243445834769756419628990315 365168752154634629443485473)
    ·
      refine ⟨273876564115975972082614105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365168752154634629443485473 273876564115975972082614105)
      ·
        refine ⟨205407423086981979061960579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273876564115975972082614105 205407423086981979061960579)
        ·
          refine ⟨308111134630472968592940869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205407423086981979061960579 308111134630472968592940869)
          ·
            refine ⟨57770837743213681611176413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308111134630472968592940869 57770837743213681611176413)
            ·
              refine ⟨21664064153705130604191155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57770837743213681611176413 21664064153705130604191155)
              ·
                refine ⟨32496096230557695906286733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21664064153705130604191155 32496096230557695906286733)
                ·
                  refine ⟨12186036086459135964857525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32496096230557695906286733 12186036086459135964857525)
                  ·
                    refine ⟨1142440883105543996705393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12186036086459135964857525 1142440883105543996705393)
                    ·
                      rfl

theorem cell23_6674687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_6674687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674687 prefixEnd_6674687 := by exact prefixLift 6674687
  have htrace : WordTrace (prefixWord ++ tailWord_6674687) baseStart_6674687 baseEnd_6674687 := by
    simpa [prefixWord, tailWord_6674687, baseEnd_6674687] using wordTrace_append hprefix tailTrace_6674687
  have hstable : (prefixWord ++ tailWord_6674687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674687).length < 2 ^ (prefixWord ++ tailWord_6674687).sum := by decide
  have hdescent : baseEnd_6674687 < baseStart_6674687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674711 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 2, 3, 2]
def baseStart_6674711 : Nat := 118140960795 + 6674711 * 2 ^ 59
def prefixEnd_6674711 : Nat := 4983230072969 + 3 ^ 40 * 6674711 * 2
def baseEnd_6674711 : Nat := 3427334972852339896216069

theorem tailTrace_6674711 : CollatzResearch.WordTrace tailWord_6674711 prefixEnd_6674711 3427334972852339896216069 := by
  unfold tailWord_6674711
  simp only [CollatzResearch.WordTrace]
  refine ⟨243446710121669471727863987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162297806747779647818575991 243446710121669471727863987)
  ·
    refine ⟨365170065182504207591795981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243446710121669471727863987 365170065182504207591795981)
    ·
      refine ⟨136938774443439077846923493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365170065182504207591795981 136938774443439077846923493)
      ·
        refine ⟨25676020208144827096298155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136938774443439077846923493 25676020208144827096298155)
        ·
          refine ⟨38514030312217240644447233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25676020208144827096298155 38514030312217240644447233)
          ·
            refine ⟨28885522734162930483335425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38514030312217240644447233 28885522734162930483335425)
            ·
              refine ⟨21664142050622197862501569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28885522734162930483335425 21664142050622197862501569)
              ·
                refine ⟨16248106537966648396876177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21664142050622197862501569 16248106537966648396876177)
                ·
                  refine ⟨12186079903474986297657133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16248106537966648396876177 12186079903474986297657133)
                  ·
                    refine ⟨4569779963803119861621425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12186079903474986297657133 4569779963803119861621425)
                    ·
                      refine ⟨3427334972852339896216069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4569779963803119861621425 3427334972852339896216069)
                      ·
                        rfl

theorem cell23_6674711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_6674711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674711 prefixEnd_6674711 := by exact prefixLift 6674711
  have htrace : WordTrace (prefixWord ++ tailWord_6674711) baseStart_6674711 baseEnd_6674711 := by
    simpa [prefixWord, tailWord_6674711, baseEnd_6674711] using wordTrace_append hprefix tailTrace_6674711
  have hstable : (prefixWord ++ tailWord_6674711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674711).length < 2 ^ (prefixWord ++ tailWord_6674711).sum := by decide
  have hdescent : baseEnd_6674711 < baseStart_6674711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674724 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6674724 : Nat := 118140960795 + 6674724 * 2 ^ 59
def prefixEnd_6674724 : Nat := 4983230072969 + 3 ^ 40 * 6674724 * 2
def baseEnd_6674724 : Nat := 3427341648100848345353509

theorem tailTrace_6674724 : CollatzResearch.WordTrace tailWord_6674724 prefixEnd_6674724 3427341648100848345353509 := by
  unfold tailWord_6674724
  simp only [CollatzResearch.WordTrace]
  refine ⟨121723592135311187474043613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162298122847081583298724817 121723592135311187474043613)
  ·
    refine ⟨45646347050741695302766355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121723592135311187474043613 45646347050741695302766355)
    ·
      refine ⟨68469520576112542954149533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45646347050741695302766355 68469520576112542954149533)
      ·
        refine ⟨25676070216042203607806075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68469520576112542954149533 25676070216042203607806075)
        ·
          refine ⟨38514105324063305411709113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25676070216042203607806075 38514105324063305411709113)
          ·
            refine ⟨28885578993047479058781835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38514105324063305411709113 28885578993047479058781835)
            ·
              refine ⟨43328368489571218588172753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28885578993047479058781835 43328368489571218588172753)
              ·
                refine ⟨32496276367178413941129565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43328368489571218588172753 32496276367178413941129565)
                ·
                  refine ⟨12186103637691905227923587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32496276367178413941129565 12186103637691905227923587)
                  ·
                    refine ⟨18279155456537857841885381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12186103637691905227923587 18279155456537857841885381)
                    ·
                      refine ⟨3427341648100848345353509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18279155456537857841885381 3427341648100848345353509)
                      ·
                        rfl

theorem cell23_6674724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6674724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674724 prefixEnd_6674724 := by exact prefixLift 6674724
  have htrace : WordTrace (prefixWord ++ tailWord_6674724) baseStart_6674724 baseEnd_6674724 := by
    simpa [prefixWord, tailWord_6674724, baseEnd_6674724] using wordTrace_append hprefix tailTrace_6674724
  have hstable : (prefixWord ++ tailWord_6674724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674724).length < 2 ^ (prefixWord ++ tailWord_6674724).sum := by decide
  have hdescent : baseEnd_6674724 < baseStart_6674724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674744 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_6674744 : Nat := 118140960795 + 6674744 * 2 ^ 59
def prefixEnd_6674744 : Nat := 4983230072969 + 3 ^ 40 * 6674744 * 2
def baseEnd_6674744 : Nat := 3427351917713938267103417

theorem tailTrace_6674744 : CollatzResearch.WordTrace tailWord_6674744 prefixEnd_6674744 3427351917713938267103417 := by
  unfold tailWord_6674744
  simp only [CollatzResearch.WordTrace]
  refine ⟨121723956865274959181907643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162298609153699945575876857 121723956865274959181907643)
  ·
    refine ⟨182585935297912438772861465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121723956865274959181907643 182585935297912438772861465)
    ·
      refine ⟨136939451473434329079646099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182585935297912438772861465 136939451473434329079646099)
      ·
        refine ⟨205409177210151493619469149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136939451473434329079646099 205409177210151493619469149)
        ·
          refine ⟨77028441453806810107300931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205409177210151493619469149 77028441453806810107300931)
          ·
            refine ⟨115542662180710215160951397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77028441453806810107300931 115542662180710215160951397)
            ·
              refine ⟨21664249158883165342678387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115542662180710215160951397 21664249158883165342678387)
              ·
                refine ⟨32496373738324748014017581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21664249158883165342678387 32496373738324748014017581)
                ·
                  refine ⟨12186140151871780505256593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32496373738324748014017581 12186140151871780505256593)
                  ·
                    refine ⟨9139605113903835378942445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12186140151871780505256593 9139605113903835378942445)
                    ·
                      refine ⟨3427351917713938267103417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9139605113903835378942445 3427351917713938267103417)
                      ·
                        rfl

theorem cell23_6674744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_6674744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674744 prefixEnd_6674744 := by exact prefixLift 6674744
  have htrace : WordTrace (prefixWord ++ tailWord_6674744) baseStart_6674744 baseEnd_6674744 := by
    simpa [prefixWord, tailWord_6674744, baseEnd_6674744] using wordTrace_append hprefix tailTrace_6674744
  have hstable : (prefixWord ++ tailWord_6674744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674744).length < 2 ^ (prefixWord ++ tailWord_6674744).sum := by decide
  have hdescent : baseEnd_6674744 < baseStart_6674744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674791 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_6674791 : Nat := 118140960795 + 6674791 * 2 ^ 59
def prefixEnd_6674791 : Nat := 4983230072969 + 3 ^ 40 * 6674791 * 2
def baseEnd_6674791 : Nat := 3427376051304699583215701

theorem tailTrace_6674791 : CollatzResearch.WordTrace tailWord_6674791 prefixEnd_6674791 3427376051304699583215701 := by
  unfold tailWord_6674791
  simp only [CollatzResearch.WordTrace]
  refine ⟨243449627961379645390776227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162299751974253096927184151 243449627961379645390776227)
  ·
    refine ⟨365174441942069468086164341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243449627961379645390776227 365174441942069468086164341)
    ·
      refine ⟨34235103932069012633077907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 365174441942069468086164341 34235103932069012633077907)
      ·
        refine ⟨51352655898103518949616861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34235103932069012633077907 51352655898103518949616861)
        ·
          refine ⟨19257245961788819606106323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51352655898103518949616861 19257245961788819606106323)
          ·
            refine ⟨28885868942683229409159485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19257245961788819606106323 28885868942683229409159485)
            ·
              refine ⟨10832200853506211028434807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28885868942683229409159485 10832200853506211028434807)
              ·
                refine ⟨16248301280259316542652211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10832200853506211028434807 16248301280259316542652211)
                ·
                  refine ⟨24372451920388974813978317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16248301280259316542652211 24372451920388974813978317)
                  ·
                    refine ⟨9139669470145865555241869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24372451920388974813978317 9139669470145865555241869)
                    ·
                      refine ⟨3427376051304699583215701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9139669470145865555241869 3427376051304699583215701)
                      ·
                        rfl

theorem cell23_6674791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_6674791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674791 prefixEnd_6674791 := by exact prefixLift 6674791
  have htrace : WordTrace (prefixWord ++ tailWord_6674791) baseStart_6674791 baseEnd_6674791 := by
    simpa [prefixWord, tailWord_6674791, baseEnd_6674791] using wordTrace_append hprefix tailTrace_6674791
  have hstable : (prefixWord ++ tailWord_6674791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674791).length < 2 ^ (prefixWord ++ tailWord_6674791).sum := by decide
  have hdescent : baseEnd_6674791 < baseStart_6674791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674807 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 4, 6]
def baseStart_6674807 : Nat := 118140960795 + 6674807 * 2 ^ 59
def prefixEnd_6674807 : Nat := 4983230072969 + 3 ^ 40 * 6674807 * 2
def baseEnd_6674807 : Nat := 1142461422331723840205209

theorem tailTrace_6674807 : CollatzResearch.WordTrace tailWord_6674807 prefixEnd_6674807 1142461422331723840205209 := by
  unfold tailWord_6674807
  simp only [CollatzResearch.WordTrace]
  refine ⟨243450211529321680123358675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162300141019547786748905783 243450211529321680123358675)
  ·
    refine ⟨365175317293982520185038013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243450211529321680123358675 365175317293982520185038013)
    ·
      refine ⟨136940743985243445069389255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 365175317293982520185038013 136940743985243445069389255)
      ·
        refine ⟨205411115977865167604083883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136940743985243445069389255 205411115977865167604083883)
        ·
          refine ⟨308116673966797751406125825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205411115977865167604083883 308116673966797751406125825)
          ·
            refine ⟨231087505475098313554594369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308116673966797751406125825 231087505475098313554594369)
            ·
              refine ⟨173315629106323735165945777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231087505475098313554594369 173315629106323735165945777)
              ·
                refine ⟨129986721829742801374459333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173315629106323735165945777 129986721829742801374459333)
                ·
                  refine ⟨24372510343076775257711125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129986721829742801374459333 24372510343076775257711125)
                  ·
                    refine ⟨1142461422331723840205209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24372510343076775257711125 1142461422331723840205209)
                    ·
                      rfl

theorem cell23_6674807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_6674807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674807 prefixEnd_6674807 := by exact prefixLift 6674807
  have htrace : WordTrace (prefixWord ++ tailWord_6674807) baseStart_6674807 baseEnd_6674807 := by
    simpa [prefixWord, tailWord_6674807, baseEnd_6674807] using wordTrace_append hprefix tailTrace_6674807
  have hstable : (prefixWord ++ tailWord_6674807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674807).length < 2 ^ (prefixWord ++ tailWord_6674807).sum := by decide
  have hdescent : baseEnd_6674807 < baseStart_6674807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674857 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_6674857 : Nat := 118140960795 + 6674857 * 2 ^ 59
def prefixEnd_6674857 : Nat := 4983230072969 + 3 ^ 40 * 6674857 * 2
def baseEnd_6674857 : Nat := 3427409941027896324990397

theorem tailTrace_6674857 : CollatzResearch.WordTrace tailWord_6674857 prefixEnd_6674857 3427409941027896324990397 := by
  unfold tailWord_6674857
  simp only [CollatzResearch.WordTrace]
  refine ⟨243452035179140538662678825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162301356786093692441785883 243452035179140538662678825)
  ·
    refine ⟨182589026384355403997009119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243452035179140538662678825 182589026384355403997009119)
    ·
      refine ⟨273883539576533105995513679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182589026384355403997009119 273883539576533105995513679)
      ·
        refine ⟨410825309364799658993270519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273883539576533105995513679 410825309364799658993270519)
        ·
          refine ⟨616237964047199488489905779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 410825309364799658993270519 616237964047199488489905779)
          ·
            refine ⟨924356946070799232734858669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616237964047199488489905779 924356946070799232734858669)
            ·
              refine ⟨346633854776549712275572001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 924356946070799232734858669 346633854776549712275572001)
              ·
                refine ⟨259975391082412284206679001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 346633854776549712275572001 259975391082412284206679001)
                ·
                  refine ⟨194981543311809213155009251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259975391082412284206679001 194981543311809213155009251)
                  ·
                    refine ⟨292472314967713819732513877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194981543311809213155009251 292472314967713819732513877)
                    ·
                      refine ⟨3427409941027896324990397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 292472314967713819732513877 3427409941027896324990397)
                      ·
                        rfl

theorem cell23_6674857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_6674857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674857 prefixEnd_6674857 := by exact prefixLift 6674857
  have htrace : WordTrace (prefixWord ++ tailWord_6674857) baseStart_6674857 baseEnd_6674857 := by
    simpa [prefixWord, tailWord_6674857, baseEnd_6674857] using wordTrace_append hprefix tailTrace_6674857
  have hstable : (prefixWord ++ tailWord_6674857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674857).length < 2 ^ (prefixWord ++ tailWord_6674857).sum := by decide
  have hdescent : baseEnd_6674857 < baseStart_6674857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674888 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 5]
def baseStart_6674888 : Nat := 118140960795 + 6674888 * 2 ^ 59
def prefixEnd_6674888 : Nat := 4983230072969 + 3 ^ 40 * 6674888 * 2
def baseEnd_6674888 : Nat := 380825095436465078189195

theorem tailTrace_6674888 : CollatzResearch.WordTrace tailWord_6674888 prefixEnd_6674888 380825095436465078189195 := by
  unfold tailWord_6674888
  simp only [CollatzResearch.WordTrace]
  refine ⟨121726582921014115478528659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162302110561352153971371545 121726582921014115478528659)
  ·
    refine ⟨182589874381521173217792989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121726582921014115478528659 182589874381521173217792989)
    ·
      refine ⟨68471202893070439956672371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182589874381521173217792989 68471202893070439956672371)
      ·
        refine ⟨102706804339605659935008557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68471202893070439956672371 102706804339605659935008557)
        ·
          refine ⟨38515051627352122475628209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102706804339605659935008557 38515051627352122475628209)
          ·
            refine ⟨28886288720514091856721157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38515051627352122475628209 28886288720514091856721157)
            ·
              refine ⟨5416179135096392223135217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28886288720514091856721157 5416179135096392223135217)
              ·
                refine ⟨4062134351322294167351413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416179135096392223135217 4062134351322294167351413)
                ·
                  refine ⟨380825095436465078189195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4062134351322294167351413 380825095436465078189195)
                  ·
                    rfl

theorem cell23_6674888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 5].length) (baseStart_6674888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674888 prefixEnd_6674888 := by exact prefixLift 6674888
  have htrace : WordTrace (prefixWord ++ tailWord_6674888) baseStart_6674888 baseEnd_6674888 := by
    simpa [prefixWord, tailWord_6674888, baseEnd_6674888] using wordTrace_append hprefix tailTrace_6674888
  have hstable : (prefixWord ++ tailWord_6674888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674888).length < 2 ^ (prefixWord ++ tailWord_6674888).sum := by decide
  have hdescent : baseEnd_6674888 < baseStart_6674888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674904 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6674904 : Nat := 118140960795 + 6674904 * 2 ^ 59
def prefixEnd_6674904 : Nat := 4983230072969 + 3 ^ 40 * 6674904 * 2
def baseEnd_6674904 : Nat := 3427434074618657641102681

theorem tailTrace_6674904 : CollatzResearch.WordTrace tailWord_6674904 prefixEnd_6674904 3427434074618657641102681 := by
  unfold tailWord_6674904
  simp only [CollatzResearch.WordTrace]
  refine ⟨121726874704985132844819883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162302499606646843793093177 121726874704985132844819883)
  ·
    refine ⟨182590312057477699267229825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121726874704985132844819883 182590312057477699267229825)
    ·
      refine ⟨136942734043108274450422369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182590312057477699267229825 136942734043108274450422369)
      ·
        refine ⟨102707050532331205837816777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136942734043108274450422369 102707050532331205837816777)
        ·
          refine ⟨77030287899248404378362583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102707050532331205837816777 77030287899248404378362583)
          ·
            refine ⟨115545431848872606567543875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77030287899248404378362583 115545431848872606567543875)
            ·
              refine ⟨173318147773308909851315813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115545431848872606567543875 173318147773308909851315813)
              ·
                refine ⟨32497152707495420597121715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173318147773308909851315813 32497152707495420597121715)
                ·
                  refine ⟨48745729061243130895682573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32497152707495420597121715 48745729061243130895682573)
                  ·
                    refine ⟨18279648397966174085880965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48745729061243130895682573 18279648397966174085880965)
                    ·
                      refine ⟨3427434074618657641102681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18279648397966174085880965 3427434074618657641102681)
                      ·
                        rfl

theorem cell23_6674904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6674904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674904 prefixEnd_6674904 := by exact prefixLift 6674904
  have htrace : WordTrace (prefixWord ++ tailWord_6674904) baseStart_6674904 baseEnd_6674904 := by
    simpa [prefixWord, tailWord_6674904, baseEnd_6674904] using wordTrace_append hprefix tailTrace_6674904
  have hstable : (prefixWord ++ tailWord_6674904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674904).length < 2 ^ (prefixWord ++ tailWord_6674904).sum := by decide
  have hdescent : baseEnd_6674904 < baseStart_6674904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674941 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_6674941 : Nat := 118140960795 + 6674941 * 2 ^ 59
def prefixEnd_6674941 : Nat := 4983230072969 + 3 ^ 40 * 6674941 * 2
def baseEnd_6674941 : Nat := 3427453073402873996340011

theorem tailTrace_6674941 : CollatzResearch.WordTrace tailWord_6674941 prefixEnd_6674941 3427453073402873996340011 := by
  unfold tailWord_6674941
  simp only [CollatzResearch.WordTrace]
  refine ⟨243455098910836221008736677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162303399273890814005824451 243455098910836221008736677)
  ·
    refine ⟨45647831045781791439138127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243455098910836221008736677 45647831045781791439138127)
    ·
      refine ⟨68471746568672687158707191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45647831045781791439138127 68471746568672687158707191)
      ·
        refine ⟨102707619853009030738060787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68471746568672687158707191 102707619853009030738060787)
        ·
          refine ⟨154061429779513546107091181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102707619853009030738060787 154061429779513546107091181)
          ·
            refine ⟨57773036167317579790159193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154061429779513546107091181 57773036167317579790159193)
            ·
              refine ⟨43329777125488184842619395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57773036167317579790159193 43329777125488184842619395)
              ·
                refine ⟨64994665688232277263929093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43329777125488184842619395 64994665688232277263929093)
                ·
                  refine ⟨12186499816543551986986705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64994665688232277263929093 12186499816543551986986705)
                  ·
                    refine ⟨9139874862407663990240029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12186499816543551986986705 9139874862407663990240029)
                    ·
                      refine ⟨3427453073402873996340011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9139874862407663990240029 3427453073402873996340011)
                      ·
                        rfl

theorem cell23_6674941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_6674941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674941 prefixEnd_6674941 := by exact prefixLift 6674941
  have htrace : WordTrace (prefixWord ++ tailWord_6674941) baseStart_6674941 baseEnd_6674941 := by
    simpa [prefixWord, tailWord_6674941, baseEnd_6674941] using wordTrace_append hprefix tailTrace_6674941
  have hstable : (prefixWord ++ tailWord_6674941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674941).length < 2 ^ (prefixWord ++ tailWord_6674941).sum := by decide
  have hdescent : baseEnd_6674941 < baseStart_6674941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6674948 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_6674948 : Nat := 118140960795 + 6674948 * 2 ^ 59
def prefixEnd_6674948 : Nat := 4983230072969 + 3 ^ 40 * 6674948 * 2
def baseEnd_6674948 : Nat := 1142485555922485156317493

theorem tailTrace_6674948 : CollatzResearch.WordTrace tailWord_6674948 prefixEnd_6674948 1142485555922485156317493 := by
  unfold tailWord_6674948
  simp only [CollatzResearch.WordTrace]
  refine ⟨121727677110905430602120749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162303569481207240802827665 121727677110905430602120749)
  ·
    refine ⟨45647878916589536475795281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121727677110905430602120749 45647878916589536475795281)
    ·
      refine ⟨34235909187442152356846461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45647878916589536475795281 34235909187442152356846461)
      ·
        refine ⟨12838465945290807133817423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34235909187442152356846461 12838465945290807133817423)
        ·
          refine ⟨19257698917936210700726135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12838465945290807133817423 19257698917936210700726135)
          ·
            refine ⟨28886548376904316051089203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19257698917936210700726135 28886548376904316051089203)
            ·
              refine ⟨43329822565356474076633805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28886548376904316051089203 43329822565356474076633805)
              ·
                refine ⟨16248683462008677778737677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43329822565356474076633805 16248683462008677778737677)
                ·
                  refine ⟨6093256298253254167026629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16248683462008677778737677 6093256298253254167026629)
                  ·
                    refine ⟨1142485555922485156317493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6093256298253254167026629 1142485555922485156317493)
                    ·
                      rfl

theorem cell23_6674948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_6674948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6674948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6674948 prefixEnd_6674948 := by exact prefixLift 6674948
  have htrace : WordTrace (prefixWord ++ tailWord_6674948) baseStart_6674948 baseEnd_6674948 := by
    simpa [prefixWord, tailWord_6674948, baseEnd_6674948] using wordTrace_append hprefix tailTrace_6674948
  have hstable : (prefixWord ++ tailWord_6674948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6674948).length < 2 ^ (prefixWord ++ tailWord_6674948).sum := by decide
  have hdescent : baseEnd_6674948 < baseStart_6674948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6674948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675005 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_6675005 : Nat := 118140960795 + 6675005 * 2 ^ 59
def prefixEnd_6675005 : Nat := 4983230072969 + 3 ^ 40 * 6675005 * 2
def baseEnd_6675005 : Nat := 3427485936164761745939717

theorem tailTrace_6675005 : CollatzResearch.WordTrace tailWord_6675005 prefixEnd_6675005 3427485936164761745939717 := by
  unfold tailWord_6675005
  simp only [CollatzResearch.WordTrace]
  refine ⟨243457433182604359939066469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162304955455069573292710979 243457433182604359939066469)
  ·
    refine ⟨45648268721738317488574963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243457433182604359939066469 45648268721738317488574963)
    ·
      refine ⟨68472403082607476232862445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45648268721738317488574963 68472403082607476232862445)
      ·
        refine ⟨25677151155977803587323417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68472403082607476232862445 25677151155977803587323417)
        ·
          refine ⟨19257863366983352690492563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25677151155977803587323417 19257863366983352690492563)
          ·
            refine ⟨28886795050475029035738845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19257863366983352690492563 28886795050475029035738845)
            ·
              refine ⟨10832548143928135888402067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28886795050475029035738845 10832548143928135888402067)
              ·
                refine ⟨16248822215892203832603101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10832548143928135888402067 16248822215892203832603101)
                ·
                  refine ⟨6093308330959576437226163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16248822215892203832603101 6093308330959576437226163)
                  ·
                    refine ⟨9139962496439364655839245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6093308330959576437226163 9139962496439364655839245)
                    ·
                      refine ⟨3427485936164761745939717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9139962496439364655839245 3427485936164761745939717)
                      ·
                        rfl

theorem cell23_6675005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_6675005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675005 prefixEnd_6675005 := by exact prefixLift 6675005
  have htrace : WordTrace (prefixWord ++ tailWord_6675005) baseStart_6675005 baseEnd_6675005 := by
    simpa [prefixWord, tailWord_6675005, baseEnd_6675005] using wordTrace_append hprefix tailTrace_6675005
  have hstable : (prefixWord ++ tailWord_6675005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675005).length < 2 ^ (prefixWord ++ tailWord_6675005).sum := by decide
  have hdescent : baseEnd_6675005 < baseStart_6675005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675012 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 6]
def baseStart_6675012 : Nat := 118140960795 + 6675012 * 2 ^ 59
def prefixEnd_6675012 : Nat := 4983230072969 + 3 ^ 40 * 6675012 * 2
def baseEnd_6675012 : Nat := 380832170058815913172465

theorem tailTrace_6675012 : CollatzResearch.WordTrace tailWord_6675012 prefixEnd_6675012 380832170058815913172465 := by
  unfold tailWord_6675012
  simp only [CollatzResearch.WordTrace]
  refine ⟨121728844246789500067285645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162305125662386000089714193 121728844246789500067285645)
  ·
    refine ⟨45648316592546062525232117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121728844246789500067285645 45648316592546062525232117)
    ·
      refine ⟨4279529680551193361740511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45648316592546062525232117 4279529680551193361740511)
      ·
        refine ⟨6419294520826790042610767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279529680551193361740511 6419294520826790042610767)
        ·
          refine ⟨9628941781240185063916151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6419294520826790042610767 9628941781240185063916151)
          ·
            refine ⟨14443412671860277595874227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9628941781240185063916151 14443412671860277595874227)
            ·
              refine ⟨21665119007790416393811341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14443412671860277595874227 21665119007790416393811341)
              ·
                refine ⟨8124419627921406147679253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21665119007790416393811341 8124419627921406147679253)
                ·
                  refine ⟨380832170058815913172465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8124419627921406147679253 380832170058815913172465)
                  ·
                    rfl

theorem cell23_6675012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_6675012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675012 prefixEnd_6675012 := by exact prefixLift 6675012
  have htrace : WordTrace (prefixWord ++ tailWord_6675012) baseStart_6675012 baseEnd_6675012 := by
    simpa [prefixWord, tailWord_6675012, baseEnd_6675012] using wordTrace_append hprefix tailTrace_6675012
  have hstable : (prefixWord ++ tailWord_6675012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675012).length < 2 ^ (prefixWord ++ tailWord_6675012).sum := by decide
  have hdescent : baseEnd_6675012 < baseStart_6675012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675028 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_6675028 : Nat := 118140960795 + 6675028 * 2 ^ 59
def prefixEnd_6675028 : Nat := 4983230072969 + 3 ^ 40 * 6675028 * 2
def baseEnd_6675028 : Nat := 3427497746219815155952111

theorem tailTrace_6675028 : CollatzResearch.WordTrace tailWord_6675028 prefixEnd_6675028 3427497746219815155952111 := by
  unfold tailWord_6675028
  simp only [CollatzResearch.WordTrace]
  refine ⟨121729136030760517433576869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162305514707680689911435825 121729136030760517433576869)
  ·
    refine ⟨22824213005767597018795663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121729136030760517433576869 22824213005767597018795663)
    ·
      refine ⟨34236319508651395528193495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22824213005767597018795663 34236319508651395528193495)
      ·
        refine ⟨51354479262977093292290243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34236319508651395528193495 51354479262977093292290243)
        ·
          refine ⟨77031718894465639938435365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51354479262977093292290243 77031718894465639938435365)
          ·
            refine ⟨14443447292712307488456631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77031718894465639938435365 14443447292712307488456631)
            ·
              refine ⟨21665170939068461232684947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14443447292712307488456631 21665170939068461232684947)
              ·
                refine ⟨32497756408602691849027421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21665170939068461232684947 32497756408602691849027421)
                ·
                  refine ⟨12186658653226009443385283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32497756408602691849027421 12186658653226009443385283)
                  ·
                    refine ⟨18279987979839014165077925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12186658653226009443385283 18279987979839014165077925)
                    ·
                      refine ⟨3427497746219815155952111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18279987979839014165077925 3427497746219815155952111)
                      ·
                        rfl

theorem cell23_6675028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_6675028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675028 prefixEnd_6675028 := by exact prefixLift 6675028
  have htrace : WordTrace (prefixWord ++ tailWord_6675028) baseStart_6675028 baseEnd_6675028 := by
    simpa [prefixWord, tailWord_6675028, baseEnd_6675028] using wordTrace_append hprefix tailTrace_6675028
  have hstable : (prefixWord ++ tailWord_6675028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675028).length < 2 ^ (prefixWord ++ tailWord_6675028).sum := by decide
  have hdescent : baseEnd_6675028 < baseStart_6675028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675041 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_6675041 : Nat := 118140960795 + 6675041 * 2 ^ 59
def prefixEnd_6675041 : Nat := 4983230072969 + 3 ^ 40 * 6675041 * 2
def baseEnd_6675041 : Nat := 3427504421468323605089551

theorem tailTrace_6675041 : CollatzResearch.WordTrace tailWord_6675041 prefixEnd_6675041 3427504421468323605089551 := by
  unfold tailWord_6675041
  simp only [CollatzResearch.WordTrace]
  refine ⟨243458746210473938087376977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162305830806982625391584651 243458746210473938087376977)
  ·
    refine ⟨182594059657855453565532733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243458746210473938087376977 182594059657855453565532733)
    ·
      refine ⟨68472772371695795087074775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182594059657855453565532733 68472772371695795087074775)
      ·
        refine ⟨102709158557543692630612163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68472772371695795087074775 102709158557543692630612163)
        ·
          refine ⟨154063737836315538945918245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102709158557543692630612163 154063737836315538945918245)
          ·
            refine ⟨28886950844309163552359671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154063737836315538945918245 28886950844309163552359671)
            ·
              refine ⟨43330426266463745328539507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28886950844309163552359671 43330426266463745328539507)
              ·
                refine ⟨64995639399695617992809261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43330426266463745328539507 64995639399695617992809261)
                ·
                  refine ⟨24373364774885856747303473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64995639399695617992809261 24373364774885856747303473)
                  ·
                    refine ⟨18280023581164392560477605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24373364774885856747303473 18280023581164392560477605)
                    ·
                      refine ⟨3427504421468323605089551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18280023581164392560477605 3427504421468323605089551)
                      ·
                        rfl

theorem cell23_6675041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_6675041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675041 prefixEnd_6675041 := by exact prefixLift 6675041
  have htrace : WordTrace (prefixWord ++ tailWord_6675041) baseStart_6675041 baseEnd_6675041 := by
    simpa [prefixWord, tailWord_6675041, baseEnd_6675041] using wordTrace_append hprefix tailTrace_6675041
  have hstable : (prefixWord ++ tailWord_6675041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675041).length < 2 ^ (prefixWord ++ tailWord_6675041).sum := by decide
  have hdescent : baseEnd_6675041 < baseStart_6675041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675056 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 1, 1, 3]
def baseStart_6675056 : Nat := 118140960795 + 6675056 * 2 ^ 59
def prefixEnd_6675056 : Nat := 4983230072969 + 3 ^ 40 * 6675056 * 2
def baseEnd_6675056 : Nat := 3427512123678141046401983

theorem tailTrace_6675056 : CollatzResearch.WordTrace tailWord_6675056 prefixEnd_6675056 3427512123678141046401983 := by
  unfold tailWord_6675056
  simp only [CollatzResearch.WordTrace]
  refine ⟨121729646652709797824586511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162306195536946397099448681 121729646652709797824586511)
  ·
    refine ⟨182594469979064696736879767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121729646652709797824586511 182594469979064696736879767)
    ·
      refine ⟨273891704968597045105319651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182594469979064696736879767 273891704968597045105319651)
      ·
        refine ⟨410837557452895567657979477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273891704968597045105319651 410837557452895567657979477)
        ·
          refine ⟨4814502626401119933491947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 410837557452895567657979477 4814502626401119933491947)
          ·
            refine ⟨7221753939601679900237921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814502626401119933491947 7221753939601679900237921)
            ·
              refine ⟨5416315454701259925178441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221753939601679900237921 5416315454701259925178441)
              ·
                refine ⟨4062236591025944943883831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5416315454701259925178441 4062236591025944943883831)
                ·
                  refine ⟨6093354886538917415825747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4062236591025944943883831 6093354886538917415825747)
                  ·
                    refine ⟨9140032329808376123738621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6093354886538917415825747 9140032329808376123738621)
                    ·
                      refine ⟨3427512123678141046401983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9140032329808376123738621 3427512123678141046401983)
                      ·
                        rfl

theorem cell23_6675056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 1, 3].length) (baseStart_6675056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675056 prefixEnd_6675056 := by exact prefixLift 6675056
  have htrace : WordTrace (prefixWord ++ tailWord_6675056) baseStart_6675056 baseEnd_6675056 := by
    simpa [prefixWord, tailWord_6675056, baseEnd_6675056] using wordTrace_append hprefix tailTrace_6675056
  have hstable : (prefixWord ++ tailWord_6675056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675056).length < 2 ^ (prefixWord ++ tailWord_6675056).sum := by decide
  have hdescent : baseEnd_6675056 < baseStart_6675056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675135 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 1, 4, 2]
def baseStart_6675135 : Nat := 118140960795 + 6675135 * 2 ^ 59
def prefixEnd_6675135 : Nat := 4983230072969 + 3 ^ 40 * 6675135 * 2
def baseEnd_6675135 : Nat := 3427552688649846237314119

theorem tailTrace_6675135 : CollatzResearch.WordTrace tailWord_6675135 prefixEnd_6675135 3427552688649846237314119 := by
  unfold tailWord_6675135
  simp only [CollatzResearch.WordTrace]
  refine ⟨243462174672133392141298859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162308116448088928094199239 243462174672133392141298859)
  ·
    refine ⟨365193262008200088211948289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243462174672133392141298859 365193262008200088211948289)
    ·
      refine ⟨273894946506150066158961217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365193262008200088211948289 273894946506150066158961217)
      ·
        refine ⟨205421209879612549619220913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273894946506150066158961217 205421209879612549619220913)
        ·
          refine ⟨154065907409709412214415685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205421209879612549619220913 154065907409709412214415685)
          ·
            refine ⟨28887357639320514790202941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154065907409709412214415685 28887357639320514790202941)
            ·
              refine ⟨10832759114745193046326103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28887357639320514790202941 10832759114745193046326103)
              ·
                refine ⟨16249138672117789569489155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10832759114745193046326103 16249138672117789569489155)
                ·
                  refine ⟨24373708008176684354233733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16249138672117789569489155 24373708008176684354233733)
                  ·
                    refine ⟨4570070251533128316418825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24373708008176684354233733 4570070251533128316418825)
                    ·
                      refine ⟨3427552688649846237314119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570070251533128316418825 3427552688649846237314119)
                      ·
                        rfl

theorem cell23_6675135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_6675135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675135 prefixEnd_6675135 := by exact prefixLift 6675135
  have htrace : WordTrace (prefixWord ++ tailWord_6675135) baseStart_6675135 baseEnd_6675135 := by
    simpa [prefixWord, tailWord_6675135, baseEnd_6675135] using wordTrace_append hprefix tailTrace_6675135
  have hstable : (prefixWord ++ tailWord_6675135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675135).length < 2 ^ (prefixWord ++ tailWord_6675135).sum := by decide
  have hdescent : baseEnd_6675135 < baseStart_6675135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675186 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_6675186 : Nat := 118140960795 + 6675186 * 2 ^ 59
def prefixEnd_6675186 : Nat := 4983230072969 + 3 ^ 40 * 6675186 * 2
def baseEnd_6675186 : Nat := 3427578876163225537776385

theorem tailTrace_6675186 : CollatzResearch.WordTrace tailWord_6675186 prefixEnd_6675186 3427578876163225537776385 := by
  unfold tailWord_6675186
  simp only [CollatzResearch.WordTrace]
  refine ⟨60866008698737156962851353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162309356529965751900936941 60866008698737156962851353)
  ·
    refine ⟨45649506524052867722138515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60866008698737156962851353 45649506524052867722138515)
    ·
      refine ⟨68474259786079301583207773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45649506524052867722138515 68474259786079301583207773)
      ·
        refine ⟨25677847419779738093702915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68474259786079301583207773 25677847419779738093702915)
        ·
          refine ⟨38516771129669607140554373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25677847419779738093702915 38516771129669607140554373)
          ·
            refine ⟨7221894586813051338853945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38516771129669607140554373 7221894586813051338853945)
            ·
              refine ⟨5416420940109788504140459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7221894586813051338853945 5416420940109788504140459)
              ·
                refine ⟨8124631410164682756210689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5416420940109788504140459 8124631410164682756210689)
                ·
                  refine ⟨6093473557623512067158017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8124631410164682756210689 6093473557623512067158017)
                  ·
                    refine ⟨4570105168217634050368513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6093473557623512067158017 4570105168217634050368513)
                    ·
                      refine ⟨3427578876163225537776385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570105168217634050368513 3427578876163225537776385)
                      ·
                        rfl

theorem cell23_6675186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_6675186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675186 prefixEnd_6675186 := by exact prefixLift 6675186
  have htrace : WordTrace (prefixWord ++ tailWord_6675186) baseStart_6675186 baseEnd_6675186 := by
    simpa [prefixWord, tailWord_6675186, baseEnd_6675186] using wordTrace_append hprefix tailTrace_6675186
  have hstable : (prefixWord ++ tailWord_6675186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675186).length < 2 ^ (prefixWord ++ tailWord_6675186).sum := by decide
  have hdescent : baseEnd_6675186 < baseStart_6675186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675262 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_6675262 : Nat := 118140960795 + 6675262 * 2 ^ 59
def prefixEnd_6675262 : Nat := 4983230072969 + 3 ^ 40 * 6675262 * 2
def baseEnd_6675262 : Nat := 3427617900692967240426035

theorem tailTrace_6675262 : CollatzResearch.WordTrace tailWord_6675262 prefixEnd_6675262 3427617900692967240426035 := by
  unfold tailWord_6675262
  simp only [CollatzResearch.WordTrace]
  refine ⟨30433350842834161603896505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162311204495115528554114693 30433350842834161603896505)
  ·
    refine ⟨22825013132125621202922379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30433350842834161603896505 22825013132125621202922379)
    ·
      refine ⟨34237519698188431804383569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22825013132125621202922379 34237519698188431804383569)
      ·
        refine ⟨25678139773641323853287677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34237519698188431804383569 25678139773641323853287677)
        ·
          refine ⟨9629302415115496444982879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25678139773641323853287677 9629302415115496444982879)
          ·
            refine ⟨14443953622673244667474319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9629302415115496444982879 14443953622673244667474319)
            ·
              refine ⟨21665930434009867001211479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14443953622673244667474319 21665930434009867001211479)
              ·
                refine ⟨32498895651014800501817219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21665930434009867001211479 32498895651014800501817219)
                ·
                  refine ⟨48748343476522200752725829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32498895651014800501817219 48748343476522200752725829)
                  ·
                    refine ⟨9140314401847912641136093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48748343476522200752725829 9140314401847912641136093)
                    ·
                      refine ⟨3427617900692967240426035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9140314401847912641136093 3427617900692967240426035)
                      ·
                        rfl

theorem cell23_6675262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_6675262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675262 prefixEnd_6675262 := by exact prefixLift 6675262
  have htrace : WordTrace (prefixWord ++ tailWord_6675262) baseStart_6675262 baseEnd_6675262 := by
    simpa [prefixWord, tailWord_6675262, baseEnd_6675262] using wordTrace_append hprefix tailTrace_6675262
  have hstable : (prefixWord ++ tailWord_6675262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675262).length < 2 ^ (prefixWord ++ tailWord_6675262).sum := by decide
  have hdescent : baseEnd_6675262 < baseStart_6675262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675315 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 4]
def baseStart_6675315 : Nat := 118140960795 + 6675315 * 2 ^ 59
def prefixEnd_6675315 : Nat := 4983230072969 + 3 ^ 40 * 6675315 * 2
def baseEnd_6675315 : Nat := 3427645115167655533063291

theorem tailTrace_6675315 : CollatzResearch.WordTrace tailWord_6675315 prefixEnd_6675315 3427645115167655533063291 := by
  unfold tailWord_6675315
  simp only [CollatzResearch.WordTrace]
  refine ⟨243468739811481282882851399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162312493207654188588567599 243468739811481282882851399)
  ·
    refine ⟨365203109717221924324277099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243468739811481282882851399 365203109717221924324277099)
    ·
      refine ⟨547804664575832886486415649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365203109717221924324277099 547804664575832886486415649)
      ·
        refine ⟨410853498431874664864811737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 547804664575832886486415649 410853498431874664864811737)
        ·
          refine ⟨308140123823905998648608803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410853498431874664864811737 308140123823905998648608803)
          ·
            refine ⟨462210185735858997972913205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308140123823905998648608803 462210185735858997972913205)
            ·
              refine ⟨43332204912736781059960613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 462210185735858997972913205 43332204912736781059960613)
              ·
                refine ⟨8124788421138146448742615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43332204912736781059960613 8124788421138146448742615)
                ·
                  refine ⟨12187182631707219673113923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8124788421138146448742615 12187182631707219673113923)
                  ·
                    refine ⟨18280773947560829509670885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12187182631707219673113923 18280773947560829509670885)
                    ·
                      refine ⟨3427645115167655533063291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18280773947560829509670885 3427645115167655533063291)
                      ·
                        rfl

theorem cell23_6675315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_6675315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675315 prefixEnd_6675315 := by exact prefixLift 6675315
  have htrace : WordTrace (prefixWord ++ tailWord_6675315) baseStart_6675315 baseEnd_6675315 := by
    simpa [prefixWord, tailWord_6675315, baseEnd_6675315] using wordTrace_append hprefix tailTrace_6675315
  have hstable : (prefixWord ++ tailWord_6675315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675315).length < 2 ^ (prefixWord ++ tailWord_6675315).sum := by decide
  have hdescent : baseEnd_6675315 < baseStart_6675315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675325 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_6675325 : Nat := 118140960795 + 6675325 * 2 ^ 59
def prefixEnd_6675325 : Nat := 4983230072969 + 3 ^ 40 * 6675325 * 2
def baseEnd_6675325 : Nat := 1142550083324733497979415

theorem tailTrace_6675325 : CollatzResearch.WordTrace tailWord_6675325 prefixEnd_6675325 1142550083324733497979415 := by
  unfold tailWord_6675325
  simp only [CollatzResearch.WordTrace]
  refine ⟨243469104541445054590715429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162312736360963369727143619 243469104541445054590715429)
  ·
    refine ⟨45650457101520947735759143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243469104541445054590715429 45650457101520947735759143)
    ·
      refine ⟨68475685652281421603638715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45650457101520947735759143 68475685652281421603638715)
      ·
        refine ⟨102713528478422132405458073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68475685652281421603638715 102713528478422132405458073)
        ·
          refine ⟨77035146358816599304093555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102713528478422132405458073 77035146358816599304093555)
          ·
            refine ⟨115552719538224898956140333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77035146358816599304093555 115552719538224898956140333)
            ·
              refine ⟨43332269826834337108552625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115552719538224898956140333 43332269826834337108552625)
              ·
                refine ⟨32499202370125752831414469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43332269826834337108552625 32499202370125752831414469)
                ·
                  refine ⟨6093600444398578655890213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32499202370125752831414469 6093600444398578655890213)
                  ·
                    refine ⟨1142550083324733497979415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6093600444398578655890213 1142550083324733497979415)
                    ·
                      rfl

theorem cell23_6675325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_6675325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675325 prefixEnd_6675325 := by exact prefixLift 6675325
  have htrace : WordTrace (prefixWord ++ tailWord_6675325) baseStart_6675325 baseEnd_6675325 := by
    simpa [prefixWord, tailWord_6675325, baseEnd_6675325] using wordTrace_append hprefix tailTrace_6675325
  have hstable : (prefixWord ++ tailWord_6675325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675325).length < 2 ^ (prefixWord ++ tailWord_6675325).sum := by decide
  have hdescent : baseEnd_6675325 < baseStart_6675325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675335 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_6675335 : Nat := 118140960795 + 6675335 * 2 ^ 59
def prefixEnd_6675335 : Nat := 4983230072969 + 3 ^ 40 * 6675335 * 2
def baseEnd_6675335 : Nat := 3427655384780745454813199

theorem tailTrace_6675335 : CollatzResearch.WordTrace tailWord_6675335 prefixEnd_6675335 3427655384780745454813199 := by
  unfold tailWord_6675335
  simp only [CollatzResearch.WordTrace]
  refine ⟨243469469271408826298579459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162312979514272550865719639 243469469271408826298579459)
  ·
    refine ⟨365204203907113239447869189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243469469271408826298579459 365204203907113239447869189)
    ·
      refine ⟨68475788232583732396475473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 365204203907113239447869189 68475788232583732396475473)
      ·
        refine ⟨51356841174437799297356605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68475788232583732396475473 51356841174437799297356605)
        ·
          refine ⟨19258815440414174736508727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51356841174437799297356605 19258815440414174736508727)
          ·
            refine ⟨28888223160621262104763091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19258815440414174736508727 28888223160621262104763091)
            ·
              refine ⟨43332334740931893157144637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28888223160621262104763091 43332334740931893157144637)
              ·
                refine ⟨16249625527849459933929239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43332334740931893157144637 16249625527849459933929239)
                ·
                  refine ⟨24374438291774189900893859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16249625527849459933929239 24374438291774189900893859)
                  ·
                    refine ⟨36561657437661284851340789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24374438291774189900893859 36561657437661284851340789)
                    ·
                      refine ⟨3427655384780745454813199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36561657437661284851340789 3427655384780745454813199)
                      ·
                        rfl

theorem cell23_6675335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_6675335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675335 prefixEnd_6675335 := by exact prefixLift 6675335
  have htrace : WordTrace (prefixWord ++ tailWord_6675335) baseStart_6675335 baseEnd_6675335 := by
    simpa [prefixWord, tailWord_6675335, baseEnd_6675335] using wordTrace_append hprefix tailTrace_6675335
  have hstable : (prefixWord ++ tailWord_6675335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675335).length < 2 ^ (prefixWord ++ tailWord_6675335).sum := by decide
  have hdescent : baseEnd_6675335 < baseStart_6675335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6675349 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_6675349 : Nat := 118140960795 + 6675349 * 2 ^ 59
def prefixEnd_6675349 : Nat := 4983230072969 + 3 ^ 40 * 6675349 * 2
def baseEnd_6675349 : Nat := 3427662573509908400038135

theorem tailTrace_6675349 : CollatzResearch.WordTrace tailWord_6675349 prefixEnd_6675349 3427662573509908400038135 := by
  unfold tailWord_6675349
  simp only [CollatzResearch.WordTrace]
  refine ⟨243469979893358106689589101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162313319928905404459726067 243469979893358106689589101)
  ·
    refine ⟨91301242460009290008595913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243469979893358106689589101 91301242460009290008595913)
    ·
      refine ⟨68475931845006967506446935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91301242460009290008595913 68475931845006967506446935)
      ·
        refine ⟨102713897767510451259670403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68475931845006967506446935 102713897767510451259670403)
        ·
          refine ⟨154070846651265676889505605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102713897767510451259670403 154070846651265676889505605)
          ·
            refine ⟨28888283747112314416782301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154070846651265676889505605 28888283747112314416782301)
            ·
              refine ⟨10833106405167117906293363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28888283747112314416782301 10833106405167117906293363)
              ·
                refine ⟨16249659607750676859440045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10833106405167117906293363 16249659607750676859440045)
                ·
                  refine ⟨6093622352906503822290017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16249659607750676859440045 6093622352906503822290017)
                  ·
                    refine ⟨4570216764679877866717513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6093622352906503822290017 4570216764679877866717513)
                    ·
                      refine ⟨3427662573509908400038135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4570216764679877866717513 3427662573509908400038135)
                      ·
                        rfl

theorem cell23_6675349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_6675349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6675349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6675349 prefixEnd_6675349 := by exact prefixLift 6675349
  have htrace : WordTrace (prefixWord ++ tailWord_6675349) baseStart_6675349 baseEnd_6675349 := by
    simpa [prefixWord, tailWord_6675349, baseEnd_6675349] using wordTrace_append hprefix tailTrace_6675349
  have hstable : (prefixWord ++ tailWord_6675349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6675349).length < 2 ^ (prefixWord ++ tailWord_6675349).sum := by decide
  have hdescent : baseEnd_6675349 < baseStart_6675349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6675349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
