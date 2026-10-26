import V185TrunkScan21Chunk073

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_896747 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_896747 : Nat := 118140960795 + 896747 * 2 ^ 59
def prefixEnd_896747 : Nat := 4983230072969 + 3 ^ 40 * 896747 * 2
def baseEnd_896747 : Nat := 204649882878892536417085

theorem tailTrace_896747 : CollatzResearch.WordTrace tailWord_896747 prefixEnd_896747 204649882878892536417085 := by
  unfold tailWord_896747
  simp only [CollatzResearch.WordTrace]
  refine ⟨32707050082246246039640495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21804700054830830693093663 32707050082246246039640495)
  ·
    refine ⟨49060575123369369059460743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32707050082246246039640495 49060575123369369059460743)
    ·
      refine ⟨73590862685054053589191115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49060575123369369059460743 73590862685054053589191115)
      ·
        refine ⟨110386294027581080383786673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73590862685054053589191115 110386294027581080383786673)
        ·
          refine ⟨82789720520685810287840005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110386294027581080383786673 82789720520685810287840005)
          ·
            refine ⟨15523072597628589428970001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82789720520685810287840005 15523072597628589428970001)
            ·
              refine ⟨11642304448221442071727501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15523072597628589428970001 11642304448221442071727501)
              ·
                refine ⟨4365864168083040776897813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11642304448221442071727501 4365864168083040776897813)
                ·
                  refine ⟨204649882878892536417085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4365864168083040776897813 204649882878892536417085)
                  ·
                    rfl

theorem cell21_896747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_896747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896747 prefixEnd_896747 := by exact prefixLift 896747
  have htrace : WordTrace (prefixWord ++ tailWord_896747) baseStart_896747 baseEnd_896747 := by
    simpa [prefixWord, tailWord_896747, baseEnd_896747] using wordTrace_append hprefix tailTrace_896747
  have hstable : (prefixWord ++ tailWord_896747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896747).length < 2 ^ (prefixWord ++ tailWord_896747).sum := by decide
  have hdescent : baseEnd_896747 < baseStart_896747 := by decide
  rcases family_descends (prefixWord ++ tailWord_896747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896764 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_896764 : Nat := 118140960795 + 896764 * 2 ^ 59
def prefixEnd_896764 : Nat := 4983230072969 + 3 ^ 40 * 896764 * 2
def baseEnd_896764 : Nat := 204653762510504284633717

theorem tailTrace_896764 : CollatzResearch.WordTrace tailWord_896764 prefixEnd_896764 204653762510504284633717 := by
  unfold tailWord_896764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353835061592328971504673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21805113415456438628672897 16353835061592328971504673)
  ·
    refine ⟨12265376296194246728628505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16353835061592328971504673 12265376296194246728628505)
    ·
      refine ⟨9199032222145685046471379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12265376296194246728628505 9199032222145685046471379)
      ·
        refine ⟨13798548333218527569707069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9199032222145685046471379 13798548333218527569707069)
        ·
          refine ⟨5174455624956947838640151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13798548333218527569707069 5174455624956947838640151)
          ·
            refine ⟨7761683437435421757960227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5174455624956947838640151 7761683437435421757960227)
            ·
              refine ⟨11642525156153132636940341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761683437435421757960227 11642525156153132636940341)
              ·
                refine ⟨1091486733389356184713157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11642525156153132636940341 1091486733389356184713157)
                ·
                  refine ⟨204653762510504284633717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091486733389356184713157 204653762510504284633717)
                  ·
                    rfl

theorem cell21_896764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_896764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896764 prefixEnd_896764 := by exact prefixLift 896764
  have htrace : WordTrace (prefixWord ++ tailWord_896764) baseStart_896764 baseEnd_896764 := by
    simpa [prefixWord, tailWord_896764, baseEnd_896764] using wordTrace_append hprefix tailTrace_896764
  have hstable : (prefixWord ++ tailWord_896764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896764).length < 2 ^ (prefixWord ++ tailWord_896764).sum := by decide
  have hdescent : baseEnd_896764 < baseStart_896764 := by decide
  rcases family_descends (prefixWord ++ tailWord_896764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896860 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_896860 : Nat := 118140960795 + 896860 * 2 ^ 59
def prefixEnd_896860 : Nat := 4983230072969 + 3 ^ 40 * 896860 * 2
def baseEnd_896860 : Nat := 204675671018429451033521

theorem tailTrace_896860 : CollatzResearch.WordTrace tailWord_896860 prefixEnd_896860 204675671018429451033521 := by
  unfold tailWord_896860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16355585765418433169252017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21807447687224577559002689 16355585765418433169252017)
  ·
    refine ⟨12266689324063824876939013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16355585765418433169252017 12266689324063824876939013)
    ·
      refine ⟨2300004248261967164426065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12266689324063824876939013 2300004248261967164426065)
      ·
        refine ⟨1725003186196475373319549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2300004248261967164426065 1725003186196475373319549)
        ·
          refine ⟨646876194823678264994831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1725003186196475373319549 646876194823678264994831)
          ·
            refine ⟨970314292235517397492247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646876194823678264994831 970314292235517397492247)
            ·
              refine ⟨1455471438353276096238371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970314292235517397492247 1455471438353276096238371)
              ·
                refine ⟨2183207157529914144357557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1455471438353276096238371 2183207157529914144357557)
                ·
                  refine ⟨204675671018429451033521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2183207157529914144357557 204675671018429451033521)
                  ·
                    rfl

theorem cell21_896860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_896860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896860 prefixEnd_896860 := by exact prefixLift 896860
  have htrace : WordTrace (prefixWord ++ tailWord_896860) baseStart_896860 baseEnd_896860 := by
    simpa [prefixWord, tailWord_896860, baseEnd_896860] using wordTrace_append hprefix tailTrace_896860
  have hstable : (prefixWord ++ tailWord_896860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896860).length < 2 ^ (prefixWord ++ tailWord_896860).sum := by decide
  have hdescent : baseEnd_896860 < baseStart_896860 := by decide
  rcases family_descends (prefixWord ++ tailWord_896860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896874 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_896874 : Nat := 118140960795 + 896874 * 2 ^ 59
def prefixEnd_896874 : Nat := 4983230072969 + 3 ^ 40 * 896874 * 2
def baseEnd_896874 : Nat := 204678866009168537800159

theorem tailTrace_896874 : CollatzResearch.WordTrace tailWord_896874 prefixEnd_896874 204678866009168537800159 := by
  unfold tailWord_896874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177920538196536682378419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21807788101857431153009117 8177920538196536682378419)
  ·
    refine ⟨12266880807294805023567629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8177920538196536682378419 12266880807294805023567629)
    ·
      refine ⟨4600080302735551883837861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12266880807294805023567629 4600080302735551883837861)
      ·
        refine ⟨862515056762915978219599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4600080302735551883837861 862515056762915978219599)
        ·
          refine ⟨1293772585144373967329399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862515056762915978219599 1293772585144373967329399)
          ·
            refine ⟨1940658877716560950994099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293772585144373967329399 1940658877716560950994099)
            ·
              refine ⟨2910988316574841426491149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1940658877716560950994099 2910988316574841426491149)
              ·
                refine ⟨1091620618715565534934181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2910988316574841426491149 1091620618715565534934181)
                ·
                  refine ⟨204678866009168537800159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1091620618715565534934181 204678866009168537800159)
                  ·
                    rfl

theorem cell21_896874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_896874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896874 prefixEnd_896874 := by exact prefixLift 896874
  have htrace : WordTrace (prefixWord ++ tailWord_896874) baseStart_896874 baseEnd_896874 := by
    simpa [prefixWord, tailWord_896874, baseEnd_896874] using wordTrace_append hprefix tailTrace_896874
  have hstable : (prefixWord ++ tailWord_896874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896874).length < 2 ^ (prefixWord ++ tailWord_896874).sum := by decide
  have hdescent : baseEnd_896874 < baseStart_896874 := by decide
  rcases family_descends (prefixWord ++ tailWord_896874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896885 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_896885 : Nat := 118140960795 + 896885 * 2 ^ 59
def prefixEnd_896885 : Nat := 4983230072969 + 3 ^ 40 * 896885 * 2
def baseEnd_896885 : Nat := 204681376359034963116803

theorem tailTrace_896885 : CollatzResearch.WordTrace tailWord_896885 prefixEnd_896885 204681376359034963116803 := by
  unfold tailWord_896885
  simp only [CollatzResearch.WordTrace]
  refine ⟨32712083355746295608164109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21808055570497530405442739 32712083355746295608164109)
  ·
    refine ⟨12267031258404860853061541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32712083355746295608164109 12267031258404860853061541)
    ·
      refine ⟨2300068360950911409949039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12267031258404860853061541 2300068360950911409949039)
      ·
        refine ⟨3450102541426367114923559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300068360950911409949039 3450102541426367114923559)
        ·
          refine ⟨5175153812139550672385339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450102541426367114923559 5175153812139550672385339)
          ·
            refine ⟨7762730718209326008578009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175153812139550672385339 7762730718209326008578009)
            ·
              refine ⟨5822048038656994506433507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762730718209326008578009 5822048038656994506433507)
              ·
                refine ⟨8733072057985491759650261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822048038656994506433507 8733072057985491759650261)
                ·
                  refine ⟨204681376359034963116803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8733072057985491759650261 204681376359034963116803)
                  ·
                    rfl

theorem cell21_896885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_896885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896885 prefixEnd_896885 := by exact prefixLift 896885
  have htrace : WordTrace (prefixWord ++ tailWord_896885) baseStart_896885 baseEnd_896885 := by
    simpa [prefixWord, tailWord_896885, baseEnd_896885] using wordTrace_append hprefix tailTrace_896885
  have hstable : (prefixWord ++ tailWord_896885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896885).length < 2 ^ (prefixWord ++ tailWord_896885).sum := by decide
  have hdescent : baseEnd_896885 < baseStart_896885 := by decide
  rcases family_descends (prefixWord ++ tailWord_896885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896919 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 3]
def baseStart_896919 : Nat := 118140960795 + 896919 * 2 ^ 59
def prefixEnd_896919 : Nat := 4983230072969 + 3 ^ 40 * 896919 * 2
def baseEnd_896919 : Nat := 204689135622258459550067

theorem tailTrace_896919 : CollatzResearch.WordTrace tailWord_896919 prefixEnd_896919 204689135622258459550067 := by
  unfold tailWord_896919
  simp only [CollatzResearch.WordTrace]
  refine ⟨32713323437623119414901811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21808882291748746276601207 32713323437623119414901811)
  ·
    refine ⟨49069985156434679122352717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32713323437623119414901811 49069985156434679122352717)
    ·
      refine ⟨18401244433663004670882269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49069985156434679122352717 18401244433663004670882269)
      ·
        refine ⟨6900466662623626751580851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18401244433663004670882269 6900466662623626751580851)
        ·
          refine ⟨10350699993935440127371277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6900466662623626751580851 10350699993935440127371277)
          ·
            refine ⟨3881512497725790047764229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10350699993935440127371277 3881512497725790047764229)
            ·
              refine ⟨727783593323585633955793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3881512497725790047764229 727783593323585633955793)
              ·
                refine ⟨545837694992689225466845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 727783593323585633955793 545837694992689225466845)
                ·
                  refine ⟨204689135622258459550067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 545837694992689225466845 204689135622258459550067)
                  ·
                    rfl

theorem cell21_896919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 3].length) (baseStart_896919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896919 prefixEnd_896919 := by exact prefixLift 896919
  have htrace : WordTrace (prefixWord ++ tailWord_896919) baseStart_896919 baseEnd_896919 := by
    simpa [prefixWord, tailWord_896919, baseEnd_896919] using wordTrace_append hprefix tailTrace_896919
  have hstable : (prefixWord ++ tailWord_896919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896919).length < 2 ^ (prefixWord ++ tailWord_896919).sum := by decide
  have hdescent : baseEnd_896919 < baseStart_896919 := by decide
  rcases family_descends (prefixWord ++ tailWord_896919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_896975 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_896975 : Nat := 118140960795 + 896975 * 2 ^ 59
def prefixEnd_896975 : Nat := 4983230072969 + 3 ^ 40 * 896975 * 2
def baseEnd_896975 : Nat := 204701915585214806616619

theorem tailTrace_896975 : CollatzResearch.WordTrace tailWord_896975 prefixEnd_896975 204701915585214806616619 := by
  unfold tailWord_896975
  simp only [CollatzResearch.WordTrace]
  refine ⟨32715365925420240978940379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21810243950280160652626919 32715365925420240978940379)
  ·
    refine ⟨49073048888130361468410569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32715365925420240978940379 49073048888130361468410569)
    ·
      refine ⟨36804786666097771101307927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49073048888130361468410569 36804786666097771101307927)
      ·
        refine ⟨55207179999146656651961891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36804786666097771101307927 55207179999146656651961891)
        ·
          refine ⟨82810769998719984977942837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55207179999146656651961891 82810769998719984977942837)
          ·
            refine ⟨7763509687379998591682141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82810769998719984977942837 7763509687379998591682141)
            ·
              refine ⟨2911316132767499471880803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7763509687379998591682141 2911316132767499471880803)
              ·
                refine ⟨4366974199151249207821205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911316132767499471880803 4366974199151249207821205)
                ·
                  refine ⟨204701915585214806616619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4366974199151249207821205 204701915585214806616619)
                  ·
                    rfl

theorem cell21_896975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_896975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_896975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_896975 prefixEnd_896975 := by exact prefixLift 896975
  have htrace : WordTrace (prefixWord ++ tailWord_896975) baseStart_896975 baseEnd_896975 := by
    simpa [prefixWord, tailWord_896975, baseEnd_896975] using wordTrace_append hprefix tailTrace_896975
  have hstable : (prefixWord ++ tailWord_896975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_896975).length < 2 ^ (prefixWord ++ tailWord_896975).sum := by decide
  have hdescent : baseEnd_896975 < baseStart_896975 := by decide
  rcases family_descends (prefixWord ++ tailWord_896975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897127 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_897127 : Nat := 118140960795 + 897127 * 2 ^ 59
def prefixEnd_897127 : Nat := 4983230072969 + 3 ^ 40 * 897127 * 2
def baseEnd_897127 : Nat := 204736604056096320082975

theorem tailTrace_897127 : CollatzResearch.WordTrace tailWord_897127 prefixEnd_897127 204736604056096320082975 := by
  unfold tailWord_897127
  simp only [CollatzResearch.WordTrace]
  refine ⟨32720909820869570938473635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21813939880579713958982423 32720909820869570938473635)
  ·
    refine ⟨49081364731304356407710453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32720909820869570938473635 49081364731304356407710453)
    ·
      refine ⟨4601377943559783413222855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49081364731304356407710453 4601377943559783413222855)
      ·
        refine ⟨6902066915339675119834283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4601377943559783413222855 6902066915339675119834283)
        ·
          refine ⟨10353100373009512679751425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6902066915339675119834283 10353100373009512679751425)
          ·
            refine ⟨7764825279757134509813569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10353100373009512679751425 7764825279757134509813569)
            ·
              refine ⟨5823618959817850882360177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7764825279757134509813569 5823618959817850882360177)
              ·
                refine ⟨4367714219863388161770133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5823618959817850882360177 4367714219863388161770133)
                ·
                  refine ⟨204736604056096320082975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4367714219863388161770133 204736604056096320082975)
                  ·
                    rfl

theorem cell21_897127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_897127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897127 prefixEnd_897127 := by exact prefixLift 897127
  have htrace : WordTrace (prefixWord ++ tailWord_897127) baseStart_897127 baseEnd_897127 := by
    simpa [prefixWord, tailWord_897127, baseEnd_897127] using wordTrace_append hprefix tailTrace_897127
  have hstable : (prefixWord ++ tailWord_897127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897127).length < 2 ^ (prefixWord ++ tailWord_897127).sum := by decide
  have hdescent : baseEnd_897127 < baseStart_897127 := by decide
  rcases family_descends (prefixWord ++ tailWord_897127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897203 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 4]
def baseStart_897203 : Nat := 118140960795 + 897203 * 2 ^ 59
def prefixEnd_897203 : Nat := 4983230072969 + 3 ^ 40 * 897203 * 2
def baseEnd_897203 : Nat := 204753948291537076816153

theorem tailTrace_897203 : CollatzResearch.WordTrace tailWord_897203 prefixEnd_897203 204753948291537076816153 := by
  unfold tailWord_897203
  simp only [CollatzResearch.WordTrace]
  refine ⟨32723681768594235918240263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21815787845729490612160175 32723681768594235918240263)
  ·
    refine ⟨49085522652891353877360395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32723681768594235918240263 49085522652891353877360395)
    ·
      refine ⟨73628283979337030816040593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49085522652891353877360395 73628283979337030816040593)
      ·
        refine ⟨55221212984502773112030445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73628283979337030816040593 55221212984502773112030445)
        ·
          refine ⟨20707954869188539917011417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55221212984502773112030445 20707954869188539917011417)
          ·
            refine ⟨15530966151891404937758563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20707954869188539917011417 15530966151891404937758563)
            ·
              refine ⟨23296449227837107406637845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15530966151891404937758563 23296449227837107406637845)
              ·
                refine ⟨1092021057554864409686149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23296449227837107406637845 1092021057554864409686149)
                ·
                  refine ⟨204753948291537076816153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092021057554864409686149 204753948291537076816153)
                  ·
                    rfl

theorem cell21_897203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_897203 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897203 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897203 prefixEnd_897203 := by exact prefixLift 897203
  have htrace : WordTrace (prefixWord ++ tailWord_897203) baseStart_897203 baseEnd_897203 := by
    simpa [prefixWord, tailWord_897203, baseEnd_897203] using wordTrace_append hprefix tailTrace_897203
  have hstable : (prefixWord ++ tailWord_897203).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897203).length < 2 ^ (prefixWord ++ tailWord_897203).sum := by decide
  have hdescent : baseEnd_897203 < baseStart_897203 := by decide
  rcases family_descends (prefixWord ++ tailWord_897203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897234 : List Nat := [3, 2, 2, 2, 1, 2, 2, 7]
def baseStart_897234 : Nat := 118140960795 + 897234 * 2 ^ 59
def prefixEnd_897234 : Nat := 4983230072969 + 3 ^ 40 * 897234 * 2
def baseEnd_897234 : Nat := 68253674304629303933141

theorem tailTrace_897234 : CollatzResearch.WordTrace tailWord_897234 prefixEnd_897234 68253674304629303933141 := by
  unfold tailWord_897234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181203107870482053154689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21816541620987952141745837 8181203107870482053154689)
  ·
    refine ⟨6135902330902861539866017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8181203107870482053154689 6135902330902861539866017)
    ·
      refine ⟨4601926748177146154899513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6135902330902861539866017 4601926748177146154899513)
      ·
        refine ⟨3451445061132859616174635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4601926748177146154899513 3451445061132859616174635)
        ·
          refine ⟨5177167591699289424261953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451445061132859616174635 5177167591699289424261953)
          ·
            refine ⟨3882875693774467068196465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5177167591699289424261953 3882875693774467068196465)
            ·
              refine ⟨2912156770330850301147349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3882875693774467068196465 2912156770330850301147349)
              ·
                refine ⟨68253674304629303933141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2912156770330850301147349 68253674304629303933141)
                ·
                  rfl

theorem cell21_897234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_897234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897234 prefixEnd_897234 := by exact prefixLift 897234
  have htrace : WordTrace (prefixWord ++ tailWord_897234) baseStart_897234 baseEnd_897234 := by
    simpa [prefixWord, tailWord_897234, baseEnd_897234] using wordTrace_append hprefix tailTrace_897234
  have hstable : (prefixWord ++ tailWord_897234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897234).length < 2 ^ (prefixWord ++ tailWord_897234).sum := by decide
  have hdescent : baseEnd_897234 < baseStart_897234 := by decide
  rcases family_descends (prefixWord ++ tailWord_897234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897251 : List Nat := [1, 1, 1, 8, 2, 8]
def baseStart_897251 : Nat := 118140960795 + 897251 * 2 ^ 59
def prefixEnd_897251 : Nat := 4983230072969 + 3 ^ 40 * 897251 * 2
def baseEnd_897251 : Nat := 7583885279462950370965

theorem tailTrace_897251 : CollatzResearch.WordTrace tailWord_897251 prefixEnd_897251 7583885279462950370965 := by
  unfold tailWord_897251
  simp only [CollatzResearch.WordTrace]
  refine ⟨32725432472420340115987607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21816954981613560077325071 32725432472420340115987607)
  ·
    refine ⟨49088148708630510173981411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32725432472420340115987607 49088148708630510173981411)
    ·
      refine ⟨73632223062945765260972117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49088148708630510173981411 73632223062945765260972117)
      ·
        refine ⟨862877614018895686652017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 73632223062945765260972117 862877614018895686652017)
        ·
          refine ⟨647158210514171764989013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862877614018895686652017 647158210514171764989013)
          ·
            refine ⟨7583885279462950370965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 647158210514171764989013 7583885279462950370965)
            ·
              rfl

theorem cell21_897251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 8].length) (baseStart_897251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897251 prefixEnd_897251 := by exact prefixLift 897251
  have htrace : WordTrace (prefixWord ++ tailWord_897251) baseStart_897251 baseEnd_897251 := by
    simpa [prefixWord, tailWord_897251, baseEnd_897251] using wordTrace_append hprefix tailTrace_897251
  have hstable : (prefixWord ++ tailWord_897251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897251).length < 2 ^ (prefixWord ++ tailWord_897251).sum := by decide
  have hdescent : baseEnd_897251 < baseStart_897251 := by decide
  rcases family_descends (prefixWord ++ tailWord_897251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897279 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 4]
def baseStart_897279 : Nat := 118140960795 + 897279 * 2 ^ 59
def prefixEnd_897279 : Nat := 4983230072969 + 3 ^ 40 * 897279 * 2
def baseEnd_897279 : Nat := 204771292526977833549331

theorem tailTrace_897279 : CollatzResearch.WordTrace tailWord_897279 prefixEnd_897279 204771292526977833549331 := by
  unfold tailWord_897279
  simp only [CollatzResearch.WordTrace]
  refine ⟨32726453716318900898006891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21817635810879267265337927 32726453716318900898006891)
  ·
    refine ⟨49089680574478351347010337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32726453716318900898006891 49089680574478351347010337)
    ·
      refine ⟨36817260430858763510257753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49089680574478351347010337 36817260430858763510257753)
      ·
        refine ⟨27612945323144072632693315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36817260430858763510257753 27612945323144072632693315)
        ·
          refine ⟨41419417984716108949039973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27612945323144072632693315 41419417984716108949039973)
          ·
            refine ⟨7766140872134270427944995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41419417984716108949039973 7766140872134270427944995)
            ·
              refine ⟨11649211308201405641917493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766140872134270427944995 11649211308201405641917493)
              ·
                refine ⟨1092113560143881778929765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11649211308201405641917493 1092113560143881778929765)
                ·
                  refine ⟨204771292526977833549331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092113560143881778929765 204771292526977833549331)
                  ·
                    rfl

theorem cell21_897279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 4].length) (baseStart_897279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897279 prefixEnd_897279 := by exact prefixLift 897279
  have htrace : WordTrace (prefixWord ++ tailWord_897279) baseStart_897279 baseEnd_897279 := by
    simpa [prefixWord, tailWord_897279, baseEnd_897279] using wordTrace_append hprefix tailTrace_897279
  have hstable : (prefixWord ++ tailWord_897279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897279).length < 2 ^ (prefixWord ++ tailWord_897279).sum := by decide
  have hdescent : baseEnd_897279 < baseStart_897279 := by decide
  rcases family_descends (prefixWord ++ tailWord_897279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897282 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_897282 : Nat := 118140960795 + 897282 * 2 ^ 59
def prefixEnd_897282 : Nat := 4983230072969 + 3 ^ 40 * 897282 * 2
def baseEnd_897282 : Nat := 204771977167850494999325

theorem tailTrace_897282 : CollatzResearch.WordTrace tailWord_897282 prefixEnd_897282 204771977167850494999325 := by
  unfold tailWord_897282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181640783827008102591525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21817708756872021606910733 8181640783827008102591525)
  ·
    refine ⟨1534057646967564019235911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8181640783827008102591525 1534057646967564019235911)
    ·
      refine ⟨2301086470451346028853867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534057646967564019235911 2301086470451346028853867)
      ·
        refine ⟨3451629705677019043280801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301086470451346028853867 3451629705677019043280801)
        ·
          refine ⟨2588722279257764282460601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3451629705677019043280801 2588722279257764282460601)
          ·
            refine ⟨1941541709443323211845451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2588722279257764282460601 1941541709443323211845451)
            ·
              refine ⟨2912312564164984817768177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941541709443323211845451 2912312564164984817768177)
              ·
                refine ⟨2184234423123738613326133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912312564164984817768177 2184234423123738613326133)
                ·
                  refine ⟨204771977167850494999325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2184234423123738613326133 204771977167850494999325)
                  ·
                    rfl

theorem cell21_897282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_897282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897282 prefixEnd_897282 := by exact prefixLift 897282
  have htrace : WordTrace (prefixWord ++ tailWord_897282) baseStart_897282 baseEnd_897282 := by
    simpa [prefixWord, tailWord_897282, baseEnd_897282] using wordTrace_append hprefix tailTrace_897282
  have hstable : (prefixWord ++ tailWord_897282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897282).length < 2 ^ (prefixWord ++ tailWord_897282).sum := by decide
  have hdescent : baseEnd_897282 < baseStart_897282 := by decide
  rcases family_descends (prefixWord ++ tailWord_897282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897324 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 5]
def baseStart_897324 : Nat := 118140960795 + 897324 * 2 ^ 59
def prefixEnd_897324 : Nat := 4983230072969 + 3 ^ 40 * 897324 * 2
def baseEnd_897324 : Nat := 204781562140067755299239

theorem tailTrace_897324 : CollatzResearch.WordTrace tailWord_897324 prefixEnd_897324 204781562140067755299239 := by
  unfold tailWord_897324
  simp only [CollatzResearch.WordTrace]
  refine ⟨16364047500577936791697513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21818730000770582388930017 16364047500577936791697513)
  ·
    refine ⟨12273035625433452593773135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16364047500577936791697513 12273035625433452593773135)
    ·
      refine ⟨18409553438150178890659703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12273035625433452593773135 18409553438150178890659703)
      ·
        refine ⟨27614330157225268335989555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18409553438150178890659703 27614330157225268335989555)
        ·
          refine ⟨41421495235837902503984333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27614330157225268335989555 41421495235837902503984333)
          ·
            refine ⟨15533060713439213438994125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41421495235837902503984333 15533060713439213438994125)
            ·
              refine ⟨5824897767539705039622797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15533060713439213438994125 5824897767539705039622797)
              ·
                refine ⟨2184336662827389389858549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5824897767539705039622797 2184336662827389389858549)
                ·
                  refine ⟨204781562140067755299239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2184336662827389389858549 204781562140067755299239)
                  ·
                    rfl

theorem cell21_897324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_897324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897324 prefixEnd_897324 := by exact prefixLift 897324
  have htrace : WordTrace (prefixWord ++ tailWord_897324) baseStart_897324 baseEnd_897324 := by
    simpa [prefixWord, tailWord_897324, baseEnd_897324] using wordTrace_append hprefix tailTrace_897324
  have hstable : (prefixWord ++ tailWord_897324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897324).length < 2 ^ (prefixWord ++ tailWord_897324).sum := by decide
  have hdescent : baseEnd_897324 < baseStart_897324 := by decide
  rcases family_descends (prefixWord ++ tailWord_897324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897386 : List Nat := [3, 1, 3, 3, 1, 1, 1, 8]
def baseStart_897386 : Nat := 118140960795 + 897386 * 2 ^ 59
def prefixEnd_897386 : Nat := 4983230072969 + 3 ^ 40 * 897386 * 2
def baseEnd_897386 : Nat := 68265237128256475088593

theorem tailTrace_897386 : CollatzResearch.WordTrace tailWord_897386 prefixEnd_897386 68265237128256475088593 := by
  unfold tailWord_897386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8182589081732814543038003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21820237551287505448101341 8182589081732814543038003)
  ·
    refine ⟨12273883622599221814557005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8182589081732814543038003 12273883622599221814557005)
    ·
      refine ⟨4602706358474708180458877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12273883622599221814557005 4602706358474708180458877)
      ·
        refine ⟨1726014884428015567672079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4602706358474708180458877 1726014884428015567672079)
        ·
          refine ⟨2589022326642023351508119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726014884428015567672079 2589022326642023351508119)
          ·
            refine ⟨3883533489963035027262179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589022326642023351508119 3883533489963035027262179)
            ·
              refine ⟨5825300234944552540893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883533489963035027262179 5825300234944552540893269)
              ·
                refine ⟨68265237128256475088593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5825300234944552540893269 68265237128256475088593)
                ·
                  rfl

theorem cell21_897386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_897386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897386 prefixEnd_897386 := by exact prefixLift 897386
  have htrace : WordTrace (prefixWord ++ tailWord_897386) baseStart_897386 baseEnd_897386 := by
    simpa [prefixWord, tailWord_897386, baseEnd_897386] using wordTrace_append hprefix tailTrace_897386
  have hstable : (prefixWord ++ tailWord_897386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897386).length < 2 ^ (prefixWord ++ tailWord_897386).sum := by decide
  have hdescent : baseEnd_897386 < baseStart_897386 := by decide
  rcases family_descends (prefixWord ++ tailWord_897386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897431 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 4]
def baseStart_897431 : Nat := 118140960795 + 897431 * 2 ^ 59
def prefixEnd_897431 : Nat := 4983230072969 + 3 ^ 40 * 897431 * 2
def baseEnd_897431 : Nat := 204805980997859347015687

theorem tailTrace_897431 : CollatzResearch.WordTrace tailWord_897431 prefixEnd_897431 204805980997859347015687 := by
  unfold tailWord_897431
  simp only [CollatzResearch.WordTrace]
  refine ⟨32731997611768230857540147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21821331741178820571693431 32731997611768230857540147)
  ·
    refine ⟨49097996417652346286310221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32731997611768230857540147 49097996417652346286310221)
    ·
      refine ⟨18411748656619629857366333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49097996417652346286310221 18411748656619629857366333)
      ·
        refine ⟨6904405746232361196512375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18411748656619629857366333 6904405746232361196512375)
        ·
          refine ⟨10356608619348541794768563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904405746232361196512375 10356608619348541794768563)
          ·
            refine ⟨15534912929022812692152845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10356608619348541794768563 15534912929022812692152845)
            ·
              refine ⟨5825592348383554759557317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15534912929022812692152845 5825592348383554759557317)
              ·
                refine ⟨1092298565321916517416997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5825592348383554759557317 1092298565321916517416997)
                ·
                  refine ⟨204805980997859347015687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1092298565321916517416997 204805980997859347015687)
                  ·
                    rfl

theorem cell21_897431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_897431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897431 prefixEnd_897431 := by exact prefixLift 897431
  have htrace : WordTrace (prefixWord ++ tailWord_897431) baseStart_897431 baseEnd_897431 := by
    simpa [prefixWord, tailWord_897431, baseEnd_897431] using wordTrace_append hprefix tailTrace_897431
  have hstable : (prefixWord ++ tailWord_897431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897431).length < 2 ^ (prefixWord ++ tailWord_897431).sum := by decide
  have hdescent : baseEnd_897431 < baseStart_897431 := by decide
  rcases family_descends (prefixWord ++ tailWord_897431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897434 : List Nat := [3, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_897434 : Nat := 118140960795 + 897434 * 2 ^ 59
def prefixEnd_897434 : Nat := 4983230072969 + 3 ^ 40 * 897434 * 2
def baseEnd_897434 : Nat := 204806665638732008465681

theorem tailTrace_897434 : CollatzResearch.WordTrace tailWord_897434 prefixEnd_897434 204806665638732008465681 := by
  unfold tailWord_897434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8183026757689340592474839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21821404687171574913266237 8183026757689340592474839)
  ·
    refine ⟨12274540136534010888712259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8183026757689340592474839 12274540136534010888712259)
    ·
      refine ⟨18411810204801016333068389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12274540136534010888712259 18411810204801016333068389)
      ·
        refine ⟨3452214413400190562450323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18411810204801016333068389 3452214413400190562450323)
        ·
          refine ⟨5178321620100285843675485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452214413400190562450323 5178321620100285843675485)
          ·
            refine ⟨1941870607537607191378307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5178321620100285843675485 1941870607537607191378307)
            ·
              refine ⟨2912805911306410787067461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1941870607537607191378307 2912805911306410787067461)
              ·
                refine ⟨546151108369952022575149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2912805911306410787067461 546151108369952022575149)
                ·
                  refine ⟨204806665638732008465681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546151108369952022575149 204806665638732008465681)
                  ·
                    rfl

theorem cell21_897434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_897434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897434 prefixEnd_897434 := by exact prefixLift 897434
  have htrace : WordTrace (prefixWord ++ tailWord_897434) baseStart_897434 baseEnd_897434 := by
    simpa [prefixWord, tailWord_897434, baseEnd_897434] using wordTrace_append hprefix tailTrace_897434
  have hstable : (prefixWord ++ tailWord_897434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897434).length < 2 ^ (prefixWord ++ tailWord_897434).sum := by decide
  have hdescent : baseEnd_897434 < baseStart_897434 := by decide
  rcases family_descends (prefixWord ++ tailWord_897434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897493 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 5]
def baseStart_897493 : Nat := 118140960795 + 897493 * 2 ^ 59
def prefixEnd_897493 : Nat := 4983230072969 + 3 ^ 40 * 897493 * 2
def baseEnd_897493 : Nat := 204820130242561016982227

theorem tailTrace_897493 : CollatzResearch.WordTrace tailWord_897493 prefixEnd_897493 204820130242561016982227 := by
  unfold tailWord_897493
  simp only [CollatzResearch.WordTrace]
  refine ⟨32734258937543615446297133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21822839291695743630864755 32734258937543615446297133)
  ·
    refine ⟨12275347101578855792361425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32734258937543615446297133 12275347101578855792361425)
    ·
      refine ⟨9206510326184141844271069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12275347101578855792361425 9206510326184141844271069)
      ·
        refine ⟨3452441372319053191601651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9206510326184141844271069 3452441372319053191601651)
        ·
          refine ⟨5178662058478579787402477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452441372319053191601651 5178662058478579787402477)
          ·
            refine ⟨1941998271929467420275929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5178662058478579787402477 1941998271929467420275929)
            ·
              refine ⟨1456498703947100565206947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1941998271929467420275929 1456498703947100565206947)
              ·
                refine ⟨2184748055920650847810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456498703947100565206947 2184748055920650847810421)
                ·
                  refine ⟨204820130242561016982227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2184748055920650847810421 204820130242561016982227)
                  ·
                    rfl

theorem cell21_897493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_897493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897493 prefixEnd_897493 := by exact prefixLift 897493
  have htrace : WordTrace (prefixWord ++ tailWord_897493) baseStart_897493 baseEnd_897493 := by
    simpa [prefixWord, tailWord_897493, baseEnd_897493] using wordTrace_append hprefix tailTrace_897493
  have hstable : (prefixWord ++ tailWord_897493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897493).length < 2 ^ (prefixWord ++ tailWord_897493).sum := by decide
  have hdescent : baseEnd_897493 < baseStart_897493 := by decide
  rcases family_descends (prefixWord ++ tailWord_897493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897521 : List Nat := [1, 2, 2, 2, 3, 1, 3, 7]
def baseStart_897521 : Nat := 118140960795 + 897521 * 2 ^ 59
def prefixEnd_897521 : Nat := 4983230072969 + 3 ^ 40 * 897521 * 2
def baseEnd_897521 : Nat := 68275506741346396838501

theorem tailTrace_897521 : CollatzResearch.WordTrace tailWord_897521 prefixEnd_897521 68275506741346396838501 := by
  unfold tailWord_897521
  simp only [CollatzResearch.WordTrace]
  refine ⟨32735280181442176228316417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21823520120961450818877611 32735280181442176228316417)
  ·
    refine ⟨24551460136081632171237313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32735280181442176228316417 24551460136081632171237313)
    ·
      refine ⟨18413595102061224128427985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24551460136081632171237313 18413595102061224128427985)
      ·
        refine ⟨13810196326545918096320989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18413595102061224128427985 13810196326545918096320989)
        ·
          refine ⟨5178823622454719286120371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13810196326545918096320989 5178823622454719286120371)
          ·
            refine ⟨7768235433682078929180557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178823622454719286120371 7768235433682078929180557)
            ·
              refine ⟨2913088287630779598442709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7768235433682078929180557 2913088287630779598442709)
              ·
                refine ⟨68275506741346396838501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2913088287630779598442709 68275506741346396838501)
                ·
                  rfl

theorem cell21_897521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_897521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897521 prefixEnd_897521 := by exact prefixLift 897521
  have htrace : WordTrace (prefixWord ++ tailWord_897521) baseStart_897521 baseEnd_897521 := by
    simpa [prefixWord, tailWord_897521, baseEnd_897521] using wordTrace_append hprefix tailTrace_897521
  have hstable : (prefixWord ++ tailWord_897521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897521).length < 2 ^ (prefixWord ++ tailWord_897521).sum := by decide
  have hdescent : baseEnd_897521 < baseStart_897521 := by decide
  rcases family_descends (prefixWord ++ tailWord_897521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897597 : List Nat := [1, 4, 1, 3, 2, 10]
def baseStart_897597 : Nat := 118140960795 + 897597 * 2 ^ 59
def prefixEnd_897597 : Nat := 4983230072969 + 3 ^ 40 * 897597 * 2
def baseEnd_897597 : Nat := 7586809794795553601803

theorem tailTrace_897597 : CollatzResearch.WordTrace tailWord_897597 prefixEnd_897597 7586809794795553601803 := by
  unfold tailWord_897597
  simp only [CollatzResearch.WordTrace]
  refine ⟨32738052129166841208083045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21825368086111227472055363 32738052129166841208083045)
  ·
    refine ⟨6138384774218782726515571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32738052129166841208083045 6138384774218782726515571)
    ·
      refine ⟨9207577161328174089773357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138384774218782726515571 9207577161328174089773357)
      ·
        refine ⟨3452841435498065283665009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9207577161328174089773357 3452841435498065283665009)
        ·
          refine ⟨2589631076623548962748757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3452841435498065283665009 2589631076623548962748757)
          ·
            refine ⟨7586809794795553601803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2589631076623548962748757 7586809794795553601803)
            ·
              rfl

theorem cell21_897597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 10].length) (baseStart_897597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897597 prefixEnd_897597 := by exact prefixLift 897597
  have htrace : WordTrace (prefixWord ++ tailWord_897597) baseStart_897597 baseEnd_897597 := by
    simpa [prefixWord, tailWord_897597, baseEnd_897597] using wordTrace_append hprefix tailTrace_897597
  have hstable : (prefixWord ++ tailWord_897597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897597).length < 2 ^ (prefixWord ++ tailWord_897597).sum := by decide
  have hdescent : baseEnd_897597 < baseStart_897597 := by decide
  rcases family_descends (prefixWord ++ tailWord_897597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897890 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_897890 : Nat := 118140960795 + 897890 * 2 ^ 59
def prefixEnd_897890 : Nat := 4983230072969 + 3 ^ 40 * 897890 * 2
def baseEnd_897890 : Nat := 204910731051376548864749

theorem tailTrace_897890 : CollatzResearch.WordTrace tailWord_897890 prefixEnd_897890 204910731051376548864749 := by
  unfold tailWord_897890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187184679276338062124781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21832492478070234832332749 8187184679276338062124781)
  ·
    refine ⟨3070194254728626773296793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8187184679276338062124781 3070194254728626773296793)
    ·
      refine ⟨2302645691046470079972595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3070194254728626773296793 2302645691046470079972595)
      ·
        refine ⟨3453968536569705119958893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302645691046470079972595 3453968536569705119958893)
        ·
          refine ⟨1295238201213639419984585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3453968536569705119958893 1295238201213639419984585)
          ·
            refine ⟨971428650910229564988439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1295238201213639419984585 971428650910229564988439)
            ·
              refine ⟨1457142976365344347482659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971428650910229564988439 1457142976365344347482659)
              ·
                refine ⟨2185714464548016521223989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457142976365344347482659 2185714464548016521223989)
                ·
                  refine ⟨204910731051376548864749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185714464548016521223989 204910731051376548864749)
                  ·
                    rfl

theorem cell21_897890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_897890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897890 prefixEnd_897890 := by exact prefixLift 897890
  have htrace : WordTrace (prefixWord ++ tailWord_897890) baseStart_897890 baseEnd_897890 := by
    simpa [prefixWord, tailWord_897890, baseEnd_897890] using wordTrace_append hprefix tailTrace_897890
  have hstable : (prefixWord ++ tailWord_897890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897890).length < 2 ^ (prefixWord ++ tailWord_897890).sum := by decide
  have hdescent : baseEnd_897890 < baseStart_897890 := by decide
  rcases family_descends (prefixWord ++ tailWord_897890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897915 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 5]
def baseStart_897915 : Nat := 118140960795 + 897915 * 2 ^ 59
def prefixEnd_897915 : Nat := 4983230072969 + 3 ^ 40 * 897915 * 2
def baseEnd_897915 : Nat := 204916436391982060948031

theorem tailTrace_897915 : CollatzResearch.WordTrace tailWord_897915 prefixEnd_897915 204916436391982060948031 := by
  unfold tailWord_897915
  simp only [CollatzResearch.WordTrace]
  refine ⟨32749650542014781518159199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21833100361343187678772799 32749650542014781518159199)
  ·
    refine ⟨49124475813022172277238799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32749650542014781518159199 49124475813022172277238799)
    ·
      refine ⟨73686713719533258415858199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49124475813022172277238799 73686713719533258415858199)
      ·
        refine ⟨110530070579299887623787299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73686713719533258415858199 110530070579299887623787299)
        ·
          refine ⟨165795105868949831435680949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110530070579299887623787299 165795105868949831435680949)
          ·
            refine ⟨15543291175214046697095089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165795105868949831435680949 15543291175214046697095089)
            ·
              refine ⟨11657468381410535022821317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15543291175214046697095089 11657468381410535022821317)
              ·
                refine ⟨2185775321514475316778997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11657468381410535022821317 2185775321514475316778997)
                ·
                  refine ⟨204916436391982060948031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2185775321514475316778997 204916436391982060948031)
                  ·
                    rfl

theorem cell21_897915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_897915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897915 prefixEnd_897915 := by exact prefixLift 897915
  have htrace : WordTrace (prefixWord ++ tailWord_897915) baseStart_897915 baseEnd_897915 := by
    simpa [prefixWord, tailWord_897915, baseEnd_897915] using wordTrace_append hprefix tailTrace_897915
  have hstable : (prefixWord ++ tailWord_897915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897915).length < 2 ^ (prefixWord ++ tailWord_897915).sum := by decide
  have hdescent : baseEnd_897915 < baseStart_897915 := by decide
  rcases family_descends (prefixWord ++ tailWord_897915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_897949 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 3]
def baseStart_897949 : Nat := 118140960795 + 897949 * 2 ^ 59
def prefixEnd_897949 : Nat := 4983230072969 + 3 ^ 40 * 897949 * 2
def baseEnd_897949 : Nat := 204924195655205557381295

theorem tailTrace_897949 : CollatzResearch.WordTrace tailWord_897949 prefixEnd_897949 204924195655205557381295 := by
  unfold tailWord_897949
  simp only [CollatzResearch.WordTrace]
  refine ⟨32750890623891605324896901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21833927082594403549931267 32750890623891605324896901)
  ·
    refine ⟨6140791991979675998418169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32750890623891605324896901 6140791991979675998418169)
    ·
      refine ⟨4605593993984756998813627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6140791991979675998418169 4605593993984756998813627)
      ·
        refine ⟨6908390990977135498220441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605593993984756998813627 6908390990977135498220441)
        ·
          refine ⟨5181293243232851623665331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6908390990977135498220441 5181293243232851623665331)
          ·
            refine ⟨7771939864849277435497997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181293243232851623665331 7771939864849277435497997)
            ·
              refine ⟨2914477449318479038311749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7771939864849277435497997 2914477449318479038311749)
              ·
                refine ⟨546464521747214819683453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2914477449318479038311749 546464521747214819683453)
                ·
                  refine ⟨204924195655205557381295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546464521747214819683453 204924195655205557381295)
                  ·
                    rfl

theorem cell21_897949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_897949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_897949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_897949 prefixEnd_897949 := by exact prefixLift 897949
  have htrace : WordTrace (prefixWord ++ tailWord_897949) baseStart_897949 baseEnd_897949 := by
    simpa [prefixWord, tailWord_897949, baseEnd_897949] using wordTrace_append hprefix tailTrace_897949
  have hstable : (prefixWord ++ tailWord_897949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_897949).length < 2 ^ (prefixWord ++ tailWord_897949).sum := by decide
  have hdescent : baseEnd_897949 < baseStart_897949 := by decide
  rcases family_descends (prefixWord ++ tailWord_897949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898008 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 5]
def baseStart_898008 : Nat := 118140960795 + 898008 * 2 ^ 59
def prefixEnd_898008 : Nat := 4983230072969 + 3 ^ 40 * 898008 * 2
def baseEnd_898008 : Nat := 204937660259034565897841

theorem tailTrace_898008 : CollatzResearch.WordTrace tailWord_898008 prefixEnd_898008 204937660259034565897841 := by
  unfold tailWord_898008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376521265338929200647339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21835361687118572267529785 16376521265338929200647339)
  ·
    refine ⟨24564781898008393800971009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16376521265338929200647339 24564781898008393800971009)
    ·
      refine ⟨18423586423506295350728257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24564781898008393800971009 18423586423506295350728257)
      ·
        refine ⟨13817689817629721513046193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18423586423506295350728257 13817689817629721513046193)
        ·
          refine ⟨10363267363222291134784645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13817689817629721513046193 10363267363222291134784645)
          ·
            refine ⟨1943112630604179587772121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10363267363222291134784645 1943112630604179587772121)
            ·
              refine ⟨1457334472953134690829091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1943112630604179587772121 1457334472953134690829091)
              ·
                refine ⟨2186001709429702036243637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457334472953134690829091 2186001709429702036243637)
                ·
                  refine ⟨204937660259034565897841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2186001709429702036243637 204937660259034565897841)
                  ·
                    rfl

theorem cell21_898008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 5].length) (baseStart_898008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898008 prefixEnd_898008 := by exact prefixLift 898008
  have htrace : WordTrace (prefixWord ++ tailWord_898008) baseStart_898008 baseEnd_898008 := by
    simpa [prefixWord, tailWord_898008, baseEnd_898008] using wordTrace_append hprefix tailTrace_898008
  have hstable : (prefixWord ++ tailWord_898008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898008).length < 2 ^ (prefixWord ++ tailWord_898008).sum := by decide
  have hdescent : baseEnd_898008 < baseStart_898008 := by decide
  rcases family_descends (prefixWord ++ tailWord_898008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898143 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 5]
def baseStart_898143 : Nat := 118140960795 + 898143 * 2 ^ 59
def prefixEnd_898143 : Nat := 4983230072969 + 3 ^ 40 * 898143 * 2
def baseEnd_898143 : Nat := 204968469098304331147565

theorem tailTrace_898143 : CollatzResearch.WordTrace tailWord_898143 prefixEnd_898143 204968469098304331147565 := by
  unfold tailWord_898143
  simp only [CollatzResearch.WordTrace]
  refine ⟨32757966385188776457459083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21838644256792517638306055 32757966385188776457459083)
  ·
    refine ⟨49136949577783164686188625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32757966385188776457459083 49136949577783164686188625)
    ·
      refine ⟨36852712183337373514641469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49136949577783164686188625 36852712183337373514641469)
      ·
        refine ⟨13819767068751515067990551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36852712183337373514641469 13819767068751515067990551)
        ·
          refine ⟨20729650603127272601985827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13819767068751515067990551 20729650603127272601985827)
          ·
            refine ⟨31094475904690908902978741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20729650603127272601985827 31094475904690908902978741)
            ·
              refine ⟨2915107116064772709654257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31094475904690908902978741 2915107116064772709654257)
              ·
                refine ⟨2186330337048579532240693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915107116064772709654257 2186330337048579532240693)
                ·
                  refine ⟨204968469098304331147565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2186330337048579532240693 204968469098304331147565)
                  ·
                    rfl

theorem cell21_898143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_898143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898143 prefixEnd_898143 := by exact prefixLift 898143
  have htrace : WordTrace (prefixWord ++ tailWord_898143) baseStart_898143 baseEnd_898143 := by
    simpa [prefixWord, tailWord_898143, baseEnd_898143] using wordTrace_append hprefix tailTrace_898143
  have hstable : (prefixWord ++ tailWord_898143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898143).length < 2 ^ (prefixWord ++ tailWord_898143).sum := by decide
  have hdescent : baseEnd_898143 < baseStart_898143 := by decide
  rcases family_descends (prefixWord ++ tailWord_898143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898177 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 3]
def baseStart_898177 : Nat := 118140960795 + 898177 * 2 ^ 59
def prefixEnd_898177 : Nat := 4983230072969 + 3 ^ 40 * 898177 * 2
def baseEnd_898177 : Nat := 204976228361527827580829

theorem tailTrace_898177 : CollatzResearch.WordTrace tailWord_898177 prefixEnd_898177 204976228361527827580829 := by
  unfold tailWord_898177
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759206467065600264196785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21839470978043733509464523 32759206467065600264196785)
  ·
    refine ⟨24569404850299200198147589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32759206467065600264196785 24569404850299200198147589)
    ·
      refine ⟨4606763409431100037152673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24569404850299200198147589 4606763409431100037152673)
      ·
        refine ⟨3455072557073325027864505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4606763409431100037152673 3455072557073325027864505)
        ·
          refine ⟨2591304417804993770898379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3455072557073325027864505 2591304417804993770898379)
          ·
            refine ⟨3886956626707490656347569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591304417804993770898379 3886956626707490656347569)
            ·
              refine ⟨2915217470030617992260677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886956626707490656347569 2915217470030617992260677)
              ·
                refine ⟨546603275630740873548877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2915217470030617992260677 546603275630740873548877)
                ·
                  refine ⟨204976228361527827580829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546603275630740873548877 204976228361527827580829)
                  ·
                    rfl

theorem cell21_898177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_898177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898177 prefixEnd_898177 := by exact prefixLift 898177
  have htrace : WordTrace (prefixWord ++ tailWord_898177) baseStart_898177 baseEnd_898177 := by
    simpa [prefixWord, tailWord_898177, baseEnd_898177] using wordTrace_append hprefix tailTrace_898177
  have hstable : (prefixWord ++ tailWord_898177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898177).length < 2 ^ (prefixWord ++ tailWord_898177).sum := by decide
  have hdescent : baseEnd_898177 < baseStart_898177 := by decide
  rcases family_descends (prefixWord ++ tailWord_898177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898236 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_898236 : Nat := 118140960795 + 898236 * 2 ^ 59
def prefixEnd_898236 : Nat := 4983230072969 + 3 ^ 40 * 898236 * 2
def baseEnd_898236 : Nat := 204989692965356836097375

theorem tailTrace_898236 : CollatzResearch.WordTrace tailWord_898236 prefixEnd_898236 204989692965356836097375 := by
  unfold tailWord_898236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380679186925926670297281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21840905582567902227063041 16380679186925926670297281)
  ·
    refine ⟨12285509390194445002722961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16380679186925926670297281 12285509390194445002722961)
    ·
      refine ⟨9214132042645833752042221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12285509390194445002722961 9214132042645833752042221)
      ·
        refine ⟨3455299515992187657015833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9214132042645833752042221 3455299515992187657015833)
        ·
          refine ⟨2591474636994140742761875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3455299515992187657015833 2591474636994140742761875)
          ·
            refine ⟨3887211955491211114142813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591474636994140742761875 3887211955491211114142813)
            ·
              refine ⟨1457704483309204167803555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3887211955491211114142813 1457704483309204167803555)
              ·
                refine ⟨2186556724963806251705333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457704483309204167803555 2186556724963806251705333)
                ·
                  refine ⟨204989692965356836097375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2186556724963806251705333 204989692965356836097375)
                  ·
                    rfl

theorem cell21_898236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_898236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898236 prefixEnd_898236 := by exact prefixLift 898236
  have htrace : WordTrace (prefixWord ++ tailWord_898236) baseStart_898236 baseEnd_898236 := by
    simpa [prefixWord, tailWord_898236, baseEnd_898236] using wordTrace_append hprefix tailTrace_898236
  have hstable : (prefixWord ++ tailWord_898236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898236).length < 2 ^ (prefixWord ++ tailWord_898236).sum := by decide
  have hdescent : baseEnd_898236 < baseStart_898236 := by decide
  rcases family_descends (prefixWord ++ tailWord_898236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898287 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 3]
def baseStart_898287 : Nat := 118140960795 + 898287 * 2 ^ 59
def prefixEnd_898287 : Nat := 4983230072969 + 3 ^ 40 * 898287 * 2
def baseEnd_898287 : Nat := 205001331860192080747271

theorem tailTrace_898287 : CollatzResearch.WordTrace tailWord_898287 prefixEnd_898287 205001331860192080747271 := by
  unfold tailWord_898287
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763218496667089050701115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21842145664444726033800743 32763218496667089050701115)
  ·
    refine ⟨49144827745000633576051673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32763218496667089050701115 49144827745000633576051673)
    ·
      refine ⟨36858620808750475182038755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49144827745000633576051673 36858620808750475182038755)
      ·
        refine ⟨55287931213125712773058133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36858620808750475182038755 55287931213125712773058133)
        ·
          refine ⟨647905443903816946559275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 55287931213125712773058133 647905443903816946559275)
          ·
            refine ⟨971858165855725419838913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647905443903816946559275 971858165855725419838913)
            ·
              refine ⟨728893624391794064879185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971858165855725419838913 728893624391794064879185)
              ·
                refine ⟨546670218293845548659389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728893624391794064879185 546670218293845548659389)
                ·
                  refine ⟨205001331860192080747271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546670218293845548659389 205001331860192080747271)
                  ·
                    rfl

theorem cell21_898287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 3].length) (baseStart_898287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898287 prefixEnd_898287 := by exact prefixLift 898287
  have htrace : WordTrace (prefixWord ++ tailWord_898287) baseStart_898287 baseEnd_898287 := by
    simpa [prefixWord, tailWord_898287, baseEnd_898287] using wordTrace_append hprefix tailTrace_898287
  have hstable : (prefixWord ++ tailWord_898287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898287).length < 2 ^ (prefixWord ++ tailWord_898287).sum := by decide
  have hdescent : baseEnd_898287 < baseStart_898287 := by decide
  rcases family_descends (prefixWord ++ tailWord_898287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898312 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_898312 : Nat := 118140960795 + 898312 * 2 ^ 59
def prefixEnd_898312 : Nat := 4983230072969 + 3 ^ 40 * 898312 * 2
def baseEnd_898312 : Nat := 205007037200797592830553

theorem tailTrace_898312 : CollatzResearch.WordTrace tailWord_898312 prefixEnd_898312 205007037200797592830553 := by
  unfold tailWord_898312
  simp only [CollatzResearch.WordTrace]
  refine ⟨16382065160788259160180595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21842753547717678880240793 16382065160788259160180595)
  ·
    refine ⟨24573097741182388740270893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16382065160788259160180595 24573097741182388740270893)
    ·
      refine ⟨9214911652943395777601585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24573097741182388740270893 9214911652943395777601585)
      ·
        refine ⟨6911183739707546833201189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9214911652943395777601585 6911183739707546833201189)
        ·
          refine ⟨1295846951195165031225223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6911183739707546833201189 1295846951195165031225223)
          ·
            refine ⟨1943770426792747546837835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295846951195165031225223 1943770426792747546837835)
            ·
              refine ⟨2915655640189121320256753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1943770426792747546837835 2915655640189121320256753)
              ·
                refine ⟨2186741730141840990192565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915655640189121320256753 2186741730141840990192565)
                ·
                  refine ⟨205007037200797592830553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2186741730141840990192565 205007037200797592830553)
                  ·
                    rfl

theorem cell21_898312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_898312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898312 prefixEnd_898312 := by exact prefixLift 898312
  have htrace : WordTrace (prefixWord ++ tailWord_898312) baseStart_898312 baseEnd_898312 := by
    simpa [prefixWord, tailWord_898312, baseEnd_898312] using wordTrace_append hprefix tailTrace_898312
  have hstable : (prefixWord ++ tailWord_898312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898312).length < 2 ^ (prefixWord ++ tailWord_898312).sum := by decide
  have hdescent : baseEnd_898312 < baseStart_898312 := by decide
  rcases family_descends (prefixWord ++ tailWord_898312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898340 : List Nat := [2, 3, 1, 3, 1, 1, 10]
def baseStart_898340 : Nat := 118140960795 + 898340 * 2 ^ 59
def prefixEnd_898340 : Nat := 4983230072969 + 3 ^ 40 * 898340 * 2
def baseEnd_898340 : Nat := 22779269686919529595981

theorem tailTrace_898340 : CollatzResearch.WordTrace tailWord_898340 prefixEnd_898340 22779269686919529595981 := by
  unfold tailWord_898340
  simp only [CollatzResearch.WordTrace]
  refine ⟨16382575782737539551190237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21843434376983386068253649 16382575782737539551190237)
  ·
    refine ⟨6143465918526577331696339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16382575782737539551190237 6143465918526577331696339)
    ·
      refine ⟨9215198877789865997544509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6143465918526577331696339 9215198877789865997544509)
      ·
        refine ⟨3455699579171199749079191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9215198877789865997544509 3455699579171199749079191)
        ·
          refine ⟨5183549368756799623618787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455699579171199749079191 5183549368756799623618787)
          ·
            refine ⟨7775324053135199435428181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183549368756799623618787 7775324053135199435428181)
            ·
              refine ⟨22779269686919529595981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7775324053135199435428181 22779269686919529595981)
              ·
                rfl

theorem cell21_898340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 10].length) (baseStart_898340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898340 prefixEnd_898340 := by exact prefixLift 898340
  have htrace : WordTrace (prefixWord ++ tailWord_898340) baseStart_898340 baseEnd_898340 := by
    simpa [prefixWord, tailWord_898340, baseEnd_898340] using wordTrace_append hprefix tailTrace_898340
  have hstable : (prefixWord ++ tailWord_898340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898340).length < 2 ^ (prefixWord ++ tailWord_898340).sum := by decide
  have hdescent : baseEnd_898340 < baseStart_898340 := by decide
  rcases family_descends (prefixWord ++ tailWord_898340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898385 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_898385 : Nat := 118140960795 + 898385 * 2 ^ 59
def prefixEnd_898385 : Nat := 4983230072969 + 3 ^ 40 * 898385 * 2
def baseEnd_898385 : Nat := 205023696795365688113737

theorem tailTrace_898385 : CollatzResearch.WordTrace tailWord_898385 prefixEnd_898385 205023696795365688113737 := by
  unfold tailWord_898385
  simp only [CollatzResearch.WordTrace]
  refine ⟨32766792850312051787768609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21844528566874701191845739 32766792850312051787768609)
  ·
    refine ⟨24575094637734038840826457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32766792850312051787768609 24575094637734038840826457)
    ·
      refine ⟨18431320978300529130619843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24575094637734038840826457 18431320978300529130619843)
      ·
        refine ⟨27646981467450793695929765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18431320978300529130619843 27646981467450793695929765)
        ·
          refine ⟨5183809025147023817986831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27646981467450793695929765 5183809025147023817986831)
          ·
            refine ⟨7775713537720535726980247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183809025147023817986831 7775713537720535726980247)
            ·
              refine ⟨11663570306580803590470371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775713537720535726980247 11663570306580803590470371)
              ·
                refine ⟨17495355459871205385705557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11663570306580803590470371 17495355459871205385705557)
                ·
                  refine ⟨205023696795365688113737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17495355459871205385705557 205023696795365688113737)
                  ·
                    rfl

theorem cell21_898385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_898385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898385 prefixEnd_898385 := by exact prefixLift 898385
  have htrace : WordTrace (prefixWord ++ tailWord_898385) baseStart_898385 baseEnd_898385 := by
    simpa [prefixWord, tailWord_898385, baseEnd_898385] using wordTrace_append hprefix tailTrace_898385
  have hstable : (prefixWord ++ tailWord_898385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898385).length < 2 ^ (prefixWord ++ tailWord_898385).sum := by decide
  have hdescent : baseEnd_898385 < baseStart_898385 := by decide
  rcases family_descends (prefixWord ++ tailWord_898385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898402 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_898402 : Nat := 118140960795 + 898402 * 2 ^ 59
def prefixEnd_898402 : Nat := 4983230072969 + 3 ^ 40 * 898402 * 2
def baseEnd_898402 : Nat := 205027576426977436330369

theorem tailTrace_898402 : CollatzResearch.WordTrace tailWord_898402 prefixEnd_898402 205027576426977436330369 := by
  unfold tailWord_898402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8191853222812615922784365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21844941927500309127424973 8191853222812615922784365)
  ·
    refine ⟨3071944958554730971044137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8191853222812615922784365 3071944958554730971044137)
    ·
      refine ⟨2303958718916048228283103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3071944958554730971044137 2303958718916048228283103)
      ·
        refine ⟨3455938078374072342424655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303958718916048228283103 3455938078374072342424655)
        ·
          refine ⟨5183907117561108513636983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455938078374072342424655 5183907117561108513636983)
          ·
            refine ⟨7775860676341662770455475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183907117561108513636983 7775860676341662770455475)
            ·
              refine ⟨11663791014512494155683213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775860676341662770455475 11663791014512494155683213)
              ·
                refine ⟨4373921630442185308381205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11663791014512494155683213 4373921630442185308381205)
                ·
                  refine ⟨205027576426977436330369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4373921630442185308381205 205027576426977436330369)
                  ·
                    rfl

theorem cell21_898402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_898402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898402 prefixEnd_898402 := by exact prefixLift 898402
  have htrace : WordTrace (prefixWord ++ tailWord_898402) baseStart_898402 baseEnd_898402 := by
    simpa [prefixWord, tailWord_898402, baseEnd_898402] using wordTrace_append hprefix tailTrace_898402
  have hstable : (prefixWord ++ tailWord_898402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898402).length < 2 ^ (prefixWord ++ tailWord_898402).sum := by decide
  have hdescent : baseEnd_898402 < baseStart_898402 := by decide
  rcases family_descends (prefixWord ++ tailWord_898402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898405 : List Nat := [1, 3, 1, 3, 1, 2, 5, 2, 3]
def baseStart_898405 : Nat := 118140960795 + 898405 * 2 ^ 59
def prefixEnd_898405 : Nat := 4983230072969 + 3 ^ 40 * 898405 * 2
def baseEnd_898405 : Nat := 205028261067850097780363

theorem tailTrace_898405 : CollatzResearch.WordTrace tailWord_898405 prefixEnd_898405 205028261067850097780363 := by
  unfold tailWord_898405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32767522310239595203496669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21845014873493063468997779 32767522310239595203496669)
  ·
    refine ⟨12287820866339848201311251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32767522310239595203496669 12287820866339848201311251)
    ·
      refine ⟨18431731299509772301966877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12287820866339848201311251 18431731299509772301966877)
      ·
        refine ⟨6911899237316164613237579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18431731299509772301966877 6911899237316164613237579)
        ·
          refine ⟨10367848855974246919856369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911899237316164613237579 10367848855974246919856369)
          ·
            refine ⟨7775886641980685189892277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10367848855974246919856369 7775886641980685189892277)
            ·
              refine ⟨728989372685689236552401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7775886641980685189892277 728989372685689236552401)
              ·
                refine ⟨546742029514266927414301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728989372685689236552401 546742029514266927414301)
                ·
                  refine ⟨205028261067850097780363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546742029514266927414301 205028261067850097780363)
                  ·
                    rfl

theorem cell21_898405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_898405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898405 prefixEnd_898405 := by exact prefixLift 898405
  have htrace : WordTrace (prefixWord ++ tailWord_898405) baseStart_898405 baseEnd_898405 := by
    simpa [prefixWord, tailWord_898405, baseEnd_898405] using wordTrace_append hprefix tailTrace_898405
  have hstable : (prefixWord ++ tailWord_898405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898405).length < 2 ^ (prefixWord ++ tailWord_898405).sum := by decide
  have hdescent : baseEnd_898405 < baseStart_898405 := by decide
  rcases family_descends (prefixWord ++ tailWord_898405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898416 : List Nat := [2, 1, 1, 1, 4, 2, 4, 6]
def baseStart_898416 : Nat := 118140960795 + 898416 * 2 ^ 59
def prefixEnd_898416 : Nat := 4983230072969 + 3 ^ 40 * 898416 * 2
def baseEnd_898416 : Nat := 68343590472572174365669

theorem tailTrace_898416 : CollatzResearch.WordTrace tailWord_898416 prefixEnd_898416 68343590472572174365669 := by
  unfold tailWord_898416
  simp only [CollatzResearch.WordTrace]
  refine ⟨16383961756599872041073551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21845282342133162721431401 16383961756599872041073551)
  ·
    refine ⟨24575942634899808061610327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16383961756599872041073551 24575942634899808061610327)
    ·
      refine ⟨36863913952349712092415491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24575942634899808061610327 36863913952349712092415491)
      ·
        refine ⟨55295870928524568138623237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36863913952349712092415491 55295870928524568138623237)
        ·
          refine ⟨10367975799098356525991857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55295870928524568138623237 10367975799098356525991857)
          ·
            refine ⟨7775981849323767394493893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10367975799098356525991857 7775981849323767394493893)
            ·
              refine ⟨1457996596748206386467605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7775981849323767394493893 1457996596748206386467605)
              ·
                refine ⟨68343590472572174365669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1457996596748206386467605 68343590472572174365669)
                ·
                  rfl

theorem cell21_898416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_898416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898416 prefixEnd_898416 := by exact prefixLift 898416
  have htrace : WordTrace (prefixWord ++ tailWord_898416) baseStart_898416 baseEnd_898416 := by
    simpa [prefixWord, tailWord_898416, baseEnd_898416] using wordTrace_append hprefix tailTrace_898416
  have hstable : (prefixWord ++ tailWord_898416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898416).length < 2 ^ (prefixWord ++ tailWord_898416).sum := by decide
  have hdescent : baseEnd_898416 < baseStart_898416 := by decide
  rcases family_descends (prefixWord ++ tailWord_898416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898450 : List Nat := [3, 2, 3, 3, 2, 8]
def baseStart_898450 : Nat := 118140960795 + 898450 * 2 ^ 59
def prefixEnd_898450 : Nat := 4983230072969 + 3 ^ 40 * 898450 * 2
def baseEnd_898450 : Nat := 7594019654849630352973

theorem tailTrace_898450 : CollatzResearch.WordTrace tailWord_898450 prefixEnd_898450 7594019654849630352973 := by
  unfold tailWord_898450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192290898769141972221201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21846109063384378592589869 8192290898769141972221201)
  ·
    refine ⟨6144218174076856479165901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8192290898769141972221201 6144218174076856479165901)
    ·
      refine ⟨2304081815278821179687213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6144218174076856479165901 2304081815278821179687213)
      ·
        refine ⟨864030680729557942382705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2304081815278821179687213 864030680729557942382705)
        ·
          refine ⟨648023010547168456787029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864030680729557942382705 648023010547168456787029)
          ·
            refine ⟨7594019654849630352973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 648023010547168456787029 7594019654849630352973)
            ·
              rfl

theorem cell21_898450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 8].length) (baseStart_898450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898450 prefixEnd_898450 := by exact prefixLift 898450
  have htrace : WordTrace (prefixWord ++ tailWord_898450) baseStart_898450 baseEnd_898450 := by
    simpa [prefixWord, tailWord_898450, baseEnd_898450] using wordTrace_append hprefix tailTrace_898450
  have hstable : (prefixWord ++ tailWord_898450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898450).length < 2 ^ (prefixWord ++ tailWord_898450).sum := by decide
  have hdescent : baseEnd_898450 < baseStart_898450 := by decide
  rcases family_descends (prefixWord ++ tailWord_898450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898464 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 3]
def baseStart_898464 : Nat := 118140960795 + 898464 * 2 ^ 59
def prefixEnd_898464 : Nat := 4983230072969 + 3 ^ 40 * 898464 * 2
def baseEnd_898464 : Nat := 205041725671679106296909

theorem tailTrace_898464 : CollatzResearch.WordTrace tailWord_898464 prefixEnd_898464 205041725671679106296909 := by
  unfold tailWord_898464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16384837108512924139947223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21846449478017232186596297 16384837108512924139947223)
  ·
    refine ⟨24577255662769386209920835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16384837108512924139947223 24577255662769386209920835)
    ·
      refine ⟨36865883494154079314881253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24577255662769386209920835 36865883494154079314881253)
      ·
        refine ⟨6912353155153889871540235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36865883494154079314881253 6912353155153889871540235)
        ·
          refine ⟨10368529732730834807310353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912353155153889871540235 10368529732730834807310353)
          ·
            refine ⟨7776397299548126105482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10368529732730834807310353 7776397299548126105482765)
            ·
              refine ⟨2916148987330547289556037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7776397299548126105482765 2916148987330547289556037)
              ·
                refine ⟨546777935124477616791757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2916148987330547289556037 546777935124477616791757)
                ·
                  refine ⟨205041725671679106296909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546777935124477616791757 205041725671679106296909)
                  ·
                    rfl

theorem cell21_898464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 3].length) (baseStart_898464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898464 prefixEnd_898464 := by exact prefixLift 898464
  have htrace : WordTrace (prefixWord ++ tailWord_898464) baseStart_898464 baseEnd_898464 := by
    simpa [prefixWord, tailWord_898464, baseEnd_898464] using wordTrace_append hprefix tailTrace_898464
  have hstable : (prefixWord ++ tailWord_898464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898464).length < 2 ^ (prefixWord ++ tailWord_898464).sum := by decide
  have hdescent : baseEnd_898464 < baseStart_898464 := by decide
  rcases family_descends (prefixWord ++ tailWord_898464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898557 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 3]
def baseStart_898557 : Nat := 118140960795 + 898557 * 2 ^ 59
def prefixEnd_898557 : Nat := 4983230072969 + 3 ^ 40 * 898557 * 2
def baseEnd_898557 : Nat := 205062949538731611246719

theorem tailTrace_898557 : CollatzResearch.WordTrace tailWord_898557 prefixEnd_898557 205062949538731611246719 := by
  unfold tailWord_898557
  simp only [CollatzResearch.WordTrace]
  refine ⟨32773066205688925163029925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21848710803792616775353283 32773066205688925163029925)
  ·
    refine ⟨6144949913566673468068111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32773066205688925163029925 6144949913566673468068111)
    ·
      refine ⟨9217424870350010202102167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6144949913566673468068111 9217424870350010202102167)
      ·
        refine ⟨13826137305525015303153251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9217424870350010202102167 13826137305525015303153251)
        ·
          refine ⟨20739205958287522954729877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826137305525015303153251 20739205958287522954729877)
          ·
            refine ⟨972150279294727638502963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20739205958287522954729877 972150279294727638502963)
            ·
              refine ⟨1458225418942091457754445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972150279294727638502963 1458225418942091457754445)
              ·
                refine ⟨546834532103284296657917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458225418942091457754445 546834532103284296657917)
                ·
                  refine ⟨205062949538731611246719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546834532103284296657917 205062949538731611246719)
                  ·
                    rfl

theorem cell21_898557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_898557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898557 prefixEnd_898557 := by exact prefixLift 898557
  have htrace : WordTrace (prefixWord ++ tailWord_898557) baseStart_898557 baseEnd_898557 := by
    simpa [prefixWord, tailWord_898557, baseEnd_898557] using wordTrace_append hprefix tailTrace_898557
  have hstable : (prefixWord ++ tailWord_898557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898557).length < 2 ^ (prefixWord ++ tailWord_898557).sum := by decide
  have hdescent : baseEnd_898557 < baseStart_898557 := by decide
  rcases family_descends (prefixWord ++ tailWord_898557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898574 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_898574 : Nat := 118140960795 + 898574 * 2 ^ 59
def prefixEnd_898574 : Nat := 4983230072969 + 3 ^ 40 * 898574 * 2
def baseEnd_898574 : Nat := 205066829170343359463351

theorem tailTrace_898574 : CollatzResearch.WordTrace tailWord_898574 prefixEnd_898574 205066829170343359463351 := by
  unfold tailWord_898574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096710780828417133299847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21849124164418224710932517 4096710780828417133299847)
  ·
    refine ⟨6145066171242625699949771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096710780828417133299847 6145066171242625699949771)
    ·
      refine ⟨9217599256863938549924657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145066171242625699949771 9217599256863938549924657)
      ·
        refine ⟨6913199442647953912443493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217599256863938549924657 6913199442647953912443493)
        ·
          refine ⟨1296224895496491358583155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6913199442647953912443493 1296224895496491358583155)
          ·
            refine ⟨1944337343244737037874733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296224895496491358583155 1944337343244737037874733)
            ·
              refine ⟨729126503716776389203025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1944337343244737037874733 729126503716776389203025)
              ·
                refine ⟨546844877787582291902269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729126503716776389203025 546844877787582291902269)
                ·
                  refine ⟨205066829170343359463351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546844877787582291902269 205066829170343359463351)
                  ·
                    rfl

theorem cell21_898574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_898574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898574 prefixEnd_898574 := by exact prefixLift 898574
  have htrace : WordTrace (prefixWord ++ tailWord_898574) baseStart_898574 baseEnd_898574 := by
    simpa [prefixWord, tailWord_898574, baseEnd_898574] using wordTrace_append hprefix tailTrace_898574
  have hstable : (prefixWord ++ tailWord_898574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898574).length < 2 ^ (prefixWord ++ tailWord_898574).sum := by decide
  have hdescent : baseEnd_898574 < baseStart_898574 := by decide
  rcases family_descends (prefixWord ++ tailWord_898574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898661 : List Nat := [1, 3, 1, 3, 3, 2, 3, 5]
def baseStart_898661 : Nat := 118140960795 + 898661 * 2 ^ 59
def prefixEnd_898661 : Nat := 4983230072969 + 3 ^ 40 * 898661 * 2
def baseEnd_898661 : Nat := 68362227918550180504391

theorem tailTrace_898661 : CollatzResearch.WordTrace tailWord_898661 prefixEnd_898661 68362227918550180504391 := by
  unfold tailWord_898661
  simp only [CollatzResearch.WordTrace]
  refine ⟨32776859397312150924815837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21851239598208100616543891 32776859397312150924815837)
  ·
    refine ⟨12291322273992056596805939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32776859397312150924815837 12291322273992056596805939)
    ·
      refine ⟨18436983410988084895208909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12291322273992056596805939 18436983410988084895208909)
      ·
        refine ⟨6913868779120531835703341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18436983410988084895208909 6913868779120531835703341)
        ·
          refine ⟨2592700792170199438388753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6913868779120531835703341 2592700792170199438388753)
          ·
            refine ⟨1944525594127649578791565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592700792170199438388753 1944525594127649578791565)
            ·
              refine ⟨729197097797868592046837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1944525594127649578791565 729197097797868592046837)
              ·
                refine ⟨68362227918550180504391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 729197097797868592046837 68362227918550180504391)
                ·
                  rfl

theorem cell21_898661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 5].length) (baseStart_898661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898661 prefixEnd_898661 := by exact prefixLift 898661
  have htrace : WordTrace (prefixWord ++ tailWord_898661) baseStart_898661 baseEnd_898661 := by
    simpa [prefixWord, tailWord_898661, baseEnd_898661] using wordTrace_append hprefix tailTrace_898661
  have hstable : (prefixWord ++ tailWord_898661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898661).length < 2 ^ (prefixWord ++ tailWord_898661).sum := by decide
  have hdescent : baseEnd_898661 < baseStart_898661 := by decide
  rcases family_descends (prefixWord ++ tailWord_898661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898692 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 5]
def baseStart_898692 : Nat := 118140960795 + 898692 * 2 ^ 59
def prefixEnd_898692 : Nat := 4983230072969 + 3 ^ 40 * 898692 * 2
def baseEnd_898692 : Nat := 205093758378001376496443

theorem tailTrace_898692 : CollatzResearch.WordTrace tailWord_898692 prefixEnd_898692 205093758378001376496443 := by
  unfold tailWord_898692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16388995030099921609597165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21851993373466562146129553 16388995030099921609597165)
  ·
    refine ⟨6145873136287470603598937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16388995030099921609597165 6145873136287470603598937)
    ·
      refine ⟨4609404852215602952699203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6145873136287470603598937 4609404852215602952699203)
      ·
        refine ⟨6914107278323404429048805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4609404852215602952699203 6914107278323404429048805)
        ·
          refine ⟨1296395114685638330446651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6914107278323404429048805 1296395114685638330446651)
          ·
            refine ⟨1944592672028457495669977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296395114685638330446651 1944592672028457495669977)
            ·
              refine ⟨1458444504021343121752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944592672028457495669977 1458444504021343121752483)
              ·
                refine ⟨2187666756032014682628725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1458444504021343121752483 2187666756032014682628725)
                ·
                  refine ⟨205093758378001376496443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187666756032014682628725 205093758378001376496443)
                  ·
                    rfl

theorem cell21_898692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_898692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898692 prefixEnd_898692 := by exact prefixLift 898692
  have htrace : WordTrace (prefixWord ++ tailWord_898692) baseStart_898692 baseEnd_898692 := by
    simpa [prefixWord, tailWord_898692, baseEnd_898692] using wordTrace_append hprefix tailTrace_898692
  have hstable : (prefixWord ++ tailWord_898692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898692).length < 2 ^ (prefixWord ++ tailWord_898692).sum := by decide
  have hdescent : baseEnd_898692 < baseStart_898692 := by decide
  rcases family_descends (prefixWord ++ tailWord_898692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898720 : List Nat := [2, 1, 1, 4, 3, 2, 1, 7]
def baseStart_898720 : Nat := 118140960795 + 898720 * 2 ^ 59
def prefixEnd_898720 : Nat := 4983230072969 + 3 ^ 40 * 898720 * 2
def baseEnd_898720 : Nat := 68366716119826516676573

theorem tailTrace_898720 : CollatzResearch.WordTrace tailWord_898720 prefixEnd_898720 68366716119826516676573 := by
  unfold tailWord_898720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16389505652049202000606807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21852674202732269334142409 16389505652049202000606807)
  ·
    refine ⟨24584258478073803000910211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16389505652049202000606807 24584258478073803000910211)
    ·
      refine ⟨36876387717110704501365317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24584258478073803000910211 36876387717110704501365317)
      ·
        refine ⟨6914322696958257094005997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36876387717110704501365317 6914322696958257094005997)
        ·
          refine ⟨2592871011359346410252249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6914322696958257094005997 2592871011359346410252249)
          ·
            refine ⟨1944653258519509807689187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2592871011359346410252249 1944653258519509807689187)
            ·
              refine ⟨2916979887779264711533781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1944653258519509807689187 2916979887779264711533781)
              ·
                refine ⟨68366716119826516676573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2916979887779264711533781 68366716119826516676573)
                ·
                  rfl

theorem cell21_898720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_898720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898720 prefixEnd_898720 := by exact prefixLift 898720
  have htrace : WordTrace (prefixWord ++ tailWord_898720) baseStart_898720 baseEnd_898720 := by
    simpa [prefixWord, tailWord_898720, baseEnd_898720] using wordTrace_append hprefix tailTrace_898720
  have hstable : (prefixWord ++ tailWord_898720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898720).length < 2 ^ (prefixWord ++ tailWord_898720).sum := by decide
  have hdescent : baseEnd_898720 < baseStart_898720 := by decide
  rcases family_descends (prefixWord ++ tailWord_898720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898810 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_898810 : Nat := 118140960795 + 898810 * 2 ^ 59
def prefixEnd_898810 : Nat := 4983230072969 + 3 ^ 40 * 898810 * 2
def baseEnd_898810 : Nat := 205120687585659393529535

theorem tailTrace_898810 : CollatzResearch.WordTrace tailWord_898810 prefixEnd_898810 205120687585659393529535 := by
  unfold tailWord_898810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195573468443087342997471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21854862582514899581326589 8195573468443087342997471)
  ·
    refine ⟨12293360202664631014496207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8195573468443087342997471 12293360202664631014496207)
    ·
      refine ⟨18440040303996946521744311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12293360202664631014496207 18440040303996946521744311)
      ·
        refine ⟨27660060455995419782616467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18440040303996946521744311 27660060455995419782616467)
        ·
          refine ⟨41490090683993129673924701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27660060455995419782616467 41490090683993129673924701)
          ·
            refine ⟨15558784006497423627721763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41490090683993129673924701 15558784006497423627721763)
            ·
              refine ⟨23338176009746135441582645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15558784006497423627721763 23338176009746135441582645)
              ·
                refine ⟨2187954000913700197648373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23338176009746135441582645 2187954000913700197648373)
                ·
                  refine ⟨205120687585659393529535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2187954000913700197648373 205120687585659393529535)
                  ·
                    rfl

theorem cell21_898810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_898810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898810 prefixEnd_898810 := by exact prefixLift 898810
  have htrace : WordTrace (prefixWord ++ tailWord_898810) baseStart_898810 baseEnd_898810 := by
    simpa [prefixWord, tailWord_898810, baseEnd_898810] using wordTrace_append hprefix tailTrace_898810
  have hstable : (prefixWord ++ tailWord_898810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898810).length < 2 ^ (prefixWord ++ tailWord_898810).sum := by decide
  have hdescent : baseEnd_898810 < baseStart_898810 := by decide
  rcases family_descends (prefixWord ++ tailWord_898810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898844 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_898844 : Nat := 118140960795 + 898844 * 2 ^ 59
def prefixEnd_898844 : Nat := 4983230072969 + 3 ^ 40 * 898844 * 2
def baseEnd_898844 : Nat := 205128446848882889962799

theorem tailTrace_898844 : CollatzResearch.WordTrace tailWord_898844 prefixEnd_898844 205128446848882889962799 := by
  unfold tailWord_898844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16391766977824586589363793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21855689303766115452485057 16391766977824586589363793)
  ·
    refine ⟨12293825233368439942022845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16391766977824586589363793 12293825233368439942022845)
    ·
      refine ⟨4610184462513164978258567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12293825233368439942022845 4610184462513164978258567)
      ·
        refine ⟨6915276693769747467387851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4610184462513164978258567 6915276693769747467387851)
        ·
          refine ⟨10372915040654621201081777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915276693769747467387851 10372915040654621201081777)
          ·
            refine ⟨7779686280490965900811333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10372915040654621201081777 7779686280490965900811333)
            ·
              refine ⟨1458691177592056106402125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7779686280490965900811333 1458691177592056106402125)
              ·
                refine ⟨547009191597021039900797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1458691177592056106402125 547009191597021039900797)
                ·
                  refine ⟨205128446848882889962799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547009191597021039900797 205128446848882889962799)
                  ·
                    rfl

theorem cell21_898844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_898844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898844 prefixEnd_898844 := by exact prefixLift 898844
  have htrace : WordTrace (prefixWord ++ tailWord_898844) baseStart_898844 baseEnd_898844 := by
    simpa [prefixWord, tailWord_898844, baseEnd_898844] using wordTrace_append hprefix tailTrace_898844
  have hstable : (prefixWord ++ tailWord_898844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898844).length < 2 ^ (prefixWord ++ tailWord_898844).sum := by decide
  have hdescent : baseEnd_898844 < baseStart_898844 := by decide
  rcases family_descends (prefixWord ++ tailWord_898844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_898917 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 4]
def baseStart_898917 : Nat := 118140960795 + 898917 * 2 ^ 59
def prefixEnd_898917 : Nat := 4983230072969 + 3 ^ 40 * 898917 * 2
def baseEnd_898917 : Nat := 205145106443450985245983

theorem tailTrace_898917 : CollatzResearch.WordTrace tailWord_898917 prefixEnd_898917 205145106443450985245983 := by
  unfold tailWord_898917
  simp only [CollatzResearch.WordTrace]
  refine ⟨32786196484384706646135005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21857464322923137764090003 32786196484384706646135005)
  ·
    refine ⟨12294823681644264992300627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32786196484384706646135005 12294823681644264992300627)
    ·
      refine ⟨18442235522466397488450941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12294823681644264992300627 18442235522466397488450941)
      ·
        refine ⟨6915838320924899058169103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18442235522466397488450941 6915838320924899058169103)
        ·
          refine ⟨10373757481387348587253655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6915838320924899058169103 10373757481387348587253655)
          ·
            refine ⟨15560636222081022880880483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10373757481387348587253655 15560636222081022880880483)
            ·
              refine ⟨23340954333121534321320725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15560636222081022880880483 23340954333121534321320725)
              ·
                refine ⟨1094107234365071921311909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23340954333121534321320725 1094107234365071921311909)
                ·
                  refine ⟨205145106443450985245983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094107234365071921311909 205145106443450985245983)
                  ·
                    rfl

theorem cell21_898917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_898917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_898917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_898917 prefixEnd_898917 := by exact prefixLift 898917
  have htrace : WordTrace (prefixWord ++ tailWord_898917) baseStart_898917 baseEnd_898917 := by
    simpa [prefixWord, tailWord_898917, baseEnd_898917] using wordTrace_append hprefix tailTrace_898917
  have hstable : (prefixWord ++ tailWord_898917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_898917).length < 2 ^ (prefixWord ++ tailWord_898917).sum := by decide
  have hdescent : baseEnd_898917 < baseStart_898917 := by decide
  rcases family_descends (prefixWord ++ tailWord_898917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899100 : List Nat := [2, 2, 3, 1, 3, 2, 2, 6]
def baseStart_899100 : Nat := 118140960795 + 899100 * 2 ^ 59
def prefixEnd_899100 : Nat := 4983230072969 + 3 ^ 40 * 899100 * 2
def baseEnd_899100 : Nat := 68395623178894444565203

theorem tailTrace_899100 : CollatzResearch.WordTrace tailWord_899100 prefixEnd_899100 68395623178894444565203 := by
  unfold tailWord_899100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16396435521360864450023377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21861914028481152600031169 16396435521360864450023377)
  ·
    refine ⟨12297326641020648337517533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16396435521360864450023377 12297326641020648337517533)
    ·
      refine ⟨4611497490382743126569075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12297326641020648337517533 4611497490382743126569075)
      ·
        refine ⟨6917246235574114689853613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4611497490382743126569075 6917246235574114689853613)
        ·
          refine ⟨2593967338340293008695105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6917246235574114689853613 2593967338340293008695105)
          ·
            refine ⟨1945475503755219756521329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2593967338340293008695105 1945475503755219756521329)
            ·
              refine ⟨1459106627816414817390997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945475503755219756521329 1459106627816414817390997)
              ·
                refine ⟨68395623178894444565203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1459106627816414817390997 68395623178894444565203)
                ·
                  rfl

theorem cell21_899100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_899100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899100 prefixEnd_899100 := by exact prefixLift 899100
  have htrace : WordTrace (prefixWord ++ tailWord_899100) baseStart_899100 baseEnd_899100 := by
    simpa [prefixWord, tailWord_899100, baseEnd_899100] using wordTrace_append hprefix tailTrace_899100
  have hstable : (prefixWord ++ tailWord_899100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899100).length < 2 ^ (prefixWord ++ tailWord_899100).sum := by decide
  have hdescent : baseEnd_899100 < baseStart_899100 := by decide
  rcases family_descends (prefixWord ++ tailWord_899100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899145 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 4]
def baseStart_899145 : Nat := 118140960795 + 899145 * 2 ^ 59
def prefixEnd_899145 : Nat := 4983230072969 + 3 ^ 40 * 899145 * 2
def baseEnd_899145 : Nat := 205197139149773255445517

theorem tailTrace_899145 : CollatzResearch.WordTrace tailWord_899145 prefixEnd_899145 205197139149773255445517 := by
  unfold tailWord_899145
  simp only [CollatzResearch.WordTrace]
  refine ⟨32794512327558701585434889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21863008218372467723623259 32794512327558701585434889)
  ·
    refine ⟨24595884245669026189076167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32794512327558701585434889 24595884245669026189076167)
    ·
      refine ⟨36893826368503539283614251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24595884245669026189076167 36893826368503539283614251)
      ·
        refine ⟨55340739552755308925421377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36893826368503539283614251 55340739552755308925421377)
        ·
          refine ⟨41505554664566481694066033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55340739552755308925421377 41505554664566481694066033)
          ·
            refine ⟨31129165998424861270549525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41505554664566481694066033 31129165998424861270549525)
            ·
              refine ⟨1459179656176165372057009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31129165998424861270549525 1459179656176165372057009)
              ·
                refine ⟨1094384742132124029042757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459179656176165372057009 1094384742132124029042757)
                ·
                  refine ⟨205197139149773255445517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094384742132124029042757 205197139149773255445517)
                  ·
                    rfl

theorem cell21_899145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_899145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899145 prefixEnd_899145 := by exact prefixLift 899145
  have htrace : WordTrace (prefixWord ++ tailWord_899145) baseStart_899145 baseEnd_899145 := by
    simpa [prefixWord, tailWord_899145, baseEnd_899145] using wordTrace_append hprefix tailTrace_899145
  have hstable : (prefixWord ++ tailWord_899145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899145).length < 2 ^ (prefixWord ++ tailWord_899145).sum := by decide
  have hdescent : baseEnd_899145 < baseStart_899145 := by decide
  rcases family_descends (prefixWord ++ tailWord_899145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899148 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 3]
def baseStart_899148 : Nat := 118140960795 + 899148 * 2 ^ 59
def prefixEnd_899148 : Nat := 4983230072969 + 3 ^ 40 * 899148 * 2
def baseEnd_899148 : Nat := 205197823790645916895511

theorem tailTrace_899148 : CollatzResearch.WordTrace tailWord_899148 prefixEnd_899148 205197823790645916895511 := by
  unfold tailWord_899148
  simp only [CollatzResearch.WordTrace]
  refine ⟨16397310873273916548897049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21863081164365222065196065 16397310873273916548897049)
  ·
    refine ⟨12297983154955437411672787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16397310873273916548897049 12297983154955437411672787)
    ·
      refine ⟨18446974732433156117509181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12297983154955437411672787 18446974732433156117509181)
      ·
        refine ⟨6917615524662433544065943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18446974732433156117509181 6917615524662433544065943)
        ·
          refine ⟨10376423286993650316098915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6917615524662433544065943 10376423286993650316098915)
          ·
            refine ⟨15564634930490475474148373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376423286993650316098915 15564634930490475474148373)
            ·
              refine ⟨729592262366741037850705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15564634930490475474148373 729592262366741037850705)
              ·
                refine ⟨547194196775055778388029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729592262366741037850705 547194196775055778388029)
                ·
                  refine ⟨205197823790645916895511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547194196775055778388029 205197823790645916895511)
                  ·
                    rfl

theorem cell21_899148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_899148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899148 prefixEnd_899148 := by exact prefixLift 899148
  have htrace : WordTrace (prefixWord ++ tailWord_899148) baseStart_899148 baseEnd_899148 := by
    simpa [prefixWord, tailWord_899148, baseEnd_899148] using wordTrace_append hprefix tailTrace_899148
  have hstable : (prefixWord ++ tailWord_899148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899148).length < 2 ^ (prefixWord ++ tailWord_899148).sum := by decide
  have hdescent : baseEnd_899148 < baseStart_899148 := by decide
  rcases family_descends (prefixWord ++ tailWord_899148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899159 : List Nat := [1, 1, 3, 2, 2, 1, 5, 6]
def baseStart_899159 : Nat := 118140960795 + 899159 * 2 ^ 59
def prefixEnd_899159 : Nat := 4983230072969 + 3 ^ 40 * 899159 * 2
def baseEnd_899159 : Nat := 68400111380170780737385

theorem tailTrace_899159 : CollatzResearch.WordTrace tailWord_899159 prefixEnd_899159 68400111380170780737385 := by
  unfold tailWord_899159
  simp only [CollatzResearch.WordTrace]
  refine ⟨32795022949507981976444531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21863348633005321317629687 32795022949507981976444531)
  ·
    refine ⟨49192534424261972964666797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32795022949507981976444531 49192534424261972964666797)
    ·
      refine ⟨18447200409098239861750049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49192534424261972964666797 18447200409098239861750049)
      ·
        refine ⟨13835400306823679896312537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18447200409098239861750049 13835400306823679896312537)
        ·
          refine ⟨10376550230117759922234403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13835400306823679896312537 10376550230117759922234403)
          ·
            refine ⟨15564825345176639883351605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10376550230117759922234403 15564825345176639883351605)
            ·
              refine ⟨1459202376110309989064213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15564825345176639883351605 1459202376110309989064213)
              ·
                refine ⟨68400111380170780737385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1459202376110309989064213 68400111380170780737385)
                ·
                  rfl

theorem cell21_899159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_899159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899159 prefixEnd_899159 := by exact prefixLift 899159
  have htrace : WordTrace (prefixWord ++ tailWord_899159) baseStart_899159 baseEnd_899159 := by
    simpa [prefixWord, tailWord_899159, baseEnd_899159] using wordTrace_append hprefix tailTrace_899159
  have hstable : (prefixWord ++ tailWord_899159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899159).length < 2 ^ (prefixWord ++ tailWord_899159).sum := by decide
  have hdescent : baseEnd_899159 < baseStart_899159 := by decide
  rcases family_descends (prefixWord ++ tailWord_899159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899207 : List Nat := [1, 1, 4, 2, 1, 1, 4, 4, 3]
def baseStart_899207 : Nat := 118140960795 + 899207 * 2 ^ 59
def prefixEnd_899207 : Nat := 4983230072969 + 3 ^ 40 * 899207 * 2
def baseEnd_899207 : Nat := 205211288394474925412057

theorem tailTrace_899207 : CollatzResearch.WordTrace tailWord_899207 prefixEnd_899207 205211288394474925412057 := by
  unfold tailWord_899207
  simp only [CollatzResearch.WordTrace]
  refine ⟨32796773653334086174191875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21864515768889390782794583 32796773653334086174191875)
  ·
    refine ⟨49195160480001129261287813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32796773653334086174191875 49195160480001129261287813)
    ·
      refine ⟨9224092590000211736491465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49195160480001129261287813 9224092590000211736491465)
      ·
        refine ⟨6918069442500158802368599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9224092590000211736491465 6918069442500158802368599)
        ·
          refine ⟨10377104163750238203552899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6918069442500158802368599 10377104163750238203552899)
          ·
            refine ⟨15565656245625357305329349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10377104163750238203552899 15565656245625357305329349)
            ·
              refine ⟨2918560546054754494749253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15565656245625357305329349 2918560546054754494749253)
              ·
                refine ⟨547230102385266467765485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2918560546054754494749253 547230102385266467765485)
                ·
                  refine ⟨205211288394474925412057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547230102385266467765485 205211288394474925412057)
                  ·
                    rfl

theorem cell21_899207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 3].length) (baseStart_899207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899207 prefixEnd_899207 := by exact prefixLift 899207
  have htrace : WordTrace (prefixWord ++ tailWord_899207) baseStart_899207 baseEnd_899207 := by
    simpa [prefixWord, tailWord_899207, baseEnd_899207] using wordTrace_append hprefix tailTrace_899207
  have hstable : (prefixWord ++ tailWord_899207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899207).length < 2 ^ (prefixWord ++ tailWord_899207).sum := by decide
  have hdescent : baseEnd_899207 < baseStart_899207 := by decide
  rcases family_descends (prefixWord ++ tailWord_899207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899314 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_899314 : Nat := 118140960795 + 899314 * 2 ^ 59
def prefixEnd_899314 : Nat := 4983230072969 + 3 ^ 40 * 899314 * 2
def baseEnd_899314 : Nat := 205235707252266517128505

theorem tailTrace_899314 : CollatzResearch.WordTrace tailWord_899314 prefixEnd_899314 205235707252266517128505 := by
  unfold tailWord_899314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8200169065986610862084249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21867117509297628965557997 8200169065986610862084249)
  ·
    refine ⟨6150126799489958146563187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8200169065986610862084249 6150126799489958146563187)
    ·
      refine ⟨9225190199234937219844781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150126799489958146563187 9225190199234937219844781)
      ·
        refine ⟨3459446324713101457441793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9225190199234937219844781 3459446324713101457441793)
        ·
          refine ⟨2594584743534826093081345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3459446324713101457441793 2594584743534826093081345)
          ·
            refine ⟨1945938557651119569811009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2594584743534826093081345 1945938557651119569811009)
            ·
              refine ⟨1459453918238339677358257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1945938557651119569811009 1459453918238339677358257)
              ·
                refine ⟨1094590438678754758018693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459453918238339677358257 1094590438678754758018693)
                ·
                  refine ⟨205235707252266517128505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1094590438678754758018693 205235707252266517128505)
                  ·
                    rfl

theorem cell21_899314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_899314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899314 prefixEnd_899314 := by exact prefixLift 899314
  have htrace : WordTrace (prefixWord ++ tailWord_899314) baseStart_899314 baseEnd_899314 := by
    simpa [prefixWord, tailWord_899314, baseEnd_899314] using wordTrace_append hprefix tailTrace_899314
  have hstable : (prefixWord ++ tailWord_899314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899314).length < 2 ^ (prefixWord ++ tailWord_899314).sum := by decide
  have hdescent : baseEnd_899314 < baseStart_899314 := by decide
  rcases family_descends (prefixWord ++ tailWord_899314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899325 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 9]
def baseStart_899325 : Nat := 118140960795 + 899325 * 2 ^ 59
def prefixEnd_899325 : Nat := 4983230072969 + 3 ^ 40 * 899325 * 2
def baseEnd_899325 : Nat := 205238217602132942445149

theorem tailTrace_899325 : CollatzResearch.WordTrace tailWord_899325 prefixEnd_899325 205238217602132942445149 := by
  unfold tailWord_899325
  simp only [CollatzResearch.WordTrace]
  refine ⟨32801077466906592326987429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21867384977937728217991619 32801077466906592326987429)
  ·
    refine ⟨6150202025044986061310143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32801077466906592326987429 6150202025044986061310143)
    ·
      refine ⟨9225303037567479091965215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150202025044986061310143 9225303037567479091965215)
      ·
        refine ⟨13837954556351218637947823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9225303037567479091965215 13837954556351218637947823)
        ·
          refine ⟨20756931834526827956921735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13837954556351218637947823 20756931834526827956921735)
          ·
            refine ⟨31135397751790241935382603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20756931834526827956921735 31135397751790241935382603)
            ·
              refine ⟨46703096627685362903073905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31135397751790241935382603 46703096627685362903073905)
              ·
                refine ⟨35027322470764022177305429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46703096627685362903073905 35027322470764022177305429)
                ·
                  refine ⟨205238217602132942445149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35027322470764022177305429 205238217602132942445149)
                  ·
                    rfl

theorem cell21_899325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_899325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899325 prefixEnd_899325 := by exact prefixLift 899325
  have htrace : WordTrace (prefixWord ++ tailWord_899325) baseStart_899325 baseEnd_899325 := by
    simpa [prefixWord, tailWord_899325, baseEnd_899325] using wordTrace_append hprefix tailTrace_899325
  have hstable : (prefixWord ++ tailWord_899325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899325).length < 2 ^ (prefixWord ++ tailWord_899325).sum := by decide
  have hdescent : baseEnd_899325 < baseStart_899325 := by decide
  rcases family_descends (prefixWord ++ tailWord_899325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899342 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_899342 : Nat := 118140960795 + 899342 * 2 ^ 59
def prefixEnd_899342 : Nat := 4983230072969 + 3 ^ 40 * 899342 * 2
def baseEnd_899342 : Nat := 205242097233744690661781

theorem tailTrace_899342 : CollatzResearch.WordTrace tailWord_899342 prefixEnd_899342 205242097233744690661781 := by
  unfold tailWord_899342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100212188480625528794535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21867798338563336153570853 4100212188480625528794535)
  ·
    refine ⟨6150318282720938293191803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4100212188480625528794535 6150318282720938293191803)
    ·
      refine ⟨9225477424081407439787705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6150318282720938293191803 9225477424081407439787705)
      ·
        refine ⟨6919108068061055579840779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9225477424081407439787705 6919108068061055579840779)
        ·
          refine ⟨10378662102091583369761169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919108068061055579840779 10378662102091583369761169)
          ·
            refine ⟨7783996576568687527320877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10378662102091583369761169 7783996576568687527320877)
            ·
              refine ⟨2918998716213257822745329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7783996576568687527320877 2918998716213257822745329)
              ·
                refine ⟨2189249037159943367058997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2918998716213257822745329 2189249037159943367058997)
                ·
                  refine ⟨205242097233744690661781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2189249037159943367058997 205242097233744690661781)
                  ·
                    rfl

theorem cell21_899342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_899342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899342 prefixEnd_899342 := by exact prefixLift 899342
  have htrace : WordTrace (prefixWord ++ tailWord_899342) baseStart_899342 baseEnd_899342 := by
    simpa [prefixWord, tailWord_899342, baseEnd_899342] using wordTrace_append hprefix tailTrace_899342
  have hstable : (prefixWord ++ tailWord_899342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899342).length < 2 ^ (prefixWord ++ tailWord_899342).sum := by decide
  have hdescent : baseEnd_899342 < baseStart_899342 := by decide
  rcases family_descends (prefixWord ++ tailWord_899342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899356 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_899356 : Nat := 118140960795 + 899356 * 2 ^ 59
def prefixEnd_899356 : Nat := 4983230072969 + 3 ^ 40 * 899356 * 2
def baseEnd_899356 : Nat := 205245292224483777428419

theorem tailTrace_899356 : CollatzResearch.WordTrace tailWord_899356 prefixEnd_899356 205245292224483777428419 := by
  unfold tailWord_899356
  simp only [CollatzResearch.WordTrace]
  refine ⟨16401104064897142310682961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21868138753196189747577281 16401104064897142310682961)
  ·
    refine ⟨12300828048672856733012221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16401104064897142310682961 12300828048672856733012221)
    ·
      refine ⟨4612810518252321274879583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12300828048672856733012221 4612810518252321274879583)
      ·
        refine ⟨6919215777378481912319375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4612810518252321274879583 6919215777378481912319375)
        ·
          refine ⟨10378823666067722868479063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6919215777378481912319375 10378823666067722868479063)
          ·
            refine ⟨15568235499101584302718595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10378823666067722868479063 15568235499101584302718595)
            ·
              refine ⟨23352353248652376454077893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15568235499101584302718595 23352353248652376454077893)
              ·
                refine ⟨4378566234122320585139605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23352353248652376454077893 4378566234122320585139605)
                ·
                  refine ⟨205245292224483777428419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4378566234122320585139605 205245292224483777428419)
                  ·
                    rfl

theorem cell21_899356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_899356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899356 prefixEnd_899356 := by exact prefixLift 899356
  have htrace : WordTrace (prefixWord ++ tailWord_899356) baseStart_899356 baseEnd_899356 := by
    simpa [prefixWord, tailWord_899356, baseEnd_899356] using wordTrace_append hprefix tailTrace_899356
  have hstable : (prefixWord ++ tailWord_899356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899356).length < 2 ^ (prefixWord ++ tailWord_899356).sum := by decide
  have hdescent : baseEnd_899356 < baseStart_899356 := by decide
  rcases family_descends (prefixWord ++ tailWord_899356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899359 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 3]
def baseStart_899359 : Nat := 118140960795 + 899359 * 2 ^ 59
def prefixEnd_899359 : Nat := 4983230072969 + 3 ^ 40 * 899359 * 2
def baseEnd_899359 : Nat := 205245976865356438878413

theorem tailTrace_899359 : CollatzResearch.WordTrace tailWord_899359 prefixEnd_899359 205245976865356438878413 := by
  unfold tailWord_899359
  simp only [CollatzResearch.WordTrace]
  refine ⟨32802317548783416133725131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21868211699188944089150087 32802317548783416133725131)
  ·
    refine ⟨49203476323175124200587697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32802317548783416133725131 49203476323175124200587697)
    ·
      refine ⟨36902607242381343150440773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49203476323175124200587697 36902607242381343150440773)
      ·
        refine ⟨6919238857946501840707645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36902607242381343150440773 6919238857946501840707645)
        ·
          refine ⟨2594714571729938190265367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6919238857946501840707645 2594714571729938190265367)
          ·
            refine ⟨3892071857594907285398051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2594714571729938190265367 3892071857594907285398051)
            ·
              refine ⟨5838107786392360928097077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892071857594907285398051 5838107786392360928097077)
              ·
                refine ⟨547322604974283837009101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5838107786392360928097077 547322604974283837009101)
                ·
                  refine ⟨205245976865356438878413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547322604974283837009101 205245976865356438878413)
                  ·
                    rfl

theorem cell21_899359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 3].length) (baseStart_899359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899359 prefixEnd_899359 := by exact prefixLift 899359
  have htrace : WordTrace (prefixWord ++ tailWord_899359) baseStart_899359 baseEnd_899359 := by
    simpa [prefixWord, tailWord_899359, baseEnd_899359] using wordTrace_append hprefix tailTrace_899359
  have hstable : (prefixWord ++ tailWord_899359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899359).length < 2 ^ (prefixWord ++ tailWord_899359).sum := by decide
  have hdescent : baseEnd_899359 < baseStart_899359 := by decide
  rcases family_descends (prefixWord ++ tailWord_899359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899486 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_899486 : Nat := 118140960795 + 899486 * 2 ^ 59
def prefixEnd_899486 : Nat := 4983230072969 + 3 ^ 40 * 899486 * 2
def baseEnd_899486 : Nat := 205274959995632440261487

theorem tailTrace_899486 : CollatzResearch.WordTrace tailWord_899486 prefixEnd_899486 205274959995632440261487 := by
  unfold tailWord_899486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4100868702415414602949789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21871299746215544549065541 4100868702415414602949789)
  ·
    refine ⟨1537825763405780476106171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4100868702415414602949789 1537825763405780476106171)
    ·
      refine ⟨2306738645108670714159257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537825763405780476106171 2306738645108670714159257)
      ·
        refine ⟨1730053983831503035619443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2306738645108670714159257 1730053983831503035619443)
        ·
          refine ⟨2595080975747254553429165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730053983831503035619443 2595080975747254553429165)
          ·
            refine ⟨973155365905220457535937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2595080975747254553429165 973155365905220457535937)
            ·
              refine ⟨729866524428915343151953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973155365905220457535937 729866524428915343151953)
              ·
                refine ⟨547399893321686507363965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729866524428915343151953 547399893321686507363965)
                ·
                  refine ⟨205274959995632440261487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547399893321686507363965 205274959995632440261487)
                  ·
                    rfl

theorem cell21_899486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_899486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899486 prefixEnd_899486 := by exact prefixLift 899486
  have htrace : WordTrace (prefixWord ++ tailWord_899486) baseStart_899486 baseEnd_899486 := by
    simpa [prefixWord, tailWord_899486, baseEnd_899486] using wordTrace_append hprefix tailTrace_899486
  have hstable : (prefixWord ++ tailWord_899486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899486).length < 2 ^ (prefixWord ++ tailWord_899486).sum := by decide
  have hdescent : baseEnd_899486 < baseStart_899486 := by decide
  rcases family_descends (prefixWord ++ tailWord_899486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899590 : List Nat := [6, 2, 1, 1, 1, 3, 7]
def baseStart_899590 : Nat := 118140960795 + 899590 * 2 ^ 59
def prefixEnd_899590 : Nat := 4983230072969 + 3 ^ 40 * 899590 * 2
def baseEnd_899590 : Nat := 22810966023616818947549

theorem tailTrace_899590 : CollatzResearch.WordTrace tailWord_899590 prefixEnd_899590 22810966023616818947549 := by
  unfold tailWord_899590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025335712842079455793257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21873828540631028390256149 1025335712842079455793257)
  ·
    refine ⟨769001784631559591844943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1025335712842079455793257 769001784631559591844943)
    ·
      refine ⟨1153502676947339387767415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769001784631559591844943 1153502676947339387767415)
      ·
        refine ⟨1730254015421009081651123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153502676947339387767415 1730254015421009081651123)
        ·
          refine ⟨2595381023131513622476685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730254015421009081651123 2595381023131513622476685)
          ·
            refine ⟨973267883674317608428757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2595381023131513622476685 973267883674317608428757)
            ·
              refine ⟨22810966023616818947549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 973267883674317608428757 22810966023616818947549)
              ·
                rfl

theorem cell21_899590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 7].length) (baseStart_899590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899590 prefixEnd_899590 := by exact prefixLift 899590
  have htrace : WordTrace (prefixWord ++ tailWord_899590) baseStart_899590 baseEnd_899590 := by
    simpa [prefixWord, tailWord_899590, baseEnd_899590] using wordTrace_append hprefix tailTrace_899590
  have hstable : (prefixWord ++ tailWord_899590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899590).length < 2 ^ (prefixWord ++ tailWord_899590).sum := by decide
  have hdescent : baseEnd_899590 < baseStart_899590 := by decide
  rcases family_descends (prefixWord ++ tailWord_899590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899604 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_899604 : Nat := 118140960795 + 899604 * 2 ^ 59
def prefixEnd_899604 : Nat := 4983230072969 + 3 ^ 40 * 899604 * 2
def baseEnd_899604 : Nat := 205301889203290457294579

theorem tailTrace_899604 : CollatzResearch.WordTrace tailWord_899604 prefixEnd_899604 205301889203290457294579 := by
  unfold tailWord_899604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16405626716447911488196933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21874168955263881984262577 16405626716447911488196933)
  ·
    refine ⟨3076055009333983404036925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16405626716447911488196933 3076055009333983404036925)
    ·
      refine ⟨1153520628500243776513847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3076055009333983404036925 1153520628500243776513847)
      ·
        refine ⟨1730280942750365664770771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153520628500243776513847 1730280942750365664770771)
        ·
          refine ⟨2595421414125548497156157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730280942750365664770771 2595421414125548497156157)
          ·
            refine ⟨973283030297080686433559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2595421414125548497156157 973283030297080686433559)
            ·
              refine ⟨1459924545445621029650339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973283030297080686433559 1459924545445621029650339)
              ·
                refine ⟨2189886818168431544475509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1459924545445621029650339 2189886818168431544475509)
                ·
                  refine ⟨205301889203290457294579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2189886818168431544475509 205301889203290457294579)
                  ·
                    rfl

theorem cell21_899604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_899604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899604 prefixEnd_899604 := by exact prefixLift 899604
  have htrace : WordTrace (prefixWord ++ tailWord_899604) baseStart_899604 baseEnd_899604 := by
    simpa [prefixWord, tailWord_899604, baseEnd_899604] using wordTrace_append hprefix tailTrace_899604
  have hstable : (prefixWord ++ tailWord_899604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899604).length < 2 ^ (prefixWord ++ tailWord_899604).sum := by decide
  have hdescent : baseEnd_899604 < baseStart_899604 := by decide
  rcases family_descends (prefixWord ++ tailWord_899604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899652 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 4]
def baseStart_899652 : Nat := 118140960795 + 899652 * 2 ^ 59
def prefixEnd_899652 : Nat := 4983230072969 + 3 ^ 40 * 899652 * 2
def baseEnd_899652 : Nat := 205312843457253040494481

theorem tailTrace_899652 : CollatzResearch.WordTrace tailWord_899652 prefixEnd_899652 205312843457253040494481 := by
  unfold tailWord_899652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16406502068360963587070605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21875336091147951449427473 16406502068360963587070605)
  ·
    refine ⟨6152438275635361345151477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16406502068360963587070605 6152438275635361345151477)
    ·
      refine ⟨576791088340815126107951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6152438275635361345151477 576791088340815126107951)
      ·
        refine ⟨865186632511222689161927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576791088340815126107951 865186632511222689161927)
        ·
          refine ⟨1297779948766834033742891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865186632511222689161927 1297779948766834033742891)
          ·
            refine ⟨1946669923150251050614337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1297779948766834033742891 1946669923150251050614337)
            ·
              refine ⟨1460002442362688287960753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1946669923150251050614337 1460002442362688287960753)
              ·
                refine ⟨1095001831772016215970565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460002442362688287960753 1095001831772016215970565)
                ·
                  refine ⟨205312843457253040494481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095001831772016215970565 205312843457253040494481)
                  ·
                    rfl

theorem cell21_899652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_899652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899652 prefixEnd_899652 := by exact prefixLift 899652
  have htrace : WordTrace (prefixWord ++ tailWord_899652) baseStart_899652 baseEnd_899652 := by
    simpa [prefixWord, tailWord_899652, baseEnd_899652] using wordTrace_append hprefix tailTrace_899652
  have hstable : (prefixWord ++ tailWord_899652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899652).length < 2 ^ (prefixWord ++ tailWord_899652).sum := by decide
  have hdescent : baseEnd_899652 < baseStart_899652 := by decide
  rcases family_descends (prefixWord ++ tailWord_899652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899663 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 3]
def baseStart_899663 : Nat := 118140960795 + 899663 * 2 ^ 59
def prefixEnd_899663 : Nat := 4983230072969 + 3 ^ 40 * 899663 * 2
def baseEnd_899663 : Nat := 205315353807119465811125

theorem tailTrace_899663 : CollatzResearch.WordTrace tailWord_899663 prefixEnd_899663 205315353807119465811125 := by
  unfold tailWord_899663
  simp only [CollatzResearch.WordTrace]
  refine ⟨32813405339682076052791643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21875603559788050701861095 32813405339682076052791643)
  ·
    refine ⟨49220108009523114079187465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32813405339682076052791643 49220108009523114079187465)
    ·
      refine ⟨36915081007142335559390599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49220108009523114079187465 36915081007142335559390599)
      ·
        refine ⟨55372621510713503339085899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36915081007142335559390599 55372621510713503339085899)
        ·
          refine ⟨83058932266070255008628849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55372621510713503339085899 83058932266070255008628849)
          ·
            refine ⟨62294199199552691256471637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83058932266070255008628849 62294199199552691256471637)
            ·
              refine ⟨730010146869758100661777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 62294199199552691256471637 730010146869758100661777)
              ·
                refine ⟨547507610152318575496333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730010146869758100661777 547507610152318575496333)
                ·
                  refine ⟨205315353807119465811125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547507610152318575496333 205315353807119465811125)
                  ·
                    rfl

theorem cell21_899663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 3].length) (baseStart_899663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899663 prefixEnd_899663 := by exact prefixLift 899663
  have htrace : WordTrace (prefixWord ++ tailWord_899663) baseStart_899663 baseEnd_899663 := by
    simpa [prefixWord, tailWord_899663, baseEnd_899663] using wordTrace_append hprefix tailTrace_899663
  have hstable : (prefixWord ++ tailWord_899663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899663).length < 2 ^ (prefixWord ++ tailWord_899663).sum := by decide
  have hdescent : baseEnd_899663 < baseStart_899663 := by decide
  rcases family_descends (prefixWord ++ tailWord_899663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899767 : List Nat := [1, 1, 3, 1, 6, 2, 7]
def baseStart_899767 : Nat := 118140960795 + 899767 * 2 ^ 59
def prefixEnd_899767 : Nat := 4983230072969 + 3 ^ 40 * 899767 * 2
def baseEnd_899767 : Nat := 22815454224893155119731

theorem tailTrace_899767 : CollatzResearch.WordTrace tailWord_899767 prefixEnd_899767 22815454224893155119731 := by
  unfold tailWord_899767
  simp only [CollatzResearch.WordTrace]
  refine ⟨32817198531305301814577555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21878132354203534543051703 32817198531305301814577555)
  ·
    refine ⟨49225797796957952721866333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32817198531305301814577555 49225797796957952721866333)
    ·
      refine ⟨18459674173859232270699875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49225797796957952721866333 18459674173859232270699875)
      ·
        refine ⟨27689511260788848406049813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18459674173859232270699875 27689511260788848406049813)
        ·
          refine ⟨1297945840349477269033585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27689511260788848406049813 1297945840349477269033585)
          ·
            refine ⟨973459380262107951775189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297945840349477269033585 973459380262107951775189)
            ·
              refine ⟨22815454224893155119731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 973459380262107951775189 22815454224893155119731)
              ·
                rfl

theorem cell21_899767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 7].length) (baseStart_899767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899767 prefixEnd_899767 := by exact prefixLift 899767
  have htrace : WordTrace (prefixWord ++ tailWord_899767) baseStart_899767 baseEnd_899767 := by
    simpa [prefixWord, tailWord_899767, baseEnd_899767] using wordTrace_append hprefix tailTrace_899767
  have hstable : (prefixWord ++ tailWord_899767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899767).length < 2 ^ (prefixWord ++ tailWord_899767).sum := by decide
  have hdescent : baseEnd_899767 < baseStart_899767 := by decide
  rcases family_descends (prefixWord ++ tailWord_899767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899826 : List Nat := [3, 2, 1, 3, 1, 11]
def baseStart_899826 : Nat := 118140960795 + 899826 * 2 ^ 59
def prefixEnd_899826 : Nat := 4983230072969 + 3 ^ 40 * 899826 * 2
def baseEnd_899826 : Nat := 7605650097328422392375

theorem tailTrace_899826 : CollatzResearch.WordTrace tailWord_899826 prefixEnd_899826 7605650097328422392375 := by
  unfold tailWord_899826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8204837609522888722743833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21879566958727703260650221 8204837609522888722743833)
  ·
    refine ⟨6153628207142166542057875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8204837609522888722743833 6153628207142166542057875)
    ·
      refine ⟨9230442310713249813086813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6153628207142166542057875 9230442310713249813086813)
      ·
        refine ⟨3461415866517468679907555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9230442310713249813086813 3461415866517468679907555)
        ·
          refine ⟨5192123799776203019861333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3461415866517468679907555 5192123799776203019861333)
          ·
            refine ⟨7605650097328422392375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5192123799776203019861333 7605650097328422392375)
            ·
              rfl

theorem cell21_899826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 11].length) (baseStart_899826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899826 prefixEnd_899826 := by exact prefixLift 899826
  have htrace : WordTrace (prefixWord ++ tailWord_899826) baseStart_899826 baseEnd_899826 := by
    simpa [prefixWord, tailWord_899826, baseEnd_899826] using wordTrace_append hprefix tailTrace_899826
  have hstable : (prefixWord ++ tailWord_899826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899826).length < 2 ^ (prefixWord ++ tailWord_899826).sum := by decide
  have hdescent : baseEnd_899826 < baseStart_899826 := by decide
  rcases family_descends (prefixWord ++ tailWord_899826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_899947 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 6]
def baseStart_899947 : Nat := 118140960795 + 899947 * 2 ^ 59
def prefixEnd_899947 : Nat := 4983230072969 + 3 ^ 40 * 899947 * 2
def baseEnd_899947 : Nat := 205380166476398083077211

theorem tailTrace_899947 : CollatzResearch.WordTrace tailWord_899947 prefixEnd_899947 205380166476398083077211 := by
  unfold tailWord_899947
  simp only [CollatzResearch.WordTrace]
  refine ⟨32823763670653192556130095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21882509113768795037420063 32823763670653192556130095)
  ·
    refine ⟨49235645505979788834195143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32823763670653192556130095 49235645505979788834195143)
    ·
      refine ⟨73853468258969683251292715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49235645505979788834195143 73853468258969683251292715)
      ·
        refine ⟨110780202388454524876939073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73853468258969683251292715 110780202388454524876939073)
        ·
          refine ⟨83085151791340893657704305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110780202388454524876939073 83085151791340893657704305)
          ·
            refine ⟨62313863843505670243278229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83085151791340893657704305 62313863843505670243278229)
            ·
              refine ⟨2920962367664328292653667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62313863843505670243278229 2920962367664328292653667)
              ·
                refine ⟨4381443551496492438980501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2920962367664328292653667 4381443551496492438980501)
                ·
                  refine ⟨205380166476398083077211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4381443551496492438980501 205380166476398083077211)
                  ·
                    rfl

theorem cell21_899947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_899947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_899947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_899947 prefixEnd_899947 := by exact prefixLift 899947
  have htrace : WordTrace (prefixWord ++ tailWord_899947) baseStart_899947 baseEnd_899947 := by
    simpa [prefixWord, tailWord_899947, baseEnd_899947] using wordTrace_append hprefix tailTrace_899947
  have hstable : (prefixWord ++ tailWord_899947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_899947).length < 2 ^ (prefixWord ++ tailWord_899947).sum := by decide
  have hdescent : baseEnd_899947 < baseStart_899947 := by decide
  rcases family_descends (prefixWord ++ tailWord_899947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900057 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 4]
def baseStart_900057 : Nat := 118140960795 + 900057 * 2 ^ 59
def prefixEnd_900057 : Nat := 4983230072969 + 3 ^ 40 * 900057 * 2
def baseEnd_900057 : Nat := 205405269975062336243653

theorem tailTrace_900057 : CollatzResearch.WordTrace tailWord_900057 prefixEnd_900057 205405269975062336243653 := by
  unfold tailWord_900057
  simp only [CollatzResearch.WordTrace]
  refine ⟨32827775700254681342634425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21885183800169787561756283 32827775700254681342634425)
  ·
    refine ⟨24620831775191011006975819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32827775700254681342634425 24620831775191011006975819)
    ·
      refine ⟨36931247662786516510463729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24620831775191011006975819 36931247662786516510463729)
      ·
        refine ⟨27698435747089887382847797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36931247662786516510463729 27698435747089887382847797)
        ·
          refine ⟨2596728351289676942141981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27698435747089887382847797 2596728351289676942141981)
          ·
            refine ⟨973773131733628853303243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2596728351289676942141981 973773131733628853303243)
            ·
              refine ⟨1460659697600443279954865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973773131733628853303243 1460659697600443279954865)
              ·
                refine ⟨1095494773200332459966149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1460659697600443279954865 1095494773200332459966149)
                ·
                  refine ⟨205405269975062336243653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095494773200332459966149 205405269975062336243653)
                  ·
                    rfl

theorem cell21_900057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_900057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900057 prefixEnd_900057 := by exact prefixLift 900057
  have htrace : WordTrace (prefixWord ++ tailWord_900057) baseStart_900057 baseEnd_900057 := by
    simpa [prefixWord, tailWord_900057, baseEnd_900057] using wordTrace_append hprefix tailTrace_900057
  have hstable : (prefixWord ++ tailWord_900057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900057).length < 2 ^ (prefixWord ++ tailWord_900057).sum := by decide
  have hdescent : baseEnd_900057 < baseStart_900057 := by decide
  rcases family_descends (prefixWord ++ tailWord_900057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900130 : List Nat := [3, 3, 1, 1, 1, 3, 1, 8]
def baseStart_900130 : Nat := 118140960795 + 900130 * 2 ^ 59
def prefixEnd_900130 : Nat := 4983230072969 + 3 ^ 40 * 900130 * 2
def baseEnd_900130 : Nat := 68473976523210143842279

theorem tailTrace_900130 : CollatzResearch.WordTrace tailWord_900130 prefixEnd_900130 68473976523210143842279 := by
  unfold tailWord_900130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207609557247553702510461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21886958819326809873361229 8207609557247553702510461)
  ·
    refine ⟨3077853583967832638441423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8207609557247553702510461 3077853583967832638441423)
    ·
      refine ⟨4616780375951748957662135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077853583967832638441423 4616780375951748957662135)
      ·
        refine ⟨6925170563927623436493203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4616780375951748957662135 6925170563927623436493203)
        ·
          refine ⟨10387755845891435154739805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6925170563927623436493203 10387755845891435154739805)
          ·
            refine ⟨3895408442209288183027427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10387755845891435154739805 3895408442209288183027427)
            ·
              refine ⟨5843112663313932274541141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3895408442209288183027427 5843112663313932274541141)
              ·
                refine ⟨68473976523210143842279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5843112663313932274541141 68473976523210143842279)
                ·
                  rfl

theorem cell21_900130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_900130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900130 prefixEnd_900130 := by exact prefixLift 900130
  have htrace : WordTrace (prefixWord ++ tailWord_900130) baseStart_900130 baseEnd_900130 := by
    simpa [prefixWord, tailWord_900130, baseEnd_900130] using wordTrace_append hprefix tailTrace_900130
  have hstable : (prefixWord ++ tailWord_900130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900130).length < 2 ^ (prefixWord ++ tailWord_900130).sum := by decide
  have hdescent : baseEnd_900130 < baseStart_900130 := by decide
  rcases family_descends (prefixWord ++ tailWord_900130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900144 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_900144 : Nat := 118140960795 + 900144 * 2 ^ 59
def prefixEnd_900144 : Nat := 4983230072969 + 3 ^ 40 * 900144 * 2
def baseEnd_900144 : Nat := 205425124560369518293475

theorem tailTrace_900144 : CollatzResearch.WordTrace tailWord_900144 prefixEnd_900144 205425124560369518293475 := by
  unfold tailWord_900144
  simp only [CollatzResearch.WordTrace]
  refine ⟨16415474425469747600525743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21887299233959663467367657 16415474425469747600525743)
  ·
    refine ⟨24623211638204621400788615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16415474425469747600525743 24623211638204621400788615)
    ·
      refine ⟨36934817457306932101182923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24623211638204621400788615 36934817457306932101182923)
      ·
        refine ⟨55402226185960398151774385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36934817457306932101182923 55402226185960398151774385)
        ·
          refine ⟨41551669639470298613830789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55402226185960398151774385 41551669639470298613830789)
          ·
            refine ⟨7790938057400680990093273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41551669639470298613830789 7790938057400680990093273)
            ·
              refine ⟨5843203543050510742569955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7790938057400680990093273 5843203543050510742569955)
              ·
                refine ⟨8764805314575766113854933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5843203543050510742569955 8764805314575766113854933)
                ·
                  refine ⟨205425124560369518293475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8764805314575766113854933 205425124560369518293475)
                  ·
                    rfl

theorem cell21_900144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_900144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900144 prefixEnd_900144 := by exact prefixLift 900144
  have htrace : WordTrace (prefixWord ++ tailWord_900144) baseStart_900144 baseEnd_900144 := by
    simpa [prefixWord, tailWord_900144, baseEnd_900144] using wordTrace_append hprefix tailTrace_900144
  have hstable : (prefixWord ++ tailWord_900144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900144).length < 2 ^ (prefixWord ++ tailWord_900144).sum := by decide
  have hdescent : baseEnd_900144 < baseStart_900144 := by decide
  rcases family_descends (prefixWord ++ tailWord_900144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900220 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_900220 : Nat := 118140960795 + 900220 * 2 ^ 59
def prefixEnd_900220 : Nat := 4983230072969 + 3 ^ 40 * 900220 * 2
def baseEnd_900220 : Nat := 205442468795810275026653

theorem tailTrace_900220 : CollatzResearch.WordTrace tailWord_900220 prefixEnd_900220 205442468795810275026653 := by
  unfold tailWord_900220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16416860399332080090409057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21889147199109440120545409 16416860399332080090409057)
  ·
    refine ⟨12312645299499060067806793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16416860399332080090409057 12312645299499060067806793)
    ·
      refine ⟨9234483974624295050855095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12312645299499060067806793 9234483974624295050855095)
      ·
        refine ⟨13851725961936442576282643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9234483974624295050855095 13851725961936442576282643)
        ·
          refine ⟨20777588942904663864423965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13851725961936442576282643 20777588942904663864423965)
          ·
            refine ⟨7791595853589248949158987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20777588942904663864423965 7791595853589248949158987)
            ·
              refine ⟨11687393780383873423738481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7791595853589248949158987 11687393780383873423738481)
              ·
                refine ⟨8765545335287905067803861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11687393780383873423738481 8765545335287905067803861)
                ·
                  refine ⟨205442468795810275026653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8765545335287905067803861 205442468795810275026653)
                  ·
                    rfl

theorem cell21_900220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_900220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900220 prefixEnd_900220 := by exact prefixLift 900220
  have htrace : WordTrace (prefixWord ++ tailWord_900220) baseStart_900220 baseEnd_900220 := by
    simpa [prefixWord, tailWord_900220, baseEnd_900220] using wordTrace_append hprefix tailTrace_900220
  have hstable : (prefixWord ++ tailWord_900220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900220).length < 2 ^ (prefixWord ++ tailWord_900220).sum := by decide
  have hdescent : baseEnd_900220 < baseStart_900220 := by decide
  rcases family_descends (prefixWord ++ tailWord_900220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900254 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_900254 : Nat := 118140960795 + 900254 * 2 ^ 59
def prefixEnd_900254 : Nat := 4983230072969 + 3 ^ 40 * 900254 * 2
def baseEnd_900254 : Nat := 205450228059033771459917

theorem tailTrace_900254 : CollatzResearch.WordTrace tailWord_900254 prefixEnd_900254 205450228059033771459917 := by
  unfold tailWord_900254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104370110067622998444477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21889973920360655991703877 4104370110067622998444477)
  ·
    refine ⟨1539138791275358624416679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4104370110067622998444477 1539138791275358624416679)
    ·
      refine ⟨2308708186913037936625019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539138791275358624416679 2308708186913037936625019)
      ·
        refine ⟨3463062280369556904937529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2308708186913037936625019 3463062280369556904937529)
        ·
          refine ⟨2597296710277167678703147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3463062280369556904937529 2597296710277167678703147)
          ·
            refine ⟨3895945065415751518054721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2597296710277167678703147 3895945065415751518054721)
            ·
              refine ⟨2921958799061813638541041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3895945065415751518054721 2921958799061813638541041)
              ·
                refine ⟨2191469099296360228905781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2921958799061813638541041 2191469099296360228905781)
                ·
                  refine ⟨205450228059033771459917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2191469099296360228905781 205450228059033771459917)
                  ·
                    rfl

theorem cell21_900254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_900254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900254 prefixEnd_900254 := by exact prefixLift 900254
  have htrace : WordTrace (prefixWord ++ tailWord_900254) baseStart_900254 baseEnd_900254 := by
    simpa [prefixWord, tailWord_900254, baseEnd_900254] using wordTrace_append hprefix tailTrace_900254
  have hstable : (prefixWord ++ tailWord_900254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900254).length < 2 ^ (prefixWord ++ tailWord_900254).sum := by decide
  have hdescent : baseEnd_900254 < baseStart_900254 := by decide
  rcases family_descends (prefixWord ++ tailWord_900254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900302 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_900302 : Nat := 118140960795 + 900302 * 2 ^ 59
def prefixEnd_900302 : Nat := 4983230072969 + 3 ^ 40 * 900302 * 2
def baseEnd_900302 : Nat := 205461182312996354659819

theorem tailTrace_900302 : CollatzResearch.WordTrace tailWord_900302 prefixEnd_900302 205461182312996354659819 := by
  unfold tailWord_900302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104588948045886023162895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21891141056244725456868773 4104588948045886023162895)
  ·
    refine ⟨6156883422068829034744343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4104588948045886023162895 6156883422068829034744343)
    ·
      refine ⟨9235325133103243552116515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6156883422068829034744343 9235325133103243552116515)
      ·
        refine ⟨13852987699654865328174773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9235325133103243552116515 13852987699654865328174773)
        ·
          refine ⟨1298717596842643624516385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13852987699654865328174773 1298717596842643624516385)
          ·
            refine ⟨974038197631982718387289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298717596842643624516385 974038197631982718387289)
            ·
              refine ⟨730528648223987038790467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974038197631982718387289 730528648223987038790467)
              ·
                refine ⟨1095792972335980558185701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 730528648223987038790467 1095792972335980558185701)
                ·
                  refine ⟨205461182312996354659819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1095792972335980558185701 205461182312996354659819)
                  ·
                    rfl

theorem cell21_900302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_900302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900302 prefixEnd_900302 := by exact prefixLift 900302
  have htrace : WordTrace (prefixWord ++ tailWord_900302) baseStart_900302 baseEnd_900302 := by
    simpa [prefixWord, tailWord_900302, baseEnd_900302] using wordTrace_append hprefix tailTrace_900302
  have hstable : (prefixWord ++ tailWord_900302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900302).length < 2 ^ (prefixWord ++ tailWord_900302).sum := by decide
  have hdescent : baseEnd_900302 < baseStart_900302 := by decide
  rcases family_descends (prefixWord ++ tailWord_900302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900403 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 6]
def baseStart_900403 : Nat := 118140960795 + 900403 * 2 ^ 59
def prefixEnd_900403 : Nat := 4983230072969 + 3 ^ 40 * 900403 * 2
def baseEnd_900403 : Nat := 205484231889042623476279

theorem tailTrace_900403 : CollatzResearch.WordTrace tailWord_900403 prefixEnd_900403 205484231889042623476279 := by
  unfold tailWord_900403
  simp only [CollatzResearch.WordTrace]
  refine ⟨32840395357001182434729863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21893596904667454956486575 32840395357001182434729863)
  ·
    refine ⟨49260593035501773652094795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32840395357001182434729863 49260593035501773652094795)
    ·
      refine ⟨73890889553252660478142193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49260593035501773652094795 73890889553252660478142193)
      ·
        refine ⟨55418167164939495358606645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73890889553252660478142193 55418167164939495358606645)
        ·
          refine ⟨5195453171713077689869373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55418167164939495358606645 5195453171713077689869373)
          ·
            refine ⟨1948294939392404133701015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5195453171713077689869373 1948294939392404133701015)
            ·
              refine ⟨2922442409088606200551523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1948294939392404133701015 2922442409088606200551523)
              ·
                refine ⟨4383663613632909300827285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2922442409088606200551523 4383663613632909300827285)
                ·
                  refine ⟨205484231889042623476279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4383663613632909300827285 205484231889042623476279)
                  ·
                    rfl

theorem cell21_900403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_900403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900403 prefixEnd_900403 := by exact prefixLift 900403
  have htrace : WordTrace (prefixWord ++ tailWord_900403) baseStart_900403 baseEnd_900403 := by
    simpa [prefixWord, tailWord_900403, baseEnd_900403] using wordTrace_append hprefix tailTrace_900403
  have hstable : (prefixWord ++ tailWord_900403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900403).length < 2 ^ (prefixWord ++ tailWord_900403).sum := by decide
  have hdescent : baseEnd_900403 < baseStart_900403 := by decide
  rcases family_descends (prefixWord ++ tailWord_900403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900465 : List Nat := [1, 2, 2, 2, 1, 2, 2, 6, 3]
def baseStart_900465 : Nat := 118140960795 + 900465 * 2 ^ 59
def prefixEnd_900465 : Nat := 4983230072969 + 3 ^ 40 * 900465 * 2
def baseEnd_900465 : Nat := 205498381133744293442819

theorem tailTrace_900465 : CollatzResearch.WordTrace tailWord_900465 prefixEnd_900465 205498381133744293442819 := by
  unfold tailWord_900465
  simp only [CollatzResearch.WordTrace]
  refine ⟨32842656682776567023486849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21895104455184378015657899 32842656682776567023486849)
  ·
    refine ⟨24631992512082425267615137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32842656682776567023486849 24631992512082425267615137)
    ·
      refine ⟨18473994384061818950711353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24631992512082425267615137 18473994384061818950711353)
      ·
        refine ⟨13855495788046364213033515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18473994384061818950711353 13855495788046364213033515)
        ·
          refine ⟨20783243682069546319550273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13855495788046364213033515 20783243682069546319550273)
          ·
            refine ⟨15587432761552159739662705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20783243682069546319550273 15587432761552159739662705)
            ·
              refine ⟨11690574571164119804747029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15587432761552159739662705 11690574571164119804747029)
              ·
                refine ⟨547995683023318115847517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11690574571164119804747029 547995683023318115847517)
                ·
                  refine ⟨205498381133744293442819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 547995683023318115847517 205498381133744293442819)
                  ·
                    rfl

theorem cell21_900465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 6, 3].length) (baseStart_900465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900465 prefixEnd_900465 := by exact prefixLift 900465
  have htrace : WordTrace (prefixWord ++ tailWord_900465) baseStart_900465 baseEnd_900465 := by
    simpa [prefixWord, tailWord_900465, baseEnd_900465] using wordTrace_append hprefix tailTrace_900465
  have hstable : (prefixWord ++ tailWord_900465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900465).length < 2 ^ (prefixWord ++ tailWord_900465).sum := by decide
  have hdescent : baseEnd_900465 < baseStart_900465 := by decide
  rcases family_descends (prefixWord ++ tailWord_900465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900510 : List Nat := [4, 3, 1, 2, 11]
def baseStart_900510 : Nat := 118140960795 + 900510 * 2 ^ 59
def prefixEnd_900510 : Nat := 4983230072969 + 3 ^ 40 * 900510 * 2
def baseEnd_900510 : Nat := 2537143836380669323367

theorem tailTrace_900510 : CollatzResearch.WordTrace tailWord_900510 prefixEnd_900510 2537143836380669323367 := by
  unfold tailWord_900510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105537245951692463609373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21896198645075693139249989 4105537245951692463609373)
  ·
    refine ⟨1539576467231884673853515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4105537245951692463609373 1539576467231884673853515)
    ·
      refine ⟨2309364700847827010780273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539576467231884673853515 2309364700847827010780273)
      ·
        refine ⟨1732023525635870258085205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2309364700847827010780273 1732023525635870258085205)
        ·
          refine ⟨2537143836380669323367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1732023525635870258085205 2537143836380669323367)
          ·
            rfl

theorem cell21_900510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 11].length) (baseStart_900510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900510 prefixEnd_900510 := by exact prefixLift 900510
  have htrace : WordTrace (prefixWord ++ tailWord_900510) baseStart_900510 baseEnd_900510 := by
    simpa [prefixWord, tailWord_900510, baseEnd_900510] using wordTrace_append hprefix tailTrace_900510
  have hstable : (prefixWord ++ tailWord_900510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900510).length < 2 ^ (prefixWord ++ tailWord_900510).sum := by decide
  have hdescent : baseEnd_900510 < baseStart_900510 := by decide
  rcases family_descends (prefixWord ++ tailWord_900510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900538 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_900538 : Nat := 118140960795 + 900538 * 2 ^ 59
def prefixEnd_900538 : Nat := 4983230072969 + 3 ^ 40 * 900538 * 2
def baseEnd_900538 : Nat := 205515040728312388726003

theorem tailTrace_900538 : CollatzResearch.WordTrace tailWord_900538 prefixEnd_900538 205515040728312388726003 := by
  unfold tailWord_900538
  simp only [CollatzResearch.WordTrace]
  refine ⟨8211329802878025122723567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21896879474341400327262845 8211329802878025122723567)
  ·
    refine ⟨12316994704317037684085351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8211329802878025122723567 12316994704317037684085351)
    ·
      refine ⟨18475492056475556526128027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12316994704317037684085351 18475492056475556526128027)
      ·
        refine ⟨27713238084713334789192041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18475492056475556526128027 27713238084713334789192041)
        ·
          refine ⟨20784928563535001091894031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27713238084713334789192041 20784928563535001091894031)
          ·
            refine ⟨31177392845302501637841047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20784928563535001091894031 31177392845302501637841047)
            ·
              refine ⟨46766089267953752456761571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31177392845302501637841047 46766089267953752456761571)
              ·
                refine ⟨70149133901930628685142357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46766089267953752456761571 70149133901930628685142357)
                ·
                  refine ⟨205515040728312388726003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70149133901930628685142357 205515040728312388726003)
                  ·
                    rfl

theorem cell21_900538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_900538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900538 prefixEnd_900538 := by exact prefixLift 900538
  have htrace : WordTrace (prefixWord ++ tailWord_900538) baseStart_900538 baseEnd_900538 := by
    simpa [prefixWord, tailWord_900538, baseEnd_900538] using wordTrace_append hprefix tailTrace_900538
  have hstable : (prefixWord ++ tailWord_900538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900538).length < 2 ^ (prefixWord ++ tailWord_900538).sum := by decide
  have hdescent : baseEnd_900538 < baseStart_900538 := by decide
  rcases family_descends (prefixWord ++ tailWord_900538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900569 : List Nat := [1, 2, 1, 2, 4, 3, 8]
def baseStart_900569 : Nat := 118140960795 + 900569 * 2 ^ 59
def prefixEnd_900569 : Nat := 4983230072969 + 3 ^ 40 * 900569 * 2
def baseEnd_900569 : Nat := 22835790594518135967697

theorem tailTrace_900569 : CollatzResearch.WordTrace tailWord_900569 prefixEnd_900569 22835790594518135967697 := by
  unfold tailWord_900569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32846449874399792785272761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21897633249599861856848507 32846449874399792785272761)
  ·
    refine ⟨24634837405799844588954571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32846449874399792785272761 24634837405799844588954571)
    ·
      refine ⟨36952256108699766883431857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24634837405799844588954571 36952256108699766883431857)
      ·
        refine ⟨27714192081524825162573893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36952256108699766883431857 27714192081524825162573893)
        ·
          refine ⟨5196411015285904717982605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27714192081524825162573893 5196411015285904717982605)
          ·
            refine ⟨1948654130732214269243477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5196411015285904717982605 1948654130732214269243477)
            ·
              refine ⟨22835790594518135967697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1948654130732214269243477 22835790594518135967697)
              ·
                rfl

theorem cell21_900569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 8].length) (baseStart_900569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900569 prefixEnd_900569 := by exact prefixLift 900569
  have htrace : WordTrace (prefixWord ++ tailWord_900569) baseStart_900569 baseEnd_900569 := by
    simpa [prefixWord, tailWord_900569, baseEnd_900569] using wordTrace_append hprefix tailTrace_900569
  have hstable : (prefixWord ++ tailWord_900569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900569).length < 2 ^ (prefixWord ++ tailWord_900569).sum := by decide
  have hdescent : baseEnd_900569 < baseStart_900569 := by decide
  rcases family_descends (prefixWord ++ tailWord_900569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900600 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 5]
def baseStart_900600 : Nat := 118140960795 + 900600 * 2 ^ 59
def prefixEnd_900600 : Nat := 4983230072969 + 3 ^ 40 * 900600 * 2
def baseEnd_900600 : Nat := 205529189973014058692543

theorem tailTrace_900600 : CollatzResearch.WordTrace tailWord_900600 prefixEnd_900600 205529189973014058692543 := by
  unfold tailWord_900600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16423790268643742539825627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21898387024858323386434169 16423790268643742539825627)
  ·
    refine ⟨24635685402965613809738441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16423790268643742539825627 24635685402965613809738441)
    ·
      refine ⟨18476764052224210357303831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24635685402965613809738441 18476764052224210357303831)
      ·
        refine ⟨27715146078336315535955747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18476764052224210357303831 27715146078336315535955747)
        ·
          refine ⟨41572719117504473303933621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27715146078336315535955747 41572719117504473303933621)
          ·
            refine ⟨3897442417266044372243777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41572719117504473303933621 3897442417266044372243777)
            ·
              refine ⟨2923081812949533279182833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897442417266044372243777 2923081812949533279182833)
              ·
                refine ⟨2192311359712149959387125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2923081812949533279182833 2192311359712149959387125)
                ·
                  refine ⟨205529189973014058692543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2192311359712149959387125 205529189973014058692543)
                  ·
                    rfl

theorem cell21_900600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_900600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900600 prefixEnd_900600 := by exact prefixLift 900600
  have htrace : WordTrace (prefixWord ++ tailWord_900600) baseStart_900600 baseEnd_900600 := by
    simpa [prefixWord, tailWord_900600, baseEnd_900600] using wordTrace_append hprefix tailTrace_900600
  have hstable : (prefixWord ++ tailWord_900600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900600).length < 2 ^ (prefixWord ++ tailWord_900600).sum := by decide
  have hdescent : baseEnd_900600 < baseStart_900600 := by decide
  rcases family_descends (prefixWord ++ tailWord_900600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900685 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 3]
def baseStart_900685 : Nat := 118140960795 + 900685 * 2 ^ 59
def prefixEnd_900685 : Nat := 4983230072969 + 3 ^ 40 * 900685 * 2
def baseEnd_900685 : Nat := 205548588131072799775703

theorem tailTrace_900685 : CollatzResearch.WordTrace tailWord_900685 prefixEnd_900685 205548588131072799775703 := by
  unfold tailWord_900685
  simp only [CollatzResearch.WordTrace]
  refine ⟨32850680741979544596495509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21900453827986363064330339 32850680741979544596495509)
  ·
    refine ⟨1539875659780291152960727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32850680741979544596495509 1539875659780291152960727)
    ·
      refine ⟨2309813489670436729441091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1539875659780291152960727 2309813489670436729441091)
      ·
        refine ⟨3464720234505655094161637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2309813489670436729441091 3464720234505655094161637)
        ·
          refine ⟨649635043969810330155307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3464720234505655094161637 649635043969810330155307)
          ·
            refine ⟨974452565954715495232961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649635043969810330155307 974452565954715495232961)
            ·
              refine ⟨730839424466036621424721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974452565954715495232961 730839424466036621424721)
              ·
                refine ⟨548129568349527466068541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730839424466036621424721 548129568349527466068541)
                ·
                  refine ⟨205548588131072799775703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548129568349527466068541 205548588131072799775703)
                  ·
                    rfl

theorem cell21_900685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_900685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900685 prefixEnd_900685 := by exact prefixLift 900685
  have htrace : WordTrace (prefixWord ++ tailWord_900685) baseStart_900685 baseEnd_900685 := by
    simpa [prefixWord, tailWord_900685, baseEnd_900685] using wordTrace_append hprefix tailTrace_900685
  have hstable : (prefixWord ++ tailWord_900685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900685).length < 2 ^ (prefixWord ++ tailWord_900685).sum := by decide
  have hdescent : baseEnd_900685 < baseStart_900685 := by decide
  rcases family_descends (prefixWord ++ tailWord_900685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900707 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 4]
def baseStart_900707 : Nat := 118140960795 + 900707 * 2 ^ 59
def prefixEnd_900707 : Nat := 4983230072969 + 3 ^ 40 * 900707 * 2
def baseEnd_900707 : Nat := 205553608830805650408991

theorem tailTrace_900707 : CollatzResearch.WordTrace tailWord_900707 prefixEnd_900707 205553608830805650408991 := by
  unfold tailWord_900707
  simp only [CollatzResearch.WordTrace]
  refine ⟨32851483147899842353796375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21900988765266561569197583 32851483147899842353796375)
  ·
    refine ⟨49277224721849763530694563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32851483147899842353796375 49277224721849763530694563)
    ·
      refine ⟨73915837082774645296041845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49277224721849763530694563 73915837082774645296041845)
      ·
        refine ⟨6929609726510122996503923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73915837082774645296041845 6929609726510122996503923)
        ·
          refine ⟨10394414589765184494755885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6929609726510122996503923 10394414589765184494755885)
          ·
            refine ⟨3897905471161944185533457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10394414589765184494755885 3897905471161944185533457)
            ·
              refine ⟨2923429103371458139150093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3897905471161944185533457 2923429103371458139150093)
              ·
                refine ⟨1096285913764296802181285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2923429103371458139150093 1096285913764296802181285)
                ·
                  refine ⟨205553608830805650408991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096285913764296802181285 205553608830805650408991)
                  ·
                    rfl

theorem cell21_900707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_900707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900707 prefixEnd_900707 := by exact prefixLift 900707
  have htrace : WordTrace (prefixWord ++ tailWord_900707) baseStart_900707 baseEnd_900707 := by
    simpa [prefixWord, tailWord_900707, baseEnd_900707] using wordTrace_append hprefix tailTrace_900707
  have hstable : (prefixWord ++ tailWord_900707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900707).length < 2 ^ (prefixWord ++ tailWord_900707).sum := by decide
  have hdescent : baseEnd_900707 < baseStart_900707 := by decide
  rcases family_descends (prefixWord ++ tailWord_900707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900842 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_900842 : Nat := 118140960795 + 900842 * 2 ^ 59
def prefixEnd_900842 : Nat := 4983230072969 + 3 ^ 40 * 900842 * 2
def baseEnd_900842 : Nat := 205584417670075415658715

theorem tailTrace_900842 : CollatzResearch.WordTrace tailWord_900842 prefixEnd_900842 205584417670075415658715 := by
  unfold tailWord_900842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214101750602690102490195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21904271334940506939973853 8214101750602690102490195)
  ·
    refine ⟨12321152625904035153735293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8214101750602690102490195 12321152625904035153735293)
    ·
      refine ⟨4620432234714013182650735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12321152625904035153735293 4620432234714013182650735)
      ·
        refine ⟨6930648352071019773976103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4620432234714013182650735 6930648352071019773976103)
        ·
          refine ⟨10395972528106529660964155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6930648352071019773976103 10395972528106529660964155)
          ·
            refine ⟨15593958792159794491446233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10395972528106529660964155 15593958792159794491446233)
            ·
              refine ⟨11695469094119845868584675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15593958792159794491446233 11695469094119845868584675)
              ·
                refine ⟨17543203641179768802877013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11695469094119845868584675 17543203641179768802877013)
                ·
                  refine ⟨205584417670075415658715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17543203641179768802877013 205584417670075415658715)
                  ·
                    rfl

theorem cell21_900842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_900842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900842 prefixEnd_900842 := by exact prefixLift 900842
  have htrace : WordTrace (prefixWord ++ tailWord_900842) baseStart_900842 baseEnd_900842 := by
    simpa [prefixWord, tailWord_900842, baseEnd_900842] using wordTrace_append hprefix tailTrace_900842
  have hstable : (prefixWord ++ tailWord_900842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900842).length < 2 ^ (prefixWord ++ tailWord_900842).sum := by decide
  have hdescent : baseEnd_900842 < baseStart_900842 := by decide
  rcases family_descends (prefixWord ++ tailWord_900842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900890 : List Nat := [3, 1, 1, 3, 2, 3, 3, 5]
def baseStart_900890 : Nat := 118140960795 + 900890 * 2 ^ 59
def prefixEnd_900890 : Nat := 4983230072969 + 3 ^ 40 * 900890 * 2
def baseEnd_900890 : Nat := 68531790641345999619539

theorem tailTrace_900890 : CollatzResearch.WordTrace tailWord_900890 prefixEnd_900890 68531790641345999619539 := by
  unfold tailWord_900890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214539426559216151927031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21905438470824576405138749 8214539426559216151927031)
  ·
    refine ⟨12321809139838824227890547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8214539426559216151927031 12321809139838824227890547)
    ·
      refine ⟨18482713709758236341835821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12321809139838824227890547 18482713709758236341835821)
      ·
        refine ⟨6931017641159338628188433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18482713709758236341835821 6931017641159338628188433)
        ·
          refine ⟨5198263230869503971141325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6931017641159338628188433 5198263230869503971141325)
          ·
            refine ⟨1949348711576063989177997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5198263230869503971141325 1949348711576063989177997)
            ·
              refine ⟨731005766841023995941749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1949348711576063989177997 731005766841023995941749)
              ·
                refine ⟨68531790641345999619539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731005766841023995941749 68531790641345999619539)
                ·
                  rfl

theorem cell21_900890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_900890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900890 prefixEnd_900890 := by exact prefixLift 900890
  have htrace : WordTrace (prefixWord ++ tailWord_900890) baseStart_900890 baseEnd_900890 := by
    simpa [prefixWord, tailWord_900890, baseEnd_900890] using wordTrace_append hprefix tailTrace_900890
  have hstable : (prefixWord ++ tailWord_900890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900890).length < 2 ^ (prefixWord ++ tailWord_900890).sum := by decide
  have hdescent : baseEnd_900890 < baseStart_900890 := by decide
  rcases family_descends (prefixWord ++ tailWord_900890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900910 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_900910 : Nat := 118140960795 + 900910 * 2 ^ 59
def prefixEnd_900910 : Nat := 4983230072969 + 3 ^ 40 * 900910 * 2
def baseEnd_900910 : Nat := 205599936196522408525243

theorem tailTrace_900910 : CollatzResearch.WordTrace tailWord_900910 prefixEnd_900910 205599936196522408525243 := by
  unfold tailWord_900910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107360895770551002929523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21905924777442938682290789 4107360895770551002929523)
  ·
    refine ⟨6161041343655826504394285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4107360895770551002929523 6161041343655826504394285)
    ·
      refine ⟨2310390503870934939147857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6161041343655826504394285 2310390503870934939147857)
      ·
        refine ⟨1732792877903201204360893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2310390503870934939147857 1732792877903201204360893)
        ·
          refine ⟨649797329213700451635335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1732792877903201204360893 649797329213700451635335)
          ·
            refine ⟨974695993820550677453003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649797329213700451635335 974695993820550677453003)
            ·
              refine ⟨1462043990730826016179505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974695993820550677453003 1462043990730826016179505)
              ·
                refine ⟨1096532993048119512134629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462043990730826016179505 1096532993048119512134629)
                ·
                  refine ⟨205599936196522408525243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096532993048119512134629 205599936196522408525243)
                  ·
                    rfl

theorem cell21_900910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_900910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900910 prefixEnd_900910 := by exact prefixLift 900910
  have htrace : WordTrace (prefixWord ++ tailWord_900910) baseStart_900910 baseEnd_900910 := by
    simpa [prefixWord, tailWord_900910, baseEnd_900910] using wordTrace_append hprefix tailTrace_900910
  have hstable : (prefixWord ++ tailWord_900910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900910).length < 2 ^ (prefixWord ++ tailWord_900910).sum := by decide
  have hdescent : baseEnd_900910 < baseStart_900910 := by decide
  rcases family_descends (prefixWord ++ tailWord_900910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_900949 : List Nat := [1, 3, 2, 2, 2, 3, 1, 7]
def baseStart_900949 : Nat := 118140960795 + 900949 * 2 ^ 59
def prefixEnd_900949 : Nat := 4983230072969 + 3 ^ 40 * 900949 * 2
def baseEnd_900949 : Nat := 68536278842622335791721

theorem tailTrace_900949 : CollatzResearch.WordTrace tailWord_900949 prefixEnd_900949 68536278842622335791721 := by
  unfold tailWord_900949
  simp only [CollatzResearch.WordTrace]
  refine ⟨32860309613023117684105901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21906873075348745122737267 32860309613023117684105901)
  ·
    refine ⟨12322616104883669131539713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32860309613023117684105901 12322616104883669131539713)
    ·
      refine ⟨9241962078662751848654785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12322616104883669131539713 9241962078662751848654785)
      ·
        refine ⟨6931471558997063886491089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9241962078662751848654785 6931471558997063886491089)
        ·
          refine ⟨5198603669247797914868317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6931471558997063886491089 5198603669247797914868317)
          ·
            refine ⟨1949476375967924218075619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5198603669247797914868317 1949476375967924218075619)
            ·
              refine ⟨2924214563951886327113429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949476375967924218075619 2924214563951886327113429)
              ·
                refine ⟨68536278842622335791721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2924214563951886327113429 68536278842622335791721)
                ·
                  rfl

theorem cell21_900949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 7].length) (baseStart_900949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_900949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_900949 prefixEnd_900949 := by exact prefixLift 900949
  have htrace : WordTrace (prefixWord ++ tailWord_900949) baseStart_900949 baseEnd_900949 := by
    simpa [prefixWord, tailWord_900949, baseEnd_900949] using wordTrace_append hprefix tailTrace_900949
  have hstable : (prefixWord ++ tailWord_900949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_900949).length < 2 ^ (prefixWord ++ tailWord_900949).sum := by decide
  have hdescent : baseEnd_900949 < baseStart_900949 := by decide
  rcases family_descends (prefixWord ++ tailWord_900949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901025 : List Nat := [1, 2, 3, 4, 2, 9]
def baseStart_901025 : Nat := 118140960795 + 901025 * 2 ^ 59
def prefixEnd_901025 : Nat := 4983230072969 + 3 ^ 40 * 901025 * 2
def baseEnd_901025 : Nat := 7615784472715102374383

theorem tailTrace_901025 : CollatzResearch.WordTrace tailWord_901025 prefixEnd_901025 7615784472715102374383 := by
  unfold tailWord_901025
  simp only [CollatzResearch.WordTrace]
  refine ⟨32863081560747782663872529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21908721040498521775915019 32863081560747782663872529)
  ·
    refine ⟨24647311170560836997904397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32863081560747782663872529 24647311170560836997904397)
    ·
      refine ⟨9242741688960313874214149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24647311170560836997904397 9242741688960313874214149)
      ·
        refine ⟨1733014066680058851415153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9242741688960313874214149 1733014066680058851415153)
        ·
          refine ⟨1299760550010044138561365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733014066680058851415153 1299760550010044138561365)
          ·
            refine ⟨7615784472715102374383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1299760550010044138561365 7615784472715102374383)
            ·
              rfl

theorem cell21_901025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 9].length) (baseStart_901025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901025 prefixEnd_901025 := by exact prefixLift 901025
  have htrace : WordTrace (prefixWord ++ tailWord_901025) baseStart_901025 baseEnd_901025 := by
    simpa [prefixWord, tailWord_901025, baseEnd_901025] using wordTrace_append hprefix tailTrace_901025
  have hstable : (prefixWord ++ tailWord_901025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901025).length < 2 ^ (prefixWord ++ tailWord_901025).sum := by decide
  have hdescent : baseEnd_901025 < baseStart_901025 := by decide
  rcases family_descends (prefixWord ++ tailWord_901025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901031 : List Nat := [1, 1, 6, 1, 2, 3, 2, 2, 3]
def baseStart_901031 : Nat := 118140960795 + 901031 * 2 ^ 59
def prefixEnd_901031 : Nat := 4983230072969 + 3 ^ 40 * 901031 * 2
def baseEnd_901031 : Nat := 205627550045053087008329

theorem tailTrace_901031 : CollatzResearch.WordTrace tailWord_901031 prefixEnd_901031 205627550045053087008329 := by
  unfold tailWord_901031
  simp only [CollatzResearch.WordTrace]
  refine ⟨32863300398726045688590947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21908866932484030459060631 32863300398726045688590947)
  ·
    refine ⟨49294950598089068532886421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32863300398726045688590947 49294950598089068532886421)
    ·
      refine ⟨2310700809285425087479051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49294950598089068532886421 2310700809285425087479051)
      ·
        refine ⟨3466051213928137631218577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2310700809285425087479051 3466051213928137631218577)
        ·
          refine ⟨2599538410446103223413933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3466051213928137631218577 2599538410446103223413933)
          ·
            refine ⟨974826903917288708780225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2599538410446103223413933 974826903917288708780225)
            ·
              refine ⟨731120177937966531585169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974826903917288708780225 731120177937966531585169)
              ·
                refine ⟨548340133453474898688877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 731120177937966531585169 548340133453474898688877)
                ·
                  refine ⟨205627550045053087008329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548340133453474898688877 205627550045053087008329)
                  ·
                    rfl

theorem cell21_901031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 3].length) (baseStart_901031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901031 prefixEnd_901031 := by exact prefixLift 901031
  have htrace : WordTrace (prefixWord ++ tailWord_901031) baseStart_901031 baseEnd_901031 := by
    simpa [prefixWord, tailWord_901031, baseEnd_901031] using wordTrace_append hprefix tailTrace_901031
  have hstable : (prefixWord ++ tailWord_901031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901031).length < 2 ^ (prefixWord ++ tailWord_901031).sum := by decide
  have hdescent : baseEnd_901031 < baseStart_901031 := by decide
  rcases family_descends (prefixWord ++ tailWord_901031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901039 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 5]
def baseStart_901039 : Nat := 118140960795 + 901039 * 2 ^ 59
def prefixEnd_901039 : Nat := 4983230072969 + 3 ^ 40 * 901039 * 2
def baseEnd_901039 : Nat := 205629375754046850874979

theorem tailTrace_901039 : CollatzResearch.WordTrace tailWord_901039 prefixEnd_901039 205629375754046850874979 := by
  unfold tailWord_901039
  simp only [CollatzResearch.WordTrace]
  refine ⟨32863592182697063054882171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21909061455131375369921447 32863592182697063054882171)
  ·
    refine ⟨49295388274045594582323257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32863592182697063054882171 49295388274045594582323257)
    ·
      refine ⟨36971541205534195936742443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49295388274045594582323257 36971541205534195936742443)
      ·
        refine ⟨55457311808301293905113665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36971541205534195936742443 55457311808301293905113665)
        ·
          refine ⟨41592983856225970428835249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55457311808301293905113665 41592983856225970428835249)
          ·
            refine ⟨31194737892169477821626437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41592983856225970428835249 31194737892169477821626437)
            ·
              refine ⟨5849013354781777091554957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31194737892169477821626437 5849013354781777091554957)
              ·
                refine ⟨2193380008043166409333109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5849013354781777091554957 2193380008043166409333109)
                ·
                  refine ⟨205629375754046850874979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2193380008043166409333109 205629375754046850874979)
                  ·
                    rfl

theorem cell21_901039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_901039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901039 prefixEnd_901039 := by exact prefixLift 901039
  have htrace : WordTrace (prefixWord ++ tailWord_901039) baseStart_901039 baseEnd_901039 := by
    simpa [prefixWord, tailWord_901039, baseEnd_901039] using wordTrace_append hprefix tailTrace_901039
  have hstable : (prefixWord ++ tailWord_901039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901039).length < 2 ^ (prefixWord ++ tailWord_901039).sum := by decide
  have hdescent : baseEnd_901039 < baseStart_901039 := by decide
  rcases family_descends (prefixWord ++ tailWord_901039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901070 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_901070 : Nat := 118140960795 + 901070 * 2 ^ 59
def prefixEnd_901070 : Nat := 4983230072969 + 3 ^ 40 * 901070 * 2
def baseEnd_901070 : Nat := 205636450376397685858249

theorem tailTrace_901070 : CollatzResearch.WordTrace tailWord_901070 prefixEnd_901070 205636450376397685858249 := by
  unfold tailWord_901070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4108090355698094418657583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21909815230389836899507109 4108090355698094418657583)
  ·
    refine ⟨6162135533547141627986375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4108090355698094418657583 6162135533547141627986375)
    ·
      refine ⟨9243203300320712441979563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6162135533547141627986375 9243203300320712441979563)
      ·
        refine ⟨13864804950481068662969345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9243203300320712441979563 13864804950481068662969345)
        ·
          refine ⟨10398603712860801497227009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13864804950481068662969345 10398603712860801497227009)
          ·
            refine ⟨7798952784645601122920257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10398603712860801497227009 7798952784645601122920257)
            ·
              refine ⟨5849214588484200842190193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7798952784645601122920257 5849214588484200842190193)
              ·
                refine ⟨4386910941363150631642645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5849214588484200842190193 4386910941363150631642645)
                ·
                  refine ⟨205636450376397685858249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4386910941363150631642645 205636450376397685858249)
                  ·
                    rfl

theorem cell21_901070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_901070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901070 prefixEnd_901070 := by exact prefixLift 901070
  have htrace : WordTrace (prefixWord ++ tailWord_901070) baseStart_901070 baseEnd_901070 := by
    simpa [prefixWord, tailWord_901070, baseEnd_901070] using wordTrace_append hprefix tailTrace_901070
  have hstable : (prefixWord ++ tailWord_901070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901070).length < 2 ^ (prefixWord ++ tailWord_901070).sum := by decide
  have hdescent : baseEnd_901070 < baseStart_901070 := by decide
  rcases family_descends (prefixWord ++ tailWord_901070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901087 : List Nat := [1, 1, 2, 3, 4, 1, 3, 2, 4]
def baseStart_901087 : Nat := 118140960795 + 901087 * 2 ^ 59
def prefixEnd_901087 : Nat := 4983230072969 + 3 ^ 40 * 901087 * 2
def baseEnd_901087 : Nat := 205640330008009434074881

theorem tailTrace_901087 : CollatzResearch.WordTrace tailWord_901087 prefixEnd_901087 205640330008009434074881 := by
  unfold tailWord_901087
  simp only [CollatzResearch.WordTrace]
  refine ⟨32865342886523167252629515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21910228591015444835086343 32865342886523167252629515)
  ·
    refine ⟨49298014329784750878944273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32865342886523167252629515 49298014329784750878944273)
    ·
      refine ⟨36973510747338563159208205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49298014329784750878944273 36973510747338563159208205)
      ·
        refine ⟨13865066530251961184703077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36973510747338563159208205 13865066530251961184703077)
        ·
          refine ⟨2599699974422242722131827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13865066530251961184703077 2599699974422242722131827)
          ·
            refine ⟨3899549961633364083197741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2599699974422242722131827 3899549961633364083197741)
            ·
              refine ⟨1462331235612511531199153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3899549961633364083197741 1462331235612511531199153)
              ·
                refine ⟨1096748426709383648399365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462331235612511531199153 1096748426709383648399365)
                ·
                  refine ⟨205640330008009434074881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096748426709383648399365 205640330008009434074881)
                  ·
                    rfl

theorem cell21_901087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 4].length) (baseStart_901087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901087 prefixEnd_901087 := by exact prefixLift 901087
  have htrace : WordTrace (prefixWord ++ tailWord_901087) baseStart_901087 baseEnd_901087 := by
    simpa [prefixWord, tailWord_901087, baseEnd_901087] using wordTrace_append hprefix tailTrace_901087
  have hstable : (prefixWord ++ tailWord_901087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901087).length < 2 ^ (prefixWord ++ tailWord_901087).sum := by decide
  have hdescent : baseEnd_901087 < baseStart_901087 := by decide
  rcases family_descends (prefixWord ++ tailWord_901087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901090 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_901090 : Nat := 118140960795 + 901090 * 2 ^ 59
def prefixEnd_901090 : Nat := 4983230072969 + 3 ^ 40 * 901090 * 2
def baseEnd_901090 : Nat := 205641014648882095524875

theorem tailTrace_901090 : CollatzResearch.WordTrace tailWord_901090 prefixEnd_901090 205641014648882095524875 := by
  unfold tailWord_901090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216363076378074691247181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21910301537008199176659149 8216363076378074691247181)
  ·
    refine ⟨3081136153641778009217693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8216363076378074691247181 3081136153641778009217693)
    ·
      refine ⟨1155426057615666753456635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3081136153641778009217693 1155426057615666753456635)
      ·
        refine ⟨1733139086423500130184953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155426057615666753456635 1733139086423500130184953)
        ·
          refine ⟨1299854314817625097638715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733139086423500130184953 1299854314817625097638715)
          ·
            refine ⟨1949781472226437646458073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299854314817625097638715 1949781472226437646458073)
            ·
              refine ⟨1462336104169828234843555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1949781472226437646458073 1462336104169828234843555)
              ·
                refine ⟨2193504156254742352265333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462336104169828234843555 2193504156254742352265333)
                ·
                  refine ⟨205641014648882095524875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2193504156254742352265333 205641014648882095524875)
                  ·
                    rfl

theorem cell21_901090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_901090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901090 prefixEnd_901090 := by exact prefixLift 901090
  have htrace : WordTrace (prefixWord ++ tailWord_901090) baseStart_901090 baseEnd_901090 := by
    simpa [prefixWord, tailWord_901090, baseEnd_901090] using wordTrace_append hprefix tailTrace_901090
  have hstable : (prefixWord ++ tailWord_901090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901090).length < 2 ^ (prefixWord ++ tailWord_901090).sum := by decide
  have hdescent : baseEnd_901090 < baseStart_901090 := by decide
  rcases family_descends (prefixWord ++ tailWord_901090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901115 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_901115 : Nat := 118140960795 + 901115 * 2 ^ 59
def prefixEnd_901115 : Nat := 4983230072969 + 3 ^ 40 * 901115 * 2
def baseEnd_901115 : Nat := 205646719989487607608157

theorem tailTrace_901115 : CollatzResearch.WordTrace tailWord_901115 prefixEnd_901115 205646719989487607608157 := by
  unfold tailWord_901115
  simp only [CollatzResearch.WordTrace]
  refine ⟨32866364130421728034648799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21910909420281152023099199 32866364130421728034648799)
  ·
    refine ⟨49299546195632592051973199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32866364130421728034648799 49299546195632592051973199)
    ·
      refine ⟨73949319293448888077959799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49299546195632592051973199 73949319293448888077959799)
      ·
        refine ⟨110923978940173332116939699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73949319293448888077959799 110923978940173332116939699)
        ·
          refine ⟨166385968410259998175409549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110923978940173332116939699 166385968410259998175409549)
          ·
            refine ⟨62394738153847499315778581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166385968410259998175409549 62394738153847499315778581)
            ·
              refine ⟨2924753350961601530427121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62394738153847499315778581 2924753350961601530427121)
              ·
                refine ⟨2193565013221201147820341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2924753350961601530427121 2193565013221201147820341)
                ·
                  refine ⟨205646719989487607608157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2193565013221201147820341 205646719989487607608157)
                  ·
                    rfl

theorem cell21_901115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_901115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901115 prefixEnd_901115 := by exact prefixLift 901115
  have htrace : WordTrace (prefixWord ++ tailWord_901115) baseStart_901115 baseEnd_901115 := by
    simpa [prefixWord, tailWord_901115, baseEnd_901115] using wordTrace_append hprefix tailTrace_901115
  have hstable : (prefixWord ++ tailWord_901115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901115).length < 2 ^ (prefixWord ++ tailWord_901115).sum := by decide
  have hdescent : baseEnd_901115 < baseStart_901115 := by decide
  rcases family_descends (prefixWord ++ tailWord_901115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901118 : List Nat := [4, 2, 2, 2, 1, 2, 1, 7]
def baseStart_901118 : Nat := 118140960795 + 901118 * 2 ^ 59
def prefixEnd_901118 : Nat := 4983230072969 + 3 ^ 40 * 901118 * 2
def baseEnd_901118 : Nat := 68549134876786756352717

theorem tailTrace_901118 : CollatzResearch.WordTrace tailWord_901118 prefixEnd_901118 68549134876786756352717 := by
  unfold tailWord_901118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4108309193676357443376001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21910982366273906364672005 4108309193676357443376001)
  ·
    refine ⟨3081231895257268082532001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4108309193676357443376001 3081231895257268082532001)
    ·
      refine ⟨2310923921442951061899001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3081231895257268082532001 2310923921442951061899001)
      ·
        refine ⟨1733192941082213296424251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2310923921442951061899001 1733192941082213296424251)
        ·
          refine ⟨2599789411623319944636377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733192941082213296424251 2599789411623319944636377)
          ·
            refine ⟨1949842058717489958477283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2599789411623319944636377 1949842058717489958477283)
            ·
              refine ⟨2924763088076234937715925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1949842058717489958477283 2924763088076234937715925)
              ·
                refine ⟨68549134876786756352717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2924763088076234937715925 68549134876786756352717)
                ·
                  rfl

theorem cell21_901118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_901118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901118 prefixEnd_901118 := by exact prefixLift 901118
  have htrace : WordTrace (prefixWord ++ tailWord_901118) baseStart_901118 baseEnd_901118 := by
    simpa [prefixWord, tailWord_901118, baseEnd_901118] using wordTrace_append hprefix tailTrace_901118
  have hstable : (prefixWord ++ tailWord_901118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901118).length < 2 ^ (prefixWord ++ tailWord_901118).sum := by decide
  have hdescent : baseEnd_901118 < baseStart_901118 := by decide
  rcases family_descends (prefixWord ++ tailWord_901118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901124 : List Nat := [2, 3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_901124 : Nat := 118140960795 + 901124 * 2 ^ 59
def prefixEnd_901124 : Nat := 4983230072969 + 3 ^ 40 * 901124 * 2
def baseEnd_901124 : Nat := 205648773912105591958139

theorem tailTrace_901124 : CollatzResearch.WordTrace tailWord_901124 prefixEnd_901124 205648773912105591958139 := by
  unfold tailWord_901124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16433346193694561285863213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21911128258259415047817617 16433346193694561285863213)
  ·
    refine ⟨6162504822635460482198705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16433346193694561285863213 6162504822635460482198705)
    ·
      refine ⟨4621878616976595361649029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6162504822635460482198705 4621878616976595361649029)
      ·
        refine ⟨866602240683111630309193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4621878616976595361649029 866602240683111630309193)
        ·
          refine ⟨649951680512333722731895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866602240683111630309193 649951680512333722731895)
          ·
            refine ⟨974927520768500584097843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649951680512333722731895 974927520768500584097843)
            ·
              refine ⟨1462391281152750876146765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974927520768500584097843 1462391281152750876146765)
              ·
                refine ⟨548396730432281578555037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1462391281152750876146765 548396730432281578555037)
                ·
                  refine ⟨205648773912105591958139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548396730432281578555037 205648773912105591958139)
                  ·
                    rfl

theorem cell21_901124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_901124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901124 prefixEnd_901124 := by exact prefixLift 901124
  have htrace : WordTrace (prefixWord ++ tailWord_901124) baseStart_901124 baseEnd_901124 := by
    simpa [prefixWord, tailWord_901124, baseEnd_901124] using wordTrace_append hprefix tailTrace_901124
  have hstable : (prefixWord ++ tailWord_901124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901124).length < 2 ^ (prefixWord ++ tailWord_901124).sum := by decide
  have hdescent : baseEnd_901124 < baseStart_901124 := by decide
  rcases family_descends (prefixWord ++ tailWord_901124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901146 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 6]
def baseStart_901146 : Nat := 118140960795 + 901146 * 2 ^ 59
def prefixEnd_901146 : Nat := 4983230072969 + 3 ^ 40 * 901146 * 2
def baseEnd_901146 : Nat := 205653794611838442591427

theorem tailTrace_901146 : CollatzResearch.WordTrace tailWord_901146 prefixEnd_901146 205653794611838442591427 := by
  unfold tailWord_901146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8216873698327355082256823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21911663195539613552684861 8216873698327355082256823)
  ·
    refine ⟨12325310547491032623385235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8216873698327355082256823 12325310547491032623385235)
    ·
      refine ⟨18487965821236548935077853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12325310547491032623385235 18487965821236548935077853)
      ·
        refine ⟨6932987182963705850654195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18487965821236548935077853 6932987182963705850654195)
        ·
          refine ⟨10399480774445558775981293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6932987182963705850654195 10399480774445558775981293)
          ·
            refine ⟨3899805290417084540992985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10399480774445558775981293 3899805290417084540992985)
            ·
              refine ⟨2924853967812813405744739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3899805290417084540992985 2924853967812813405744739)
              ·
                refine ⟨4387280951719220108617109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2924853967812813405744739 4387280951719220108617109)
                ·
                  refine ⟨205653794611838442591427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4387280951719220108617109 205653794611838442591427)
                  ·
                    rfl

theorem cell21_901146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_901146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901146 prefixEnd_901146 := by exact prefixLift 901146
  have htrace : WordTrace (prefixWord ++ tailWord_901146) baseStart_901146 baseEnd_901146 := by
    simpa [prefixWord, tailWord_901146, baseEnd_901146] using wordTrace_append hprefix tailTrace_901146
  have hstable : (prefixWord ++ tailWord_901146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901146).length < 2 ^ (prefixWord ++ tailWord_901146).sum := by decide
  have hdescent : baseEnd_901146 < baseStart_901146 := by decide
  rcases family_descends (prefixWord ++ tailWord_901146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901149 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 5]
def baseStart_901149 : Nat := 118140960795 + 901149 * 2 ^ 59
def prefixEnd_901149 : Nat := 4983230072969 + 3 ^ 40 * 901149 * 2
def baseEnd_901149 : Nat := 205654479252711104041421

theorem tailTrace_901149 : CollatzResearch.WordTrace tailWord_901149 prefixEnd_901149 205654479252711104041421 := by
  unfold tailWord_901149
  simp only [CollatzResearch.WordTrace]
  refine ⟨32867604212298551841386501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21911736141532367894257667 32867604212298551841386501)
  ·
    refine ⟨6162675789805978470259969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32867604212298551841386501 6162675789805978470259969)
    ·
      refine ⟨4622006842354483852694977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6162675789805978470259969 4622006842354483852694977)
      ·
        refine ⟨3466505131765862889521233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4622006842354483852694977 3466505131765862889521233)
        ·
          refine ⟨2599878848824397167140925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3466505131765862889521233 2599878848824397167140925)
          ·
            refine ⟨974954568309148937677847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2599878848824397167140925 974954568309148937677847)
            ·
              refine ⟨1462431852463723406516771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 974954568309148937677847 1462431852463723406516771)
              ·
                refine ⟨2193647778695585109775157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1462431852463723406516771 2193647778695585109775157)
                ·
                  refine ⟨205654479252711104041421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2193647778695585109775157 205654479252711104041421)
                  ·
                    rfl

theorem cell21_901149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_901149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901149 prefixEnd_901149 := by exact prefixLift 901149
  have htrace : WordTrace (prefixWord ++ tailWord_901149) baseStart_901149 baseEnd_901149 := by
    simpa [prefixWord, tailWord_901149, baseEnd_901149] using wordTrace_append hprefix tailTrace_901149
  have hstable : (prefixWord ++ tailWord_901149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901149).length < 2 ^ (prefixWord ++ tailWord_901149).sum := by decide
  have hdescent : baseEnd_901149 < baseStart_901149 := by decide
  rcases family_descends (prefixWord ++ tailWord_901149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901256 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_901256 : Nat := 118140960795 + 901256 * 2 ^ 59
def prefixEnd_901256 : Nat := 4983230072969 + 3 ^ 40 * 901256 * 2
def baseEnd_901256 : Nat := 205678898110502695757869

theorem tailTrace_901256 : CollatzResearch.WordTrace tailWord_901256 prefixEnd_901256 205678898110502695757869 := by
  unfold tailWord_901256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16435753411455454557765811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21914337881940606077021081 16435753411455454557765811)
  ·
    refine ⟨24653630117183181836648717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16435753411455454557765811 24653630117183181836648717)
    ·
      refine ⟨9245111293943693188743269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24653630117183181836648717 9245111293943693188743269)
      ·
        refine ⟨1733458367614442472889363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9245111293943693188743269 1733458367614442472889363)
        ·
          refine ⟨2600187551421663709334045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1733458367614442472889363 2600187551421663709334045)
          ·
            refine ⟨975070331783123891000267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2600187551421663709334045 975070331783123891000267)
            ·
              refine ⟨1462605497674685836500401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975070331783123891000267 1462605497674685836500401)
              ·
                refine ⟨1096954123256014377375301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1462605497674685836500401 1096954123256014377375301)
                ·
                  refine ⟨205678898110502695757869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1096954123256014377375301 205678898110502695757869)
                  ·
                    rfl

theorem cell21_901256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_901256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901256 prefixEnd_901256 := by exact prefixLift 901256
  have htrace : WordTrace (prefixWord ++ tailWord_901256) baseStart_901256 baseEnd_901256 := by
    simpa [prefixWord, tailWord_901256, baseEnd_901256] using wordTrace_append hprefix tailTrace_901256
  have hstable : (prefixWord ++ tailWord_901256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901256).length < 2 ^ (prefixWord ++ tailWord_901256).sum := by decide
  have hdescent : baseEnd_901256 < baseStart_901256 := by decide
  rcases family_descends (prefixWord ++ tailWord_901256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901287 : List Nat := [1, 1, 6, 2, 2, 2, 2, 5]
def baseStart_901287 : Nat := 118140960795 + 901287 * 2 ^ 59
def prefixEnd_901287 : Nat := 4983230072969 + 3 ^ 40 * 901287 * 2
def baseEnd_901287 : Nat := 68561990910951176913713

theorem tailTrace_901287 : CollatzResearch.WordTrace tailWord_901287 prefixEnd_901287 68561990910951176913713 := by
  unfold tailWord_901287
  simp only [CollatzResearch.WordTrace]
  refine ⟨32872637485798601409910115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21915091657199067606606743 32872637485798601409910115)
  ·
    refine ⟨49308956228697902114865173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32872637485798601409910115 49308956228697902114865173)
    ·
      refine ⟨2311357323220214161634305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49308956228697902114865173 2311357323220214161634305)
      ·
        refine ⟨1733517992415160621225729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2311357323220214161634305 1733517992415160621225729)
        ·
          refine ⟨1300138494311370465919297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733517992415160621225729 1300138494311370465919297)
          ·
            refine ⟨975103870733527849439473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300138494311370465919297 975103870733527849439473)
            ·
              refine ⟨731327903050145887079605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975103870733527849439473 731327903050145887079605)
              ·
                refine ⟨68561990910951176913713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731327903050145887079605 68561990910951176913713)
                ·
                  rfl

theorem cell21_901287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 5].length) (baseStart_901287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901287 prefixEnd_901287 := by exact prefixLift 901287
  have htrace : WordTrace (prefixWord ++ tailWord_901287) baseStart_901287 baseEnd_901287 := by
    simpa [prefixWord, tailWord_901287, baseEnd_901287] using wordTrace_append hprefix tailTrace_901287
  have hstable : (prefixWord ++ tailWord_901287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901287).length < 2 ^ (prefixWord ++ tailWord_901287).sum := by decide
  have hdescent : baseEnd_901287 < baseStart_901287 := by decide
  rcases family_descends (prefixWord ++ tailWord_901287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901312 : List Nat := [2, 1, 1, 2, 5, 1, 9]
def baseStart_901312 : Nat := 118140960795 + 901312 * 2 ^ 59
def prefixEnd_901312 : Nat := 4983230072969 + 3 ^ 40 * 901312 * 2
def baseEnd_901312 : Nat := 22854630897051004758269

theorem tailTrace_901312 : CollatzResearch.WordTrace tailWord_901312 prefixEnd_901312 22854630897051004758269 := by
  unfold tailWord_901312
  simp only [CollatzResearch.WordTrace]
  refine ⟨16436774655354015339785095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21915699540472020453046793 16436774655354015339785095)
  ·
    refine ⟨24655161983031023009677643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16436774655354015339785095 24655161983031023009677643)
    ·
      refine ⟨36982742974546534514516465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24655161983031023009677643 36982742974546534514516465)
      ·
        refine ⟨27737057230909900885887349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36982742974546534514516465 27737057230909900885887349)
        ·
          refine ⟨2600349115397803208051939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27737057230909900885887349 2600349115397803208051939)
          ·
            refine ⟨3900523673096704812077909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2600349115397803208051939 3900523673096704812077909)
            ·
              refine ⟨22854630897051004758269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3900523673096704812077909 22854630897051004758269)
              ·
                rfl

theorem cell21_901312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 9].length) (baseStart_901312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901312 prefixEnd_901312 := by exact prefixLift 901312
  have htrace : WordTrace (prefixWord ++ tailWord_901312) baseStart_901312 baseEnd_901312 := by
    simpa [prefixWord, tailWord_901312, baseEnd_901312] using wordTrace_append hprefix tailTrace_901312
  have hstable : (prefixWord ++ tailWord_901312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901312).length < 2 ^ (prefixWord ++ tailWord_901312).sum := by decide
  have hdescent : baseEnd_901312 < baseStart_901312 := by decide
  rcases family_descends (prefixWord ++ tailWord_901312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901422 : List Nat := [4, 1, 3, 3, 1, 1, 8]
def baseStart_901422 : Nat := 118140960795 + 901422 * 2 ^ 59
def prefixEnd_901422 : Nat := 4983230072969 + 3 ^ 40 * 901422 * 2
def baseEnd_901422 : Nat := 22857420174680366221207

theorem tailTrace_901422 : CollatzResearch.WordTrace tailWord_901422 prefixEnd_901422 22857420174680366221207 := by
  unfold tailWord_901422
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109695167538689933259315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21918374226873012977383013 4109695167538689933259315)
  ·
    refine ⟨6164542751308034899888973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4109695167538689933259315 6164542751308034899888973)
    ·
      refine ⟨2311703531740513087458365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6164542751308034899888973 2311703531740513087458365)
      ·
        refine ⟨866888824402692407796887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2311703531740513087458365 866888824402692407796887)
        ·
          refine ⟨1300333236604038611695331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866888824402692407796887 1300333236604038611695331)
          ·
            refine ⟨1950499854906057917542997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300333236604038611695331 1950499854906057917542997)
            ·
              refine ⟨22857420174680366221207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1950499854906057917542997 22857420174680366221207)
              ·
                rfl

theorem cell21_901422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 8].length) (baseStart_901422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901422 prefixEnd_901422 := by exact prefixLift 901422
  have htrace : WordTrace (prefixWord ++ tailWord_901422) baseStart_901422 baseEnd_901422 := by
    simpa [prefixWord, tailWord_901422, baseEnd_901422] using wordTrace_append hprefix tailTrace_901422
  have hstable : (prefixWord ++ tailWord_901422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901422).length < 2 ^ (prefixWord ++ tailWord_901422).sum := by decide
  have hdescent : baseEnd_901422 < baseStart_901422 := by decide
  rcases family_descends (prefixWord ++ tailWord_901422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901436 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_901436 : Nat := 118140960795 + 901436 * 2 ^ 59
def prefixEnd_901436 : Nat := 4983230072969 + 3 ^ 40 * 901436 * 2
def baseEnd_901436 : Nat := 205719976562862382757501

theorem tailTrace_901436 : CollatzResearch.WordTrace tailWord_901436 prefixEnd_901436 205719976562862382757501 := by
  unfold tailWord_901436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16439035981129399928542081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21918714641505866571389441 16439035981129399928542081)
  ·
    refine ⟨12329276985847049946406561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16439035981129399928542081 12329276985847049946406561)
    ·
      refine ⟨9246957739385287459804921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12329276985847049946406561 9246957739385287459804921)
      ·
        refine ⟨6935218304538965594853691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9246957739385287459804921 6935218304538965594853691)
        ·
          refine ⟨10402827456808448392280537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6935218304538965594853691 10402827456808448392280537)
          ·
            refine ⟨7802120592606336294210403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10402827456808448392280537 7802120592606336294210403)
            ·
              refine ⟨11703180888909504441315605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7802120592606336294210403 11703180888909504441315605)
              ·
                refine ⟨548586604167633020686669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11703180888909504441315605 548586604167633020686669)
                ·
                  refine ⟨205719976562862382757501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548586604167633020686669 205719976562862382757501)
                  ·
                    rfl

theorem cell21_901436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_901436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901436 prefixEnd_901436 := by exact prefixLift 901436
  have htrace : WordTrace (prefixWord ++ tailWord_901436) baseStart_901436 baseEnd_901436 := by
    simpa [prefixWord, tailWord_901436, baseEnd_901436] using wordTrace_append hprefix tailTrace_901436
  have hstable : (prefixWord ++ tailWord_901436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901436).length < 2 ^ (prefixWord ++ tailWord_901436).sum := by decide
  have hdescent : baseEnd_901436 < baseStart_901436 := by decide
  rcases family_descends (prefixWord ++ tailWord_901436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901543 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 4]
def baseStart_901543 : Nat := 118140960795 + 901543 * 2 ^ 59
def prefixEnd_901543 : Nat := 4983230072969 + 3 ^ 40 * 901543 * 2
def baseEnd_901543 : Nat := 205744395420653974473949

theorem tailTrace_901543 : CollatzResearch.WordTrace tailWord_901543 prefixEnd_901543 205744395420653974473949 := by
  unfold tailWord_901543
  simp only [CollatzResearch.WordTrace]
  refine ⟨32881974572871157131229283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21921316381914104754152855 32881974572871157131229283)
  ·
    refine ⟨49322961859306735696843925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32881974572871157131229283 49322961859306735696843925)
    ·
      refine ⟨2312013837155003235789559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49322961859306735696843925 2312013837155003235789559)
      ·
        refine ⟨3468020755732504853684339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312013837155003235789559 3468020755732504853684339)
        ·
          refine ⟨5202031133598757280526509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468020755732504853684339 5202031133598757280526509)
          ·
            refine ⟨1950761675099533980197441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5202031133598757280526509 1950761675099533980197441)
            ·
              refine ⟨1463071256324650485148081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1950761675099533980197441 1463071256324650485148081)
              ·
                refine ⟨1097303442243487863861061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463071256324650485148081 1097303442243487863861061)
                ·
                  refine ⟨205744395420653974473949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097303442243487863861061 205744395420653974473949)
                  ·
                    rfl

theorem cell21_901543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_901543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901543 prefixEnd_901543 := by exact prefixLift 901543
  have htrace : WordTrace (prefixWord ++ tailWord_901543) baseStart_901543 baseEnd_901543 := by
    simpa [prefixWord, tailWord_901543, baseEnd_901543] using wordTrace_append hprefix tailTrace_901543
  have hstable : (prefixWord ++ tailWord_901543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901543).length < 2 ^ (prefixWord ++ tailWord_901543).sum := by decide
  have hdescent : baseEnd_901543 < baseStart_901543 := by decide
  rcases family_descends (prefixWord ++ tailWord_901543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901633 : List Nat := [1, 2, 4, 1, 3, 1, 4, 5]
def baseStart_901633 : Nat := 118140960795 + 901633 * 2 ^ 59
def prefixEnd_901633 : Nat := 4983230072969 + 3 ^ 40 * 901633 * 2
def baseEnd_901633 : Nat := 68588311548944605991255

theorem tailTrace_901633 : CollatzResearch.WordTrace tailWord_901633 prefixEnd_901633 68588311548944605991255 := by
  unfold tailWord_901633
  simp only [CollatzResearch.WordTrace]
  refine ⟨32885257142545102502005553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21923504761696735001337035 32885257142545102502005553)
  ·
    refine ⟨24663942856908826876504165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32885257142545102502005553 24663942856908826876504165)
    ·
      refine ⟨4624489285670405039344531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24663942856908826876504165 4624489285670405039344531)
      ·
        refine ⟨6936733928505607559016797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4624489285670405039344531 6936733928505607559016797)
        ·
          refine ⟨2601275223189602834631299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6936733928505607559016797 2601275223189602834631299)
          ·
            refine ⟨3901912834784404251946949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601275223189602834631299 3901912834784404251946949)
            ·
              refine ⟨731608656522075797240053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3901912834784404251946949 731608656522075797240053)
              ·
                refine ⟨68588311548944605991255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731608656522075797240053 68588311548944605991255)
                ·
                  rfl

theorem cell21_901633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 5].length) (baseStart_901633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901633 prefixEnd_901633 := by exact prefixLift 901633
  have htrace : WordTrace (prefixWord ++ tailWord_901633) baseStart_901633 baseEnd_901633 := by
    simpa [prefixWord, tailWord_901633, baseEnd_901633] using wordTrace_append hprefix tailTrace_901633
  have hstable : (prefixWord ++ tailWord_901633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901633).length < 2 ^ (prefixWord ++ tailWord_901633).sum := by decide
  have hdescent : baseEnd_901633 < baseStart_901633 := by decide
  rcases family_descends (prefixWord ++ tailWord_901633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901692 : List Nat := [2, 2, 2, 2, 3, 1, 2, 7]
def baseStart_901692 : Nat := 118140960795 + 901692 * 2 ^ 59
def prefixEnd_901692 : Nat := 4983230072969 + 3 ^ 40 * 901692 * 2
def baseEnd_901692 : Nat := 68592799750220942163437

theorem tailTrace_901692 : CollatzResearch.WordTrace tailWord_901692 prefixEnd_901692 68592799750220942163437 := by
  unfold tailWord_901692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16443704524665677789201665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21924939366220903718935553 16443704524665677789201665)
  ·
    refine ⟨12332778393499258341901249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16443704524665677789201665 12332778393499258341901249)
    ·
      refine ⟨9249583795124443756425937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12332778393499258341901249 9249583795124443756425937)
      ·
        refine ⟨6937187846343332817319453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9249583795124443756425937 6937187846343332817319453)
        ·
          refine ⟨2601445442378749806494795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6937187846343332817319453 2601445442378749806494795)
          ·
            refine ⟨3902168163568124709742193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601445442378749806494795 3902168163568124709742193)
            ·
              refine ⟨2926626122676093532306645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3902168163568124709742193 2926626122676093532306645)
              ·
                refine ⟨68592799750220942163437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2926626122676093532306645 68592799750220942163437)
                ·
                  rfl

theorem cell21_901692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_901692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901692 prefixEnd_901692 := by exact prefixLift 901692
  have htrace : WordTrace (prefixWord ++ tailWord_901692) baseStart_901692 baseEnd_901692 := by
    simpa [prefixWord, tailWord_901692, baseEnd_901692] using wordTrace_append hprefix tailTrace_901692
  have hstable : (prefixWord ++ tailWord_901692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901692).length < 2 ^ (prefixWord ++ tailWord_901692).sum := by decide
  have hdescent : baseEnd_901692 < baseStart_901692 := by decide
  rcases family_descends (prefixWord ++ tailWord_901692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901751 : List Nat := [1, 1, 3, 1, 1, 3, 2, 9]
def baseStart_901751 : Nat := 118140960795 + 901751 * 2 ^ 59
def prefixEnd_901751 : Nat := 4983230072969 + 3 ^ 40 * 901751 * 2
def baseEnd_901751 : Nat := 68597287951497278335619

theorem tailTrace_901751 : CollatzResearch.WordTrace tailWord_901751 prefixEnd_901751 68597287951497278335619 := by
  unfold tailWord_901751
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889560956117608654801107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21926373970745072436534071 32889560956117608654801107)
  ·
    refine ⟨49334341434176412982201661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32889560956117608654801107 49334341434176412982201661)
    ·
      refine ⟨18500378037816154868325623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49334341434176412982201661 18500378037816154868325623)
      ·
        refine ⟨27750567056724232302488435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18500378037816154868325623 27750567056724232302488435)
        ·
          refine ⟨41625850585086348453732653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27750567056724232302488435 41625850585086348453732653)
          ·
            refine ⟨15609693969407380670149745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41625850585086348453732653 15609693969407380670149745)
            ·
              refine ⟨11707270477055535502612309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15609693969407380670149745 11707270477055535502612309)
              ·
                refine ⟨68597287951497278335619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11707270477055535502612309 68597287951497278335619)
                ·
                  rfl

theorem cell21_901751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_901751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901751 prefixEnd_901751 := by exact prefixLift 901751
  have htrace : WordTrace (prefixWord ++ tailWord_901751) baseStart_901751 baseEnd_901751 := by
    simpa [prefixWord, tailWord_901751, baseEnd_901751] using wordTrace_append hprefix tailTrace_901751
  have hstable : (prefixWord ++ tailWord_901751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901751).length < 2 ^ (prefixWord ++ tailWord_901751).sum := by decide
  have hdescent : baseEnd_901751 < baseStart_901751 := by decide
  rcases family_descends (prefixWord ++ tailWord_901751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901757 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 3]
def baseStart_901757 : Nat := 118140960795 + 901757 * 2 ^ 59
def prefixEnd_901757 : Nat := 4983230072969 + 3 ^ 40 * 901757 * 2
def baseEnd_901757 : Nat := 205793233136237157906845

theorem tailTrace_901757 : CollatzResearch.WordTrace tailWord_901757 prefixEnd_901757 205793233136237157906845 := by
  unfold tailWord_901757
  simp only [CollatzResearch.WordTrace]
  refine ⟨32889779794095871679519525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21926519862730581119679683 32889779794095871679519525)
  ·
    refine ⟨6166833711392975939909911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32889779794095871679519525 6166833711392975939909911)
    ·
      refine ⟨9250250567089463909864867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6166833711392975939909911 9250250567089463909864867)
      ·
        refine ⟨13875375850634195864797301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9250250567089463909864867 13875375850634195864797301)
        ·
          refine ⟨1300816485996955862324747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13875375850634195864797301 1300816485996955862324747)
          ·
            refine ⟨1951224728995433793487121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300816485996955862324747 1951224728995433793487121)
            ·
              refine ⟨1463418546746575345115341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951224728995433793487121 1463418546746575345115341)
              ·
                refine ⟨548781955029965754418253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1463418546746575345115341 548781955029965754418253)
                ·
                  refine ⟨205793233136237157906845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548781955029965754418253 205793233136237157906845)
                  ·
                    rfl

theorem cell21_901757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_901757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901757 prefixEnd_901757 := by exact prefixLift 901757
  have htrace : WordTrace (prefixWord ++ tailWord_901757) baseStart_901757 baseEnd_901757 := by
    simpa [prefixWord, tailWord_901757, baseEnd_901757] using wordTrace_append hprefix tailTrace_901757
  have hstable : (prefixWord ++ tailWord_901757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901757).length < 2 ^ (prefixWord ++ tailWord_901757).sum := by decide
  have hdescent : baseEnd_901757 < baseStart_901757 := by decide
  rcases family_descends (prefixWord ++ tailWord_901757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901802 : List Nat := [3, 1, 5, 2, 1, 1, 1, 7]
def baseStart_901802 : Nat := 118140960795 + 901802 * 2 ^ 59
def prefixEnd_901802 : Nat := 4983230072969 + 3 ^ 40 * 901802 * 2
def baseEnd_901802 : Nat := 68601167583109026552251

theorem tailTrace_901802 : CollatzResearch.WordTrace tailWord_901802 prefixEnd_901802 68601167583109026552251 := by
  unfold tailWord_901802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222855269733211091226915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21927614052621896243271773 8222855269733211091226915)
  ·
    refine ⟨12334282904599816636840373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8222855269733211091226915 12334282904599816636840373)
    ·
      refine ⟨1156339022306232809703785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12334282904599816636840373 1156339022306232809703785)
      ·
        refine ⟨867254266729674607277839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1156339022306232809703785 867254266729674607277839)
        ·
          refine ⟨1300881400094511910916759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867254266729674607277839 1300881400094511910916759)
          ·
            refine ⟨1951322100141767866375139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300881400094511910916759 1951322100141767866375139)
            ·
              refine ⟨2926983150212651799562709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951322100141767866375139 2926983150212651799562709)
              ·
                refine ⟨68601167583109026552251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2926983150212651799562709 68601167583109026552251)
                ·
                  rfl

theorem cell21_901802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_901802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901802 prefixEnd_901802 := by exact prefixLift 901802
  have htrace : WordTrace (prefixWord ++ tailWord_901802) baseStart_901802 baseEnd_901802 := by
    simpa [prefixWord, tailWord_901802, baseEnd_901802] using wordTrace_append hprefix tailTrace_901802
  have hstable : (prefixWord ++ tailWord_901802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901802).length < 2 ^ (prefixWord ++ tailWord_901802).sum := by decide
  have hdescent : baseEnd_901802 < baseStart_901802 := by decide
  rcases family_descends (prefixWord ++ tailWord_901802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901847 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 4]
def baseStart_901847 : Nat := 118140960795 + 901847 * 2 ^ 59
def prefixEnd_901847 : Nat := 4983230072969 + 3 ^ 40 * 901847 * 2
def baseEnd_901847 : Nat := 205813772362417001406661

theorem tailTrace_901847 : CollatzResearch.WordTrace tailWord_901847 prefixEnd_901847 205813772362417001406661 := by
  unfold tailWord_901847
  simp only [CollatzResearch.WordTrace]
  refine ⟨32893062363769817050295795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21928708242513211366863863 32893062363769817050295795)
  ·
    refine ⟨49339593545654725575443693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32893062363769817050295795 49339593545654725575443693)
    ·
      refine ⟨18502347579620522090791385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49339593545654725575443693 18502347579620522090791385)
      ·
        refine ⟨13876760684715391568093539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18502347579620522090791385 13876760684715391568093539)
        ·
          refine ⟨20815141027073087352140309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13876760684715391568093539 20815141027073087352140309)
          ·
            refine ⟨975709735644050969631577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20815141027073087352140309 975709735644050969631577)
            ·
              refine ⟨731782301733038227223683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 975709735644050969631577 731782301733038227223683)
              ·
                refine ⟨1097673452599557340835525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731782301733038227223683 1097673452599557340835525)
                ·
                  refine ⟨205813772362417001406661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097673452599557340835525 205813772362417001406661)
                  ·
                    rfl

theorem cell21_901847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 4].length) (baseStart_901847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901847 prefixEnd_901847 := by exact prefixLift 901847
  have htrace : WordTrace (prefixWord ++ tailWord_901847) baseStart_901847 baseEnd_901847 := by
    simpa [prefixWord, tailWord_901847, baseEnd_901847] using wordTrace_append hprefix tailTrace_901847
  have hstable : (prefixWord ++ tailWord_901847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901847).length < 2 ^ (prefixWord ++ tailWord_901847).sum := by decide
  have hdescent : baseEnd_901847 < baseStart_901847 := by decide
  rcases family_descends (prefixWord ++ tailWord_901847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901875 : List Nat := [1, 1, 1, 2, 2, 3, 1, 7, 3]
def baseStart_901875 : Nat := 118140960795 + 901875 * 2 ^ 59
def prefixEnd_901875 : Nat := 4983230072969 + 3 ^ 40 * 901875 * 2
def baseEnd_901875 : Nat := 205820162343895174939937

theorem tailTrace_901875 : CollatzResearch.WordTrace tailWord_901875 prefixEnd_901875 205820162343895174939937 := by
  unfold tailWord_901875
  simp only [CollatzResearch.WordTrace]
  refine ⟨32894083607668377832315079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21929389071778918554876719 32894083607668377832315079)
  ·
    refine ⟨49341125411502566748472619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32894083607668377832315079 49341125411502566748472619)
    ·
      refine ⟨74011688117253850122708929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49341125411502566748472619 74011688117253850122708929)
      ·
        refine ⟨55508766087940387592031697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74011688117253850122708929 55508766087940387592031697)
        ·
          refine ⟨41631574565955290694023773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55508766087940387592031697 41631574565955290694023773)
          ·
            refine ⟨15611840462233234010258915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41631574565955290694023773 15611840462233234010258915)
            ·
              refine ⟨23417760693349851015388373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15611840462233234010258915 23417760693349851015388373)
              ·
                refine ⟨548853766250387133173165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23417760693349851015388373 548853766250387133173165)
                ·
                  refine ⟨205820162343895174939937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548853766250387133173165 205820162343895174939937)
                  ·
                    rfl

theorem cell21_901875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 7, 3].length) (baseStart_901875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901875 prefixEnd_901875 := by exact prefixLift 901875
  have htrace : WordTrace (prefixWord ++ tailWord_901875) baseStart_901875 baseEnd_901875 := by
    simpa [prefixWord, tailWord_901875, baseEnd_901875] using wordTrace_append hprefix tailTrace_901875
  have hstable : (prefixWord ++ tailWord_901875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901875).length < 2 ^ (prefixWord ++ tailWord_901875).sum := by decide
  have hdescent : baseEnd_901875 < baseStart_901875 := by decide
  rcases family_descends (prefixWord ++ tailWord_901875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901892 : List Nat := [2, 3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_901892 : Nat := 118140960795 + 901892 * 2 ^ 59
def prefixEnd_901892 : Nat := 4983230072969 + 3 ^ 40 * 901892 * 2
def baseEnd_901892 : Nat := 205824041975506923156569

theorem tailTrace_901892 : CollatzResearch.WordTrace tailWord_901892 prefixEnd_901892 205824041975506923156569 := by
  unfold tailWord_901892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16447351824303394867841965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21929802432404526490455953 16447351824303394867841965)
  ·
    refine ⟨6167756934113773075440737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16447351824303394867841965 6167756934113773075440737)
    ·
      refine ⟨4625817700585329806580553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6167756934113773075440737 4625817700585329806580553)
      ·
        refine ⟨3469363275438997354935415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4625817700585329806580553 3469363275438997354935415)
        ·
          refine ⟨5204044913158496032403123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3469363275438997354935415 5204044913158496032403123)
          ·
            refine ⟨7806067369737744048604685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5204044913158496032403123 7806067369737744048604685)
            ·
              refine ⟨2927275263651654018226757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7806067369737744048604685 2927275263651654018226757)
              ·
                refine ⟨548864111934685128417517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2927275263651654018226757 548864111934685128417517)
                ·
                  refine ⟨205824041975506923156569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 548864111934685128417517 205824041975506923156569)
                  ·
                    rfl

theorem cell21_901892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_901892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901892 prefixEnd_901892 := by exact prefixLift 901892
  have htrace : WordTrace (prefixWord ++ tailWord_901892) baseStart_901892 baseEnd_901892 := by
    simpa [prefixWord, tailWord_901892, baseEnd_901892] using wordTrace_append hprefix tailTrace_901892
  have hstable : (prefixWord ++ tailWord_901892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901892).length < 2 ^ (prefixWord ++ tailWord_901892).sum := by decide
  have hdescent : baseEnd_901892 < baseStart_901892 := by decide
  rcases family_descends (prefixWord ++ tailWord_901892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901940 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_901940 : Nat := 118140960795 + 901940 * 2 ^ 59
def prefixEnd_901940 : Nat := 4983230072969 + 3 ^ 40 * 901940 * 2
def baseEnd_901940 : Nat := 205834996229469506356471

theorem tailTrace_901940 : CollatzResearch.WordTrace tailWord_901940 prefixEnd_901940 205834996229469506356471 := by
  unfold tailWord_901940
  simp only [CollatzResearch.WordTrace]
  refine ⟨16448227176216446966715637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21930969568288595955620849 16448227176216446966715637)
  ·
    refine ⟨1542021297770291903129591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16448227176216446966715637 1542021297770291903129591)
    ·
      refine ⟨2313031946655437854694387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1542021297770291903129591 2313031946655437854694387)
      ·
        refine ⟨3469547919983156782041581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313031946655437854694387 3469547919983156782041581)
        ·
          refine ⟨1301080469993683793265593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3469547919983156782041581 1301080469993683793265593)
          ·
            refine ⟨975810352495262844949195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301080469993683793265593 975810352495262844949195)
            ·
              refine ⟨1463715528742894267423793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975810352495262844949195 1463715528742894267423793)
              ·
                refine ⟨1097786646557170700567845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1463715528742894267423793 1097786646557170700567845)
                ·
                  refine ⟨205834996229469506356471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1097786646557170700567845 205834996229469506356471)
                  ·
                    rfl

theorem cell21_901940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_901940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901940 prefixEnd_901940 := by exact prefixLift 901940
  have htrace : WordTrace (prefixWord ++ tailWord_901940) baseStart_901940 baseEnd_901940 := by
    simpa [prefixWord, tailWord_901940, baseEnd_901940] using wordTrace_append hprefix tailTrace_901940
  have hstable : (prefixWord ++ tailWord_901940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901940).length < 2 ^ (prefixWord ++ tailWord_901940).sum := by decide
  have hdescent : baseEnd_901940 < baseStart_901940 := by decide
  rcases family_descends (prefixWord ++ tailWord_901940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_901951 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 5]
def baseStart_901951 : Nat := 118140960795 + 901951 * 2 ^ 59
def prefixEnd_901951 : Nat := 4983230072969 + 3 ^ 40 * 901951 * 2
def baseEnd_901951 : Nat := 205837506579335931673115

theorem tailTrace_901951 : CollatzResearch.WordTrace tailWord_901951 prefixEnd_901951 205837506579335931673115 := by
  unfold tailWord_901951
  simp only [CollatzResearch.WordTrace]
  refine ⟨32896855555393042812081707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21931237036928695208054471 32896855555393042812081707)
  ·
    refine ⟨49345283333089564218122561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32896855555393042812081707 49345283333089564218122561)
    ·
      refine ⟨37008962499817173163591921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49345283333089564218122561 37008962499817173163591921)
      ·
        refine ⟨27756721874862879872693941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37008962499817173163591921 27756721874862879872693941)
        ·
          refine ⟨2602192675768394988065057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27756721874862879872693941 2602192675768394988065057)
          ·
            refine ⟨1951644506826296241048793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2602192675768394988065057 1951644506826296241048793)
            ·
              refine ⟨1463733380119722180786595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1951644506826296241048793 1463733380119722180786595)
              ·
                refine ⟨2195600070179583271179893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463733380119722180786595 2195600070179583271179893)
                ·
                  refine ⟨205837506579335931673115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2195600070179583271179893 205837506579335931673115)
                  ·
                    rfl

theorem cell21_901951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_901951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_901951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_901951 prefixEnd_901951 := by exact prefixLift 901951
  have htrace : WordTrace (prefixWord ++ tailWord_901951) baseStart_901951 baseEnd_901951 := by
    simpa [prefixWord, tailWord_901951, baseEnd_901951] using wordTrace_append hprefix tailTrace_901951
  have hstable : (prefixWord ++ tailWord_901951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_901951).length < 2 ^ (prefixWord ++ tailWord_901951).sum := by decide
  have hdescent : baseEnd_901951 < baseStart_901951 := by decide
  rcases family_descends (prefixWord ++ tailWord_901951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902055 : List Nat := [1, 1, 6, 1, 12]
def baseStart_902055 : Nat := 118140960795 + 902055 * 2 ^ 59
def prefixEnd_902055 : Nat := 4983230072969 + 3 ^ 40 * 902055 * 2
def baseEnd_902055 : Nat := 2541496799953763727649

theorem tailTrace_902055 : CollatzResearch.WordTrace tailWord_902055 prefixEnd_902055 2541496799953763727649 := by
  unfold tailWord_902055
  simp only [CollatzResearch.WordTrace]
  refine ⟨32900648747016268573867619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21933765831344179049245079 32900648747016268573867619)
  ·
    refine ⟨49350973120524402860801429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32900648747016268573867619 49350973120524402860801429)
    ·
      refine ⟨2313326865024581384100067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49350973120524402860801429 2313326865024581384100067)
      ·
        refine ⟨3469990297536872076150101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2313326865024581384100067 3469990297536872076150101)
        ·
          refine ⟨2541496799953763727649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3469990297536872076150101 2541496799953763727649)
          ·
            rfl

theorem cell21_902055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 12].length) (baseStart_902055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902055 prefixEnd_902055 := by exact prefixLift 902055
  have htrace : WordTrace (prefixWord ++ tailWord_902055) baseStart_902055 baseEnd_902055 := by
    simpa [prefixWord, tailWord_902055, baseEnd_902055] using wordTrace_append hprefix tailTrace_902055
  have hstable : (prefixWord ++ tailWord_902055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902055).length < 2 ^ (prefixWord ++ tailWord_902055).sum := by decide
  have hdescent : baseEnd_902055 < baseStart_902055 := by decide
  rcases family_descends (prefixWord ++ tailWord_902055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902072 : List Nat := [2, 1, 2, 1, 2, 6, 1, 6]
def baseStart_902072 : Nat := 118140960795 + 902072 * 2 ^ 59
def prefixEnd_902072 : Nat := 4983230072969 + 3 ^ 40 * 902072 * 2
def baseEnd_902072 : Nat := 68621706809288870052067

theorem tailTrace_902072 : CollatzResearch.WordTrace tailWord_902072 prefixEnd_902072 68621706809288870052067 := by
  unfold tailWord_902072
  simp only [CollatzResearch.WordTrace]
  refine ⟨16450634393977340238618235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21934179191969786984824313 16450634393977340238618235)
  ·
    refine ⟨24675951590966010357927353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16450634393977340238618235 24675951590966010357927353)
    ·
      refine ⟨18506963693224507768445515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24675951590966010357927353 18506963693224507768445515)
      ·
        refine ⟨27760445539836761652668273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18506963693224507768445515 27760445539836761652668273)
        ·
          refine ⟨20820334154877571239501205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27760445539836761652668273 20820334154877571239501205)
          ·
            refine ⟨975953163509886151851619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20820334154877571239501205 975953163509886151851619)
            ·
              refine ⟨1463929745264829227777429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975953163509886151851619 1463929745264829227777429)
              ·
                refine ⟨68621706809288870052067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1463929745264829227777429 68621706809288870052067)
                ·
                  rfl

theorem cell21_902072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_902072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902072 prefixEnd_902072 := by exact prefixLift 902072
  have htrace : WordTrace (prefixWord ++ tailWord_902072) baseStart_902072 baseEnd_902072 := by
    simpa [prefixWord, tailWord_902072, baseEnd_902072] using wordTrace_append hprefix tailTrace_902072
  have hstable : (prefixWord ++ tailWord_902072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902072).length < 2 ^ (prefixWord ++ tailWord_902072).sum := by decide
  have hdescent : baseEnd_902072 < baseStart_902072 := by decide
  rcases family_descends (prefixWord ++ tailWord_902072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902179 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 5]
def baseStart_902179 : Nat := 118140960795 + 902179 * 2 ^ 59
def prefixEnd_902179 : Nat := 4983230072969 + 3 ^ 40 * 902179 * 2
def baseEnd_902179 : Nat := 205889539285658201872649

theorem tailTrace_902179 : CollatzResearch.WordTrace tailWord_902179 prefixEnd_902179 205889539285658201872649 := by
  unfold tailWord_902179
  simp only [CollatzResearch.WordTrace]
  refine ⟨32905171398567037751381591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21936780932378025167587727 32905171398567037751381591)
  ·
    refine ⟨49357757097850556627072387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32905171398567037751381591 49357757097850556627072387)
    ·
      refine ⟨74036635646775834940608581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49357757097850556627072387 74036635646775834940608581)
      ·
        refine ⟨13881869183770469051364109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74036635646775834940608581 13881869183770469051364109)
        ·
          refine ⟨5205700943913925894261541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13881869183770469051364109 5205700943913925894261541)
          ·
            refine ⟨976068926983861105174039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5205700943913925894261541 976068926983861105174039)
            ·
              refine ⟨1464103390475791657761059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976068926983861105174039 1464103390475791657761059)
              ·
                refine ⟨2196155085713687486641589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464103390475791657761059 2196155085713687486641589)
                ·
                  refine ⟨205889539285658201872649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2196155085713687486641589 205889539285658201872649)
                  ·
                    rfl

theorem cell21_902179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 5].length) (baseStart_902179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902179 prefixEnd_902179 := by exact prefixLift 902179
  have htrace : WordTrace (prefixWord ++ tailWord_902179) baseStart_902179 baseEnd_902179 := by
    simpa [prefixWord, tailWord_902179, baseEnd_902179] using wordTrace_append hprefix tailTrace_902179
  have hstable : (prefixWord ++ tailWord_902179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902179).length < 2 ^ (prefixWord ++ tailWord_902179).sum := by decide
  have hdescent : baseEnd_902179 < baseStart_902179 := by decide
  rcases family_descends (prefixWord ++ tailWord_902179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902193 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 4]
def baseStart_902193 : Nat := 118140960795 + 902193 * 2 ^ 59
def prefixEnd_902193 : Nat := 4983230072969 + 3 ^ 40 * 902193 * 2
def baseEnd_902193 : Nat := 205892734276397288639287

theorem tailTrace_902193 : CollatzResearch.WordTrace tailWord_902193 prefixEnd_902193 205892734276397288639287 := by
  unfold tailWord_902193
  simp only [CollatzResearch.WordTrace]
  refine ⟨32905682020516318142391233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21937121347010878761594155 32905682020516318142391233)
  ·
    refine ⟨24679261515387238606793425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32905682020516318142391233 24679261515387238606793425)
    ·
      refine ⟨18509446136540428955095069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24679261515387238606793425 18509446136540428955095069)
      ·
        refine ⟨6941042301202660858160651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18509446136540428955095069 6941042301202660858160651)
        ·
          refine ⟨10411563451803991287240977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6941042301202660858160651 10411563451803991287240977)
          ·
            refine ⟨7808672588852993465430733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10411563451803991287240977 7808672588852993465430733)
            ·
              refine ⟨2928252220819872549536525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7808672588852993465430733 2928252220819872549536525)
              ·
                refine ⟨1098094582807452206076197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2928252220819872549536525 1098094582807452206076197)
                ·
                  refine ⟨205892734276397288639287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098094582807452206076197 205892734276397288639287)
                  ·
                    rfl

theorem cell21_902193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 4].length) (baseStart_902193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902193 prefixEnd_902193 := by exact prefixLift 902193
  have htrace : WordTrace (prefixWord ++ tailWord_902193) baseStart_902193 baseEnd_902193 := by
    simpa [prefixWord, tailWord_902193, baseEnd_902193] using wordTrace_append hprefix tailTrace_902193
  have hstable : (prefixWord ++ tailWord_902193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902193).length < 2 ^ (prefixWord ++ tailWord_902193).sum := by decide
  have hdescent : baseEnd_902193 < baseStart_902193 := by decide
  rcases family_descends (prefixWord ++ tailWord_902193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902230 : List Nat := [5, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_902230 : Nat := 118140960795 + 902230 * 2 ^ 59
def prefixEnd_902230 : Nat := 4983230072969 + 3 ^ 40 * 902230 * 2
def baseEnd_902230 : Nat := 205901178180493446522545

theorem tailTrace_902230 : CollatzResearch.WordTrace tailWord_902230 prefixEnd_902230 205901178180493446522545 := by
  unfold tailWord_902230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056689470086392091343009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21938021014254848974325429 2056689470086392091343009)
  ·
    refine ⟨1542517102564794068507257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2056689470086392091343009 1542517102564794068507257)
    ·
      refine ⟨1156887826923595551380443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542517102564794068507257 1156887826923595551380443)
      ·
        refine ⟨1735331740385393327070665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156887826923595551380443 1735331740385393327070665)
        ·
          refine ⟨1301498805289044995302999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1735331740385393327070665 1301498805289044995302999)
          ·
            refine ⟨1952248207933567492954499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301498805289044995302999 1952248207933567492954499)
            ·
              refine ⟨2928372311900351239431749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952248207933567492954499 2928372311900351239431749)
              ·
                refine ⟨549069808481315857393453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2928372311900351239431749 549069808481315857393453)
                ·
                  refine ⟨205901178180493446522545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549069808481315857393453 205901178180493446522545)
                  ·
                    rfl

theorem cell21_902230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_902230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902230 prefixEnd_902230 := by exact prefixLift 902230
  have htrace : WordTrace (prefixWord ++ tailWord_902230) baseStart_902230 baseEnd_902230 := by
    simpa [prefixWord, tailWord_902230, baseEnd_902230] using wordTrace_append hprefix tailTrace_902230
  have hstable : (prefixWord ++ tailWord_902230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902230).length < 2 ^ (prefixWord ++ tailWord_902230).sum := by decide
  have hdescent : baseEnd_902230 < baseStart_902230 := by decide
  rcases family_descends (prefixWord ++ tailWord_902230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902286 : List Nat := [4, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_902286 : Nat := 118140960795 + 902286 * 2 ^ 59
def prefixEnd_902286 : Nat := 4983230072969 + 3 ^ 40 * 902286 * 2
def baseEnd_902286 : Nat := 205913958143449793589097

theorem tailTrace_902286 : CollatzResearch.WordTrace tailWord_902286 prefixEnd_902286 205913958143449793589097 := by
  unfold tailWord_902286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113634251147424378190839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21939382672786263350351141 4113634251147424378190839)
  ·
    refine ⟨6170451376721136567286259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4113634251147424378190839 6170451376721136567286259)
    ·
      refine ⟨9255677065081704850929389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6170451376721136567286259 9255677065081704850929389)
      ·
        refine ⟨3470878899405639319098521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9255677065081704850929389 3470878899405639319098521)
        ·
          refine ⟨2603159174554229489323891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3470878899405639319098521 2603159174554229489323891)
          ·
            refine ⟨3904738761831344233985837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603159174554229489323891 3904738761831344233985837)
            ·
              refine ⟨1464277035686754087744689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3904738761831344233985837 1464277035686754087744689)
              ·
                refine ⟨1098207776765065565808517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1464277035686754087744689 1098207776765065565808517)
                ·
                  refine ⟨205913958143449793589097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098207776765065565808517 205913958143449793589097)
                  ·
                    rfl

theorem cell21_902286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_902286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902286 prefixEnd_902286 := by exact prefixLift 902286
  have htrace : WordTrace (prefixWord ++ tailWord_902286) baseStart_902286 baseEnd_902286 := by
    simpa [prefixWord, tailWord_902286, baseEnd_902286] using wordTrace_append hprefix tailTrace_902286
  have hstable : (prefixWord ++ tailWord_902286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902286).length < 2 ^ (prefixWord ++ tailWord_902286).sum := by decide
  have hdescent : baseEnd_902286 < baseStart_902286 := by decide
  rcases family_descends (prefixWord ++ tailWord_902286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902303 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 4]
def baseStart_902303 : Nat := 118140960795 + 902303 * 2 ^ 59
def prefixEnd_902303 : Nat := 4983230072969 + 3 ^ 40 * 902303 * 2
def baseEnd_902303 : Nat := 205917837775061541805729

theorem tailTrace_902303 : CollatzResearch.WordTrace tailWord_902303 prefixEnd_902303 205917837775061541805729 := by
  unfold tailWord_902303
  simp only [CollatzResearch.WordTrace]
  refine ⟨32909694050117806928895563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21939796033411871285930375 32909694050117806928895563)
  ·
    refine ⟨49364541075176710393343345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32909694050117806928895563 49364541075176710393343345)
    ·
      refine ⟨37023405806382532795007509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49364541075176710393343345 37023405806382532795007509)
      ·
        refine ⟨1735472147174181224765977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37023405806382532795007509 1735472147174181224765977)
        ·
          refine ⟨1301604110380635918574483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1735472147174181224765977 1301604110380635918574483)
          ·
            refine ⟨1952406165570953877861725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301604110380635918574483 1952406165570953877861725)
            ·
              refine ⟨732152312089107704198147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1952406165570953877861725 732152312089107704198147)
              ·
                refine ⟨1098228468133661556297221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732152312089107704198147 1098228468133661556297221)
                ·
                  refine ⟨205917837775061541805729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098228468133661556297221 205917837775061541805729)
                  ·
                    rfl

theorem cell21_902303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 4].length) (baseStart_902303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902303 prefixEnd_902303 := by exact prefixLift 902303
  have htrace : WordTrace (prefixWord ++ tailWord_902303) baseStart_902303 baseEnd_902303 := by
    simpa [prefixWord, tailWord_902303, baseEnd_902303] using wordTrace_append hprefix tailTrace_902303
  have hstable : (prefixWord ++ tailWord_902303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902303).length < 2 ^ (prefixWord ++ tailWord_902303).sum := by decide
  have hdescent : baseEnd_902303 < baseStart_902303 := by decide
  rcases family_descends (prefixWord ++ tailWord_902303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902500 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_902500 : Nat := 118140960795 + 902500 * 2 ^ 59
def prefixEnd_902500 : Nat := 4983230072969 + 3 ^ 40 * 902500 * 2
def baseEnd_902500 : Nat := 205962795859032977021993

theorem tailTrace_902500 : CollatzResearch.WordTrace tailWord_902500 prefixEnd_902500 205962795859032977021993 := by
  unfold tailWord_902500
  simp only [CollatzResearch.WordTrace]
  refine ⟨16458439615202054786908477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21944586153602739715877969 16458439615202054786908477)
  ·
    refine ⟨6171914855700770545090679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16458439615202054786908477 6171914855700770545090679)
    ·
      refine ⟨9257872283551155817636019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6171914855700770545090679 9257872283551155817636019)
      ·
        refine ⟨13886808425326733726454029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9257872283551155817636019 13886808425326733726454029)
        ·
          refine ⟨5207553159497525147420261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13886808425326733726454029 5207553159497525147420261)
          ·
            refine ⟨976416217405785965141299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5207553159497525147420261 976416217405785965141299)
            ·
              refine ⟨1464624326108678947711949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976416217405785965141299 1464624326108678947711949)
              ·
                refine ⟨549234122290754605391981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1464624326108678947711949 549234122290754605391981)
                ·
                  refine ⟨205962795859032977021993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549234122290754605391981 205962795859032977021993)
                  ·
                    rfl

theorem cell21_902500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_902500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902500 prefixEnd_902500 := by exact prefixLift 902500
  have htrace : WordTrace (prefixWord ++ tailWord_902500) baseStart_902500 baseEnd_902500 := by
    simpa [prefixWord, tailWord_902500, baseEnd_902500] using wordTrace_append hprefix tailTrace_902500
  have hstable : (prefixWord ++ tailWord_902500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902500).length < 2 ^ (prefixWord ++ tailWord_902500).sum := by decide
  have hdescent : baseEnd_902500 < baseStart_902500 := by decide
  rcases family_descends (prefixWord ++ tailWord_902500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902517 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 3]
def baseStart_902517 : Nat := 118140960795 + 902517 * 2 ^ 59
def prefixEnd_902517 : Nat := 4983230072969 + 3 ^ 40 * 902517 * 2
def baseEnd_902517 : Nat := 205966675490644725238625

theorem tailTrace_902517 : CollatzResearch.WordTrace tailWord_902517 prefixEnd_902517 205966675490644725238625 := by
  unfold tailWord_902517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32917499271342521477185805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21944999514228347651457203 32917499271342521477185805)
  ·
    refine ⟨12344062226753445553944677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32917499271342521477185805 12344062226753445553944677)
    ·
      refine ⟨2314511667516271041364627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12344062226753445553944677 2314511667516271041364627)
      ·
        refine ⟨3471767501274406562046941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2314511667516271041364627 3471767501274406562046941)
        ·
          refine ⟨1301912812977902460767603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3471767501274406562046941 1301912812977902460767603)
          ·
            refine ⟨1952869219466853691151405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301912812977902460767603 1952869219466853691151405)
            ·
              refine ⟨732325957300070134181777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1952869219466853691151405 732325957300070134181777)
              ·
                refine ⟨549244467975052600636333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732325957300070134181777 549244467975052600636333)
                ·
                  refine ⟨205966675490644725238625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549244467975052600636333 205966675490644725238625)
                  ·
                    rfl

theorem cell21_902517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_902517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902517 prefixEnd_902517 := by exact prefixLift 902517
  have htrace : WordTrace (prefixWord ++ tailWord_902517) baseStart_902517 baseEnd_902517 := by
    simpa [prefixWord, tailWord_902517, baseEnd_902517] using wordTrace_append hprefix tailTrace_902517
  have hstable : (prefixWord ++ tailWord_902517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902517).length < 2 ^ (prefixWord ++ tailWord_902517).sum := by decide
  have hdescent : baseEnd_902517 < baseStart_902517 := by decide
  rcases family_descends (prefixWord ++ tailWord_902517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902604 : List Nat := [2, 2, 1, 4, 2, 2, 3, 5]
def baseStart_902604 : Nat := 118140960795 + 902604 * 2 ^ 59
def prefixEnd_902604 : Nat := 4983230072969 + 3 ^ 40 * 902604 * 2
def baseEnd_902604 : Nat := 68662176691983969096149

theorem tailTrace_902604 : CollatzResearch.WordTrace tailWord_902604 prefixEnd_902604 68662176691983969096149 := by
  unfold tailWord_902604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460336211013667667801433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21947114948018223557068577 16460336211013667667801433)
  ·
    refine ⟨12345252158260250750851075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16460336211013667667801433 12345252158260250750851075)
    ·
      refine ⟨18517878237390376126276613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12345252158260250750851075 18517878237390376126276613)
      ·
        refine ⟨3472102169510695523676865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18517878237390376126276613 3472102169510695523676865)
        ·
          refine ⟨2604076627133021642757649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472102169510695523676865 2604076627133021642757649)
          ·
            refine ⟨1953057470349766232068237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604076627133021642757649 1953057470349766232068237)
            ·
              refine ⟨732396551381162337025589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953057470349766232068237 732396551381162337025589)
              ·
                refine ⟨68662176691983969096149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 732396551381162337025589 68662176691983969096149)
                ·
                  rfl

theorem cell21_902604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 5].length) (baseStart_902604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902604 prefixEnd_902604 := by exact prefixLift 902604
  have htrace : WordTrace (prefixWord ++ tailWord_902604) baseStart_902604 baseEnd_902604 := by
    simpa [prefixWord, tailWord_902604, baseEnd_902604] using wordTrace_append hprefix tailTrace_902604
  have hstable : (prefixWord ++ tailWord_902604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902604).length < 2 ^ (prefixWord ++ tailWord_902604).sum := by decide
  have hdescent : baseEnd_902604 < baseStart_902604 := by decide
  rcases family_descends (prefixWord ++ tailWord_902604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902632 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_902632 : Nat := 118140960795 + 902632 * 2 ^ 59
def prefixEnd_902632 : Nat := 4983230072969 + 3 ^ 40 * 902632 * 2
def baseEnd_902632 : Nat := 205992920057430080821723

theorem tailTrace_902632 : CollatzResearch.WordTrace tailWord_902632 prefixEnd_902632 205992920057430080821723 := by
  unfold tailWord_902632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16460846832962948058811075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21947795777283930745081433 16460846832962948058811075)
  ·
    refine ⟨24691270249444422088216613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16460846832962948058811075 24691270249444422088216613)
    ·
      refine ⟨4629613171770829141540615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24691270249444422088216613 4629613171770829141540615)
      ·
        refine ⟨6944419757656243712310923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4629613171770829141540615 6944419757656243712310923)
        ·
          refine ⟨10416629636484365568466385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6944419757656243712310923 10416629636484365568466385)
          ·
            refine ⟨7812472227363274176349789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10416629636484365568466385 7812472227363274176349789)
            ·
              refine ⟨2929677085261227816131171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7812472227363274176349789 2929677085261227816131171)
              ·
                refine ⟨4394515627891841724196757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929677085261227816131171 4394515627891841724196757)
                ·
                  refine ⟨205992920057430080821723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4394515627891841724196757 205992920057430080821723)
                  ·
                    rfl

theorem cell21_902632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_902632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902632 prefixEnd_902632 := by exact prefixLift 902632
  have htrace : WordTrace (prefixWord ++ tailWord_902632) baseStart_902632 baseEnd_902632 := by
    simpa [prefixWord, tailWord_902632, baseEnd_902632] using wordTrace_append hprefix tailTrace_902632
  have hstable : (prefixWord ++ tailWord_902632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902632).length < 2 ^ (prefixWord ++ tailWord_902632).sum := by decide
  have hdescent : baseEnd_902632 < baseStart_902632 := by decide
  rcases family_descends (prefixWord ++ tailWord_902632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902663 : List Nat := [1, 1, 4, 3, 2, 2, 1, 7]
def baseStart_902663 : Nat := 118140960795 + 902663 * 2 ^ 59
def prefixEnd_902663 : Nat := 4983230072969 + 3 ^ 40 * 902663 * 2
def baseEnd_902663 : Nat := 68666664893260305268331

theorem tailTrace_902663 : CollatzResearch.WordTrace tailWord_902663 prefixEnd_902663 68666664893260305268331 := by
  unfold tailWord_902663
  simp only [CollatzResearch.WordTrace]
  refine ⟨32922824328813588412000643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21948549552542392274667095 32922824328813588412000643)
  ·
    refine ⟨49384236493220382618000965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32922824328813588412000643 49384236493220382618000965)
    ·
      refine ⟨9259544342478821740875181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49384236493220382618000965 9259544342478821740875181)
      ·
        refine ⟨3472329128429558152828193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9259544342478821740875181 3472329128429558152828193)
        ·
          refine ⟨2604246846322168614621145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3472329128429558152828193 2604246846322168614621145)
          ·
            refine ⟨1953185134741626460965859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604246846322168614621145 1953185134741626460965859)
            ·
              refine ⟨2929777702112439691448789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953185134741626460965859 2929777702112439691448789)
              ·
                refine ⟨68666664893260305268331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2929777702112439691448789 68666664893260305268331)
                ·
                  rfl

theorem cell21_902663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_902663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902663 prefixEnd_902663 := by exact prefixLift 902663
  have htrace : WordTrace (prefixWord ++ tailWord_902663) baseStart_902663 baseEnd_902663 := by
    simpa [prefixWord, tailWord_902663, baseEnd_902663] using wordTrace_append hprefix tailTrace_902663
  have hstable : (prefixWord ++ tailWord_902663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902663).length < 2 ^ (prefixWord ++ tailWord_902663).sum := by decide
  have hdescent : baseEnd_902663 < baseStart_902663 := by decide
  rcases family_descends (prefixWord ++ tailWord_902663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902680 : List Nat := [2, 1, 2, 3, 5, 1, 7]
def baseStart_902680 : Nat := 118140960795 + 902680 * 2 ^ 59
def prefixEnd_902680 : Nat := 4983230072969 + 3 ^ 40 * 902680 * 2
def baseEnd_902680 : Nat := 22889319367932518224625

theorem tailTrace_902680 : CollatzResearch.WordTrace tailWord_902680 prefixEnd_902680 22889319367932518224625 := by
  unfold tailWord_902680
  simp only [CollatzResearch.WordTrace]
  refine ⟨16461722184876000157684747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21948962913168000210246329 16461722184876000157684747)
  ·
    refine ⟨24692583277314000236527121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16461722184876000157684747 24692583277314000236527121)
    ·
      refine ⟨18519437457985500177395341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24692583277314000236527121 18519437457985500177395341)
      ·
        refine ⟨6944789046744562566523253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18519437457985500177395341 6944789046744562566523253)
        ·
          refine ⟨651073973132302740611555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6944789046744562566523253 651073973132302740611555)
          ·
            refine ⟨976610959698454110917333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651073973132302740611555 976610959698454110917333)
            ·
              refine ⟨22889319367932518224625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 976610959698454110917333 22889319367932518224625)
              ·
                rfl

theorem cell21_902680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 7].length) (baseStart_902680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902680 prefixEnd_902680 := by exact prefixLift 902680
  have htrace : WordTrace (prefixWord ++ tailWord_902680) baseStart_902680 baseEnd_902680 := by
    simpa [prefixWord, tailWord_902680, baseEnd_902680] using wordTrace_append hprefix tailTrace_902680
  have hstable : (prefixWord ++ tailWord_902680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902680).length < 2 ^ (prefixWord ++ tailWord_902680).sum := by decide
  have hdescent : baseEnd_902680 < baseStart_902680 := by decide
  rcases family_descends (prefixWord ++ tailWord_902680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902686 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_902686 : Nat := 118140960795 + 902686 * 2 ^ 59
def prefixEnd_902686 : Nat := 4983230072969 + 3 ^ 40 * 902686 * 2
def baseEnd_902686 : Nat := 206005243593137986921613

theorem tailTrace_902686 : CollatzResearch.WordTrace tailWord_902686 prefixEnd_902686 206005243593137986921613 := by
  unfold tailWord_902686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4115457900966282917510989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21949108805153508893391941 4115457900966282917510989)
  ·
    refine ⟨1543296712862356094066621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4115457900966282917510989 1543296712862356094066621)
    ·
      refine ⟨578736267323383535274983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1543296712862356094066621 578736267323383535274983)
      ·
        refine ⟨868104400985075302912475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578736267323383535274983 868104400985075302912475)
        ·
          refine ⟨1302156601477612954368713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868104400985075302912475 1302156601477612954368713)
          ·
            refine ⟨976617451108209715776535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1302156601477612954368713 976617451108209715776535)
            ·
              refine ⟨1464926176662314573664803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976617451108209715776535 1464926176662314573664803)
              ·
                refine ⟨2197389264993471860497205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464926176662314573664803 2197389264993471860497205)
                ·
                  refine ⟨206005243593137986921613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2197389264993471860497205 206005243593137986921613)
                  ·
                    rfl

theorem cell21_902686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_902686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902686 prefixEnd_902686 := by exact prefixLift 902686
  have htrace : WordTrace (prefixWord ++ tailWord_902686) baseStart_902686 baseEnd_902686 := by
    simpa [prefixWord, tailWord_902686, baseEnd_902686] using wordTrace_append hprefix tailTrace_902686
  have hstable : (prefixWord ++ tailWord_902686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902686).length < 2 ^ (prefixWord ++ tailWord_902686).sum := by decide
  have hdescent : baseEnd_902686 < baseStart_902686 := by decide
  rcases family_descends (prefixWord ++ tailWord_902686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902753 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_902753 : Nat := 118140960795 + 902753 * 2 ^ 59
def prefixEnd_902753 : Nat := 4983230072969 + 3 ^ 40 * 902753 * 2
def baseEnd_902753 : Nat := 206020533905960759304809

theorem tailTrace_902753 : CollatzResearch.WordTrace tailWord_902753 prefixEnd_902753 206020533905960759304809 := by
  unfold tailWord_902753
  simp only [CollatzResearch.WordTrace]
  refine ⟨32926106898487533782776913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21950737932325022521851275 32926106898487533782776913)
  ·
    refine ⟨24694580173865650337082685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32926106898487533782776913 24694580173865650337082685)
    ·
      refine ⟨9260467565199618876406007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24694580173865650337082685 9260467565199618876406007)
      ·
        refine ⟨13890701347799428314609011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9260467565199618876406007 13890701347799428314609011)
        ·
          refine ⟨20836052021699142471913517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13890701347799428314609011 20836052021699142471913517)
          ·
            refine ⟨7813519508137178426967569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20836052021699142471913517 7813519508137178426967569)
            ·
              refine ⟨5860139631102883820225677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7813519508137178426967569 5860139631102883820225677)
              ·
                refine ⟨2197552361663581432584629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5860139631102883820225677 2197552361663581432584629)
                ·
                  refine ⟨206020533905960759304809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2197552361663581432584629 206020533905960759304809)
                  ·
                    rfl

theorem cell21_902753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_902753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902753 prefixEnd_902753 := by exact prefixLift 902753
  have htrace : WordTrace (prefixWord ++ tailWord_902753) baseStart_902753 baseEnd_902753 := by
    simpa [prefixWord, tailWord_902753, baseEnd_902753] using wordTrace_append hprefix tailTrace_902753
  have hstable : (prefixWord ++ tailWord_902753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902753).length < 2 ^ (prefixWord ++ tailWord_902753).sum := by decide
  have hdescent : baseEnd_902753 < baseStart_902753 := by decide
  rcases family_descends (prefixWord ++ tailWord_902753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902767 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 8]
def baseStart_902767 : Nat := 118140960795 + 902767 * 2 ^ 59
def prefixEnd_902767 : Nat := 4983230072969 + 3 ^ 40 * 902767 * 2
def baseEnd_902767 : Nat := 206023728896699846071447

theorem tailTrace_902767 : CollatzResearch.WordTrace tailWord_902767 prefixEnd_902767 206023728896699846071447 := by
  unfold tailWord_902767
  simp only [CollatzResearch.WordTrace]
  refine ⟨32926617520436814173786555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21951078346957876115857703 32926617520436814173786555)
  ·
    refine ⟨49389926280655221260679833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32926617520436814173786555 49389926280655221260679833)
    ·
      refine ⟨37042444710491415945509875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49389926280655221260679833 37042444710491415945509875)
      ·
        refine ⟨55563667065737123918264813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37042444710491415945509875 55563667065737123918264813)
        ·
          refine ⟨20836375149651421469349305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55563667065737123918264813 20836375149651421469349305)
          ·
            refine ⟨15627281362238566102011979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20836375149651421469349305 15627281362238566102011979)
            ·
              refine ⟨23440922043357849153017969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15627281362238566102011979 23440922043357849153017969)
              ·
                refine ⟨17580691532518386864763477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23440922043357849153017969 17580691532518386864763477)
                ·
                  refine ⟨206023728896699846071447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17580691532518386864763477 206023728896699846071447)
                  ·
                    rfl

theorem cell21_902767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_902767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902767 prefixEnd_902767 := by exact prefixLift 902767
  have htrace : WordTrace (prefixWord ++ tailWord_902767) baseStart_902767 baseEnd_902767 := by
    simpa [prefixWord, tailWord_902767, baseEnd_902767] using wordTrace_append hprefix tailTrace_902767
  have hstable : (prefixWord ++ tailWord_902767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902767).length < 2 ^ (prefixWord ++ tailWord_902767).sum := by decide
  have hdescent : baseEnd_902767 < baseStart_902767 := by decide
  rcases family_descends (prefixWord ++ tailWord_902767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902770 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_902770 : Nat := 118140960795 + 902770 * 2 ^ 59
def prefixEnd_902770 : Nat := 4983230072969 + 3 ^ 40 * 902770 * 2
def baseEnd_902770 : Nat := 206024413537572507521441

theorem tailTrace_902770 : CollatzResearch.WordTrace tailWord_902770 prefixEnd_902770 206024413537572507521441 := by
  unfold tailWord_902770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8231681734856486421536441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21951151292950630457430509 8231681734856486421536441)
  ·
    refine ⟨6173761301142364816152331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8231681734856486421536441 6173761301142364816152331)
    ·
      refine ⟨9260641951713547224228497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6173761301142364816152331 9260641951713547224228497)
      ·
        refine ⟨6945481463785160418171373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9260641951713547224228497 6945481463785160418171373)
        ·
          refine ⟨2604555548919435156814265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6945481463785160418171373 2604555548919435156814265)
          ·
            refine ⟨1953416661689576367610699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2604555548919435156814265 1953416661689576367610699)
            ·
              refine ⟨2930124992534364551416049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1953416661689576367610699 2930124992534364551416049)
              ·
                refine ⟨2197593744400773413562037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2930124992534364551416049 2197593744400773413562037)
                ·
                  refine ⟨206024413537572507521441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2197593744400773413562037 206024413537572507521441)
                  ·
                    rfl

theorem cell21_902770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_902770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902770 prefixEnd_902770 := by exact prefixLift 902770
  have htrace : WordTrace (prefixWord ++ tailWord_902770) baseStart_902770 baseEnd_902770 := by
    simpa [prefixWord, tailWord_902770, baseEnd_902770] using wordTrace_append hprefix tailTrace_902770
  have hstable : (prefixWord ++ tailWord_902770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902770).length < 2 ^ (prefixWord ++ tailWord_902770).sum := by decide
  have hdescent : baseEnd_902770 < baseStart_902770 := by decide
  rcases family_descends (prefixWord ++ tailWord_902770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902874 : List Nat := [3, 1, 1, 2, 2, 3, 1, 8]
def baseStart_902874 : Nat := 118140960795 + 902874 * 2 ^ 59
def prefixEnd_902874 : Nat := 4983230072969 + 3 ^ 40 * 902874 * 2
def baseEnd_902874 : Nat := 68682715918163812595965

theorem tailTrace_902874 : CollatzResearch.WordTrace tailWord_902874 prefixEnd_902874 68682715918163812595965 := by
  unfold tailWord_902874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8232630032762292861982919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21953680087366114298621117 8232630032762292861982919)
  ·
    refine ⟨12348945049143439292974379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8232630032762292861982919 12348945049143439292974379)
    ·
      refine ⟨18523417573715158939461569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12348945049143439292974379 18523417573715158939461569)
      ·
        refine ⟨13892563180286369204596177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18523417573715158939461569 13892563180286369204596177)
        ·
          refine ⟨10419422385214776903447133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13892563180286369204596177 10419422385214776903447133)
          ·
            refine ⟨3907283394455541338792675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10419422385214776903447133 3907283394455541338792675)
            ·
              refine ⟨5860925091683312008189013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3907283394455541338792675 5860925091683312008189013)
              ·
                refine ⟨68682715918163812595965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5860925091683312008189013 68682715918163812595965)
                ·
                  rfl

theorem cell21_902874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_902874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902874 prefixEnd_902874 := by exact prefixLift 902874
  have htrace : WordTrace (prefixWord ++ tailWord_902874) baseStart_902874 baseEnd_902874 := by
    simpa [prefixWord, tailWord_902874, baseEnd_902874] using wordTrace_append hprefix tailTrace_902874
  have hstable : (prefixWord ++ tailWord_902874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902874).length < 2 ^ (prefixWord ++ tailWord_902874).sum := by decide
  have hdescent : baseEnd_902874 < baseStart_902874 := by decide
  rcases family_descends (prefixWord ++ tailWord_902874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902936 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_902936 : Nat := 118140960795 + 902936 * 2 ^ 59
def prefixEnd_902936 : Nat := 4983230072969 + 3 ^ 40 * 902936 * 2
def baseEnd_902936 : Nat := 206062296999193107754435

theorem tailTrace_902936 : CollatzResearch.WordTrace tailWord_902936 prefixEnd_902936 206062296999193107754435 := by
  unfold tailWord_902936
  simp only [CollatzResearch.WordTrace]
  refine ⟨16466390728412278018344331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21955187637883037357792441 16466390728412278018344331)
  ·
    refine ⟨24699586092618417027516497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16466390728412278018344331 24699586092618417027516497)
    ·
      refine ⟨18524689569463812770637373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24699586092618417027516497 18524689569463812770637373)
      ·
        refine ⟨6946758588548929788989015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18524689569463812770637373 6946758588548929788989015)
        ·
          refine ⟨10420137882823394683483523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6946758588548929788989015 10420137882823394683483523)
          ·
            refine ⟨15630206824235092025225285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10420137882823394683483523 15630206824235092025225285)
            ·
              refine ⟨2930663779544079754729741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15630206824235092025225285 2930663779544079754729741)
              ·
                refine ⟨1098998917329029908023653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2930663779544079754729741 1098998917329029908023653)
                ·
                  refine ⟨206062296999193107754435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1098998917329029908023653 206062296999193107754435)
                  ·
                    rfl

theorem cell21_902936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_902936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902936 prefixEnd_902936 := by exact prefixLift 902936
  have htrace : WordTrace (prefixWord ++ tailWord_902936) baseStart_902936 baseEnd_902936 := by
    simpa [prefixWord, tailWord_902936, baseEnd_902936] using wordTrace_append hprefix tailTrace_902936
  have hstable : (prefixWord ++ tailWord_902936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902936).length < 2 ^ (prefixWord ++ tailWord_902936).sum := by decide
  have hdescent : baseEnd_902936 < baseStart_902936 := by decide
  rcases family_descends (prefixWord ++ tailWord_902936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902942 : List Nat := [4, 3, 2, 2, 1, 1, 3, 5]
def baseStart_902942 : Nat := 118140960795 + 902942 * 2 ^ 59
def prefixEnd_902942 : Nat := 4983230072969 + 3 ^ 40 * 902942 * 2
def baseEnd_902942 : Nat := 68687888760312810218141

theorem tailTrace_902942 : CollatzResearch.WordTrace tailWord_902942 prefixEnd_902942 68687888760312810218141 := by
  unfold tailWord_902942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116625036850352382675885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21955333529868546040938053 4116625036850352382675885)
  ·
    refine ⟨1543734388818882143503457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4116625036850352382675885 1543734388818882143503457)
    ·
      refine ⟨1157800791614161607627593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1543734388818882143503457 1157800791614161607627593)
      ·
        refine ⟨868350593710621205720695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157800791614161607627593 868350593710621205720695)
        ·
          refine ⟨1302525890565931808581043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 868350593710621205720695 1302525890565931808581043)
          ·
            refine ⟨1953788835848897712871565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302525890565931808581043 1953788835848897712871565)
            ·
              refine ⟨732670813443336642326837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1953788835848897712871565 732670813443336642326837)
              ·
                refine ⟨68687888760312810218141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 732670813443336642326837 68687888760312810218141)
                ·
                  rfl

theorem cell21_902942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_902942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902942 prefixEnd_902942 := by exact prefixLift 902942
  have htrace : WordTrace (prefixWord ++ tailWord_902942) baseStart_902942 baseEnd_902942 := by
    simpa [prefixWord, tailWord_902942, baseEnd_902942] using wordTrace_append hprefix tailTrace_902942
  have hstable : (prefixWord ++ tailWord_902942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902942).length < 2 ^ (prefixWord ++ tailWord_902942).sum := by decide
  have hdescent : baseEnd_902942 < baseStart_902942 := by decide
  rcases family_descends (prefixWord ++ tailWord_902942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_902981 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 5]
def baseStart_902981 : Nat := 118140960795 + 902981 * 2 ^ 59
def prefixEnd_902981 : Nat := 4983230072969 + 3 ^ 40 * 902981 * 2
def baseEnd_902981 : Nat := 206072566612283029504343

theorem tailTrace_902981 : CollatzResearch.WordTrace tailWord_902981 prefixEnd_902981 206072566612283029504343 := by
  unfold tailWord_902981
  simp only [CollatzResearch.WordTrace]
  refine ⟨32934422741661528722076797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21956281827774352481384531 32934422741661528722076797)
  ·
    refine ⟨12350408528123073270778799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32934422741661528722076797 12350408528123073270778799)
    ·
      refine ⟨18525612792184609906168199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12350408528123073270778799 18525612792184609906168199)
      ·
        refine ⟨27788419188276914859252299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18525612792184609906168199 27788419188276914859252299)
        ·
          refine ⟨41682628782415372288878449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27788419188276914859252299 41682628782415372288878449)
          ·
            refine ⟨31261971586811529216658837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41682628782415372288878449 31261971586811529216658837)
            ·
              refine ⟨1465404918131790432030883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31261971586811529216658837 1465404918131790432030883)
              ·
                refine ⟨2198107377197685648046325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465404918131790432030883 2198107377197685648046325)
                ·
                  refine ⟨206072566612283029504343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2198107377197685648046325 206072566612283029504343)
                  ·
                    rfl

theorem cell21_902981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_902981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_902981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_902981 prefixEnd_902981 := by exact prefixLift 902981
  have htrace : WordTrace (prefixWord ++ tailWord_902981) baseStart_902981 baseEnd_902981 := by
    simpa [prefixWord, tailWord_902981, baseEnd_902981] using wordTrace_append hprefix tailTrace_902981
  have hstable : (prefixWord ++ tailWord_902981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_902981).length < 2 ^ (prefixWord ++ tailWord_902981).sum := by decide
  have hdescent : baseEnd_902981 < baseStart_902981 := by decide
  rcases family_descends (prefixWord ++ tailWord_902981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903150 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_903150 : Nat := 118140960795 + 903150 * 2 ^ 59
def prefixEnd_903150 : Nat := 4983230072969 + 3 ^ 40 * 903150 * 2
def baseEnd_903150 : Nat := 206111134714776291187331

theorem tailTrace_903150 : CollatzResearch.WordTrace tailWord_903150 prefixEnd_903150 206111134714776291187331 := by
  unfold tailWord_903150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4117573334756158823122363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21960391118699513723319269 4117573334756158823122363)
  ·
    refine ⟨6176360002134238234683545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4117573334756158823122363 6176360002134238234683545)
    ·
      refine ⟨4632270001600678676012659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6176360002134238234683545 4632270001600678676012659)
      ·
        refine ⟨6948405002401018014018989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4632270001600678676012659 6948405002401018014018989)
        ·
          refine ⟨2605651875900381755257121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6948405002401018014018989 2605651875900381755257121)
          ·
            refine ⟨1954238906925286316442841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605651875900381755257121 1954238906925286316442841)
            ·
              refine ⟨1465679180193964737332131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1954238906925286316442841 1465679180193964737332131)
              ·
                refine ⟨2198518770290947105998197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1465679180193964737332131 2198518770290947105998197)
                ·
                  refine ⟨206111134714776291187331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2198518770290947105998197 206111134714776291187331)
                  ·
                    rfl

theorem cell21_903150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_903150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903150 prefixEnd_903150 := by exact prefixLift 903150
  have htrace : WordTrace (prefixWord ++ tailWord_903150) baseStart_903150 baseEnd_903150 := by
    simpa [prefixWord, tailWord_903150, baseEnd_903150] using wordTrace_append hprefix tailTrace_903150
  have hstable : (prefixWord ++ tailWord_903150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903150).length < 2 ^ (prefixWord ++ tailWord_903150).sum := by decide
  have hdescent : baseEnd_903150 < baseStart_903150 := by decide
  rcases family_descends (prefixWord ++ tailWord_903150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903260 : List Nat := [2, 2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_903260 : Nat := 118140960795 + 903260 * 2 ^ 59
def prefixEnd_903260 : Nat := 4983230072969 + 3 ^ 40 * 903260 * 2
def baseEnd_903260 : Nat := 206136238213440544353773

theorem tailTrace_903260 : CollatzResearch.WordTrace tailWord_903260 prefixEnd_903260 206136238213440544353773 := by
  unfold tailWord_903260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16472299353825379685741617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21963065805100506247655489 16472299353825379685741617)
  ·
    refine ⟨12354224515369034764306213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16472299353825379685741617 12354224515369034764306213)
    ·
      refine ⟨2316417096631694018307415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12354224515369034764306213 2316417096631694018307415)
      ·
        refine ⟨3474625644947541027461123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316417096631694018307415 3474625644947541027461123)
        ·
          refine ⟨5211938467421311541191685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474625644947541027461123 5211938467421311541191685)
          ·
            refine ⟨977238462641495913973441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5211938467421311541191685 977238462641495913973441)
            ·
              refine ⟨732928846981121935480081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977238462641495913973441 732928846981121935480081)
              ·
                refine ⟨549696635235841451610061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732928846981121935480081 549696635235841451610061)
                ·
                  refine ⟨206136238213440544353773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549696635235841451610061 206136238213440544353773)
                  ·
                    rfl

theorem cell21_903260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_903260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903260 prefixEnd_903260 := by exact prefixLift 903260
  have htrace : WordTrace (prefixWord ++ tailWord_903260) baseStart_903260 baseEnd_903260 := by
    simpa [prefixWord, tailWord_903260, baseEnd_903260] using wordTrace_append hprefix tailTrace_903260
  have hstable : (prefixWord ++ tailWord_903260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903260).length < 2 ^ (prefixWord ++ tailWord_903260).sum := by decide
  have hdescent : baseEnd_903260 < baseStart_903260 := by decide
  rcases family_descends (prefixWord ++ tailWord_903260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903375 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 4]
def baseStart_903375 : Nat := 118140960795 + 903375 * 2 ^ 59
def prefixEnd_903375 : Nat := 4983230072969 + 3 ^ 40 * 903375 * 2
def baseEnd_903375 : Nat := 206162482780225899936871

theorem tailTrace_903375 : CollatzResearch.WordTrace tailWord_903375 prefixEnd_903375 206162482780225899936871 := by
  unfold tailWord_903375
  simp only [CollatzResearch.WordTrace]
  refine ⟨32948793102234134011919579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21965862068156089341279719 32948793102234134011919579)
  ·
    refine ⟨49423189653351201017879369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32948793102234134011919579 49423189653351201017879369)
    ·
      refine ⟨37067392240013400763409527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49423189653351201017879369 37067392240013400763409527)
      ·
        refine ⟨55601088360020101145114291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37067392240013400763409527 55601088360020101145114291)
        ·
          refine ⟨83401632540030151717671437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55601088360020101145114291 83401632540030151717671437)
          ·
            refine ⟨31275612202511306894126789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83401632540030151717671437 31275612202511306894126789)
            ·
              refine ⟨5864177287970870042648773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31275612202511306894126789 5864177287970870042648773)
              ·
                refine ⟨1099533241494538132996645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5864177287970870042648773 1099533241494538132996645)
                ·
                  refine ⟨206162482780225899936871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099533241494538132996645 206162482780225899936871)
                  ·
                    rfl

theorem cell21_903375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 4].length) (baseStart_903375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903375 prefixEnd_903375 := by exact prefixLift 903375
  have htrace : WordTrace (prefixWord ++ tailWord_903375) baseStart_903375 baseEnd_903375 := by
    simpa [prefixWord, tailWord_903375, baseEnd_903375] using wordTrace_append hprefix tailTrace_903375
  have hstable : (prefixWord ++ tailWord_903375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903375).length < 2 ^ (prefixWord ++ tailWord_903375).sum := by decide
  have hdescent : baseEnd_903375 < baseStart_903375 := by decide
  rcases family_descends (prefixWord ++ tailWord_903375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903378 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 5]
def baseStart_903378 : Nat := 118140960795 + 903378 * 2 ^ 59
def prefixEnd_903378 : Nat := 4983230072969 + 3 ^ 40 * 903378 * 2
def baseEnd_903378 : Nat := 206163167421098561386865

theorem tailTrace_903378 : CollatzResearch.WordTrace tailWord_903378 prefixEnd_903378 206163167421098561386865 := by
  unfold tailWord_903378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8237225630305816381069697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21965935014148843682852525 8237225630305816381069697)
  ·
    refine ⟨6177919222729362285802273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8237225630305816381069697 6177919222729362285802273)
    ·
      refine ⟨4633439417047021714351705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6177919222729362285802273 4633439417047021714351705)
      ·
        refine ⟨3475079562785266285763779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4633439417047021714351705 3475079562785266285763779)
        ·
          refine ⟨5212619344177899428645669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3475079562785266285763779 5212619344177899428645669)
          ·
            refine ⟨977366127033356142871063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5212619344177899428645669 977366127033356142871063)
            ·
              refine ⟨1466049190550034214306595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977366127033356142871063 1466049190550034214306595)
              ·
                refine ⟨2199073785825051321459893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466049190550034214306595 2199073785825051321459893)
                ·
                  refine ⟨206163167421098561386865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2199073785825051321459893 206163167421098561386865)
                  ·
                    rfl

theorem cell21_903378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_903378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903378 prefixEnd_903378 := by exact prefixLift 903378
  have htrace : WordTrace (prefixWord ++ tailWord_903378) baseStart_903378 baseEnd_903378 := by
    simpa [prefixWord, tailWord_903378, baseEnd_903378] using wordTrace_append hprefix tailTrace_903378
  have hstable : (prefixWord ++ tailWord_903378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903378).length < 2 ^ (prefixWord ++ tailWord_903378).sum := by decide
  have hdescent : baseEnd_903378 < baseStart_903378 := by decide
  rcases family_descends (prefixWord ++ tailWord_903378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903451 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 4]
def baseStart_903451 : Nat := 118140960795 + 903451 * 2 ^ 59
def prefixEnd_903451 : Nat := 4983230072969 + 3 ^ 40 * 903451 * 2
def baseEnd_903451 : Nat := 206179827015666656670049

theorem tailTrace_903451 : CollatzResearch.WordTrace tailWord_903451 prefixEnd_903451 206179827015666656670049 := by
  unfold tailWord_903451
  simp only [CollatzResearch.WordTrace]
  refine ⟨32951565049958798991686207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21967710033305865994457471 32951565049958798991686207)
  ·
    refine ⟨49427347574938198487529311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32951565049958798991686207 49427347574938198487529311)
    ·
      refine ⟨74141021362407297731293967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49427347574938198487529311 74141021362407297731293967)
      ·
        refine ⟨111211532043610946596940951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74141021362407297731293967 111211532043610946596940951)
        ·
          refine ⟨166817298065416419895411427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111211532043610946596940951 166817298065416419895411427)
          ·
            refine ⟨250225947098124629843117141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166817298065416419895411427 250225947098124629843117141)
            ·
              refine ⟨2932335317556148005974029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 250225947098124629843117141 2932335317556148005974029)
              ·
                refine ⟨1099625744083555502240261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2932335317556148005974029 1099625744083555502240261)
                ·
                  refine ⟨206179827015666656670049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099625744083555502240261 206179827015666656670049)
                  ·
                    rfl

theorem cell21_903451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_903451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903451 prefixEnd_903451 := by exact prefixLift 903451
  have htrace : WordTrace (prefixWord ++ tailWord_903451) baseStart_903451 baseEnd_903451 := by
    simpa [prefixWord, tailWord_903451, baseEnd_903451] using wordTrace_append hprefix tailTrace_903451
  have hstable : (prefixWord ++ tailWord_903451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903451).length < 2 ^ (prefixWord ++ tailWord_903451).sum := by decide
  have hdescent : baseEnd_903451 < baseStart_903451 := by decide
  rcases family_descends (prefixWord ++ tailWord_903451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903454 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_903454 : Nat := 118140960795 + 903454 * 2 ^ 59
def prefixEnd_903454 : Nat := 4983230072969 + 3 ^ 40 * 903454 * 2
def baseEnd_903454 : Nat := 206180511656539318120043

theorem tailTrace_903454 : CollatzResearch.WordTrace tailWord_903454 prefixEnd_903454 206180511656539318120043 := by
  unfold tailWord_903454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118959308618491313005677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21967782979298620336030277 4118959308618491313005677)
  ·
    refine ⟨1544609740731934242377129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4118959308618491313005677 1544609740731934242377129)
    ·
      refine ⟨1158457305548950681782847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1544609740731934242377129 1158457305548950681782847)
      ·
        refine ⟨1737685958323426022674271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1158457305548950681782847 1737685958323426022674271)
        ·
          refine ⟨2606528937485139034011407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737685958323426022674271 2606528937485139034011407)
          ·
            refine ⟨3909793406227708551017111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606528937485139034011407 3909793406227708551017111)
            ·
              refine ⟨5864690109341562826525667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3909793406227708551017111 5864690109341562826525667)
              ·
                refine ⟨8797035164012344239788501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5864690109341562826525667 8797035164012344239788501)
                ·
                  refine ⟨206180511656539318120043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8797035164012344239788501 206180511656539318120043)
                  ·
                    rfl

theorem cell21_903454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_903454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903454 prefixEnd_903454 := by exact prefixLift 903454
  have htrace : WordTrace (prefixWord ++ tailWord_903454) baseStart_903454 baseEnd_903454 := by
    simpa [prefixWord, tailWord_903454, baseEnd_903454] using wordTrace_append hprefix tailTrace_903454
  have hstable : (prefixWord ++ tailWord_903454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903454).length < 2 ^ (prefixWord ++ tailWord_903454).sum := by decide
  have hdescent : baseEnd_903454 < baseStart_903454 := by decide
  rcases family_descends (prefixWord ++ tailWord_903454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903496 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_903496 : Nat := 118140960795 + 903496 * 2 ^ 59
def prefixEnd_903496 : Nat := 4983230072969 + 3 ^ 40 * 903496 * 2
def baseEnd_903496 : Nat := 206190096628756578419957

theorem tailTrace_903496 : CollatzResearch.WordTrace tailWord_903496 prefixEnd_903496 206190096628756578419957 := by
  unfold tailWord_903496
  simp only [CollatzResearch.WordTrace]
  refine ⟨16476603167397885838537171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21968804223197181118049561 16476603167397885838537171)
  ·
    refine ⟨24714904751096828757805757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16476603167397885838537171 24714904751096828757805757)
    ·
      refine ⟨9268089281661310784177159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24714904751096828757805757 9268089281661310784177159)
      ·
        refine ⟨13902133922491966176265739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9268089281661310784177159 13902133922491966176265739)
        ·
          refine ⟨20853200883737949264398609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13902133922491966176265739 20853200883737949264398609)
          ·
            refine ⟨15639900662803461948298957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20853200883737949264398609 15639900662803461948298957)
            ·
              refine ⟨5864962748551298230612109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15639900662803461948298957 5864962748551298230612109)
              ·
                refine ⟨2199361030706736836479541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5864962748551298230612109 2199361030706736836479541)
                ·
                  refine ⟨206190096628756578419957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2199361030706736836479541 206190096628756578419957)
                  ·
                    rfl

theorem cell21_903496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_903496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903496 prefixEnd_903496 := by exact prefixLift 903496
  have htrace : WordTrace (prefixWord ++ tailWord_903496) baseStart_903496 baseEnd_903496 := by
    simpa [prefixWord, tailWord_903496, baseEnd_903496] using wordTrace_append hprefix tailTrace_903496
  have hstable : (prefixWord ++ tailWord_903496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903496).length < 2 ^ (prefixWord ++ tailWord_903496).sum := by decide
  have hdescent : baseEnd_903496 < baseStart_903496 := by decide
  rcases family_descends (prefixWord ++ tailWord_903496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903527 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_903527 : Nat := 118140960795 + 903527 * 2 ^ 59
def prefixEnd_903527 : Nat := 4983230072969 + 3 ^ 40 * 903527 * 2
def baseEnd_903527 : Nat := 206197171251107413403227

theorem tailTrace_903527 : CollatzResearch.WordTrace tailWord_903527 prefixEnd_903527 206197171251107413403227 := by
  unfold tailWord_903527
  simp only [CollatzResearch.WordTrace]
  refine ⟨32954336997683463971452835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21969557998455642647635223 32954336997683463971452835)
  ·
    refine ⟨49431505496525195957179253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32954336997683463971452835 49431505496525195957179253)
    ·
      refine ⟨4634203640299237120985555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49431505496525195957179253 4634203640299237120985555)
      ·
        refine ⟨6951305460448855681478333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4634203640299237120985555 6951305460448855681478333)
        ·
          refine ⟨2606739547668320880554375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6951305460448855681478333 2606739547668320880554375)
          ·
            refine ⟨3910109321502481320831563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2606739547668320880554375 3910109321502481320831563)
            ·
              refine ⟨5865163982253721981247345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3910109321502481320831563 5865163982253721981247345)
              ·
                refine ⟨4398872986690291485935509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5865163982253721981247345 4398872986690291485935509)
                ·
                  refine ⟨206197171251107413403227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4398872986690291485935509 206197171251107413403227)
                  ·
                    rfl

theorem cell21_903527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_903527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903527 prefixEnd_903527 := by exact prefixLift 903527
  have htrace : WordTrace (prefixWord ++ tailWord_903527) baseStart_903527 baseEnd_903527 := by
    simpa [prefixWord, tailWord_903527, baseEnd_903527] using wordTrace_append hprefix tailTrace_903527
  have hstable : (prefixWord ++ tailWord_903527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903527).length < 2 ^ (prefixWord ++ tailWord_903527).sum := by decide
  have hdescent : baseEnd_903527 < baseStart_903527 := by decide
  rcases family_descends (prefixWord ++ tailWord_903527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903561 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 4]
def baseStart_903561 : Nat := 118140960795 + 903561 * 2 ^ 59
def prefixEnd_903561 : Nat := 4983230072969 + 3 ^ 40 * 903561 * 2
def baseEnd_903561 : Nat := 206204930514330909836491

theorem tailTrace_903561 : CollatzResearch.WordTrace tailWord_903561 prefixEnd_903561 206204930514330909836491 := by
  unfold tailWord_903561
  simp only [CollatzResearch.WordTrace]
  refine ⟨32955577079560287778190537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21970384719706858518793691 32955577079560287778190537)
  ·
    refine ⟨24716682809670215833642903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32955577079560287778190537 24716682809670215833642903)
    ·
      refine ⟨37075024214505323750464355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24716682809670215833642903 37075024214505323750464355)
      ·
        refine ⟨55612536321757985625696533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37075024214505323750464355 55612536321757985625696533)
        ·
          refine ⟨2606837640082405576204525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55612536321757985625696533 2606837640082405576204525)
          ·
            refine ⟨977564115030902091076697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2606837640082405576204525 977564115030902091076697)
            ·
              refine ⟨733173086273176568307523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977564115030902091076697 733173086273176568307523)
              ·
                refine ⟨1099759629409764852461285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733173086273176568307523 1099759629409764852461285)
                ·
                  refine ⟨206204930514330909836491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1099759629409764852461285 206204930514330909836491)
                  ·
                    rfl

theorem cell21_903561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 4].length) (baseStart_903561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903561 prefixEnd_903561 := by exact prefixLift 903561
  have htrace : WordTrace (prefixWord ++ tailWord_903561) baseStart_903561 baseEnd_903561 := by
    simpa [prefixWord, tailWord_903561, baseEnd_903561] using wordTrace_append hprefix tailTrace_903561
  have hstable : (prefixWord ++ tailWord_903561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903561).length < 2 ^ (prefixWord ++ tailWord_903561).sum := by decide
  have hdescent : baseEnd_903561 < baseStart_903561 := by decide
  rcases family_descends (prefixWord ++ tailWord_903561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903589 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 3]
def baseStart_903589 : Nat := 118140960795 + 903589 * 2 ^ 59
def prefixEnd_903589 : Nat := 4983230072969 + 3 ^ 40 * 903589 * 2
def baseEnd_903589 : Nat := 206211320495809083369767

theorem tailTrace_903589 : CollatzResearch.WordTrace tailWord_903589 prefixEnd_903589 206211320495809083369767 := by
  unfold tailWord_903589
  simp only [CollatzResearch.WordTrace]
  refine ⟨32956598323458848560209821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21971065548972565706806547 32956598323458848560209821)
  ·
    refine ⟨12358724371297068210078683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32956598323458848560209821 12358724371297068210078683)
    ·
      refine ⟨18538086556945602315118025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12358724371297068210078683 18538086556945602315118025)
      ·
        refine ⟨13903564917709201736338519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18538086556945602315118025 13903564917709201736338519)
        ·
          refine ⟨20855347376563802604507779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13903564917709201736338519 20855347376563802604507779)
          ·
            refine ⟨31283021064845703906761669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20855347376563802604507779 31283021064845703906761669)
            ·
              refine ⟨5865566449658569482517813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31283021064845703906761669 5865566449658569482517813)
              ·
                refine ⟨549896854655490888986045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5865566449658569482517813 549896854655490888986045)
                ·
                  refine ⟨206211320495809083369767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549896854655490888986045 206211320495809083369767)
                  ·
                    rfl

theorem cell21_903589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_903589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903589 prefixEnd_903589 := by exact prefixLift 903589
  have htrace : WordTrace (prefixWord ++ tailWord_903589) baseStart_903589 baseEnd_903589 := by
    simpa [prefixWord, tailWord_903589, baseEnd_903589] using wordTrace_append hprefix tailTrace_903589
  have hstable : (prefixWord ++ tailWord_903589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903589).length < 2 ^ (prefixWord ++ tailWord_903589).sum := by decide
  have hdescent : baseEnd_903589 < baseStart_903589 := by decide
  rcases family_descends (prefixWord ++ tailWord_903589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903665 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 3]
def baseStart_903665 : Nat := 118140960795 + 903665 * 2 ^ 59
def prefixEnd_903665 : Nat := 4983230072969 + 3 ^ 40 * 903665 * 2
def baseEnd_903665 : Nat := 206228664731249840102945

theorem tailTrace_903665 : CollatzResearch.WordTrace tailWord_903665 prefixEnd_903665 206228664731249840102945 := by
  unfold tailWord_903665
  simp only [CollatzResearch.WordTrace]
  refine ⟨32959370271183513539976449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21972913514122342359984299 32959370271183513539976449)
  ·
    refine ⟨24719527703387635154982337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32959370271183513539976449 24719527703387635154982337)
    ·
      refine ⟨18539645777540726366236753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24719527703387635154982337 18539645777540726366236753)
      ·
        refine ⟨13904734333155544774677565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18539645777540726366236753 13904734333155544774677565)
        ·
          refine ⟨5214275374933329290504087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13904734333155544774677565 5214275374933329290504087)
          ·
            refine ⟨7821413062399993935756131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5214275374933329290504087 7821413062399993935756131)
            ·
              refine ⟨11732119593599990903634197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7821413062399993935756131 11732119593599990903634197)
              ·
                refine ⟨549943105949999573607853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11732119593599990903634197 549943105949999573607853)
                ·
                  refine ⟨206228664731249840102945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549943105949999573607853 206228664731249840102945)
                  ·
                    rfl

theorem cell21_903665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_903665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903665 prefixEnd_903665 := by exact prefixLift 903665
  have htrace : WordTrace (prefixWord ++ tailWord_903665) baseStart_903665 baseEnd_903665 := by
    simpa [prefixWord, tailWord_903665, baseEnd_903665] using wordTrace_append hprefix tailTrace_903665
  have hstable : (prefixWord ++ tailWord_903665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903665).length < 2 ^ (prefixWord ++ tailWord_903665).sum := by decide
  have hdescent : baseEnd_903665 < baseStart_903665 := by decide
  rcases family_descends (prefixWord ++ tailWord_903665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903716 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_903716 : Nat := 118140960795 + 903716 * 2 ^ 59
def prefixEnd_903716 : Nat := 4983230072969 + 3 ^ 40 * 903716 * 2
def baseEnd_903716 : Nat := 206240303626085084752841

theorem tailTrace_903716 : CollatzResearch.WordTrace tailWord_903716 prefixEnd_903716 206240303626085084752841 := by
  unfold tailWord_903716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480615196999374625041501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21974153595999166166722001 16480615196999374625041501)
  ·
    refine ⟨6180230698874765484390563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16480615196999374625041501 6180230698874765484390563)
    ·
      refine ⟨9270346048312148226585845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6180230698874765484390563 9270346048312148226585845)
      ·
        refine ⟨869094942029263896242423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9270346048312148226585845 869094942029263896242423)
        ·
          refine ⟨1303642413043895844363635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869094942029263896242423 1303642413043895844363635)
          ·
            refine ⟨1955463619565843766545453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303642413043895844363635 1955463619565843766545453)
            ·
              refine ⟨733298857337191412454545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1955463619565843766545453 733298857337191412454545)
              ·
                refine ⟨549974143002893559340909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733298857337191412454545 549974143002893559340909)
                ·
                  refine ⟨206240303626085084752841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549974143002893559340909 206240303626085084752841)
                  ·
                    rfl

theorem cell21_903716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_903716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903716 prefixEnd_903716 := by exact prefixLift 903716
  have htrace : WordTrace (prefixWord ++ tailWord_903716) baseStart_903716 baseEnd_903716 := by
    simpa [prefixWord, tailWord_903716, baseEnd_903716] using wordTrace_append hprefix tailTrace_903716
  have hstable : (prefixWord ++ tailWord_903716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903716).length < 2 ^ (prefixWord ++ tailWord_903716).sum := by decide
  have hdescent : baseEnd_903716 < baseStart_903716 := by decide
  rcases family_descends (prefixWord ++ tailWord_903716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_903834 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_903834 : Nat := 118140960795 + 903834 * 2 ^ 59
def prefixEnd_903834 : Nat := 4983230072969 + 3 ^ 40 * 903834 * 2
def baseEnd_903834 : Nat := 206267232833743101785933

theorem tailTrace_903834 : CollatzResearch.WordTrace tailWord_903834 prefixEnd_903834 206267232833743101785933 := by
  unfold tailWord_903834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241383551892813850719639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21977022805047503601919037 8241383551892813850719639)
  ·
    refine ⟨12362075327839220776079459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241383551892813850719639 12362075327839220776079459)
    ·
      refine ⟨18543112991758831164119189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12362075327839220776079459 18543112991758831164119189)
      ·
        refine ⟨869208421488695210818087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18543112991758831164119189 869208421488695210818087)
        ·
          refine ⟨1303812632233042816227131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869208421488695210818087 1303812632233042816227131)
          ·
            refine ⟨1955718948349564224340697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303812632233042816227131 1955718948349564224340697)
            ·
              refine ⟨1466789211262173168255523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1955718948349564224340697 1466789211262173168255523)
              ·
                refine ⟨2200183816893259752383285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1466789211262173168255523 2200183816893259752383285)
                ·
                  refine ⟨206267232833743101785933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2200183816893259752383285 206267232833743101785933)
                  ·
                    rfl

theorem cell21_903834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_903834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_903834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_903834 prefixEnd_903834 := by exact prefixLift 903834
  have htrace : WordTrace (prefixWord ++ tailWord_903834) baseStart_903834 baseEnd_903834 := by
    simpa [prefixWord, tailWord_903834, baseEnd_903834] using wordTrace_append hprefix tailTrace_903834
  have hstable : (prefixWord ++ tailWord_903834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_903834).length < 2 ^ (prefixWord ++ tailWord_903834).sum := by decide
  have hdescent : baseEnd_903834 < baseStart_903834 := by decide
  rcases family_descends (prefixWord ++ tailWord_903834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904073 : List Nat := [1, 2, 1, 1, 5, 3, 2, 6]
def baseStart_904073 : Nat := 118140960795 + 904073 * 2 ^ 59
def prefixEnd_904073 : Nat := 4983230072969 + 3 ^ 40 * 904073 * 2
def baseEnd_904073 : Nat := 68773925296643932434037

theorem tailTrace_904073 : CollatzResearch.WordTrace tailWord_904073 prefixEnd_904073 68773925296643932434037 := by
  unfold tailWord_904073
  simp only [CollatzResearch.WordTrace]
  refine ⟨32974251253705399220828873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21982834169136932813885915 32974251253705399220828873)
  ·
    refine ⟨24730688440279049415621655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32974251253705399220828873 24730688440279049415621655)
    ·
      refine ⟨37096032660418574123432483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24730688440279049415621655 37096032660418574123432483)
      ·
        refine ⟨55644048990627861185148725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37096032660418574123432483 55644048990627861185148725)
        ·
          refine ⟨5216629592871361986107693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55644048990627861185148725 5216629592871361986107693)
          ·
            refine ⟨1956236097326760744790385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5216629592871361986107693 1956236097326760744790385)
            ·
              refine ⟨1467177072995070558592789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1956236097326760744790385 1467177072995070558592789)
              ·
                refine ⟨68773925296643932434037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1467177072995070558592789 68773925296643932434037)
                ·
                  rfl

theorem cell21_904073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 6].length) (baseStart_904073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904073 prefixEnd_904073 := by exact prefixLift 904073
  have htrace : WordTrace (prefixWord ++ tailWord_904073) baseStart_904073 baseEnd_904073 := by
    simpa [prefixWord, tailWord_904073, baseEnd_904073] using wordTrace_append hprefix tailTrace_904073
  have hstable : (prefixWord ++ tailWord_904073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904073).length < 2 ^ (prefixWord ++ tailWord_904073).sum := by decide
  have hdescent : baseEnd_904073 < baseStart_904073 := by decide
  rcases family_descends (prefixWord ++ tailWord_904073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904087 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_904087 : Nat := 118140960795 + 904087 * 2 ^ 59
def prefixEnd_904087 : Nat := 4983230072969 + 3 ^ 40 * 904087 * 2
def baseEnd_904087 : Nat := 206324970880670884068749

theorem tailTrace_904087 : CollatzResearch.WordTrace tailWord_904087 prefixEnd_904087 206324970880670884068749 := by
  unfold tailWord_904087
  simp only [CollatzResearch.WordTrace]
  refine ⟨32974761875654679611838515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21983174583769786407892343 32974761875654679611838515)
  ·
    refine ⟨49462142813482019417757773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32974761875654679611838515 49462142813482019417757773)
    ·
      refine ⟨18548303555055757281659165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49462142813482019417757773 18548303555055757281659165)
      ·
        refine ⟨6955613833145908980622187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18548303555055757281659165 6955613833145908980622187)
        ·
          refine ⟨10433420749718863470933281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6955613833145908980622187 10433420749718863470933281)
          ·
            refine ⟨7825065562289147603199961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10433420749718863470933281 7825065562289147603199961)
            ·
              refine ⟨5868799171716860702399971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825065562289147603199961 5868799171716860702399971)
              ·
                refine ⟨8803198757575291053599957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5868799171716860702399971 8803198757575291053599957)
                ·
                  refine ⟨206324970880670884068749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8803198757575291053599957 206324970880670884068749)
                  ·
                    rfl

theorem cell21_904087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_904087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904087 prefixEnd_904087 := by exact prefixLift 904087
  have htrace : WordTrace (prefixWord ++ tailWord_904087) baseStart_904087 baseEnd_904087 := by
    simpa [prefixWord, tailWord_904087, baseEnd_904087] using wordTrace_append hprefix tailTrace_904087
  have hstable : (prefixWord ++ tailWord_904087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904087).length < 2 ^ (prefixWord ++ tailWord_904087).sum := by decide
  have hdescent : baseEnd_904087 < baseStart_904087 := by decide
  rcases family_descends (prefixWord ++ tailWord_904087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904121 : List Nat := [1, 2, 1, 4, 2, 3, 1, 4, 3]
def baseStart_904121 : Nat := 118140960795 + 904121 * 2 ^ 59
def prefixEnd_904121 : Nat := 4983230072969 + 3 ^ 40 * 904121 * 2
def baseEnd_904121 : Nat := 206332730143894380502013

theorem tailTrace_904121 : CollatzResearch.WordTrace tailWord_904121 prefixEnd_904121 206332730143894380502013 := by
  unfold tailWord_904121
  simp only [CollatzResearch.WordTrace]
  refine ⟨32976001957531503418576217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21984001305021002279050811 32976001957531503418576217)
  ·
    refine ⟨24732001468148627563932163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32976001957531503418576217 24732001468148627563932163)
    ·
      refine ⟨37098002202222941345898245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24732001468148627563932163 37098002202222941345898245)
      ·
        refine ⟨6955875412916801502355921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37098002202222941345898245 6955875412916801502355921)
        ·
          refine ⟨5216906559687601126766941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6955875412916801502355921 5216906559687601126766941)
          ·
            refine ⟨1956339959882850422537603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5216906559687601126766941 1956339959882850422537603)
            ·
              refine ⟨2934509939824275633806405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956339959882850422537603 2934509939824275633806405)
              ·
                refine ⟨550220613717051681338701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2934509939824275633806405 550220613717051681338701)
                ·
                  refine ⟨206332730143894380502013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550220613717051681338701 206332730143894380502013)
                  ·
                    rfl

theorem cell21_904121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_904121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904121 prefixEnd_904121 := by exact prefixLift 904121
  have htrace : WordTrace (prefixWord ++ tailWord_904121) baseStart_904121 baseEnd_904121 := by
    simpa [prefixWord, tailWord_904121, baseEnd_904121] using wordTrace_append hprefix tailTrace_904121
  have hstable : (prefixWord ++ tailWord_904121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904121).length < 2 ^ (prefixWord ++ tailWord_904121).sum := by decide
  have hdescent : baseEnd_904121 < baseStart_904121 := by decide
  rcases family_descends (prefixWord ++ tailWord_904121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904141 : List Nat := [1, 6, 3, 1, 1, 1, 3, 5]
def baseStart_904141 : Nat := 118140960795 + 904141 * 2 ^ 59
def prefixEnd_904141 : Nat := 4983230072969 + 3 ^ 40 * 904141 * 2
def baseEnd_904141 : Nat := 68779098138792930056213

theorem tailTrace_904141 : CollatzResearch.WordTrace tailWord_904141 prefixEnd_904141 68779098138792930056213 := by
  unfold tailWord_904141
  simp only [CollatzResearch.WordTrace]
  refine ⟨32976731417459046834304277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21984487611639364556202851 32976731417459046834304277)
  ·
    refine ⟨1545784285193392820358013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32976731417459046834304277 1545784285193392820358013)
    ·
      refine ⟨579669106947522307634255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1545784285193392820358013 579669106947522307634255)
      ·
        refine ⟨869503660421283461451383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579669106947522307634255 869503660421283461451383)
        ·
          refine ⟨1304255490631925192177075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869503660421283461451383 1304255490631925192177075)
          ·
            refine ⟨1956383235947887788265613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1304255490631925192177075 1956383235947887788265613)
            ·
              refine ⟨733643713480457920599605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1956383235947887788265613 733643713480457920599605)
              ·
                refine ⟨68779098138792930056213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733643713480457920599605 68779098138792930056213)
                ·
                  rfl

theorem cell21_904141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 5].length) (baseStart_904141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904141 prefixEnd_904141 := by exact prefixLift 904141
  have htrace : WordTrace (prefixWord ++ tailWord_904141) baseStart_904141 baseEnd_904141 := by
    simpa [prefixWord, tailWord_904141, baseEnd_904141] using wordTrace_append hprefix tailTrace_904141
  have hstable : (prefixWord ++ tailWord_904141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904141).length < 2 ^ (prefixWord ++ tailWord_904141).sum := by decide
  have hdescent : baseEnd_904141 < baseStart_904141 := by decide
  rcases family_descends (prefixWord ++ tailWord_904141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904163 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_904163 : Nat := 118140960795 + 904163 * 2 ^ 59
def prefixEnd_904163 : Nat := 4983230072969 + 3 ^ 40 * 904163 * 2
def baseEnd_904163 : Nat := 206342315116111640801927

theorem tailTrace_904163 : CollatzResearch.WordTrace tailWord_904163 prefixEnd_904163 206342315116111640801927 := by
  unfold tailWord_904163
  simp only [CollatzResearch.WordTrace]
  refine ⟨32977533823379344591605143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21985022548919563061070095 32977533823379344591605143)
  ·
    refine ⟨49466300735069016887407715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32977533823379344591605143 49466300735069016887407715)
    ·
      refine ⟨74199451102603525331111573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49466300735069016887407715 74199451102603525331111573)
      ·
        refine ⟨3478099270434540249895855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74199451102603525331111573 3478099270434540249895855)
        ·
          refine ⟨5217148905651810374843783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3478099270434540249895855 5217148905651810374843783)
          ·
            refine ⟨7825723358477715562265675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5217148905651810374843783 7825723358477715562265675)
            ·
              refine ⟨11738585037716573343398513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7825723358477715562265675 11738585037716573343398513)
              ·
                refine ⟨8803938778287430007548885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11738585037716573343398513 8803938778287430007548885)
                ·
                  refine ⟨206342315116111640801927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8803938778287430007548885 206342315116111640801927)
                  ·
                    rfl

theorem cell21_904163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_904163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904163 prefixEnd_904163 := by exact prefixLift 904163
  have htrace : WordTrace (prefixWord ++ tailWord_904163) baseStart_904163 baseEnd_904163 := by
    simpa [prefixWord, tailWord_904163, baseEnd_904163] using wordTrace_append hprefix tailTrace_904163
  have hstable : (prefixWord ++ tailWord_904163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904163).length < 2 ^ (prefixWord ++ tailWord_904163).sum := by decide
  have hdescent : baseEnd_904163 < baseStart_904163 := by decide
  rcases family_descends (prefixWord ++ tailWord_904163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904225 : List Nat := [1, 2, 3, 2, 3, 3, 7]
def baseStart_904225 : Nat := 118140960795 + 904225 * 2 ^ 59
def prefixEnd_904225 : Nat := 4983230072969 + 3 ^ 40 * 904225 * 2
def baseEnd_904225 : Nat := 22928496040090367863163

theorem tailTrace_904225 : CollatzResearch.WordTrace tailWord_904225 prefixEnd_904225 22928496040090367863163 := by
  unfold tailWord_904225
  simp only [CollatzResearch.WordTrace]
  refine ⟨32979795149154729180362129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21986530099436486120241419 32979795149154729180362129)
  ·
    refine ⟨24734846361866046885271597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32979795149154729180362129 24734846361866046885271597)
    ·
      refine ⟨9275567385699767581976849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24734846361866046885271597 9275567385699767581976849)
      ·
        refine ⟨6956675539274825686482637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9275567385699767581976849 6956675539274825686482637)
        ·
          refine ⟨2608753327228059632430989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6956675539274825686482637 2608753327228059632430989)
          ·
            refine ⟨978282497710522362161621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2608753327228059632430989 978282497710522362161621)
            ·
              refine ⟨22928496040090367863163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 978282497710522362161621 22928496040090367863163)
              ·
                rfl

theorem cell21_904225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 7].length) (baseStart_904225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904225 prefixEnd_904225 := by exact prefixLift 904225
  have htrace : WordTrace (prefixWord ++ tailWord_904225) baseStart_904225 baseEnd_904225 := by
    simpa [prefixWord, tailWord_904225, baseEnd_904225] using wordTrace_append hprefix tailTrace_904225
  have hstable : (prefixWord ++ tailWord_904225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904225).length < 2 ^ (prefixWord ++ tailWord_904225).sum := by decide
  have hdescent : baseEnd_904225 < baseStart_904225 := by decide
  rcases family_descends (prefixWord ++ tailWord_904225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904231 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 3]
def baseStart_904231 : Nat := 118140960795 + 904231 * 2 ^ 59
def prefixEnd_904231 : Nat := 4983230072969 + 3 ^ 40 * 904231 * 2
def baseEnd_904231 : Nat := 206357833642558633668455

theorem tailTrace_904231 : CollatzResearch.WordTrace tailWord_904231 prefixEnd_904231 206357833642558633668455 := by
  unfold tailWord_904231
  simp only [CollatzResearch.WordTrace]
  refine ⟨32980013987132992205080547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21986675991421994803387031 32980013987132992205080547)
  ·
    refine ⟨49470020980699488307620821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32980013987132992205080547 49470020980699488307620821)
    ·
      refine ⟨1159453616735144257209863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 49470020980699488307620821 1159453616735144257209863)
      ·
        refine ⟨1739180425102716385814795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159453616735144257209863 1739180425102716385814795)
        ·
          refine ⟨2608770637654074578722193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739180425102716385814795 2608770637654074578722193)
          ·
            refine ⟨1956577978240555934041645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608770637654074578722193 1956577978240555934041645)
            ·
              refine ⟨733716741840208475265617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1956577978240555934041645 733716741840208475265617)
              ·
                refine ⟨550287556380156356449213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733716741840208475265617 550287556380156356449213)
                ·
                  refine ⟨206357833642558633668455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550287556380156356449213 206357833642558633668455)
                  ·
                    rfl

theorem cell21_904231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 3].length) (baseStart_904231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904231 prefixEnd_904231 := by exact prefixLift 904231
  have htrace : WordTrace (prefixWord ++ tailWord_904231) baseStart_904231 baseEnd_904231 := by
    simpa [prefixWord, tailWord_904231, baseEnd_904231] using wordTrace_append hprefix tailTrace_904231
  have hstable : (prefixWord ++ tailWord_904231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904231).length < 2 ^ (prefixWord ++ tailWord_904231).sum := by decide
  have hdescent : baseEnd_904231 < baseStart_904231 := by decide
  rcases family_descends (prefixWord ++ tailWord_904231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904290 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_904290 : Nat := 118140960795 + 904290 * 2 ^ 59
def prefixEnd_904290 : Nat := 4983230072969 + 3 ^ 40 * 904290 * 2
def baseEnd_904290 : Nat := 206371298246387642185001

theorem tailTrace_904290 : CollatzResearch.WordTrace tailWord_904290 prefixEnd_904290 206371298246387642185001 := by
  unfold tailWord_904290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8245541473479811320369581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21988110595946163520985549 8245541473479811320369581)
  ·
    refine ⟨3092078052554929245138593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8245541473479811320369581 3092078052554929245138593)
    ·
      refine ⟨2319058539416196933853945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3092078052554929245138593 2319058539416196933853945)
      ·
        refine ⟨1739293904562147700390459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2319058539416196933853945 1739293904562147700390459)
        ·
          refine ⟨2608940856843221550585689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739293904562147700390459 2608940856843221550585689)
          ·
            refine ⟨1956705642632416162939267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2608940856843221550585689 1956705642632416162939267)
            ·
              refine ⟨2935058463948624244408901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1956705642632416162939267 2935058463948624244408901)
              ·
                refine ⟨550323461990367045826669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2935058463948624244408901 550323461990367045826669)
                ·
                  refine ⟨206371298246387642185001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550323461990367045826669 206371298246387642185001)
                  ·
                    rfl

theorem cell21_904290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_904290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904290 prefixEnd_904290 := by exact prefixLift 904290
  have htrace : WordTrace (prefixWord ++ tailWord_904290) baseStart_904290 baseEnd_904290 := by
    simpa [prefixWord, tailWord_904290, baseEnd_904290] using wordTrace_append hprefix tailTrace_904290
  have hstable : (prefixWord ++ tailWord_904290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904290).length < 2 ^ (prefixWord ++ tailWord_904290).sum := by decide
  have hdescent : baseEnd_904290 < baseStart_904290 := by decide
  rcases family_descends (prefixWord ++ tailWord_904290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904301 : List Nat := [1, 5, 1, 1, 2, 2, 3, 6]
def baseStart_904301 : Nat := 118140960795 + 904301 * 2 ^ 59
def prefixEnd_904301 : Nat := 4983230072969 + 3 ^ 40 * 904301 * 2
def baseEnd_904301 : Nat := 68791269532084689167215

theorem tailTrace_904301 : CollatzResearch.WordTrace tailWord_904301 prefixEnd_904301 68791269532084689167215 := by
  unfold tailWord_904301
  simp only [CollatzResearch.WordTrace]
  refine ⟨32982567096879394160128757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21988378064586262773419171 32982567096879394160128757)
  ·
    refine ⟨3092115665332443202512071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32982567096879394160128757 3092115665332443202512071)
    ·
      refine ⟨4638173497998664803768107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092115665332443202512071 4638173497998664803768107)
      ·
        refine ⟨6957260246997997205652161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638173497998664803768107 6957260246997997205652161)
        ·
          refine ⟨5217945185248497904239121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6957260246997997205652161 5217945185248497904239121)
          ·
            refine ⟨3913458888936373428179341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5217945185248497904239121 3913458888936373428179341)
            ·
              refine ⟨1467547083351140035567253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3913458888936373428179341 1467547083351140035567253)
              ·
                refine ⟨68791269532084689167215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1467547083351140035567253 68791269532084689167215)
                ·
                  rfl

theorem cell21_904301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 6].length) (baseStart_904301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904301 prefixEnd_904301 := by exact prefixLift 904301
  have htrace : WordTrace (prefixWord ++ tailWord_904301) baseStart_904301 baseEnd_904301 := by
    simpa [prefixWord, tailWord_904301, baseEnd_904301] using wordTrace_append hprefix tailTrace_904301
  have hstable : (prefixWord ++ tailWord_904301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904301).length < 2 ^ (prefixWord ++ tailWord_904301).sum := by decide
  have hdescent : baseEnd_904301 < baseStart_904301 := by decide
  rcases family_descends (prefixWord ++ tailWord_904301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904377 : List Nat := [1, 2, 1, 4, 1, 3, 4, 5]
def baseStart_904377 : Nat := 118140960795 + 904377 * 2 ^ 59
def prefixEnd_904377 : Nat := 4983230072969 + 3 ^ 40 * 904377 * 2
def baseEnd_904377 : Nat := 68797050943898274744941

theorem tailTrace_904377 : CollatzResearch.WordTrace tailWord_904377 prefixEnd_904377 68797050943898274744941 := by
  unfold tailWord_904377
  simp only [CollatzResearch.WordTrace]
  refine ⟨32985339044604059139895385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21990226029736039426596923 32985339044604059139895385)
  ·
    refine ⟨24739004283453044354921539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32985339044604059139895385 24739004283453044354921539)
    ·
      refine ⟨37108506425179566532382309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24739004283453044354921539 37108506425179566532382309)
      ·
        refine ⟨6957844954721168724821683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37108506425179566532382309 6957844954721168724821683)
        ·
          refine ⟨10436767432081753087232525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6957844954721168724821683 10436767432081753087232525)
          ·
            refine ⟨3913787787030657407712197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10436767432081753087232525 3913787787030657407712197)
            ·
              refine ⟨733835210068248263946037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3913787787030657407712197 733835210068248263946037)
              ·
                refine ⟨68797050943898274744941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 733835210068248263946037 68797050943898274744941)
                ·
                  rfl

theorem cell21_904377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 5].length) (baseStart_904377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904377 prefixEnd_904377 := by exact prefixLift 904377
  have htrace : WordTrace (prefixWord ++ tailWord_904377) baseStart_904377 baseEnd_904377 := by
    simpa [prefixWord, tailWord_904377, baseEnd_904377] using wordTrace_append hprefix tailTrace_904377
  have hstable : (prefixWord ++ tailWord_904377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904377).length < 2 ^ (prefixWord ++ tailWord_904377).sum := by decide
  have hdescent : baseEnd_904377 < baseStart_904377 := by decide
  rcases family_descends (prefixWord ++ tailWord_904377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904481 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_904481 : Nat := 118140960795 + 904481 * 2 ^ 59
def prefixEnd_904481 : Nat := 4983230072969 + 3 ^ 40 * 904481 * 2
def baseEnd_904481 : Nat := 206414887048613754501277

theorem tailTrace_904481 : CollatzResearch.WordTrace tailWord_904481 prefixEnd_904481 206414887048613754501277 := by
  unfold tailWord_904481
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989132236227284901681297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21992754824151523267787531 32989132236227284901681297)
  ·
    refine ⟨24741849177170463676260973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32989132236227284901681297 24741849177170463676260973)
    ·
      refine ⟨9278193441438923878597865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24741849177170463676260973 9278193441438923878597865)
      ·
        refine ⟨6958645081079192908948399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9278193441438923878597865 6958645081079192908948399)
        ·
          refine ⟨10437967621618789363422599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958645081079192908948399 10437967621618789363422599)
          ·
            refine ⟨15656951432428184045133899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437967621618789363422599 15656951432428184045133899)
            ·
              refine ⟨23485427148642276067700849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656951432428184045133899 23485427148642276067700849)
              ·
                refine ⟨17614070361481707050775637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23485427148642276067700849 17614070361481707050775637)
                ·
                  refine ⟨206414887048613754501277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17614070361481707050775637 206414887048613754501277)
                  ·
                    rfl

theorem cell21_904481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_904481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904481 prefixEnd_904481 := by exact prefixLift 904481
  have htrace : WordTrace (prefixWord ++ tailWord_904481) baseStart_904481 baseEnd_904481 := by
    simpa [prefixWord, tailWord_904481, baseEnd_904481] using wordTrace_append hprefix tailTrace_904481
  have hstable : (prefixWord ++ tailWord_904481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904481).length < 2 ^ (prefixWord ++ tailWord_904481).sum := by decide
  have hdescent : baseEnd_904481 < baseStart_904481 := by decide
  rcases family_descends (prefixWord ++ tailWord_904481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904501 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 3]
def baseStart_904501 : Nat := 118140960795 + 904501 * 2 ^ 59
def prefixEnd_904501 : Nat := 4983230072969 + 3 ^ 40 * 904501 * 2
def baseEnd_904501 : Nat := 206419451321098164167903

theorem tailTrace_904501 : CollatzResearch.WordTrace tailWord_904501 prefixEnd_904501 206419451321098164167903 := by
  unfold tailWord_904501
  simp only [CollatzResearch.WordTrace]
  refine ⟨32989861696154828317409357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21993241130769885544939571 32989861696154828317409357)
  ·
    refine ⟨12371198136058060619028509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32989861696154828317409357 12371198136058060619028509)
    ·
      refine ⟨4639199301021772732135691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12371198136058060619028509 4639199301021772732135691)
      ·
        refine ⟨6958798951532659098203537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4639199301021772732135691 6958798951532659098203537)
        ·
          refine ⟨5219099213649494323652653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6958798951532659098203537 5219099213649494323652653)
          ·
            refine ⟨1957162205118560371369745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5219099213649494323652653 1957162205118560371369745)
            ·
              refine ⟨1467871653838920278527309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1957162205118560371369745 1467871653838920278527309)
              ·
                refine ⟨550451870189595104447741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467871653838920278527309 550451870189595104447741)
                ·
                  refine ⟨206419451321098164167903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550451870189595104447741 206419451321098164167903)
                  ·
                    rfl

theorem cell21_904501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_904501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904501 prefixEnd_904501 := by exact prefixLift 904501
  have htrace : WordTrace (prefixWord ++ tailWord_904501) baseStart_904501 baseEnd_904501 := by
    simpa [prefixWord, tailWord_904501, baseEnd_904501] using wordTrace_append hprefix tailTrace_904501
  have hstable : (prefixWord ++ tailWord_904501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904501).length < 2 ^ (prefixWord ++ tailWord_904501).sum := by decide
  have hdescent : baseEnd_904501 < baseStart_904501 := by decide
  rcases family_descends (prefixWord ++ tailWord_904501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904577 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 5]
def baseStart_904577 : Nat := 118140960795 + 904577 * 2 ^ 59
def prefixEnd_904577 : Nat := 4983230072969 + 3 ^ 40 * 904577 * 2
def baseEnd_904577 : Nat := 206436795556538920901081

theorem tailTrace_904577 : CollatzResearch.WordTrace tailWord_904577 prefixEnd_904577 206436795556538920901081 := by
  unfold tailWord_904577
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992633643879493297175985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21995089095919662198117323 32992633643879493297175985)
  ·
    refine ⟨24744475232909619972881989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32992633643879493297175985 24744475232909619972881989)
    ·
      refine ⟨4639589106170553744915373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24744475232909619972881989 4639589106170553744915373)
      ·
        refine ⟨1739845914813957654343265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4639589106170553744915373 1739845914813957654343265)
        ·
          refine ⟨1304884436110468240757449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1739845914813957654343265 1304884436110468240757449)
          ·
            refine ⟨978663327082851180568087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304884436110468240757449 978663327082851180568087)
            ·
              refine ⟨1467994990624276770852131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978663327082851180568087 1467994990624276770852131)
              ·
                refine ⟨2201992485936415156278197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1467994990624276770852131 2201992485936415156278197)
                ·
                  refine ⟨206436795556538920901081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2201992485936415156278197 206436795556538920901081)
                  ·
                    rfl

theorem cell21_904577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_904577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904577 prefixEnd_904577 := by exact prefixLift 904577
  have htrace : WordTrace (prefixWord ++ tailWord_904577) baseStart_904577 baseEnd_904577 := by
    simpa [prefixWord, tailWord_904577, baseEnd_904577] using wordTrace_append hprefix tailTrace_904577
  have hstable : (prefixWord ++ tailWord_904577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904577).length < 2 ^ (prefixWord ++ tailWord_904577).sum := by decide
  have hdescent : baseEnd_904577 < baseStart_904577 := by decide
  rcases family_descends (prefixWord ++ tailWord_904577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904588 : List Nat := [2, 2, 1, 2, 1, 3, 4, 6]
def baseStart_904588 : Nat := 118140960795 + 904588 * 2 ^ 59
def prefixEnd_904588 : Nat := 4983230072969 + 3 ^ 40 * 904588 * 2
def baseEnd_904588 : Nat := 68813101968801782072575

theorem tailTrace_904588 : CollatzResearch.WordTrace tailWord_904588 prefixEnd_904588 68813101968801782072575 := by
  unfold tailWord_904588
  simp only [CollatzResearch.WordTrace]
  refine ⟨16496517423419821087913209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21995356564559761450550945 16496517423419821087913209)
  ·
    refine ⟨12372388067564865815934907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16496517423419821087913209 12372388067564865815934907)
    ·
      refine ⟨18558582101347298723902361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12372388067564865815934907 18558582101347298723902361)
      ·
        refine ⟨13918936576010474042926771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18558582101347298723902361 13918936576010474042926771)
        ·
          refine ⟨20878404864015711064390157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13918936576010474042926771 20878404864015711064390157)
          ·
            refine ⟨7829401824005891649146309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20878404864015711064390157 7829401824005891649146309)
            ·
              refine ⟨1468012842001104684214933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7829401824005891649146309 1468012842001104684214933)
              ·
                refine ⟨68813101968801782072575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1468012842001104684214933 68813101968801782072575)
                ·
                  rfl

theorem cell21_904588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_904588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904588 prefixEnd_904588 := by exact prefixLift 904588
  have htrace : WordTrace (prefixWord ++ tailWord_904588) baseStart_904588 baseEnd_904588 := by
    simpa [prefixWord, tailWord_904588, baseEnd_904588] using wordTrace_append hprefix tailTrace_904588
  have hstable : (prefixWord ++ tailWord_904588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904588).length < 2 ^ (prefixWord ++ tailWord_904588).sum := by decide
  have hdescent : baseEnd_904588 < baseStart_904588 := by decide
  rcases family_descends (prefixWord ++ tailWord_904588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904650 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_904650 : Nat := 118140960795 + 904650 * 2 ^ 59
def prefixEnd_904650 : Nat := 4983230072969 + 3 ^ 40 * 904650 * 2
def baseEnd_904650 : Nat := 206453455151107016184265

theorem tailTrace_904650 : CollatzResearch.WordTrace tailWord_904650 prefixEnd_904650 206453455151107016184265 := by
  unfold tailWord_904650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8248824043153756691145851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21996864115076684509722269 8248824043153756691145851)
  ·
    refine ⟨12373236064730635036718777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8248824043153756691145851 12373236064730635036718777)
    ·
      refine ⟨9279927048547976277539083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12373236064730635036718777 9279927048547976277539083)
      ·
        refine ⟨13919890572821964416308625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9279927048547976277539083 13919890572821964416308625)
        ·
          refine ⟨10439917929616473312231469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13919890572821964416308625 10439917929616473312231469)
          ·
            refine ⟨3914969223606177492086801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10439917929616473312231469 3914969223606177492086801)
            ·
              refine ⟨2936226917704633119065101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3914969223606177492086801 2936226917704633119065101)
              ·
                refine ⟨1101085094139237419649413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2936226917704633119065101 1101085094139237419649413)
                ·
                  refine ⟨206453455151107016184265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101085094139237419649413 206453455151107016184265)
                  ·
                    rfl

theorem cell21_904650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_904650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904650 prefixEnd_904650 := by exact prefixLift 904650
  have htrace : WordTrace (prefixWord ++ tailWord_904650) baseStart_904650 baseEnd_904650 := by
    simpa [prefixWord, tailWord_904650, baseEnd_904650] using wordTrace_append hprefix tailTrace_904650
  have hstable : (prefixWord ++ tailWord_904650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904650).length < 2 ^ (prefixWord ++ tailWord_904650).sum := by decide
  have hdescent : baseEnd_904650 < baseStart_904650 := by decide
  rcases family_descends (prefixWord ++ tailWord_904650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904788 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_904788 : Nat := 118140960795 + 904788 * 2 ^ 59
def prefixEnd_904788 : Nat := 4983230072969 + 3 ^ 40 * 904788 * 2
def baseEnd_904788 : Nat := 206484948631249442883983

theorem tailTrace_904788 : CollatzResearch.WordTrace tailWord_904788 prefixEnd_904788 206484948631249442883983 := by
  unfold tailWord_904788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500164723057538166553509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22000219630743384222071345 16500164723057538166553509)
  ·
    refine ⟨3093780885573288406228783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16500164723057538166553509 3093780885573288406228783)
    ·
      refine ⟨4640671328359932609343175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3093780885573288406228783 4640671328359932609343175)
      ·
        refine ⟨6961006992539898914014763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640671328359932609343175 6961006992539898914014763)
        ·
          refine ⟨10441510488809848371022145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961006992539898914014763 10441510488809848371022145)
          ·
            refine ⟨7831132866607386278266609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10441510488809848371022145 7831132866607386278266609)
            ·
              refine ⟨5873349649955539708699957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7831132866607386278266609 5873349649955539708699957)
              ·
                refine ⟨550626529683331847690621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5873349649955539708699957 550626529683331847690621)
                ·
                  refine ⟨206484948631249442883983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550626529683331847690621 206484948631249442883983)
                  ·
                    rfl

theorem cell21_904788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_904788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904788 prefixEnd_904788 := by exact prefixLift 904788
  have htrace : WordTrace (prefixWord ++ tailWord_904788) baseStart_904788 baseEnd_904788 := by
    simpa [prefixWord, tailWord_904788, baseEnd_904788] using wordTrace_append hprefix tailTrace_904788
  have hstable : (prefixWord ++ tailWord_904788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904788).length < 2 ^ (prefixWord ++ tailWord_904788).sum := by decide
  have hdescent : baseEnd_904788 < baseStart_904788 := by decide
  rcases family_descends (prefixWord ++ tailWord_904788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904805 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 3]
def baseStart_904805 : Nat := 118140960795 + 904805 * 2 ^ 59
def prefixEnd_904805 : Nat := 4983230072969 + 3 ^ 40 * 904805 * 2
def baseEnd_904805 : Nat := 206488828262861191100615

theorem tailTrace_904805 : CollatzResearch.WordTrace tailWord_904805 prefixEnd_904805 206488828262861191100615 := by
  unfold tailWord_904805
  simp only [CollatzResearch.WordTrace]
  refine ⟨33000949487053488236475869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22000632991368992157650579 33000949487053488236475869)
  ·
    refine ⟨12375356057645058088678451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33000949487053488236475869 12375356057645058088678451)
    ·
      refine ⟨18563034086467587133017677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12375356057645058088678451 18563034086467587133017677)
      ·
        refine ⟨6961137782425345174881629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18563034086467587133017677 6961137782425345174881629)
        ·
          refine ⟨2610426668409504440580611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6961137782425345174881629 2610426668409504440580611)
          ·
            refine ⟨3915640002614256660870917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610426668409504440580611 3915640002614256660870917)
            ·
              refine ⟨734182500490173123913297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3915640002614256660870917 734182500490173123913297)
              ·
                refine ⟨550636875367629842934973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734182500490173123913297 550636875367629842934973)
                ·
                  refine ⟨206488828262861191100615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550636875367629842934973 206488828262861191100615)
                  ·
                    rfl

theorem cell21_904805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_904805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904805 prefixEnd_904805 := by exact prefixLift 904805
  have htrace : WordTrace (prefixWord ++ tailWord_904805) baseStart_904805 baseEnd_904805 := by
    simpa [prefixWord, tailWord_904805, baseEnd_904805] using wordTrace_append hprefix tailTrace_904805
  have hstable : (prefixWord ++ tailWord_904805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904805).length < 2 ^ (prefixWord ++ tailWord_904805).sum := by decide
  have hdescent : baseEnd_904805 < baseStart_904805 := by decide
  rcases family_descends (prefixWord ++ tailWord_904805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904816 : List Nat := [2, 1, 1, 1, 6, 1, 3, 6]
def baseStart_904816 : Nat := 118140960795 + 904816 * 2 ^ 59
def prefixEnd_904816 : Nat := 4983230072969 + 3 ^ 40 * 904816 * 2
def baseEnd_904816 : Nat := 68830446204242538805753

theorem tailTrace_904816 : CollatzResearch.WordTrace tailWord_904816 prefixEnd_904816 68830446204242538805753 := by
  unfold tailWord_904816
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500675345006818557563151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22000900460009091410084201 16500675345006818557563151)
  ·
    refine ⟨24751013017510227836344727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16500675345006818557563151 24751013017510227836344727)
    ·
      refine ⟨37126519526265341754517091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24751013017510227836344727 37126519526265341754517091)
      ·
        refine ⟨55689779289398012631775637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37126519526265341754517091 55689779289398012631775637)
        ·
          refine ⟨2610458404190531842114483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55689779289398012631775637 2610458404190531842114483)
          ·
            refine ⟨3915687606285797763171725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610458404190531842114483 3915687606285797763171725)
            ·
              refine ⟨1468382852357174161189397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915687606285797763171725 1468382852357174161189397)
              ·
                refine ⟨68830446204242538805753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1468382852357174161189397 68830446204242538805753)
                ·
                  rfl

theorem cell21_904816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_904816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904816 prefixEnd_904816 := by exact prefixLift 904816
  have htrace : WordTrace (prefixWord ++ tailWord_904816) baseStart_904816 baseEnd_904816 := by
    simpa [prefixWord, tailWord_904816, baseEnd_904816] using wordTrace_append hprefix tailTrace_904816
  have hstable : (prefixWord ++ tailWord_904816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904816).length < 2 ^ (prefixWord ++ tailWord_904816).sum := by decide
  have hdescent : baseEnd_904816 < baseStart_904816 := by decide
  rcases family_descends (prefixWord ++ tailWord_904816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904833 : List Nat := [1, 2, 4, 2, 1, 3, 3, 5]
def baseStart_904833 : Nat := 118140960795 + 904833 * 2 ^ 59
def prefixEnd_904833 : Nat := 4983230072969 + 3 ^ 40 * 904833 * 2
def baseEnd_904833 : Nat := 68831739414779788211297

theorem tailTrace_904833 : CollatzResearch.WordTrace tailWord_904833 prefixEnd_904833 68831739414779788211297 := by
  unfold tailWord_904833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33001970730952049018495153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22001313820634699345663435 33001970730952049018495153)
  ·
    refine ⟨24751478048214036763871365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33001970730952049018495153 24751478048214036763871365)
    ·
      refine ⟨4640902134040131893225881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24751478048214036763871365 4640902134040131893225881)
      ·
        refine ⟨3480676600530098919919411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4640902134040131893225881 3480676600530098919919411)
        ·
          refine ⟨5221014900795148379879117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480676600530098919919411 5221014900795148379879117)
          ·
            refine ⟨1957880587798180642454669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5221014900795148379879117 1957880587798180642454669)
            ·
              refine ⟨734205220424317740920501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1957880587798180642454669 734205220424317740920501)
              ·
                refine ⟨68831739414779788211297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 734205220424317740920501 68831739414779788211297)
                ·
                  rfl

theorem cell21_904833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 5].length) (baseStart_904833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904833 prefixEnd_904833 := by exact prefixLift 904833
  have htrace : WordTrace (prefixWord ++ tailWord_904833) baseStart_904833 baseEnd_904833 := by
    simpa [prefixWord, tailWord_904833, baseEnd_904833] using wordTrace_append hprefix tailTrace_904833
  have hstable : (prefixWord ++ tailWord_904833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904833).length < 2 ^ (prefixWord ++ tailWord_904833).sum := by decide
  have hdescent : baseEnd_904833 < baseStart_904833 := by decide
  rcases family_descends (prefixWord ++ tailWord_904833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904864 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_904864 : Nat := 118140960795 + 904864 * 2 ^ 59
def prefixEnd_904864 : Nat := 4983230072969 + 3 ^ 40 * 904864 * 2
def baseEnd_904864 : Nat := 206502292866690199617161

theorem tailTrace_904864 : CollatzResearch.WordTrace tailWord_904864 prefixEnd_904864 206502292866690199617161 := by
  unfold tailWord_904864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16501550696919870656436823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22002067595893160875249097 16501550696919870656436823)
  ·
    refine ⟨24752326045379805984655235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16501550696919870656436823 24752326045379805984655235)
    ·
      refine ⟨37128489068069708976982853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24752326045379805984655235 37128489068069708976982853)
      ·
        refine ⟨6961591700263070433184285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37128489068069708976982853 6961591700263070433184285)
        ·
          refine ⟨2610596887598651412444107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6961591700263070433184285 2610596887598651412444107)
          ·
            refine ⟨3915895331397977118666161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610596887598651412444107 3915895331397977118666161)
            ·
              refine ⟨2936921498548482838999621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3915895331397977118666161 2936921498548482838999621)
              ·
                refine ⟨550672780977840532312429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2936921498548482838999621 550672780977840532312429)
                ·
                  refine ⟨206502292866690199617161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550672780977840532312429 206502292866690199617161)
                  ·
                    rfl

theorem cell21_904864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_904864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904864 prefixEnd_904864 := by exact prefixLift 904864
  have htrace : WordTrace (prefixWord ++ tailWord_904864) baseStart_904864 baseEnd_904864 := by
    simpa [prefixWord, tailWord_904864, baseEnd_904864] using wordTrace_append hprefix tailTrace_904864
  have hstable : (prefixWord ++ tailWord_904864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904864).length < 2 ^ (prefixWord ++ tailWord_904864).sum := by decide
  have hdescent : baseEnd_904864 < baseStart_904864 := by decide
  rcases family_descends (prefixWord ++ tailWord_904864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904892 : List Nat := [2, 2, 2, 3, 1, 3, 1, 7]
def baseStart_904892 : Nat := 118140960795 + 904892 * 2 ^ 59
def prefixEnd_904892 : Nat := 4983230072969 + 3 ^ 40 * 904892 * 2
def baseEnd_904892 : Nat := 68836227616056124383479

theorem tailTrace_904892 : CollatzResearch.WordTrace tailWord_904892 prefixEnd_904892 68836227616056124383479 := by
  unfold tailWord_904892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502061318869151047446465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22002748425158868063261953 16502061318869151047446465)
  ·
    refine ⟨12376545989151863285584849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16502061318869151047446465 12376545989151863285584849)
    ·
      refine ⟨9282409491863897464188637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12376545989151863285584849 9282409491863897464188637)
      ·
        refine ⟨3480903559448961549070739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9282409491863897464188637 3480903559448961549070739)
        ·
          refine ⟨5221355339173442323606109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3480903559448961549070739 5221355339173442323606109)
          ·
            refine ⟨1958008252190040871352291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5221355339173442323606109 1958008252190040871352291)
            ·
              refine ⟨2937012378285061307028437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1958008252190040871352291 2937012378285061307028437)
              ·
                refine ⟨68836227616056124383479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2937012378285061307028437 68836227616056124383479)
                ·
                  rfl

theorem cell21_904892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_904892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904892 prefixEnd_904892 := by exact prefixLift 904892
  have htrace : WordTrace (prefixWord ++ tailWord_904892) baseStart_904892 baseEnd_904892 := by
    simpa [prefixWord, tailWord_904892, baseEnd_904892] using wordTrace_append hprefix tailTrace_904892
  have hstable : (prefixWord ++ tailWord_904892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904892).length < 2 ^ (prefixWord ++ tailWord_904892).sum := by decide
  have hdescent : baseEnd_904892 < baseStart_904892 := by decide
  rcases family_descends (prefixWord ++ tailWord_904892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904909 : List Nat := [1, 6, 2, 1, 1, 1, 9]
def baseStart_904909 : Nat := 118140960795 + 904909 * 2 ^ 59
def prefixEnd_904909 : Nat := 4983230072969 + 3 ^ 40 * 904909 * 2
def baseEnd_904909 : Nat := 22945840275531124596341

theorem tailTrace_904909 : CollatzResearch.WordTrace tailWord_904909 prefixEnd_904909 22945840275531124596341 := by
  unfold tailWord_904909
  simp only [CollatzResearch.WordTrace]
  refine ⟨33004742678676713998261781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22003161785784475998841187 33004742678676713998261781)
  ·
    refine ⟨1547097313062970968668521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33004742678676713998261781 1547097313062970968668521)
    ·
      refine ⟨1160322984797228226501391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1547097313062970968668521 1160322984797228226501391)
      ·
        refine ⟨1740484477195842339752087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160322984797228226501391 1740484477195842339752087)
        ·
          refine ⟨2610726715793763509628131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740484477195842339752087 2610726715793763509628131)
          ·
            refine ⟨3916090073690645264442197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610726715793763509628131 3916090073690645264442197)
            ·
              refine ⟨22945840275531124596341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3916090073690645264442197 22945840275531124596341)
              ·
                rfl

theorem cell21_904909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 9].length) (baseStart_904909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904909 prefixEnd_904909 := by exact prefixLift 904909
  have htrace : WordTrace (prefixWord ++ tailWord_904909) baseStart_904909 baseEnd_904909 := by
    simpa [prefixWord, tailWord_904909, baseEnd_904909] using wordTrace_append hprefix tailTrace_904909
  have hstable : (prefixWord ++ tailWord_904909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904909).length < 2 ^ (prefixWord ++ tailWord_904909).sum := by decide
  have hdescent : baseEnd_904909 < baseStart_904909 := by decide
  rcases family_descends (prefixWord ++ tailWord_904909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904951 : List Nat := [1, 1, 3, 1, 1, 1, 6, 7]
def baseStart_904951 : Nat := 118140960795 + 904951 * 2 ^ 59
def prefixEnd_904951 : Nat := 4983230072969 + 3 ^ 40 * 904951 * 2
def baseEnd_904951 : Nat := 68840715817332460555661

theorem tailTrace_904951 : CollatzResearch.WordTrace tailWord_904951 prefixEnd_904951 68840715817332460555661 := by
  unfold tailWord_904951
  simp only [CollatzResearch.WordTrace]
  refine ⟨33006274544524555171290707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22004183029683036780860471 33006274544524555171290707)
  ·
    refine ⟨49509411816786832756936061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33006274544524555171290707 49509411816786832756936061)
    ·
      refine ⟨18566029431295062283851023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49509411816786832756936061 18566029431295062283851023)
      ·
        refine ⟨27849044146942593425776535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18566029431295062283851023 27849044146942593425776535)
        ·
          refine ⟨41773566220413890138664803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27849044146942593425776535 41773566220413890138664803)
          ·
            refine ⟨62660349330620835207997205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41773566220413890138664803 62660349330620835207997205)
            ·
              refine ⟨2937203874872851650374869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62660349330620835207997205 2937203874872851650374869)
              ·
                refine ⟨68840715817332460555661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2937203874872851650374869 68840715817332460555661)
                ·
                  rfl

theorem cell21_904951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_904951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904951 prefixEnd_904951 := by exact prefixLift 904951
  have htrace : WordTrace (prefixWord ++ tailWord_904951) baseStart_904951 baseEnd_904951 := by
    simpa [prefixWord, tailWord_904951, baseEnd_904951] using wordTrace_append hprefix tailTrace_904951
  have hstable : (prefixWord ++ tailWord_904951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904951).length < 2 ^ (prefixWord ++ tailWord_904951).sum := by decide
  have hdescent : baseEnd_904951 < baseStart_904951 := by decide
  rcases family_descends (prefixWord ++ tailWord_904951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_904966 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_904966 : Nat := 118140960795 + 904966 * 2 ^ 59
def prefixEnd_904966 : Nat := 4983230072969 + 3 ^ 40 * 904966 * 2
def baseEnd_904966 : Nat := 206525570656360688916953

theorem tailTrace_904966 : CollatzResearch.WordTrace tailWord_904966 prefixEnd_904966 206525570656360688916953 := by
  unfold tailWord_904966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031463176233444147908961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22004547759646808488724501 1031463176233444147908961)
  ·
    refine ⟨773597382175083110931721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1031463176233444147908961 773597382175083110931721)
    ·
      refine ⟨580198036631312333198791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 773597382175083110931721 580198036631312333198791)
      ·
        refine ⟨870297054946968499798187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580198036631312333198791 870297054946968499798187)
        ·
          refine ⟨1305445582420452749697281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870297054946968499798187 1305445582420452749697281)
          ·
            refine ⟨979084186815339562272961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305445582420452749697281 979084186815339562272961)
            ·
              refine ⟨734313140111504671704721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979084186815339562272961 734313140111504671704721)
              ·
                refine ⟨550734855083628503778541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734313140111504671704721 550734855083628503778541)
                ·
                  refine ⟨206525570656360688916953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550734855083628503778541 206525570656360688916953)
                  ·
                    rfl

theorem cell21_904966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_904966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_904966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_904966 prefixEnd_904966 := by exact prefixLift 904966
  have htrace : WordTrace (prefixWord ++ tailWord_904966) baseStart_904966 baseEnd_904966 := by
    simpa [prefixWord, tailWord_904966, baseEnd_904966] using wordTrace_append hprefix tailTrace_904966
  have hstable : (prefixWord ++ tailWord_904966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_904966).length < 2 ^ (prefixWord ++ tailWord_904966).sum := by decide
  have hdescent : baseEnd_904966 < baseStart_904966 := by decide
  rcases family_descends (prefixWord ++ tailWord_904966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905016 : List Nat := [2, 1, 2, 1, 3, 4, 2, 3, 3]
def baseStart_905016 : Nat := 118140960795 + 905016 * 2 ^ 59
def prefixEnd_905016 : Nat := 4983230072969 + 3 ^ 40 * 905016 * 2
def baseEnd_905016 : Nat := 206536981337571713083517

theorem tailTrace_905016 : CollatzResearch.WordTrace tailWord_905016 prefixEnd_905016 206536981337571713083517 := by
  unfold tailWord_905016
  simp only [CollatzResearch.WordTrace]
  refine ⟨16504322644644535636203451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22005763526192714181604601 16504322644644535636203451)
  ·
    refine ⟨24756483966966803454305177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16504322644644535636203451 24756483966966803454305177)
    ·
      refine ⟨18567362975225102590728883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24756483966966803454305177 18567362975225102590728883)
      ·
        refine ⟨27851044462837653886093325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18567362975225102590728883 27851044462837653886093325)
        ·
          refine ⟨10444141673564120207284997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27851044462837653886093325 10444141673564120207284997)
          ·
            refine ⟨1958276563793272538865937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10444141673564120207284997 1958276563793272538865937)
            ·
              refine ⟨1468707422844954404149453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958276563793272538865937 1468707422844954404149453)
              ·
                refine ⟨550765283566857901556045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1468707422844954404149453 550765283566857901556045)
                ·
                  refine ⟨206536981337571713083517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550765283566857901556045 206536981337571713083517)
                  ·
                    rfl

theorem cell21_905016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_905016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905016 prefixEnd_905016 := by exact prefixLift 905016
  have htrace : WordTrace (prefixWord ++ tailWord_905016) baseStart_905016 baseEnd_905016 := by
    simpa [prefixWord, tailWord_905016, baseEnd_905016] using wordTrace_append hprefix tailTrace_905016
  have hstable : (prefixWord ++ tailWord_905016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905016).length < 2 ^ (prefixWord ++ tailWord_905016).sum := by decide
  have hdescent : baseEnd_905016 < baseStart_905016 := by decide
  rcases family_descends (prefixWord ++ tailWord_905016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905027 : List Nat := [1, 1, 1, 3, 1, 6, 8]
def baseStart_905027 : Nat := 118140960795 + 905027 * 2 ^ 59
def prefixEnd_905027 : Nat := 4983230072969 + 3 ^ 40 * 905027 * 2
def baseEnd_905027 : Nat := 22948832409715348711129

theorem tailTrace_905027 : CollatzResearch.WordTrace tailWord_905027 prefixEnd_905027 22948832409715348711129 := by
  unfold tailWord_905027
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009046492249220151057335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22006030994832813434038223 33009046492249220151057335)
  ·
    refine ⟨49513569738373830226586003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33009046492249220151057335 49513569738373830226586003)
    ·
      refine ⟨74270354607560745339879005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49513569738373830226586003 74270354607560745339879005)
      ·
        refine ⟨27851382977835279502454627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74270354607560745339879005 27851382977835279502454627)
        ·
          refine ⟨41777074466752919253681941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27851382977835279502454627 41777074466752919253681941)
          ·
            refine ⟨1958300365629043090016341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41777074466752919253681941 1958300365629043090016341)
            ·
              refine ⟨22948832409715348711129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1958300365629043090016341 22948832409715348711129)
              ·
                rfl

theorem cell21_905027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 8].length) (baseStart_905027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905027 prefixEnd_905027 := by exact prefixLift 905027
  have htrace : WordTrace (prefixWord ++ tailWord_905027) baseStart_905027 baseEnd_905027 := by
    simpa [prefixWord, tailWord_905027, baseEnd_905027] using wordTrace_append hprefix tailTrace_905027
  have hstable : (prefixWord ++ tailWord_905027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905027).length < 2 ^ (prefixWord ++ tailWord_905027).sum := by decide
  have hdescent : baseEnd_905027 < baseStart_905027 := by decide
  rcases family_descends (prefixWord ++ tailWord_905027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905047 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 4]
def baseStart_905047 : Nat := 118140960795 + 905047 * 2 ^ 59
def prefixEnd_905047 : Nat := 4983230072969 + 3 ^ 40 * 905047 * 2
def baseEnd_905047 : Nat := 206544055959922548066787

theorem tailTrace_905047 : CollatzResearch.WordTrace tailWord_905047 prefixEnd_905047 206544055959922548066787 := by
  unfold tailWord_905047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009775952176763566785395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22006517301451175711190263 33009775952176763566785395)
  ·
    refine ⟨49514663928265145350178093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33009775952176763566785395 49514663928265145350178093)
    ·
      refine ⟨18567998973099429506316785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49514663928265145350178093 18567998973099429506316785)
      ·
        refine ⟨13925999229824572129737589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18567998973099429506316785 13925999229824572129737589)
        ·
          refine ⟨1305562427796053637162899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13925999229824572129737589 1305562427796053637162899)
          ·
            refine ⟨1958343641694080455744349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305562427796053637162899 1958343641694080455744349)
            ·
              refine ⟨734378865635280170904131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1958343641694080455744349 734378865635280170904131)
              ·
                refine ⟨1101568298452920256356197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 734378865635280170904131 1101568298452920256356197)
                ·
                  refine ⟨206544055959922548066787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101568298452920256356197 206544055959922548066787)
                  ·
                    rfl

theorem cell21_905047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 4].length) (baseStart_905047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905047 prefixEnd_905047 := by exact prefixLift 905047
  have htrace : WordTrace (prefixWord ++ tailWord_905047) baseStart_905047 baseEnd_905047 := by
    simpa [prefixWord, tailWord_905047, baseEnd_905047] using wordTrace_append hprefix tailTrace_905047
  have hstable : (prefixWord ++ tailWord_905047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905047).length < 2 ^ (prefixWord ++ tailWord_905047).sum := by decide
  have hdescent : baseEnd_905047 < baseStart_905047 := by decide
  rcases family_descends (prefixWord ++ tailWord_905047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905078 : List Nat := [5, 1, 1, 3, 3, 1, 7]
def baseStart_905078 : Nat := 118140960795 + 905078 * 2 ^ 59
def prefixEnd_905078 : Nat := 4983230072969 + 3 ^ 40 * 905078 * 2
def baseEnd_905078 : Nat := 22950125620252598116673

theorem tailTrace_905078 : CollatzResearch.WordTrace tailWord_905078 prefixEnd_905078 22950125620252598116673 := by
  unfold tailWord_905078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063181663441528491322743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22007271076709637240775925 2063181663441528491322743)
  ·
    refine ⟨3094772495162292736984115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063181663441528491322743 3094772495162292736984115)
    ·
      refine ⟨4642158742743439105476173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3094772495162292736984115 4642158742743439105476173)
      ·
        refine ⟨1740809528528789664553565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4642158742743439105476173 1740809528528789664553565)
        ·
          refine ⟨652803573198296124207587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1740809528528789664553565 652803573198296124207587)
          ·
            refine ⟨979205359797444186311381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652803573198296124207587 979205359797444186311381)
            ·
              refine ⟨22950125620252598116673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 979205359797444186311381 22950125620252598116673)
              ·
                rfl

theorem cell21_905078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 7].length) (baseStart_905078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905078 prefixEnd_905078 := by exact prefixLift 905078
  have htrace : WordTrace (prefixWord ++ tailWord_905078) baseStart_905078 baseEnd_905078 := by
    simpa [prefixWord, tailWord_905078, baseEnd_905078] using wordTrace_append hprefix tailTrace_905078
  have hstable : (prefixWord ++ tailWord_905078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905078).length < 2 ^ (prefixWord ++ tailWord_905078).sum := by decide
  have hdescent : baseEnd_905078 < baseStart_905078 := by decide
  rcases family_descends (prefixWord ++ tailWord_905078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905140 : List Nat := [2, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_905140 : Nat := 118140960795 + 905140 * 2 ^ 59
def prefixEnd_905140 : Nat := 4983230072969 + 3 ^ 40 * 905140 * 2
def baseEnd_905140 : Nat := 206565279826975053016597

theorem tailTrace_905140 : CollatzResearch.WordTrace tailWord_905140 prefixEnd_905140 206565279826975053016597 := by
  unfold tailWord_905140
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506583970419920224960437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22008778627226560299947249 16506583970419920224960437)
  ·
    refine ⟨1547492247226867521090041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16506583970419920224960437 1547492247226867521090041)
    ·
      refine ⟨1160619185420150640817531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1547492247226867521090041 1160619185420150640817531)
      ·
        refine ⟨1740928778130225961226297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160619185420150640817531 1740928778130225961226297)
        ·
          refine ⟨1305696583597669470919723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1740928778130225961226297 1305696583597669470919723)
          ·
            refine ⟨1958544875396504206379585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305696583597669470919723 1958544875396504206379585)
            ·
              refine ⟨1468908656547378154784689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958544875396504206379585 1468908656547378154784689)
              ·
                refine ⟨1101681492410533616088517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1468908656547378154784689 1101681492410533616088517)
                ·
                  refine ⟨206565279826975053016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101681492410533616088517 206565279826975053016597)
                  ·
                    rfl

theorem cell21_905140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_905140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905140 prefixEnd_905140 := by exact prefixLift 905140
  have htrace : WordTrace (prefixWord ++ tailWord_905140) baseStart_905140 baseEnd_905140 := by
    simpa [prefixWord, tailWord_905140, baseEnd_905140] using wordTrace_append hprefix tailTrace_905140
  have hstable : (prefixWord ++ tailWord_905140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905140).length < 2 ^ (prefixWord ++ tailWord_905140).sum := by decide
  have hdescent : baseEnd_905140 < baseStart_905140 := by decide
  rcases family_descends (prefixWord ++ tailWord_905140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905151 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 3]
def baseStart_905151 : Nat := 118140960795 + 905151 * 2 ^ 59
def prefixEnd_905151 : Nat := 4983230072969 + 3 ^ 40 * 905151 * 2
def baseEnd_905151 : Nat := 206567790176841478333241

theorem tailTrace_905151 : CollatzResearch.WordTrace tailWord_905151 prefixEnd_905151 206567790176841478333241 := by
  unfold tailWord_905151
  simp only [CollatzResearch.WordTrace]
  refine ⟨33013569143799989328571307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22009046095866659552380871 33013569143799989328571307)
  ·
    refine ⟨49520353715699983992856961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33013569143799989328571307 49520353715699983992856961)
    ·
      refine ⟨37140265286774987994642721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49520353715699983992856961 37140265286774987994642721)
      ·
        refine ⟨27855198965081240995982041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37140265286774987994642721 27855198965081240995982041)
        ·
          refine ⟨20891399223810930746986531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27855198965081240995982041 20891399223810930746986531)
          ·
            refine ⟨31337098835716396120479797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20891399223810930746986531 31337098835716396120479797)
            ·
              refine ⟨2937853015848412136294981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31337098835716396120479797 2937853015848412136294981)
              ·
                refine ⟨550847440471577275555309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2937853015848412136294981 550847440471577275555309)
                ·
                  refine ⟨206567790176841478333241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550847440471577275555309 206567790176841478333241)
                  ·
                    rfl

theorem cell21_905151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 3].length) (baseStart_905151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905151 prefixEnd_905151 := by exact prefixLift 905151
  have htrace : WordTrace (prefixWord ++ tailWord_905151) baseStart_905151 baseEnd_905151 := by
    simpa [prefixWord, tailWord_905151, baseEnd_905151] using wordTrace_append hprefix tailTrace_905151
  have hstable : (prefixWord ++ tailWord_905151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905151).length < 2 ^ (prefixWord ++ tailWord_905151).sum := by decide
  have hdescent : baseEnd_905151 < baseStart_905151 := by decide
  rcases family_descends (prefixWord ++ tailWord_905151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905244 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 3]
def baseStart_905244 : Nat := 118140960795 + 905244 * 2 ^ 59
def prefixEnd_905244 : Nat := 4983230072969 + 3 ^ 40 * 905244 * 2
def baseEnd_905244 : Nat := 206589014043893983283051

theorem tailTrace_905244 : CollatzResearch.WordTrace tailWord_905244 prefixEnd_905244 206589014043893983283051 := by
  unfold tailWord_905244
  simp only [CollatzResearch.WordTrace]
  refine ⟨16508480566231533105853393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22011307421642044141137857 16508480566231533105853393)
  ·
    refine ⟨12381360424673649829390045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16508480566231533105853393 12381360424673649829390045)
    ·
      refine ⟨4643010159252618686021267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12381360424673649829390045 4643010159252618686021267)
      ·
        refine ⟨6964515238878928029031901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643010159252618686021267 6964515238878928029031901)
        ·
          refine ⟨2611693214579598010886963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6964515238878928029031901 2611693214579598010886963)
          ·
            refine ⟨3917539821869397016330445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2611693214579598010886963 3917539821869397016330445)
            ·
              refine ⟨1469077433201023881123917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3917539821869397016330445 1469077433201023881123917)
              ·
                refine ⟨550904037450383955421469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1469077433201023881123917 550904037450383955421469)
                ·
                  refine ⟨206589014043893983283051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 550904037450383955421469 206589014043893983283051)
                  ·
                    rfl

theorem cell21_905244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_905244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905244 prefixEnd_905244 := by exact prefixLift 905244
  have htrace : WordTrace (prefixWord ++ tailWord_905244) baseStart_905244 baseEnd_905244 := by
    simpa [prefixWord, tailWord_905244, baseEnd_905244] using wordTrace_append hprefix tailTrace_905244
  have hstable : (prefixWord ++ tailWord_905244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905244).length < 2 ^ (prefixWord ++ tailWord_905244).sum := by decide
  have hdescent : baseEnd_905244 < baseStart_905244 := by decide
  rcases family_descends (prefixWord ++ tailWord_905244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905272 : List Nat := [2, 1, 2, 1, 6, 1, 2, 6]
def baseStart_905272 : Nat := 118140960795 + 905272 * 2 ^ 59
def prefixEnd_905272 : Nat := 4983230072969 + 3 ^ 40 * 905272 * 2
def baseEnd_905272 : Nat := 68865134675124052272109

theorem tailTrace_905272 : CollatzResearch.WordTrace tailWord_905272 prefixEnd_905272 68865134675124052272109 := by
  unfold tailWord_905272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16508991188180813496863035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22011988250907751329150713 16508991188180813496863035)
  ·
    refine ⟨24763486782271220245294553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16508991188180813496863035 24763486782271220245294553)
    ·
      refine ⟨18572615086703415183970915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24763486782271220245294553 18572615086703415183970915)
      ·
        refine ⟨27858922630055122775956373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18572615086703415183970915 27858922630055122775956373)
        ·
          refine ⟨1305886998283833880122955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27858922630055122775956373 1305886998283833880122955)
          ·
            refine ⟨1958830497425750820184433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1305886998283833880122955 1958830497425750820184433)
            ·
              refine ⟨1469122873069313115138325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1958830497425750820184433 1469122873069313115138325)
              ·
                refine ⟨68865134675124052272109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1469122873069313115138325 68865134675124052272109)
                ·
                  rfl

theorem cell21_905272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_905272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905272 prefixEnd_905272 := by exact prefixLift 905272
  have htrace : WordTrace (prefixWord ++ tailWord_905272) baseStart_905272 baseEnd_905272 := by
    simpa [prefixWord, tailWord_905272, baseEnd_905272] using wordTrace_append hprefix tailTrace_905272
  have hstable : (prefixWord ++ tailWord_905272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905272).length < 2 ^ (prefixWord ++ tailWord_905272).sum := by decide
  have hdescent : baseEnd_905272 < baseStart_905272 := by decide
  rcases family_descends (prefixWord ++ tailWord_905272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905317 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 4]
def baseStart_905317 : Nat := 118140960795 + 905317 * 2 ^ 59
def prefixEnd_905317 : Nat := 4983230072969 + 3 ^ 40 * 905317 * 2
def baseEnd_905317 : Nat := 206605673638462078566235

theorem tailTrace_905317 : CollatzResearch.WordTrace tailWord_905317 prefixEnd_905317 206605673638462078566235 := by
  unfold tailWord_905317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33019623661198599679114205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22013082440799066452742803 33019623661198599679114205)
  ·
    refine ⟨12382358872949474879667827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33019623661198599679114205 12382358872949474879667827)
    ·
      refine ⟨18573538309424212319501741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12382358872949474879667827 18573538309424212319501741)
      ·
        refine ⟨6965076866034079619813153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18573538309424212319501741 6965076866034079619813153)
        ·
          refine ⟨5223807649525559714859865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6965076866034079619813153 5223807649525559714859865)
          ·
            refine ⟨3917855737144169786144899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5223807649525559714859865 3917855737144169786144899)
            ·
              refine ⟨5876783605716254679217349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3917855737144169786144899 5876783605716254679217349)
              ·
                refine ⟨1101896926071797752353253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5876783605716254679217349 1101896926071797752353253)
                ·
                  refine ⟨206605673638462078566235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101896926071797752353253 206605673638462078566235)
                  ·
                    rfl

theorem cell21_905317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_905317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905317 prefixEnd_905317 := by exact prefixLift 905317
  have htrace : WordTrace (prefixWord ++ tailWord_905317) baseStart_905317 baseEnd_905317 := by
    simpa [prefixWord, tailWord_905317, baseEnd_905317] using wordTrace_append hprefix tailTrace_905317
  have hstable : (prefixWord ++ tailWord_905317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905317).length < 2 ^ (prefixWord ++ tailWord_905317).sum := by decide
  have hdescent : baseEnd_905317 < baseStart_905317 := by decide
  rcases family_descends (prefixWord ++ tailWord_905317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905334 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_905334 : Nat := 118140960795 + 905334 * 2 ^ 59
def prefixEnd_905334 : Nat := 4983230072969 + 3 ^ 40 * 905334 * 2
def baseEnd_905334 : Nat := 206609553270073826782867

theorem tailTrace_905334 : CollatzResearch.WordTrace tailWord_905334 prefixEnd_905334 206609553270073826782867 := by
  unfold tailWord_905334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063765231383563223905191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22013495801424674388322037 2063765231383563223905191)
  ·
    refine ⟨3095647847075344835857787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063765231383563223905191 3095647847075344835857787)
    ·
      refine ⟨4643471770613017253786681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095647847075344835857787 4643471770613017253786681)
      ·
        refine ⟨3482603827959762940340011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4643471770613017253786681 3482603827959762940340011)
        ·
          refine ⟨5223905741939644410510017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482603827959762940340011 5223905741939644410510017)
          ·
            refine ⟨3917929306454733307882513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5223905741939644410510017 3917929306454733307882513)
            ·
              refine ⟨2938446979841049980911885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3917929306454733307882513 2938446979841049980911885)
              ·
                refine ⟨1101917617440393742841957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2938446979841049980911885 1101917617440393742841957)
                ·
                  refine ⟨206609553270073826782867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1101917617440393742841957 206609553270073826782867)
                  ·
                    rfl

theorem cell21_905334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_905334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905334 prefixEnd_905334 := by exact prefixLift 905334
  have htrace : WordTrace (prefixWord ++ tailWord_905334) baseStart_905334 baseEnd_905334 := by
    simpa [prefixWord, tailWord_905334, baseEnd_905334] using wordTrace_append hprefix tailTrace_905334
  have hstable : (prefixWord ++ tailWord_905334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905334).length < 2 ^ (prefixWord ++ tailWord_905334).sum := by decide
  have hdescent : baseEnd_905334 < baseStart_905334 := by decide
  rcases family_descends (prefixWord ++ tailWord_905334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905348 : List Nat := [2, 3, 2, 1, 2, 1, 5, 5]
def baseStart_905348 : Nat := 118140960795 + 905348 * 2 ^ 59
def prefixEnd_905348 : Nat := 4983230072969 + 3 ^ 40 * 905348 * 2
def baseEnd_905348 : Nat := 68870916086937637849835

theorem tailTrace_905348 : CollatzResearch.WordTrace tailWord_905348 prefixEnd_905348 68870916086937637849835 := by
  unfold tailWord_905348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16510377162043145986746349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22013836216057527982328465 16510377162043145986746349)
  ·
    refine ⟨6191391435766179745029881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16510377162043145986746349 6191391435766179745029881)
    ·
      refine ⟨4643543576824634808772411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6191391435766179745029881 4643543576824634808772411)
      ·
        refine ⟨6965315365236952213158617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643543576824634808772411 6965315365236952213158617)
        ·
          refine ⟨5223986523927714159868963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6965315365236952213158617 5223986523927714159868963)
          ·
            refine ⟨7835979785891571239803445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5223986523927714159868963 7835979785891571239803445)
            ·
              refine ⟨734623104927334803731573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7835979785891571239803445 734623104927334803731573)
              ·
                refine ⟨68870916086937637849835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 734623104927334803731573 68870916086937637849835)
                ·
                  rfl

theorem cell21_905348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_905348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905348 prefixEnd_905348 := by exact prefixLift 905348
  have htrace : WordTrace (prefixWord ++ tailWord_905348) baseStart_905348 baseEnd_905348 := by
    simpa [prefixWord, tailWord_905348, baseEnd_905348] using wordTrace_append hprefix tailTrace_905348
  have hstable : (prefixWord ++ tailWord_905348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905348).length < 2 ^ (prefixWord ++ tailWord_905348).sum := by decide
  have hdescent : baseEnd_905348 < baseStart_905348 := by decide
  rcases family_descends (prefixWord ++ tailWord_905348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905362 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_905362 : Nat := 118140960795 + 905362 * 2 ^ 59
def prefixEnd_905362 : Nat := 4983230072969 + 3 ^ 40 * 905362 * 2
def baseEnd_905362 : Nat := 206615943251552000316143

theorem tailTrace_905362 : CollatzResearch.WordTrace tailWord_905362 prefixEnd_905362 206615943251552000316143 := by
  unfold tailWord_905362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255316236508893091125585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22014176630690381576334893 8255316236508893091125585)
  ·
    refine ⟨6191487177381669818344189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8255316236508893091125585 6191487177381669818344189)
    ·
      refine ⟨2321807691518126181879071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6191487177381669818344189 2321807691518126181879071)
      ·
        refine ⟨3482711537277189272818607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2321807691518126181879071 3482711537277189272818607)
        ·
          refine ⟨5224067305915783909227911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3482711537277189272818607 5224067305915783909227911)
          ·
            refine ⟨7836100958873675863841867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224067305915783909227911 7836100958873675863841867)
            ·
              refine ⟨11754151438310513795762801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7836100958873675863841867 11754151438310513795762801)
              ·
                refine ⟨8815613578732885346822101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11754151438310513795762801 8815613578732885346822101)
                ·
                  refine ⟨206615943251552000316143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8815613578732885346822101 206615943251552000316143)
                  ·
                    rfl

theorem cell21_905362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_905362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905362 prefixEnd_905362 := by exact prefixLift 905362
  have htrace : WordTrace (prefixWord ++ tailWord_905362) baseStart_905362 baseEnd_905362 := by
    simpa [prefixWord, tailWord_905362, baseEnd_905362] using wordTrace_append hprefix tailTrace_905362
  have hstable : (prefixWord ++ tailWord_905362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905362).length < 2 ^ (prefixWord ++ tailWord_905362).sum := by decide
  have hdescent : baseEnd_905362 < baseStart_905362 := by decide
  rcases family_descends (prefixWord ++ tailWord_905362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905430 : List Nat := [5, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_905430 : Nat := 118140960795 + 905430 * 2 ^ 59
def prefixEnd_905430 : Nat := 4983230072969 + 3 ^ 40 * 905430 * 2
def baseEnd_905430 : Nat := 206631461777998993182671

theorem tailTrace_905430 : CollatzResearch.WordTrace tailWord_905430 prefixEnd_905430 206631461777998993182671 := by
  unfold tailWord_905430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063984069361826248623609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22015830073192813318651829 2063984069361826248623609)
  ·
    refine ⟨1547988052021369686467707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2063984069361826248623609 1547988052021369686467707)
    ·
      refine ⟨2321982078032054529701561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547988052021369686467707 2321982078032054529701561)
      ·
        refine ⟨1741486558524040897276171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2321982078032054529701561 1741486558524040897276171)
        ·
          refine ⟨2612229837786061345914257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741486558524040897276171 2612229837786061345914257)
          ·
            refine ⟨1959172378339546009435693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2612229837786061345914257 1959172378339546009435693)
            ·
              refine ⟨734689641877329753538385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1959172378339546009435693 734689641877329753538385)
              ·
                refine ⟨551017231407997315153789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 734689641877329753538385 551017231407997315153789)
                ·
                  refine ⟨206631461777998993182671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551017231407997315153789 206631461777998993182671)
                  ·
                    rfl

theorem cell21_905430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_905430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905430 prefixEnd_905430 := by exact prefixLift 905430
  have htrace : WordTrace (prefixWord ++ tailWord_905430) baseStart_905430 baseEnd_905430 := by
    simpa [prefixWord, tailWord_905430, baseEnd_905430] using wordTrace_append hprefix tailTrace_905430
  have hstable : (prefixWord ++ tailWord_905430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905430).length < 2 ^ (prefixWord ++ tailWord_905430).sum := by decide
  have hdescent : baseEnd_905430 < baseStart_905430 := by decide
  rcases family_descends (prefixWord ++ tailWord_905430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905576 : List Nat := [2, 1, 4, 2, 2, 1, 4, 5]
def baseStart_905576 : Nat := 118140960795 + 905576 * 2 ^ 59
def prefixEnd_905576 : Nat := 4983230072969 + 3 ^ 40 * 905576 * 2
def baseEnd_905576 : Nat := 68888260322378394583013

theorem tailTrace_905576 : CollatzResearch.WordTrace tailWord_905576 prefixEnd_905576 68888260322378394583013 := by
  unfold tailWord_905576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16514535083630143456396291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22019380111506857941861721 16514535083630143456396291)
  ·
    refine ⟨24771802625445215184594437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16514535083630143456396291 24771802625445215184594437)
    ·
      refine ⟨4644712992270977847111457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24771802625445215184594437 4644712992270977847111457)
      ·
        refine ⟨3483534744203233385333593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4644712992270977847111457 3483534744203233385333593)
        ·
          refine ⟨2612651058152425039000195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3483534744203233385333593 2612651058152425039000195)
          ·
            refine ⟨3918976587228637558500293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2612651058152425039000195 3918976587228637558500293)
            ·
              refine ⟨734808110105369542218805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3918976587228637558500293 734808110105369542218805)
              ·
                refine ⟨68888260322378394583013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 734808110105369542218805 68888260322378394583013)
                ·
                  rfl

theorem cell21_905576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_905576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905576 prefixEnd_905576 := by exact prefixLift 905576
  have htrace : WordTrace (prefixWord ++ tailWord_905576) baseStart_905576 baseEnd_905576 := by
    simpa [prefixWord, tailWord_905576, baseEnd_905576] using wordTrace_append hprefix tailTrace_905576
  have hstable : (prefixWord ++ tailWord_905576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905576).length < 2 ^ (prefixWord ++ tailWord_905576).sum := by decide
  have hdescent : baseEnd_905576 < baseStart_905576 := by decide
  rcases family_descends (prefixWord ++ tailWord_905576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905604 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_905604 : Nat := 118140960795 + 905604 * 2 ^ 59
def prefixEnd_905604 : Nat := 4983230072969 + 3 ^ 40 * 905604 * 2
def baseEnd_905604 : Nat := 206671170948613357282315

theorem tailTrace_905604 : CollatzResearch.WordTrace tailWord_905604 prefixEnd_905604 206671170948613357282315 := by
  unfold tailWord_905604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515045705579423847405933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22020060940772565129874577 16515045705579423847405933)
  ·
    refine ⟨6193142139592283942777225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16515045705579423847405933 6193142139592283942777225)
    ·
      refine ⟨4644856604694212957082919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6193142139592283942777225 4644856604694212957082919)
      ·
        refine ⟨6967284907041319435624379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4644856604694212957082919 6967284907041319435624379)
        ·
          refine ⟨10450927360561979153436569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6967284907041319435624379 10450927360561979153436569)
          ·
            refine ⟨7838195520421484365077427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10450927360561979153436569 7838195520421484365077427)
            ·
              refine ⟨11757293280632226547616141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7838195520421484365077427 11757293280632226547616141)
              ·
                refine ⟨4408984980237084955356053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11757293280632226547616141 4408984980237084955356053)
                ·
                  refine ⟨206671170948613357282315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4408984980237084955356053 206671170948613357282315)
                  ·
                    rfl

theorem cell21_905604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_905604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905604 prefixEnd_905604 := by exact prefixLift 905604
  have htrace : WordTrace (prefixWord ++ tailWord_905604) baseStart_905604 baseEnd_905604 := by
    simpa [prefixWord, tailWord_905604, baseEnd_905604] using wordTrace_append hprefix tailTrace_905604
  have hstable : (prefixWord ++ tailWord_905604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905604).length < 2 ^ (prefixWord ++ tailWord_905604).sum := by decide
  have hdescent : baseEnd_905604 < baseStart_905604 := by decide
  rcases family_descends (prefixWord ++ tailWord_905604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905652 : List Nat := [2, 5, 2, 2, 10]
def baseStart_905652 : Nat := 118140960795 + 905652 * 2 ^ 59
def prefixEnd_905652 : Nat := 4983230072969 + 3 ^ 40 * 905652 * 2
def baseEnd_905652 : Nat := 2551631175340443709657

theorem tailTrace_905652 : CollatzResearch.WordTrace tailWord_905652 prefixEnd_905652 2551631175340443709657 := by
  unfold tailWord_905652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515921057492475946279605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22021228076656634595039473 16515921057492475946279605)
  ·
    refine ⟨1548367599139919619963713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16515921057492475946279605 1548367599139919619963713)
    ·
      refine ⟨1161275699354939714972785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1548367599139919619963713 1161275699354939714972785)
      ·
        refine ⟨870956774516204786229589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1161275699354939714972785 870956774516204786229589)
        ·
          refine ⟨2551631175340443709657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 870956774516204786229589 2551631175340443709657)
          ·
            rfl

theorem cell21_905652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 10].length) (baseStart_905652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905652 prefixEnd_905652 := by exact prefixLift 905652
  have htrace : WordTrace (prefixWord ++ tailWord_905652) baseStart_905652 baseEnd_905652 := by
    simpa [prefixWord, tailWord_905652, baseEnd_905652] using wordTrace_append hprefix tailTrace_905652
  have hstable : (prefixWord ++ tailWord_905652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905652).length < 2 ^ (prefixWord ++ tailWord_905652).sum := by decide
  have hdescent : baseEnd_905652 < baseStart_905652 := by decide
  rcases family_descends (prefixWord ++ tailWord_905652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905742 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_905742 : Nat := 118140960795 + 905742 * 2 ^ 59
def prefixEnd_905742 : Nat := 4983230072969 + 3 ^ 40 * 905742 * 2
def baseEnd_905742 : Nat := 206702664428755783982033

theorem tailTrace_905742 : CollatzResearch.WordTrace tailWord_905742 prefixEnd_905742 206702664428755783982033 := by
  unfold tailWord_905742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129390585582362157916935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22023416456439264842223653 4129390585582362157916935)
  ·
    refine ⟨6194085878373543236875403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129390585582362157916935 6194085878373543236875403)
    ·
      refine ⟨9291128817560314855313105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6194085878373543236875403 9291128817560314855313105)
      ·
        refine ⟨6968346613170236141484829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9291128817560314855313105 6968346613170236141484829)
        ·
          refine ⟨2613129979938838553056811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6968346613170236141484829 2613129979938838553056811)
          ·
            refine ⟨3919694969908257829585217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613129979938838553056811 3919694969908257829585217)
            ·
              refine ⟨2939771227431193372188913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3919694969908257829585217 2939771227431193372188913)
              ·
                refine ⟨2204828420573395029141685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2939771227431193372188913 2204828420573395029141685)
                ·
                  refine ⟨206702664428755783982033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2204828420573395029141685 206702664428755783982033)
                  ·
                    rfl

theorem cell21_905742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_905742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905742 prefixEnd_905742 := by exact prefixLift 905742
  have htrace : WordTrace (prefixWord ++ tailWord_905742) baseStart_905742 baseEnd_905742 := by
    simpa [prefixWord, tailWord_905742, baseEnd_905742] using wordTrace_append hprefix tailTrace_905742
  have hstable : (prefixWord ++ tailWord_905742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905742).length < 2 ^ (prefixWord ++ tailWord_905742).sum := by decide
  have hdescent : baseEnd_905742 < baseStart_905742 := by decide
  rcases family_descends (prefixWord ++ tailWord_905742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905756 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_905756 : Nat := 118140960795 + 905756 * 2 ^ 59
def prefixEnd_905756 : Nat := 4983230072969 + 3 ^ 40 * 905756 * 2
def baseEnd_905756 : Nat := 206705859419494870748671

theorem tailTrace_905756 : CollatzResearch.WordTrace tailWord_905756 prefixEnd_905756 206705859419494870748671 := by
  unfold tailWord_905756
  simp only [CollatzResearch.WordTrace]
  refine ⟨16517817653304088827172561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22023756871072118436230081 16517817653304088827172561)
  ·
    refine ⟨12388363239978066620379421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16517817653304088827172561 12388363239978066620379421)
    ·
      refine ⟨4645636214991774982642283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12388363239978066620379421 4645636214991774982642283)
      ·
        refine ⟨6968454322487662473963425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4645636214991774982642283 6968454322487662473963425)
        ·
          refine ⟨5226340741865746855472569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6968454322487662473963425 5226340741865746855472569)
          ·
            refine ⟨3919755556399310141604427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5226340741865746855472569 3919755556399310141604427)
            ·
              refine ⟨5879633334598965212406641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919755556399310141604427 5879633334598965212406641)
              ·
                refine ⟨4409725000949223909304981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5879633334598965212406641 4409725000949223909304981)
                ·
                  refine ⟨206705859419494870748671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4409725000949223909304981 206705859419494870748671)
                  ·
                    rfl

theorem cell21_905756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_905756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905756 prefixEnd_905756 := by exact prefixLift 905756
  have htrace : WordTrace (prefixWord ++ tailWord_905756) baseStart_905756 baseEnd_905756 := by
    simpa [prefixWord, tailWord_905756, baseEnd_905756] using wordTrace_append hprefix tailTrace_905756
  have hstable : (prefixWord ++ tailWord_905756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905756).length < 2 ^ (prefixWord ++ tailWord_905756).sum := by decide
  have hdescent : baseEnd_905756 < baseStart_905756 := by decide
  rcases family_descends (prefixWord ++ tailWord_905756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905863 : List Nat := [1, 1, 4, 2, 1, 2, 5, 5]
def baseStart_905863 : Nat := 118140960795 + 905863 * 2 ^ 59
def prefixEnd_905863 : Nat := 4983230072969 + 3 ^ 40 * 905863 * 2
def baseEnd_905863 : Nat := 68910092759095487488373

theorem tailTrace_905863 : CollatzResearch.WordTrace tailWord_905863 prefixEnd_905863 68910092759095487488373 := by
  unfold tailWord_905863
  simp only [CollatzResearch.WordTrace]
  refine ⟨33039537917220534928490243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22026358611480356618993495 33039537917220534928490243)
  ·
    refine ⟨49559306875830802392735365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33039537917220534928490243 49559306875830802392735365)
    ·
      refine ⟨9292370039218275448637881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49559306875830802392735365 9292370039218275448637881)
      ·
        refine ⟨6969277529413706586478411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9292370039218275448637881 6969277529413706586478411)
        ·
          refine ⟨10453916294120559879717617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6969277529413706586478411 10453916294120559879717617)
          ·
            refine ⟨7840437220590419909788213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10453916294120559879717617 7840437220590419909788213)
            ·
              refine ⟨735040989430351866542645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7840437220590419909788213 735040989430351866542645)
              ·
                refine ⟨68910092759095487488373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 735040989430351866542645 68910092759095487488373)
                ·
                  rfl

theorem cell21_905863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 5].length) (baseStart_905863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_905863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_905863 prefixEnd_905863 := by exact prefixLift 905863
  have htrace : WordTrace (prefixWord ++ tailWord_905863) baseStart_905863 baseEnd_905863 := by
    simpa [prefixWord, tailWord_905863, baseEnd_905863] using wordTrace_append hprefix tailTrace_905863
  have hstable : (prefixWord ++ tailWord_905863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905863).length < 2 ^ (prefixWord ++ tailWord_905863).sum := by decide
  have hdescent : baseEnd_905863 < baseStart_905863 := by decide
  rcases family_descends (prefixWord ++ tailWord_905863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906015 : List Nat := [1, 1, 2, 4, 2, 4, 1, 6]
def baseStart_906015 : Nat := 118140960795 + 906015 * 2 ^ 59
def prefixEnd_906015 : Nat := 4983230072969 + 3 ^ 40 * 906015 * 2
def baseEnd_906015 : Nat := 68921655582722658643825

theorem tailTrace_906015 : CollatzResearch.WordTrace tailWord_906015 prefixEnd_906015 68921655582722658643825 := by
  unfold tailWord_906015
  simp only [CollatzResearch.WordTrace]
  refine ⟨33045081812669864888023499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22030054541779909925348999 33045081812669864888023499)
  ·
    refine ⟨49567622719004797332035249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33045081812669864888023499 49567622719004797332035249)
    ·
      refine ⟨37175717039253597999026437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49567622719004797332035249 37175717039253597999026437)
      ·
        refine ⟨6970446944860049624817457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37175717039253597999026437 6970446944860049624817457)
        ·
          refine ⟨5227835208645037218613093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6970446944860049624817457 5227835208645037218613093)
          ·
            refine ⟨980219101620944478489955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5227835208645037218613093 980219101620944478489955)
            ·
              refine ⟨1470328652431416717734933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980219101620944478489955 1470328652431416717734933)
              ·
                refine ⟨68921655582722658643825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1470328652431416717734933 68921655582722658643825)
                ·
                  rfl

theorem cell21_906015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 6].length) (baseStart_906015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906015 prefixEnd_906015 := by exact prefixLift 906015
  have htrace : WordTrace (prefixWord ++ tailWord_906015) baseStart_906015 baseEnd_906015 := by
    simpa [prefixWord, tailWord_906015, baseEnd_906015] using wordTrace_append hprefix tailTrace_906015
  have hstable : (prefixWord ++ tailWord_906015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906015).length < 2 ^ (prefixWord ++ tailWord_906015).sum := by decide
  have hdescent : baseEnd_906015 < baseStart_906015 := by decide
  rcases family_descends (prefixWord ++ tailWord_906015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906052 : List Nat := [2, 3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_906052 : Nat := 118140960795 + 906052 * 2 ^ 59
def prefixEnd_906052 : Nat := 4983230072969 + 3 ^ 40 * 906052 * 2
def baseEnd_906052 : Nat := 206773410652264133814733

theorem tailTrace_906052 : CollatzResearch.WordTrace tailWord_906052 prefixEnd_906052 206773410652264133814733 := by
  unfold tailWord_906052
  simp only [CollatzResearch.WordTrace]
  refine ⟨16523215656767910103560205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22030954209023880138080273 16523215656767910103560205)
  ·
    refine ⟨6196205871287966288835077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16523215656767910103560205 6196205871287966288835077)
    ·
      refine ⟨1161788600866493679156577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6196205871287966288835077 1161788600866493679156577)
      ·
        refine ⟨871341450649870259367433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1161788600866493679156577 871341450649870259367433)
        ·
          refine ⟨653506087987402694525575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871341450649870259367433 653506087987402694525575)
          ·
            refine ⟨980259131981104041788363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653506087987402694525575 980259131981104041788363)
            ·
              refine ⟨1470388697971656062682545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980259131981104041788363 1470388697971656062682545)
              ·
                refine ⟨1102791523478742047011909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470388697971656062682545 1102791523478742047011909)
                ·
                  refine ⟨206773410652264133814733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1102791523478742047011909 206773410652264133814733)
                  ·
                    rfl

theorem cell21_906052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_906052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906052 prefixEnd_906052 := by exact prefixLift 906052
  have htrace : WordTrace (prefixWord ++ tailWord_906052) baseStart_906052 baseEnd_906052 := by
    simpa [prefixWord, tailWord_906052, baseEnd_906052] using wordTrace_append hprefix tailTrace_906052
  have hstable : (prefixWord ++ tailWord_906052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906052).length < 2 ^ (prefixWord ++ tailWord_906052).sum := by decide
  have hdescent : baseEnd_906052 < baseStart_906052 := by decide
  rcases family_descends (prefixWord ++ tailWord_906052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906060 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_906060 : Nat := 118140960795 + 906060 * 2 ^ 59
def prefixEnd_906060 : Nat := 4983230072969 + 3 ^ 40 * 906060 * 2
def baseEnd_906060 : Nat := 206775236361257897681383

theorem tailTrace_906060 : CollatzResearch.WordTrace tailWord_906060 prefixEnd_906060 206775236361257897681383 := by
  unfold tailWord_906060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16523361548753418786705817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22031148731671225048941089 16523361548753418786705817)
  ·
    refine ⟨12392521161565064090029363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16523361548753418786705817 12392521161565064090029363)
    ·
      refine ⟨18588781742347596135044045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12392521161565064090029363 18588781742347596135044045)
      ·
        refine ⟨6970793153380348550641517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18588781742347596135044045 6970793153380348550641517)
        ·
          refine ⟨2614047432517630706490569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6970793153380348550641517 2614047432517630706490569)
          ·
            refine ⟨1960535574388223029867927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614047432517630706490569 1960535574388223029867927)
            ·
              refine ⟨2940803361582334544801891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960535574388223029867927 2940803361582334544801891)
              ·
                refine ⟨4411205042373501817202837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2940803361582334544801891 4411205042373501817202837)
                ·
                  refine ⟨206775236361257897681383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4411205042373501817202837 206775236361257897681383)
                  ·
                    rfl

theorem cell21_906060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_906060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906060 prefixEnd_906060 := by exact prefixLift 906060
  have htrace : WordTrace (prefixWord ++ tailWord_906060) baseStart_906060 baseEnd_906060 := by
    simpa [prefixWord, tailWord_906060, baseEnd_906060] using wordTrace_append hprefix tailTrace_906060
  have hstable : (prefixWord ++ tailWord_906060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906060).length < 2 ^ (prefixWord ++ tailWord_906060).sum := by decide
  have hdescent : baseEnd_906060 < baseStart_906060 := by decide
  rcases family_descends (prefixWord ++ tailWord_906060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906114 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 3]
def baseStart_906114 : Nat := 118140960795 + 906114 * 2 ^ 59
def prefixEnd_906114 : Nat := 4983230072969 + 3 ^ 40 * 906114 * 2
def baseEnd_906114 : Nat := 206787559896965803781273

theorem tailTrace_906114 : CollatzResearch.WordTrace tailWord_906114 prefixEnd_906114 206787559896965803781273 := by
  unfold tailWord_906114
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262173159827801198969349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22032461759540803197251597 8262173159827801198969349)
  ·
    refine ⟨1549157467467712724806753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8262173159827801198969349 1549157467467712724806753)
    ·
      refine ⟨1161868100600784543605065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1549157467467712724806753 1161868100600784543605065)
      ·
        refine ⟨871401075450588407703799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1161868100600784543605065 871401075450588407703799)
        ·
          refine ⟨1307101613175882611555699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871401075450588407703799 1307101613175882611555699)
          ·
            refine ⟨1960652419763823917333549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307101613175882611555699 1960652419763823917333549)
            ·
              refine ⟨735244657411433969000081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1960652419763823917333549 735244657411433969000081)
              ·
                refine ⟨551433493058575476750061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735244657411433969000081 551433493058575476750061)
                ·
                  refine ⟨206787559896965803781273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551433493058575476750061 206787559896965803781273)
                  ·
                    rfl

theorem cell21_906114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_906114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906114 prefixEnd_906114 := by exact prefixLift 906114
  have htrace : WordTrace (prefixWord ++ tailWord_906114) baseStart_906114 baseEnd_906114 := by
    simpa [prefixWord, tailWord_906114, baseEnd_906114] using wordTrace_append hprefix tailTrace_906114
  have hstable : (prefixWord ++ tailWord_906114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906114).length < 2 ^ (prefixWord ++ tailWord_906114).sum := by decide
  have hdescent : baseEnd_906114 < baseStart_906114 := by decide
  rcases family_descends (prefixWord ++ tailWord_906114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906122 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_906122 : Nat := 118140960795 + 906122 * 2 ^ 59
def prefixEnd_906122 : Nat := 4983230072969 + 3 ^ 40 * 906122 * 2
def baseEnd_906122 : Nat := 206789385605959567647923

theorem tailTrace_906122 : CollatzResearch.WordTrace tailWord_906122 prefixEnd_906122 206789385605959567647923 := by
  unfold tailWord_906122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262246105820555540542155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22032656282188148108112413 8262246105820555540542155)
  ·
    refine ⟨12393369158730833310813233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8262246105820555540542155 12393369158730833310813233)
    ·
      refine ⟨9295026869048124983109925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12393369158730833310813233 9295026869048124983109925)
      ·
        refine ⟨1742817537946523434333111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9295026869048124983109925 1742817537946523434333111)
        ·
          refine ⟨2614226306919785151499667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1742817537946523434333111 2614226306919785151499667)
          ·
            refine ⟨3921339460379677727249501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614226306919785151499667 3921339460379677727249501)
            ·
              refine ⟨1470502297642379147718563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3921339460379677727249501 1470502297642379147718563)
              ·
                refine ⟨2205753446463568721577845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470502297642379147718563 2205753446463568721577845)
                ·
                  refine ⟨206789385605959567647923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2205753446463568721577845 206789385605959567647923)
                  ·
                    rfl

theorem cell21_906122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_906122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906122 prefixEnd_906122 := by exact prefixLift 906122
  have htrace : WordTrace (prefixWord ++ tailWord_906122) baseStart_906122 baseEnd_906122 := by
    simpa [prefixWord, tailWord_906122, baseEnd_906122] using wordTrace_append hprefix tailTrace_906122
  have hstable : (prefixWord ++ tailWord_906122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906122).length < 2 ^ (prefixWord ++ tailWord_906122).sum := by decide
  have hdescent : baseEnd_906122 < baseStart_906122 := by decide
  rcases family_descends (prefixWord ++ tailWord_906122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906173 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 3]
def baseStart_906173 : Nat := 118140960795 + 906173 * 2 ^ 59
def prefixEnd_906173 : Nat := 4983230072969 + 3 ^ 40 * 906173 * 2
def baseEnd_906173 : Nat := 206801024500794812297819

theorem tailTrace_906173 : CollatzResearch.WordTrace tailWord_906173 prefixEnd_906173 206801024500794812297819 := by
  unfold tailWord_906173
  simp only [CollatzResearch.WordTrace]
  refine ⟨33050844546097457872275173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22033896364064971914850115 33050844546097457872275173)
  ·
    refine ⟨6197033352393273351051595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33050844546097457872275173 6197033352393273351051595)
    ·
      refine ⟨9295550028589910026577393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197033352393273351051595 9295550028589910026577393)
      ·
        refine ⟨6971662521442432519933045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9295550028589910026577393 6971662521442432519933045)
        ·
          refine ⟨653593361385228048743723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6971662521442432519933045 653593361385228048743723)
          ·
            refine ⟨980390042077842073115585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653593361385228048743723 980390042077842073115585)
            ·
              refine ⟨735292531558381554836689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980390042077842073115585 735292531558381554836689)
              ·
                refine ⟨551469398668786166127517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735292531558381554836689 551469398668786166127517)
                ·
                  refine ⟨206801024500794812297819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551469398668786166127517 206801024500794812297819)
                  ·
                    rfl

theorem cell21_906173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_906173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906173 prefixEnd_906173 := by exact prefixLift 906173
  have htrace : WordTrace (prefixWord ++ tailWord_906173) baseStart_906173 baseEnd_906173 := by
    simpa [prefixWord, tailWord_906173, baseEnd_906173] using wordTrace_append hprefix tailTrace_906173
  have hstable : (prefixWord ++ tailWord_906173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906173).length < 2 ^ (prefixWord ++ tailWord_906173).sum := by decide
  have hdescent : baseEnd_906173 < baseStart_906173 := by decide
  rcases family_descends (prefixWord ++ tailWord_906173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906184 : List Nat := [2, 1, 3, 1, 6, 1, 1, 6]
def baseStart_906184 : Nat := 118140960795 + 906184 * 2 ^ 59
def prefixEnd_906184 : Nat := 4983230072969 + 3 ^ 40 * 906184 * 2
def baseEnd_906184 : Nat := 68934511616887079204821

theorem tailTrace_906184 : CollatzResearch.WordTrace tailWord_906184 prefixEnd_906184 68934511616887079204821 := by
  unfold tailWord_906184
  simp only [CollatzResearch.WordTrace]
  refine ⟨16525622874528803375462803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22034163832705071167283737 16525622874528803375462803)
  ·
    refine ⟨24788434311793205063194205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16525622874528803375462803 24788434311793205063194205)
    ·
      refine ⟨9295662866922451898697827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24788434311793205063194205 9295662866922451898697827)
      ·
        refine ⟨13943494300383677848046741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9295662866922451898697827 13943494300383677848046741)
        ·
          refine ⟨653601295330484899127191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13943494300383677848046741 653601295330484899127191)
          ·
            refine ⟨980401942995727348690787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653601295330484899127191 980401942995727348690787)
            ·
              refine ⟨1470602914493591023036181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980401942995727348690787 1470602914493591023036181)
              ·
                refine ⟨68934511616887079204821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1470602914493591023036181 68934511616887079204821)
                ·
                  rfl

theorem cell21_906184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_906184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906184 prefixEnd_906184 := by exact prefixLift 906184
  have htrace : WordTrace (prefixWord ++ tailWord_906184) baseStart_906184 baseEnd_906184 := by
    simpa [prefixWord, tailWord_906184, baseEnd_906184] using wordTrace_append hprefix tailTrace_906184
  have hstable : (prefixWord ++ tailWord_906184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906184).length < 2 ^ (prefixWord ++ tailWord_906184).sum := by decide
  have hdescent : baseEnd_906184 < baseStart_906184 := by decide
  rcases family_descends (prefixWord ++ tailWord_906184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906198 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_906198 : Nat := 118140960795 + 906198 * 2 ^ 59
def prefixEnd_906198 : Nat := 4983230072969 + 3 ^ 40 * 906198 * 2
def baseEnd_906198 : Nat := 206806729841400324381101

theorem tailTrace_906198 : CollatzResearch.WordTrace tailWord_906198 prefixEnd_906198 206806729841400324381101 := by
  unfold tailWord_906198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065734773187930446370953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22034504247337924761290165 2065734773187930446370953)
  ·
    refine ⟨1549301079890947834778215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2065734773187930446370953 1549301079890947834778215)
    ·
      refine ⟨2323951619836421752167323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1549301079890947834778215 2323951619836421752167323)
      ·
        refine ⟨3485927429754632628250985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2323951619836421752167323 3485927429754632628250985)
        ·
          refine ⟨2614445572315974471188239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485927429754632628250985 2614445572315974471188239)
          ·
            refine ⟨3921668358473961706782359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2614445572315974471188239 3921668358473961706782359)
            ·
              refine ⟨5882502537710942560173539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921668358473961706782359 5882502537710942560173539)
              ·
                refine ⟨8823753806566413840260309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5882502537710942560173539 8823753806566413840260309)
                ·
                  refine ⟨206806729841400324381101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8823753806566413840260309 206806729841400324381101)
                  ·
                    rfl

theorem cell21_906198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_906198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906198 prefixEnd_906198 := by exact prefixLift 906198
  have htrace : WordTrace (prefixWord ++ tailWord_906198) baseStart_906198 baseEnd_906198 := by
    simpa [prefixWord, tailWord_906198, baseEnd_906198] using wordTrace_append hprefix tailTrace_906198
  have hstable : (prefixWord ++ tailWord_906198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906198).length < 2 ^ (prefixWord ++ tailWord_906198).sum := by decide
  have hdescent : baseEnd_906198 < baseStart_906198 := by decide
  rcases family_descends (prefixWord ++ tailWord_906198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906215 : List Nat := [1, 1, 5, 2, 2, 2, 2, 3, 3]
def baseStart_906215 : Nat := 118140960795 + 906215 * 2 ^ 59
def prefixEnd_906215 : Nat := 4983230072969 + 3 ^ 40 * 906215 * 2
def baseEnd_906215 : Nat := 206810609473012072597733

theorem tailTrace_906215 : CollatzResearch.WordTrace tailWord_906215 prefixEnd_906215 206810609473012072597733 := by
  unfold tailWord_906215
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052376411945299045304099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22034917607963532696869399 33052376411945299045304099)
  ·
    refine ⟨49578564617917948567956149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33052376411945299045304099 49578564617917948567956149)
    ·
      refine ⟨4647990432929807678245889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49578564617917948567956149 4647990432929807678245889)
      ·
        refine ⟨3485992824697355758684417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4647990432929807678245889 3485992824697355758684417)
        ·
          refine ⟨2614494618523016819013313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3485992824697355758684417 2614494618523016819013313)
          ·
            refine ⟨1960870963892262614259985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2614494618523016819013313 1960870963892262614259985)
            ·
              refine ⟨1470653222919196960694989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960870963892262614259985 1470653222919196960694989)
              ·
                refine ⟨551494958594698860260621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470653222919196960694989 551494958594698860260621)
                ·
                  refine ⟨206810609473012072597733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551494958594698860260621 206810609473012072597733)
                  ·
                    rfl

theorem cell21_906215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 3].length) (baseStart_906215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906215 prefixEnd_906215 := by exact prefixLift 906215
  have htrace : WordTrace (prefixWord ++ tailWord_906215) baseStart_906215 baseEnd_906215 := by
    simpa [prefixWord, tailWord_906215, baseEnd_906215] using wordTrace_append hprefix tailTrace_906215
  have hstable : (prefixWord ++ tailWord_906215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906215).length < 2 ^ (prefixWord ++ tailWord_906215).sum := by decide
  have hdescent : baseEnd_906215 < baseStart_906215 := by decide
  rcases family_descends (prefixWord ++ tailWord_906215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906271 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_906271 : Nat := 118140960795 + 906271 * 2 ^ 59
def prefixEnd_906271 : Nat := 4983230072969 + 3 ^ 40 * 906271 * 2
def baseEnd_906271 : Nat := 206823389435968419664285

theorem tailTrace_906271 : CollatzResearch.WordTrace tailWord_906271 prefixEnd_906271 206823389435968419664285 := by
  unfold tailWord_906271
  simp only [CollatzResearch.WordTrace]
  refine ⟨33054418899742420609342667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22036279266494947072895111 33054418899742420609342667)
  ·
    refine ⟨49581628349613630914014001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33054418899742420609342667 49581628349613630914014001)
    ·
      refine ⟨37186221262210223185510501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49581628349613630914014001 37186221262210223185510501)
      ·
        refine ⟨6972416486664416847283219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37186221262210223185510501 6972416486664416847283219)
        ·
          refine ⟨10458624729996625270924829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972416486664416847283219 10458624729996625270924829)
          ·
            refine ⟨3921984273748734476596811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10458624729996625270924829 3921984273748734476596811)
            ·
              refine ⟨5882976410623101714895217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3921984273748734476596811 5882976410623101714895217)
              ·
                refine ⟨4412232307967326286171413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5882976410623101714895217 4412232307967326286171413)
                ·
                  refine ⟨206823389435968419664285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4412232307967326286171413 206823389435968419664285)
                  ·
                    rfl

theorem cell21_906271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_906271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906271 prefixEnd_906271 := by exact prefixLift 906271
  have htrace : WordTrace (prefixWord ++ tailWord_906271) baseStart_906271 baseEnd_906271 := by
    simpa [prefixWord, tailWord_906271, baseEnd_906271] using wordTrace_append hprefix tailTrace_906271
  have hstable : (prefixWord ++ tailWord_906271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906271).length < 2 ^ (prefixWord ++ tailWord_906271).sum := by decide
  have hdescent : baseEnd_906271 < baseStart_906271 := by decide
  rcases family_descends (prefixWord ++ tailWord_906271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906305 : List Nat := [1, 2, 5, 1, 3, 1, 1, 3, 4]
def baseStart_906305 : Nat := 118140960795 + 906305 * 2 ^ 59
def prefixEnd_906305 : Nat := 4983230072969 + 3 ^ 40 * 906305 * 2
def baseEnd_906305 : Nat := 206831148699191916097549

theorem tailTrace_906305 : CollatzResearch.WordTrace tailWord_906305 prefixEnd_906305 206831148699191916097549 := by
  unfold tailWord_906305
  simp only [CollatzResearch.WordTrace]
  refine ⟨33055658981619244416080369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22037105987746162944053579 33055658981619244416080369)
  ·
    refine ⟨24791744236214433312060277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33055658981619244416080369 24791744236214433312060277)
    ·
      refine ⟨2324226022145103123005651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24791744236214433312060277 2324226022145103123005651)
      ·
        refine ⟨3486339033217654684508477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324226022145103123005651 3486339033217654684508477)
        ·
          refine ⟨1307377137456620506690679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3486339033217654684508477 1307377137456620506690679)
          ·
            refine ⟨1961065706184930760036019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307377137456620506690679 1961065706184930760036019)
            ·
              refine ⟨2941598559277396140054029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1961065706184930760036019 2941598559277396140054029)
              ·
                refine ⟨1103099459729023552520261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2941598559277396140054029 1103099459729023552520261)
                ·
                  refine ⟨206831148699191916097549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103099459729023552520261 206831148699191916097549)
                  ·
                    rfl

theorem cell21_906305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_906305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906305 prefixEnd_906305 := by exact prefixLift 906305
  have htrace : WordTrace (prefixWord ++ tailWord_906305) baseStart_906305 baseEnd_906305 := by
    simpa [prefixWord, tailWord_906305, baseEnd_906305] using wordTrace_append hprefix tailTrace_906305
  have hstable : (prefixWord ++ tailWord_906305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906305).length < 2 ^ (prefixWord ++ tailWord_906305).sum := by decide
  have hdescent : baseEnd_906305 < baseStart_906305 := by decide
  rcases family_descends (prefixWord ++ tailWord_906305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906316 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_906316 : Nat := 118140960795 + 906316 * 2 ^ 59
def prefixEnd_906316 : Nat := 4983230072969 + 3 ^ 40 * 906316 * 2
def baseEnd_906316 : Nat := 206833659049058341414193

theorem tailTrace_906316 : CollatzResearch.WordTrace tailWord_906316 prefixEnd_906316 206833659049058341414193 := by
  unfold tailWord_906316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16528030092289696647365401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22037373456386262196487201 16528030092289696647365401)
  ·
    refine ⟨12396022569217272485524051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16528030092289696647365401 12396022569217272485524051)
    ·
      refine ⟨18594033853825908728286077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12396022569217272485524051 18594033853825908728286077)
      ·
        refine ⟨6972762695184715773107279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18594033853825908728286077 6972762695184715773107279)
        ·
          refine ⟨10459144042777073659660919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972762695184715773107279 10459144042777073659660919)
          ·
            refine ⟨15688716064165610489491379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10459144042777073659660919 15688716064165610489491379)
            ·
              refine ⟨23533074096248415734237069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15688716064165610489491379 23533074096248415734237069)
              ·
                refine ⟨8824902786093155900338901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23533074096248415734237069 8824902786093155900338901)
                ·
                  refine ⟨206833659049058341414193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8824902786093155900338901 206833659049058341414193)
                  ·
                    rfl

theorem cell21_906316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_906316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906316 prefixEnd_906316 := by exact prefixLift 906316
  have htrace : WordTrace (prefixWord ++ tailWord_906316) baseStart_906316 baseEnd_906316 := by
    simpa [prefixWord, tailWord_906316, baseEnd_906316] using wordTrace_append hprefix tailTrace_906316
  have hstable : (prefixWord ++ tailWord_906316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906316).length < 2 ^ (prefixWord ++ tailWord_906316).sum := by decide
  have hdescent : baseEnd_906316 < baseStart_906316 := by decide
  rcases family_descends (prefixWord ++ tailWord_906316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906398 : List Nat := [4, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_906398 : Nat := 118140960795 + 906398 * 2 ^ 59
def prefixEnd_906398 : Nat := 4983230072969 + 3 ^ 40 * 906398 * 2
def baseEnd_906398 : Nat := 206852372566244421047359

theorem tailTrace_906398 : CollatzResearch.WordTrace tailWord_906398 prefixEnd_906398 206852372566244421047359 := by
  unfold tailWord_906398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4132381371285290162401981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22039367313521547532810565 4132381371285290162401981)
  ·
    refine ⟨1549643014231983810900743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4132381371285290162401981 1549643014231983810900743)
    ·
      refine ⟨2324464521347975716351115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1549643014231983810900743 2324464521347975716351115)
      ·
        refine ⟨3486696782021963574526673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324464521347975716351115 3486696782021963574526673)
        ·
          refine ⟨2615022586516472680895005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3486696782021963574526673 2615022586516472680895005)
          ·
            refine ⟨980633469943677255335627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2615022586516472680895005 980633469943677255335627)
            ·
              refine ⟨1470950204915515883003441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980633469943677255335627 1470950204915515883003441)
              ·
                refine ⟨1103212653686636912252581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470950204915515883003441 1103212653686636912252581)
                ·
                  refine ⟨206852372566244421047359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103212653686636912252581 206852372566244421047359)
                  ·
                    rfl

theorem cell21_906398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_906398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906398 prefixEnd_906398 := by exact prefixLift 906398
  have htrace : WordTrace (prefixWord ++ tailWord_906398) baseStart_906398 baseEnd_906398 := by
    simpa [prefixWord, tailWord_906398, baseEnd_906398] using wordTrace_append hprefix tailTrace_906398
  have hstable : (prefixWord ++ tailWord_906398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906398).length < 2 ^ (prefixWord ++ tailWord_906398).sum := by decide
  have hdescent : baseEnd_906398 < baseStart_906398 := by decide
  rcases family_descends (prefixWord ++ tailWord_906398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906471 : List Nat := [1, 1, 5, 3, 2, 1, 2, 6]
def baseStart_906471 : Nat := 118140960795 + 906471 * 2 ^ 59
def prefixEnd_906471 : Nat := 4983230072969 + 3 ^ 40 * 906471 * 2
def baseEnd_906471 : Nat := 68956344053604172110181

theorem tailTrace_906471 : CollatzResearch.WordTrace tailWord_906471 prefixEnd_906471 68956344053604172110181 := by
  unfold tailWord_906471
  simp only [CollatzResearch.WordTrace]
  refine ⟨33061713499017854766623267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22041142332678569844415511 33061713499017854766623267)
  ·
    refine ⟨49592570248526782149934901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33061713499017854766623267 49592570248526782149934901)
    ·
      refine ⟨4649303460799385826556397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49592570248526782149934901 4649303460799385826556397)
      ·
        refine ⟨1743488797799769684958649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4649303460799385826556397 1743488797799769684958649)
        ·
          refine ⟨1307616598349827263718987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1743488797799769684958649 1307616598349827263718987)
          ·
            refine ⟨1961424897524740895578481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307616598349827263718987 1961424897524740895578481)
            ·
              refine ⟨1471068673143555671683861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961424897524740895578481 1471068673143555671683861)
              ·
                refine ⟨68956344053604172110181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1471068673143555671683861 68956344053604172110181)
                ·
                  rfl

theorem cell21_906471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_906471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906471 prefixEnd_906471 := by exact prefixLift 906471
  have htrace : WordTrace (prefixWord ++ tailWord_906471) baseStart_906471 baseEnd_906471 := by
    simpa [prefixWord, tailWord_906471, baseEnd_906471] using wordTrace_append hprefix tailTrace_906471
  have hstable : (prefixWord ++ tailWord_906471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906471).length < 2 ^ (prefixWord ++ tailWord_906471).sum := by decide
  have hdescent : baseEnd_906471 < baseStart_906471 := by decide
  rcases family_descends (prefixWord ++ tailWord_906471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906544 : List Nat := [2, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_906544 : Nat := 118140960795 + 906544 * 2 ^ 59
def prefixEnd_906544 : Nat := 4983230072969 + 3 ^ 40 * 906544 * 2
def baseEnd_906544 : Nat := 206885691755380611613727

theorem tailTrace_906544 : CollatzResearch.WordTrace tailWord_906544 prefixEnd_906544 206885691755380611613727 := by
  unfold tailWord_906544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532188013876694117015343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22042917351835592156020457 16532188013876694117015343)
  ·
    refine ⟨24798282020815041175523015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16532188013876694117015343 24798282020815041175523015)
    ·
      refine ⟨37197423031222561763284523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24798282020815041175523015 37197423031222561763284523)
      ·
        refine ⟨55796134546833842644926785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37197423031222561763284523 55796134546833842644926785)
        ·
          refine ⟨41847100910125381983695089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55796134546833842644926785 41847100910125381983695089)
          ·
            refine ⟨31385325682594036487771317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41847100910125381983695089 31385325682594036487771317)
            ·
              refine ⟨2942374282743190920728561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31385325682594036487771317 2942374282743190920728561)
              ·
                refine ⟨2206780712057393190546421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2942374282743190920728561 2206780712057393190546421)
                ·
                  refine ⟨206885691755380611613727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2206780712057393190546421 206885691755380611613727)
                  ·
                    rfl

theorem cell21_906544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_906544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906544 prefixEnd_906544 := by exact prefixLift 906544
  have htrace : WordTrace (prefixWord ++ tailWord_906544) baseStart_906544 baseEnd_906544 := by
    simpa [prefixWord, tailWord_906544, baseEnd_906544] using wordTrace_append hprefix tailTrace_906544
  have hstable : (prefixWord ++ tailWord_906544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906544).length < 2 ^ (prefixWord ++ tailWord_906544).sum := by decide
  have hdescent : baseEnd_906544 < baseStart_906544 := by decide
  rcases family_descends (prefixWord ++ tailWord_906544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906696 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_906696 : Nat := 118140960795 + 906696 * 2 ^ 59
def prefixEnd_906696 : Nat := 4983230072969 + 3 ^ 40 * 906696 * 2
def baseEnd_906696 : Nat := 206920380226262125080083

theorem tailTrace_906696 : CollatzResearch.WordTrace tailWord_906696 prefixEnd_906696 206920380226262125080083 := by
  unfold tailWord_906696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534959961601359096781971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22046613282135145462375961 16534959961601359096781971)
  ·
    refine ⟨24802439942402038645172957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16534959961601359096781971 24802439942402038645172957)
    ·
      refine ⟨9300914978400764491939859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24802439942402038645172957 9300914978400764491939859)
      ·
        refine ⟨13951372467601146737909789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300914978400764491939859 13951372467601146737909789)
        ·
          refine ⟨5231764675350430026716171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13951372467601146737909789 5231764675350430026716171)
          ·
            refine ⟨7847647013025645040074257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231764675350430026716171 7847647013025645040074257)
            ·
              refine ⟨5885735259769233780055693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847647013025645040074257 5885735259769233780055693)
              ·
                refine ⟨2207150722413462667520885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5885735259769233780055693 2207150722413462667520885)
                ·
                  refine ⟨206920380226262125080083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2207150722413462667520885 206920380226262125080083)
                  ·
                    rfl

theorem cell21_906696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_906696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906696 prefixEnd_906696 := by exact prefixLift 906696
  have htrace : WordTrace (prefixWord ++ tailWord_906696) baseStart_906696 baseEnd_906696 := by
    simpa [prefixWord, tailWord_906696, baseEnd_906696] using wordTrace_append hprefix tailTrace_906696
  have hstable : (prefixWord ++ tailWord_906696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906696).length < 2 ^ (prefixWord ++ tailWord_906696).sum := by decide
  have hdescent : baseEnd_906696 < baseStart_906696 := by decide
  rcases family_descends (prefixWord ++ tailWord_906696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906744 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_906744 : Nat := 118140960795 + 906744 * 2 ^ 59
def prefixEnd_906744 : Nat := 4983230072969 + 3 ^ 40 * 906744 * 2
def baseEnd_906744 : Nat := 206931334480224708279985

theorem tailTrace_906744 : CollatzResearch.WordTrace tailWord_906744 prefixEnd_906744 206931334480224708279985 := by
  unfold tailWord_906744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16535835313514411195655643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22047780418019214927540857 16535835313514411195655643)
  ·
    refine ⟨24803752970271616793483465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16535835313514411195655643 24803752970271616793483465)
    ·
      refine ⟨18602814727703712595112599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24803752970271616793483465 18602814727703712595112599)
      ·
        refine ⟨27904222091555568892668899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18602814727703712595112599 27904222091555568892668899)
        ·
          refine ⟨41856333137333353339003349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27904222091555568892668899 41856333137333353339003349)
          ·
            refine ⟨981007807906250468882891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 41856333137333353339003349 981007807906250468882891)
            ·
              refine ⟨1471511711859375703324337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981007807906250468882891 1471511711859375703324337)
              ·
                refine ⟨1103633783894531777493253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471511711859375703324337 1103633783894531777493253)
                ·
                  refine ⟨206931334480224708279985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103633783894531777493253 206931334480224708279985)
                  ·
                    rfl

theorem cell21_906744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_906744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906744 prefixEnd_906744 := by exact prefixLift 906744
  have htrace : WordTrace (prefixWord ++ tailWord_906744) baseStart_906744 baseEnd_906744 := by
    simpa [prefixWord, tailWord_906744, baseEnd_906744] using wordTrace_append hprefix tailTrace_906744
  have hstable : (prefixWord ++ tailWord_906744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906744).length < 2 ^ (prefixWord ++ tailWord_906744).sum := by decide
  have hdescent : baseEnd_906744 < baseStart_906744 := by decide
  rcases family_descends (prefixWord ++ tailWord_906744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906831 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_906831 : Nat := 118140960795 + 906831 * 2 ^ 59
def prefixEnd_906831 : Nat := 4983230072969 + 3 ^ 40 * 906831 * 2
def baseEnd_906831 : Nat := 206951189065531890329807

theorem tailTrace_906831 : CollatzResearch.WordTrace tailWord_906831 prefixEnd_906831 206951189065531890329807 := by
  unfold tailWord_906831
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074843777713636249728347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22049895851809090833152231 33074843777713636249728347)
  ·
    refine ⟨49612265666570454374592521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33074843777713636249728347 49612265666570454374592521)
    ·
      refine ⟨37209199249927840780944391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49612265666570454374592521 37209199249927840780944391)
      ·
        refine ⟨55813798874891761171416587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37209199249927840780944391 55813798874891761171416587)
        ·
          refine ⟨83720698312337641757124881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55813798874891761171416587 83720698312337641757124881)
          ·
            refine ⟨62790523734253231317843661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83720698312337641757124881 62790523734253231317843661)
            ·
              refine ⟨23546446400344961744191373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62790523734253231317843661 23546446400344961744191373)
              ·
                refine ⟨8829917400129360654071765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23546446400344961744191373 8829917400129360654071765)
                ·
                  refine ⟨206951189065531890329807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8829917400129360654071765 206951189065531890329807)
                  ·
                    rfl

theorem cell21_906831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_906831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906831 prefixEnd_906831 := by exact prefixLift 906831
  have htrace : WordTrace (prefixWord ++ tailWord_906831) baseStart_906831 baseEnd_906831 := by
    simpa [prefixWord, tailWord_906831, baseEnd_906831] using wordTrace_append hprefix tailTrace_906831
  have hstable : (prefixWord ++ tailWord_906831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906831).length < 2 ^ (prefixWord ++ tailWord_906831).sum := by decide
  have hdescent : baseEnd_906831 < baseStart_906831 := by decide
  rcases family_descends (prefixWord ++ tailWord_906831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906910 : List Nat := [4, 3, 1, 1, 1, 3, 8]
def baseStart_906910 : Nat := 118140960795 + 906910 * 2 ^ 59
def prefixEnd_906910 : Nat := 4983230072969 + 3 ^ 40 * 906910 * 2
def baseEnd_906910 : Nat := 22996579771316145390331

theorem tailTrace_906910 : CollatzResearch.WordTrace tailWord_906910 prefixEnd_906910 22996579771316145390331 := by
  unfold tailWord_906910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4134715643053429092731773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22051816762951621827902789 4134715643053429092731773)
  ·
    refine ⟨1550518366145035909774415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4134715643053429092731773 1550518366145035909774415)
    ·
      refine ⟨2325777549217553864661623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550518366145035909774415 2325777549217553864661623)
      ·
        refine ⟨3488666323826330796992435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325777549217553864661623 3488666323826330796992435)
        ·
          refine ⟨5232999485739496195488653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488666323826330796992435 5232999485739496195488653)
          ·
            refine ⟨1962374807152311073308245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5232999485739496195488653 1962374807152311073308245)
            ·
              refine ⟨22996579771316145390331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1962374807152311073308245 22996579771316145390331)
              ·
                rfl

theorem cell21_906910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 8].length) (baseStart_906910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906910 prefixEnd_906910 := by exact prefixLift 906910
  have htrace : WordTrace (prefixWord ++ tailWord_906910) baseStart_906910 baseEnd_906910 := by
    simpa [prefixWord, tailWord_906910, baseEnd_906910] using wordTrace_append hprefix tailTrace_906910
  have hstable : (prefixWord ++ tailWord_906910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906910).length < 2 ^ (prefixWord ++ tailWord_906910).sum := by decide
  have hdescent : baseEnd_906910 < baseStart_906910 := by decide
  rcases family_descends (prefixWord ++ tailWord_906910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906969 : List Nat := [1, 2, 1, 2, 3, 5, 7]
def baseStart_906969 : Nat := 118140960795 + 906969 * 2 ^ 59
def prefixEnd_906969 : Nat := 4983230072969 + 3 ^ 40 * 906969 * 2
def baseEnd_906969 : Nat := 22998075838408257447725

theorem tailTrace_906969 : CollatzResearch.WordTrace tailWord_906969 prefixEnd_906969 22998075838408257447725 := by
  unfold tailWord_906969
  simp only [CollatzResearch.WordTrace]
  refine ⟨33079877051213685818251961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22053251367475790545501307 33079877051213685818251961)
  ·
    refine ⟨24809907788410264363688971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33079877051213685818251961 24809907788410264363688971)
    ·
      refine ⟨37214861682615396545533457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24809907788410264363688971 37214861682615396545533457)
      ·
        refine ⟨27911146261961547409150093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37214861682615396545533457 27911146261961547409150093)
        ·
          refine ⟨10466679848235580278431285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27911146261961547409150093 10466679848235580278431285)
          ·
            refine ⟨981251235772085651102933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10466679848235580278431285 981251235772085651102933)
            ·
              refine ⟨22998075838408257447725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 981251235772085651102933 22998075838408257447725)
              ·
                rfl

theorem cell21_906969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 7].length) (baseStart_906969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906969 prefixEnd_906969 := by exact prefixLift 906969
  have htrace : WordTrace (prefixWord ++ tailWord_906969) baseStart_906969 baseEnd_906969 := by
    simpa [prefixWord, tailWord_906969, baseEnd_906969] using wordTrace_append hprefix tailTrace_906969
  have hstable : (prefixWord ++ tailWord_906969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906969).length < 2 ^ (prefixWord ++ tailWord_906969).sum := by decide
  have hdescent : baseEnd_906969 < baseStart_906969 := by decide
  rcases family_descends (prefixWord ++ tailWord_906969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906989 : List Nat := [1, 5, 1, 2, 1, 4, 2, 1, 4]
def baseStart_906989 : Nat := 118140960795 + 906989 * 2 ^ 59
def prefixEnd_906989 : Nat := 4983230072969 + 3 ^ 40 * 906989 * 2
def baseEnd_906989 : Nat := 206987246818158726696151

theorem tailTrace_906989 : CollatzResearch.WordTrace tailWord_906989 prefixEnd_906989 206987246818158726696151 := by
  unfold tailWord_906989
  simp only [CollatzResearch.WordTrace]
  refine ⟨33080606511141229233980021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22053737674094152822653347 33080606511141229233980021)
  ·
    refine ⟨3101306860419490240685627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33080606511141229233980021 3101306860419490240685627)
    ·
      refine ⟨4651960290629235361028441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101306860419490240685627 4651960290629235361028441)
      ·
        refine ⟨3488970217971926520771331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4651960290629235361028441 3488970217971926520771331)
        ·
          refine ⟨5233455326957889781156997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488970217971926520771331 5233455326957889781156997)
          ·
            refine ⟨981272873804604333966937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5233455326957889781156997 981272873804604333966937)
            ·
              refine ⟨735954655353453250475203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981272873804604333966937 735954655353453250475203)
              ·
                refine ⟨1103931983030179875712805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735954655353453250475203 1103931983030179875712805)
                ·
                  refine ⟨206987246818158726696151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103931983030179875712805 206987246818158726696151)
                  ·
                    rfl

theorem cell21_906989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_906989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_906989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_906989 prefixEnd_906989 := by exact prefixLift 906989
  have htrace : WordTrace (prefixWord ++ tailWord_906989) baseStart_906989 baseEnd_906989 := by
    simpa [prefixWord, tailWord_906989, baseEnd_906989] using wordTrace_append hprefix tailTrace_906989
  have hstable : (prefixWord ++ tailWord_906989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906989).length < 2 ^ (prefixWord ++ tailWord_906989).sum := by decide
  have hdescent : baseEnd_906989 < baseStart_906989 := by decide
  rcases family_descends (prefixWord ++ tailWord_906989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907031 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 4]
def baseStart_907031 : Nat := 118140960795 + 907031 * 2 ^ 59
def prefixEnd_907031 : Nat := 4983230072969 + 3 ^ 40 * 907031 * 2
def baseEnd_907031 : Nat := 206996831790375986996065

theorem tailTrace_907031 : CollatzResearch.WordTrace tailWord_907031 prefixEnd_907031 206996831790375986996065 := by
  unfold tailWord_907031
  simp only [CollatzResearch.WordTrace]
  refine ⟨33082138376989070407008947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22054758917992713604672631 33082138376989070407008947)
  ·
    refine ⟨49623207565483605610513421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33082138376989070407008947 49623207565483605610513421)
    ·
      refine ⟨18608702837056352103942533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49623207565483605610513421 18608702837056352103942533)
      ·
        refine ⟨3489131781948066019489225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18608702837056352103942533 3489131781948066019489225)
        ·
          refine ⟨2616848836461049514616919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3489131781948066019489225 2616848836461049514616919)
          ·
            refine ⟨3925273254691574271925379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616848836461049514616919 3925273254691574271925379)
            ·
              refine ⟨5887909882037361407888069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925273254691574271925379 5887909882037361407888069)
              ·
                refine ⟨1103983102882005263979013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5887909882037361407888069 1103983102882005263979013)
                ·
                  refine ⟨206996831790375986996065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1103983102882005263979013 206996831790375986996065)
                  ·
                    rfl

theorem cell21_907031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_907031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907031 prefixEnd_907031 := by exact prefixLift 907031
  have htrace : WordTrace (prefixWord ++ tailWord_907031) baseStart_907031 baseEnd_907031 := by
    simpa [prefixWord, tailWord_907031, baseEnd_907031] using wordTrace_append hprefix tailTrace_907031
  have hstable : (prefixWord ++ tailWord_907031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907031).length < 2 ^ (prefixWord ++ tailWord_907031).sum := by decide
  have hdescent : baseEnd_907031 < baseStart_907031 := by decide
  rcases family_descends (prefixWord ++ tailWord_907031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907034 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_907034 : Nat := 118140960795 + 907034 * 2 ^ 59
def prefixEnd_907034 : Nat := 4983230072969 + 3 ^ 40 * 907034 * 2
def baseEnd_907034 : Nat := 206997516431248648446059

theorem tailTrace_907034 : CollatzResearch.WordTrace tailWord_907034 prefixEnd_907034 206997516431248648446059 := by
  unfold tailWord_907034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270561948994550479842039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22054831863985467946245437 8270561948994550479842039)
  ·
    refine ⟨12405842923491825719763059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8270561948994550479842039 12405842923491825719763059)
    ·
      refine ⟨18608764385237738579644589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12405842923491825719763059 18608764385237738579644589)
      ·
        refine ⟨6978286644464151967366721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18608764385237738579644589 6978286644464151967366721)
        ·
          refine ⟨5233714983348113975525041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978286644464151967366721 5233714983348113975525041)
          ·
            refine ⟨3925286237511085481643781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233714983348113975525041 3925286237511085481643781)
            ·
              refine ⟨735991169533328527808209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3925286237511085481643781 735991169533328527808209)
              ·
                refine ⟨551993377149996395856157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735991169533328527808209 551993377149996395856157)
                ·
                  refine ⟨206997516431248648446059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 551993377149996395856157 206997516431248648446059)
                  ·
                    rfl

theorem cell21_907034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_907034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907034 prefixEnd_907034 := by exact prefixLift 907034
  have htrace : WordTrace (prefixWord ++ tailWord_907034) baseStart_907034 baseEnd_907034 := by
    simpa [prefixWord, tailWord_907034, baseEnd_907034] using wordTrace_append hprefix tailTrace_907034
  have hstable : (prefixWord ++ tailWord_907034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907034).length < 2 ^ (prefixWord ++ tailWord_907034).sum := by decide
  have hdescent : baseEnd_907034 < baseStart_907034 := by decide
  rcases family_descends (prefixWord ++ tailWord_907034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907045 : List Nat := [1, 3, 1, 2, 3, 2, 3, 6]
def baseStart_907045 : Nat := 118140960795 + 907045 * 2 ^ 59
def prefixEnd_907045 : Nat := 4983230072969 + 3 ^ 40 * 907045 * 2
def baseEnd_907045 : Nat := 69000008927038357920901

theorem tailTrace_907045 : CollatzResearch.WordTrace tailWord_907045 prefixEnd_907045 69000008927038357920901 := by
  unfold tailWord_907045
  simp only [CollatzResearch.WordTrace]
  refine ⟨33082648998938350798018589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22055099332625567198679059 33082648998938350798018589)
  ·
    refine ⟨12405993374601881549256971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33082648998938350798018589 12405993374601881549256971)
    ·
      refine ⟨18608990061902822323885457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12405993374601881549256971 18608990061902822323885457)
      ·
        refine ⟨13956742546427116742914093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18608990061902822323885457 13956742546427116742914093)
        ·
          refine ⟨5233778454910168778592785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13956742546427116742914093 5233778454910168778592785)
          ·
            refine ⟨3925333841182626583944589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233778454910168778592785 3925333841182626583944589)
            ·
              refine ⟨1472000190443484968979221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3925333841182626583944589 1472000190443484968979221)
              ·
                refine ⟨69000008927038357920901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1472000190443484968979221 69000008927038357920901)
                ·
                  rfl

theorem cell21_907045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 6].length) (baseStart_907045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907045 prefixEnd_907045 := by exact prefixLift 907045
  have htrace : WordTrace (prefixWord ++ tailWord_907045) baseStart_907045 baseEnd_907045 := by
    simpa [prefixWord, tailWord_907045, baseEnd_907045] using wordTrace_append hprefix tailTrace_907045
  have hstable : (prefixWord ++ tailWord_907045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907045).length < 2 ^ (prefixWord ++ tailWord_907045).sum := by decide
  have hdescent : baseEnd_907045 < baseStart_907045 := by decide
  rcases family_descends (prefixWord ++ tailWord_907045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907093 : List Nat := [1, 3, 2, 2, 2, 2, 2, 4, 3]
def baseStart_907093 : Nat := 118140960795 + 907093 * 2 ^ 59
def prefixEnd_907093 : Nat := 4983230072969 + 3 ^ 40 * 907093 * 2
def baseEnd_907093 : Nat := 207010981035077656962605

theorem tailTrace_907093 : CollatzResearch.WordTrace tailWord_907093 prefixEnd_907093 207010981035077656962605 := by
  unfold tailWord_907093
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084399702764454995765933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22056266468509636663843955 33084399702764454995765933)
  ·
    refine ⟨12406649888536670623412225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33084399702764454995765933 12406649888536670623412225)
    ·
      refine ⟨9304987416402502967559169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12406649888536670623412225 9304987416402502967559169)
      ·
        refine ⟨6978740562301877225669377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9304987416402502967559169 6978740562301877225669377)
        ·
          refine ⟨5234055421726407919252033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978740562301877225669377 5234055421726407919252033)
          ·
            refine ⟨3925541566294805939439025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234055421726407919252033 3925541566294805939439025)
            ·
              refine ⟨2944156174721104454579269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925541566294805939439025 2944156174721104454579269)
              ·
                refine ⟨552029282760207085233613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2944156174721104454579269 552029282760207085233613)
                ·
                  refine ⟨207010981035077656962605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552029282760207085233613 207010981035077656962605)
                  ·
                    rfl

theorem cell21_907093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_907093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907093 prefixEnd_907093 := by exact prefixLift 907093
  have htrace : WordTrace (prefixWord ++ tailWord_907093) baseStart_907093 baseEnd_907093 := by
    simpa [prefixWord, tailWord_907093, baseEnd_907093] using wordTrace_append hprefix tailTrace_907093
  have hstable : (prefixWord ++ tailWord_907093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907093).length < 2 ^ (prefixWord ++ tailWord_907093).sum := by decide
  have hdescent : baseEnd_907093 < baseStart_907093 := by decide
  rcases family_descends (prefixWord ++ tailWord_907093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907158 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_907158 : Nat := 118140960795 + 907158 * 2 ^ 59
def prefixEnd_907158 : Nat := 4983230072969 + 3 ^ 40 * 907158 * 2
def baseEnd_907158 : Nat := 207025814920651988379139

theorem tailTrace_907158 : CollatzResearch.WordTrace tailWord_907158 prefixEnd_907158 207025814920651988379139 := by
  unfold tailWord_907158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067923152970560693555133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22057846965019314064588085 2067923152970560693555133)
  ·
    refine ⟨775471182363960260083175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2067923152970560693555133 775471182363960260083175)
    ·
      refine ⟨1163206773545940390124763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775471182363960260083175 1163206773545940390124763)
      ·
        refine ⟨1744810160318910585187145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163206773545940390124763 1744810160318910585187145)
        ·
          refine ⟨1308607620239182938890359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744810160318910585187145 1308607620239182938890359)
          ·
            refine ⟨1962911430358774408335539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308607620239182938890359 1962911430358774408335539)
            ·
              refine ⟨2944367145538161612503309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962911430358774408335539 2944367145538161612503309)
              ·
                refine ⟨1104137679576810604688741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2944367145538161612503309 1104137679576810604688741)
                ·
                  refine ⟨207025814920651988379139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104137679576810604688741 207025814920651988379139)
                  ·
                    rfl

theorem cell21_907158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_907158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907158 prefixEnd_907158 := by exact prefixLift 907158
  have htrace : WordTrace (prefixWord ++ tailWord_907158) baseStart_907158 baseEnd_907158 := by
    simpa [prefixWord, tailWord_907158, baseEnd_907158] using wordTrace_append hprefix tailTrace_907158
  have hstable : (prefixWord ++ tailWord_907158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907158).length < 2 ^ (prefixWord ++ tailWord_907158).sum := by decide
  have hdescent : baseEnd_907158 < baseStart_907158 := by decide
  rcases family_descends (prefixWord ++ tailWord_907158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907211 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_907211 : Nat := 118140960795 + 907211 * 2 ^ 59
def prefixEnd_907211 : Nat := 4983230072969 + 3 ^ 40 * 907211 * 2
def baseEnd_907211 : Nat := 207037910242735673995697

theorem tailTrace_907211 : CollatzResearch.WordTrace tailWord_907211 prefixEnd_907211 207037910242735673995697 := by
  unfold tailWord_907211
  simp only [CollatzResearch.WordTrace]
  refine ⟨33088703516336961148561487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22059135677557974099040991 33088703516336961148561487)
  ·
    refine ⟨49633055274505441722842231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33088703516336961148561487 49633055274505441722842231)
    ·
      refine ⟨74449582911758162584263347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49633055274505441722842231 74449582911758162584263347)
      ·
        refine ⟨111674374367637243876395021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74449582911758162584263347 111674374367637243876395021)
        ·
          refine ⟨41877890387863966453648133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111674374367637243876395021 41877890387863966453648133)
          ·
            refine ⟨7852104447724493710059025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41877890387863966453648133 7852104447724493710059025)
            ·
              refine ⟨5889078335793370282544269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852104447724493710059025 5889078335793370282544269)
              ·
                refine ⟨2208404375922513855954101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889078335793370282544269 2208404375922513855954101)
                ·
                  refine ⟨207037910242735673995697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2208404375922513855954101 207037910242735673995697)
                  ·
                    rfl

theorem cell21_907211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_907211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907211 prefixEnd_907211 := by exact prefixLift 907211
  have htrace : WordTrace (prefixWord ++ tailWord_907211) baseStart_907211 baseEnd_907211 := by
    simpa [prefixWord, tailWord_907211, baseEnd_907211] using wordTrace_append hprefix tailTrace_907211
  have hstable : (prefixWord ++ tailWord_907211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907211).length < 2 ^ (prefixWord ++ tailWord_907211).sum := by decide
  have hdescent : baseEnd_907211 < baseStart_907211 := by decide
  rcases family_descends (prefixWord ++ tailWord_907211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907242 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_907242 : Nat := 118140960795 + 907242 * 2 ^ 59
def prefixEnd_907242 : Nat := 4983230072969 + 3 ^ 40 * 907242 * 2
def baseEnd_907242 : Nat := 207044984865086508978967

theorem tailTrace_907242 : CollatzResearch.WordTrace tailWord_907242 prefixEnd_907242 207044984865086508978967 := by
  unfold tailWord_907242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272458544806163360734995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22059889452816435628626653 8272458544806163360734995)
  ·
    refine ⟨12408687817209245041102493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8272458544806163360734995 12408687817209245041102493)
    ·
      refine ⟨4653257931453466890413435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12408687817209245041102493 4653257931453466890413435)
      ·
        refine ⟨6979886897180200335620153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4653257931453466890413435 6979886897180200335620153)
        ·
          refine ⟨5234915172885150251715115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6979886897180200335620153 5234915172885150251715115)
          ·
            refine ⟨7852372759327725377572673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234915172885150251715115 7852372759327725377572673)
            ·
              refine ⟨5889279569495794033179505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852372759327725377572673 5889279569495794033179505)
              ·
                refine ⟨4416959677121845524884629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5889279569495794033179505 4416959677121845524884629)
                ·
                  refine ⟨207044984865086508978967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4416959677121845524884629 207044984865086508978967)
                  ·
                    rfl

theorem cell21_907242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_907242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907242 prefixEnd_907242 := by exact prefixLift 907242
  have htrace : WordTrace (prefixWord ++ tailWord_907242) baseStart_907242 baseEnd_907242 := by
    simpa [prefixWord, tailWord_907242, baseEnd_907242] using wordTrace_append hprefix tailTrace_907242
  have hstable : (prefixWord ++ tailWord_907242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907242).length < 2 ^ (prefixWord ++ tailWord_907242).sum := by decide
  have hdescent : baseEnd_907242 < baseStart_907242 := by decide
  rcases family_descends (prefixWord ++ tailWord_907242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907262 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_907262 : Nat := 118140960795 + 907262 * 2 ^ 59
def prefixEnd_907262 : Nat := 4983230072969 + 3 ^ 40 * 907262 * 2
def baseEnd_907262 : Nat := 207049549137570918645593

theorem tailTrace_907262 : CollatzResearch.WordTrace tailWord_907262 prefixEnd_907262 207049549137570918645593 := by
  unfold tailWord_907262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136320454894024607333505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22060375759434797905778693 4136320454894024607333505)
  ·
    refine ⟨3102240341170518455500129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4136320454894024607333505 3102240341170518455500129)
    ·
      refine ⟨2326680255877888841625097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3102240341170518455500129 2326680255877888841625097)
      ·
        refine ⟨1745010191908416631218823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2326680255877888841625097 1745010191908416631218823)
        ·
          refine ⟨2617515287862624946828235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745010191908416631218823 2617515287862624946828235)
          ·
            refine ⟨3926272931793937420242353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617515287862624946828235 3926272931793937420242353)
            ·
              refine ⟨2944704698845453065181765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926272931793937420242353 2944704698845453065181765)
              ·
                refine ⟨552132131033522449721581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2944704698845453065181765 552132131033522449721581)
                ·
                  refine ⟨207049549137570918645593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552132131033522449721581 207049549137570918645593)
                  ·
                    rfl

theorem cell21_907262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_907262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907262 prefixEnd_907262 := by exact prefixLift 907262
  have htrace : WordTrace (prefixWord ++ tailWord_907262) baseStart_907262 baseEnd_907262 := by
    simpa [prefixWord, tailWord_907262, baseEnd_907262] using wordTrace_append hprefix tailTrace_907262
  have hstable : (prefixWord ++ tailWord_907262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907262).length < 2 ^ (prefixWord ++ tailWord_907262).sum := by decide
  have hdescent : baseEnd_907262 < baseStart_907262 := by decide
  rcases family_descends (prefixWord ++ tailWord_907262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907290 : List Nat := [3, 1, 1, 3, 1, 5, 2, 5]
def baseStart_907290 : Nat := 118140960795 + 907290 * 2 ^ 59
def prefixEnd_907290 : Nat := 4983230072969 + 3 ^ 40 * 907290 * 2
def baseEnd_907290 : Nat := 69018646373016364059623

theorem tailTrace_907290 : CollatzResearch.WordTrace tailWord_907290 prefixEnd_907290 69018646373016364059623 := by
  unfold tailWord_907290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272896220762689410171831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22061056588700505093791549 8272896220762689410171831)
  ·
    refine ⟨12409344331144034115257747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8272896220762689410171831 12409344331144034115257747)
    ·
      refine ⟨18614016496716051172886621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409344331144034115257747 18614016496716051172886621)
      ·
        refine ⟨6980256186268519189832483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18614016496716051172886621 6980256186268519189832483)
        ·
          refine ⟨10470384279402778784748725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6980256186268519189832483 10470384279402778784748725)
          ·
            refine ⟨981598526194010511070193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10470384279402778784748725 981598526194010511070193)
            ·
              refine ⟨736198894645507883302645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981598526194010511070193 736198894645507883302645)
              ·
                refine ⟨69018646373016364059623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 736198894645507883302645 69018646373016364059623)
                ·
                  rfl

theorem cell21_907290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_907290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907290 prefixEnd_907290 := by exact prefixLift 907290
  have htrace : WordTrace (prefixWord ++ tailWord_907290) baseStart_907290 baseEnd_907290 := by
    simpa [prefixWord, tailWord_907290, baseEnd_907290] using wordTrace_append hprefix tailTrace_907290
  have hstable : (prefixWord ++ tailWord_907290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907290).length < 2 ^ (prefixWord ++ tailWord_907290).sum := by decide
  have hdescent : baseEnd_907290 < baseStart_907290 := by decide
  rcases family_descends (prefixWord ++ tailWord_907290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907321 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 5]
def baseStart_907321 : Nat := 118140960795 + 907321 * 2 ^ 59
def prefixEnd_907321 : Nat := 4983230072969 + 3 ^ 40 * 907321 * 2
def baseEnd_907321 : Nat := 207063013741399927162139

theorem tailTrace_907321 : CollatzResearch.WordTrace tailWord_907321 prefixEnd_907321 207063013741399927162139 := by
  unfold tailWord_907321
  simp only [CollatzResearch.WordTrace]
  refine ⟨33092715545938449935065817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22061810363958966623377211 33092715545938449935065817)
  ·
    refine ⟨24819536659453837451299363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33092715545938449935065817 24819536659453837451299363)
    ·
      refine ⟨37229304989180756176949045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24819536659453837451299363 37229304989180756176949045)
      ·
        refine ⟨3490247342735695891588973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37229304989180756176949045 3490247342735695891588973)
        ·
          refine ⟨1308842753525885959345865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3490247342735695891588973 1308842753525885959345865)
          ·
            refine ⟨981632065144414469509399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308842753525885959345865 981632065144414469509399)
            ·
              refine ⟨1472448097716621704264099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981632065144414469509399 1472448097716621704264099)
              ·
                refine ⟨2208672146574932556396149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1472448097716621704264099 2208672146574932556396149)
                ·
                  refine ⟨207063013741399927162139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2208672146574932556396149 207063013741399927162139)
                  ·
                    rfl

theorem cell21_907321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_907321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907321 prefixEnd_907321 := by exact prefixLift 907321
  have htrace : WordTrace (prefixWord ++ tailWord_907321) baseStart_907321 baseEnd_907321 := by
    simpa [prefixWord, tailWord_907321, baseEnd_907321] using wordTrace_append hprefix tailTrace_907321
  have hstable : (prefixWord ++ tailWord_907321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907321).length < 2 ^ (prefixWord ++ tailWord_907321).sum := by decide
  have hdescent : baseEnd_907321 < baseStart_907321 := by decide
  rcases family_descends (prefixWord ++ tailWord_907321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907428 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_907428 : Nat := 118140960795 + 907428 * 2 ^ 59
def prefixEnd_907428 : Nat := 4983230072969 + 3 ^ 40 * 907428 * 2
def baseEnd_907428 : Nat := 207087432599191518878587

theorem tailTrace_907428 : CollatzResearch.WordTrace tailWord_907428 prefixEnd_907428 207087432599191518878587 := by
  unfold tailWord_907428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16548309078275403604605469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22064412104367204806140625 16548309078275403604605469)
  ·
    refine ⟨6205615904353276351727051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16548309078275403604605469 6205615904353276351727051)
    ·
      refine ⟨9308423856529914527590577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6205615904353276351727051 9308423856529914527590577)
      ·
        refine ⟨6981317892397435895692933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9308423856529914527590577 6981317892397435895692933)
        ·
          refine ⟨1308997104824519230442425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6981317892397435895692933 1308997104824519230442425)
          ·
            refine ⟨981747828618389422831819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308997104824519230442425 981747828618389422831819)
            ·
              refine ⟨1472621742927584134247729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981747828618389422831819 1472621742927584134247729)
              ·
                refine ⟨1104466307195688100685797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472621742927584134247729 1104466307195688100685797)
                ·
                  refine ⟨207087432599191518878587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104466307195688100685797 207087432599191518878587)
                  ·
                    rfl

theorem cell21_907428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_907428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907428 prefixEnd_907428 := by exact prefixLift 907428
  have htrace : WordTrace (prefixWord ++ tailWord_907428) baseStart_907428 baseEnd_907428 := by
    simpa [prefixWord, tailWord_907428, baseEnd_907428] using wordTrace_append hprefix tailTrace_907428
  have hstable : (prefixWord ++ tailWord_907428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907428).length < 2 ^ (prefixWord ++ tailWord_907428).sum := by decide
  have hdescent : baseEnd_907428 < baseStart_907428 := by decide
  rcases family_descends (prefixWord ++ tailWord_907428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907445 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 4]
def baseStart_907445 : Nat := 118140960795 + 907445 * 2 ^ 59
def prefixEnd_907445 : Nat := 4983230072969 + 3 ^ 40 * 907445 * 2
def baseEnd_907445 : Nat := 207091312230803267095219

theorem tailTrace_907445 : CollatzResearch.WordTrace tailWord_907445 prefixEnd_907445 207091312230803267095219 := by
  unfold tailWord_907445
  simp only [CollatzResearch.WordTrace]
  refine ⟨33097238197489219112579789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22064825464992812741719859 33097238197489219112579789)
  ·
    refine ⟨12411464324058457167217421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33097238197489219112579789 12411464324058457167217421)
    ·
      refine ⟨4654299121521921437706533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12411464324058457167217421 4654299121521921437706533)
      ·
        refine ⟨872681085285360269569975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4654299121521921437706533 872681085285360269569975)
        ·
          refine ⟨1309021627928040404354963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872681085285360269569975 1309021627928040404354963)
          ·
            refine ⟨1963532441892060606532445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309021627928040404354963 1963532441892060606532445)
            ·
              refine ⟨736324665709522727449667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1963532441892060606532445 736324665709522727449667)
              ·
                refine ⟨1104486998564284091174501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736324665709522727449667 1104486998564284091174501)
                ·
                  refine ⟨207091312230803267095219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104486998564284091174501 207091312230803267095219)
                  ·
                    rfl

theorem cell21_907445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_907445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907445 prefixEnd_907445 := by exact prefixLift 907445
  have htrace : WordTrace (prefixWord ++ tailWord_907445) baseStart_907445 baseEnd_907445 := by
    simpa [prefixWord, tailWord_907445, baseEnd_907445] using wordTrace_append hprefix tailTrace_907445
  have hstable : (prefixWord ++ tailWord_907445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907445).length < 2 ^ (prefixWord ++ tailWord_907445).sum := by decide
  have hdescent : baseEnd_907445 < baseStart_907445 := by decide
  rcases family_descends (prefixWord ++ tailWord_907445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907470 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_907470 : Nat := 118140960795 + 907470 * 2 ^ 59
def prefixEnd_907470 : Nat := 4983230072969 + 3 ^ 40 * 907470 * 2
def baseEnd_907470 : Nat := 207097017571408779178501

theorem tailTrace_907470 : CollatzResearch.WordTrace tailWord_907470 prefixEnd_907470 207097017571408779178501 := by
  unfold tailWord_907470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137268752799831047779983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22065433348265765588159909 4137268752799831047779983)
  ·
    refine ⟨6205903129199746571669975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4137268752799831047779983 6205903129199746571669975)
    ·
      refine ⟨9308854693799619857504963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6205903129199746571669975 9308854693799619857504963)
      ·
        refine ⟨13963282040699429786257445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308854693799619857504963 13963282040699429786257445)
        ·
          refine ⟨2618115382631143084923271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13963282040699429786257445 2618115382631143084923271)
          ·
            refine ⟨3927173073946714627384907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618115382631143084923271 3927173073946714627384907)
            ·
              refine ⟨5890759610920071941077361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927173073946714627384907 5890759610920071941077361)
              ·
                refine ⟨4418069708190053955808021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890759610920071941077361 4418069708190053955808021)
                ·
                  refine ⟨207097017571408779178501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4418069708190053955808021 207097017571408779178501)
                  ·
                    rfl

theorem cell21_907470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_907470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907470 prefixEnd_907470 := by exact prefixLift 907470
  have htrace : WordTrace (prefixWord ++ tailWord_907470) baseStart_907470 baseEnd_907470 := by
    simpa [prefixWord, tailWord_907470, baseEnd_907470] using wordTrace_append hprefix tailTrace_907470
  have hstable : (prefixWord ++ tailWord_907470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907470).length < 2 ^ (prefixWord ++ tailWord_907470).sum := by decide
  have hdescent : baseEnd_907470 < baseStart_907470 := by decide
  rcases family_descends (prefixWord ++ tailWord_907470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907532 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_907532 : Nat := 118140960795 + 907532 * 2 ^ 59
def prefixEnd_907532 : Nat := 4983230072969 + 3 ^ 40 * 907532 * 2
def baseEnd_907532 : Nat := 207111166816110449145041

theorem tailTrace_907532 : CollatzResearch.WordTrace tailWord_907532 prefixEnd_907532 207111166816110449145041 := by
  unfold tailWord_907532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550205674087016485498425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22066940898782688647331233 16550205674087016485498425)
  ·
    refine ⟨12412654255565262364123819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16550205674087016485498425 12412654255565262364123819)
    ·
      refine ⟨18618981383347893546185729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12412654255565262364123819 18618981383347893546185729)
      ·
        refine ⟨13964236037510920159639297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18618981383347893546185729 13964236037510920159639297)
        ·
          refine ⟨10473177028133190119729473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13964236037510920159639297 10473177028133190119729473)
          ·
            refine ⟨7854882771099892589797105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10473177028133190119729473 7854882771099892589797105)
            ·
              refine ⟨5891162078324919442347829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7854882771099892589797105 5891162078324919442347829)
              ·
                refine ⟨552296444842961197720109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5891162078324919442347829 552296444842961197720109)
                ·
                  refine ⟨207111166816110449145041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552296444842961197720109 207111166816110449145041)
                  ·
                    rfl

theorem cell21_907532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_907532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907532 prefixEnd_907532 := by exact prefixLift 907532
  have htrace : WordTrace (prefixWord ++ tailWord_907532) baseStart_907532 baseEnd_907532 := by
    simpa [prefixWord, tailWord_907532, baseEnd_907532] using wordTrace_append hprefix tailTrace_907532
  have hstable : (prefixWord ++ tailWord_907532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907532).length < 2 ^ (prefixWord ++ tailWord_907532).sum := by decide
  have hdescent : baseEnd_907532 < baseStart_907532 := by decide
  rcases family_descends (prefixWord ++ tailWord_907532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907743 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 5]
def baseStart_907743 : Nat := 118140960795 + 907743 * 2 ^ 59
def prefixEnd_907743 : Nat := 4983230072969 + 3 ^ 40 * 907743 * 2
def baseEnd_907743 : Nat := 207159319890820971127943

theorem tailTrace_907743 : CollatzResearch.WordTrace tailWord_907743 prefixEnd_907743 207159319890820971127943 := by
  unfold tailWord_907743
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108107150409616006927883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22072071433606410671285255 33108107150409616006927883)
  ·
    refine ⟨49662160725614424010391825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33108107150409616006927883 49662160725614424010391825)
    ·
      refine ⟨37246620544210818007793869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49662160725614424010391825 37246620544210818007793869)
      ·
        refine ⟨13967482704079056752922701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37246620544210818007793869 13967482704079056752922701)
        ·
          refine ⟨5237806014029646282346013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13967482704079056752922701 5237806014029646282346013)
          ·
            refine ⟨1964177255261117355879755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5237806014029646282346013 1964177255261117355879755)
            ·
              refine ⟨2946265882891676033819633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964177255261117355879755 2946265882891676033819633)
              ·
                refine ⟨2209699412168757025364725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946265882891676033819633 2209699412168757025364725)
                ·
                  refine ⟨207159319890820971127943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209699412168757025364725 207159319890820971127943)
                  ·
                    rfl

theorem cell21_907743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_907743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907743 prefixEnd_907743 := by exact prefixLift 907743
  have htrace : WordTrace (prefixWord ++ tailWord_907743) baseStart_907743 baseEnd_907743 := by
    simpa [prefixWord, tailWord_907743, baseEnd_907743] using wordTrace_append hprefix tailTrace_907743
  have hstable : (prefixWord ++ tailWord_907743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907743).length < 2 ^ (prefixWord ++ tailWord_907743).sum := by decide
  have hdescent : baseEnd_907743 < baseStart_907743 := by decide
  rcases family_descends (prefixWord ++ tailWord_907743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907760 : List Nat := [2, 1, 1, 1, 3, 3, 4, 3, 3]
def baseStart_907760 : Nat := 118140960795 + 907760 * 2 ^ 59
def prefixEnd_907760 : Nat := 4983230072969 + 3 ^ 40 * 907760 * 2
def baseEnd_907760 : Nat := 207163199522432719344575

theorem tailTrace_907760 : CollatzResearch.WordTrace tailWord_907760 prefixEnd_907760 207163199522432719344575 := by
  unfold tailWord_907760
  simp only [CollatzResearch.WordTrace]
  refine ⟨16554363595674013955148367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22072484794232018606864489 16554363595674013955148367)
  ·
    refine ⟨24831545393511020932722551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16554363595674013955148367 24831545393511020932722551)
    ·
      refine ⟨37247318090266531399083827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24831545393511020932722551 37247318090266531399083827)
      ·
        refine ⟨55870977135399797098625741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37247318090266531399083827 55870977135399797098625741)
        ·
          refine ⟨20951616425774923911984653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55870977135399797098625741 20951616425774923911984653)
          ·
            refine ⟨7856856159665596466994245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20951616425774923911984653 7856856159665596466994245)
            ·
              refine ⟨1473160529937299337561421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7856856159665596466994245 1473160529937299337561421)
              ·
                refine ⟨552435198726487251585533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1473160529937299337561421 552435198726487251585533)
                ·
                  refine ⟨207163199522432719344575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552435198726487251585533 207163199522432719344575)
                  ·
                    rfl

theorem cell21_907760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_907760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907760 prefixEnd_907760 := by exact prefixLift 907760
  have htrace : WordTrace (prefixWord ++ tailWord_907760) baseStart_907760 baseEnd_907760 := by
    simpa [prefixWord, tailWord_907760, baseEnd_907760] using wordTrace_append hprefix tailTrace_907760
  have hstable : (prefixWord ++ tailWord_907760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907760).length < 2 ^ (prefixWord ++ tailWord_907760).sum := by decide
  have hdescent : baseEnd_907760 < baseStart_907760 := by decide
  rcases family_descends (prefixWord ++ tailWord_907760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907805 : List Nat := [1, 4, 2, 2, 1, 2, 4, 5]
def baseStart_907805 : Nat := 118140960795 + 907805 * 2 ^ 59
def prefixEnd_907805 : Nat := 4983230072969 + 3 ^ 40 * 907805 * 2
def baseEnd_907805 : Nat := 69057823045174213698161

theorem tailTrace_907805 : CollatzResearch.WordTrace tailWord_907805 prefixEnd_907805 69057823045174213698161 := by
  unfold tailWord_907805
  simp only [CollatzResearch.WordTrace]
  refine ⟨33110368476185000595684869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22073578984123333730456579 33110368476185000595684869)
  ·
    refine ⟨6208194089284687611690913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33110368476185000595684869 6208194089284687611690913)
    ·
      refine ⟨4656145566963515708768185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208194089284687611690913 4656145566963515708768185)
      ·
        refine ⟨3492109175222636781576139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4656145566963515708768185 3492109175222636781576139)
        ·
          refine ⟨5238163762833955172364209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492109175222636781576139 5238163762833955172364209)
          ·
            refine ⟨3928622822125466379273157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5238163762833955172364209 3928622822125466379273157)
            ·
              refine ⟨736616779148524946113717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3928622822125466379273157 736616779148524946113717)
              ·
                refine ⟨69057823045174213698161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 736616779148524946113717 69057823045174213698161)
                ·
                  rfl

theorem cell21_907805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 5].length) (baseStart_907805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907805 prefixEnd_907805 := by exact prefixLift 907805
  have htrace : WordTrace (prefixWord ++ tailWord_907805) baseStart_907805 baseEnd_907805 := by
    simpa [prefixWord, tailWord_907805, baseEnd_907805] using wordTrace_append hprefix tailTrace_907805
  have hstable : (prefixWord ++ tailWord_907805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907805).length < 2 ^ (prefixWord ++ tailWord_907805).sum := by decide
  have hdescent : baseEnd_907805 < baseStart_907805 := by decide
  rcases family_descends (prefixWord ++ tailWord_907805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907822 : List Nat := [4, 1, 3, 1, 4, 1, 7]
def baseStart_907822 : Nat := 118140960795 + 907822 * 2 ^ 59
def prefixEnd_907822 : Nat := 4983230072969 + 3 ^ 40 * 907822 * 2
def baseEnd_907822 : Nat := 23019705418570487701235

theorem tailTrace_907822 : CollatzResearch.WordTrace tailWord_907822 prefixEnd_907822 23019705418570487701235 := by
  unfold tailWord_907822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138873564640426562381715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22073992344748941666035813 4138873564640426562381715)
  ·
    refine ⟨6208310346960639843572573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138873564640426562381715 6208310346960639843572573)
    ·
      refine ⟨2328116380110239941339715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6208310346960639843572573 2328116380110239941339715)
      ·
        refine ⟨3492174570165359912009573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328116380110239941339715 3492174570165359912009573)
        ·
          refine ⟨654782731906004983501795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3492174570165359912009573 654782731906004983501795)
          ·
            refine ⟨982174097859007475252693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654782731906004983501795 982174097859007475252693)
            ·
              refine ⟨23019705418570487701235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 982174097859007475252693 23019705418570487701235)
              ·
                rfl

theorem cell21_907822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 7].length) (baseStart_907822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907822 prefixEnd_907822 := by exact prefixLift 907822
  have htrace : WordTrace (prefixWord ++ tailWord_907822) baseStart_907822 baseEnd_907822 := by
    simpa [prefixWord, tailWord_907822, baseEnd_907822] using wordTrace_append hprefix tailTrace_907822
  have hstable : (prefixWord ++ tailWord_907822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907822).length < 2 ^ (prefixWord ++ tailWord_907822).sum := by decide
  have hdescent : baseEnd_907822 < baseStart_907822 := by decide
  rcases family_descends (prefixWord ++ tailWord_907822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907833 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_907833 : Nat := 118140960795 + 907833 * 2 ^ 59
def prefixEnd_907833 : Nat := 4983230072969 + 3 ^ 40 * 907833 * 2
def baseEnd_907833 : Nat := 207179859117000814627759

theorem tailTrace_907833 : CollatzResearch.WordTrace tailWord_907833 prefixEnd_907833 207179859117000814627759 := by
  unfold tailWord_907833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33111389720083561377704153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22074259813389040918469435 33111389720083561377704153)
  ·
    refine ⟨24833542290062671033278115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33111389720083561377704153 24833542290062671033278115)
    ·
      refine ⟨37250313435094006549917173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24833542290062671033278115 37250313435094006549917173)
      ·
        refine ⟨3492216884540063114054735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37250313435094006549917173 3492216884540063114054735)
        ·
          refine ⟨5238325326810094671082103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492216884540063114054735 5238325326810094671082103)
          ·
            refine ⟨7857487990215142006623155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238325326810094671082103 7857487990215142006623155)
            ·
              refine ⟨11786231985322713009934733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857487990215142006623155 11786231985322713009934733)
              ·
                refine ⟨4419836994496017378725525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11786231985322713009934733 4419836994496017378725525)
                ·
                  refine ⟨207179859117000814627759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4419836994496017378725525 207179859117000814627759)
                  ·
                    rfl

theorem cell21_907833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_907833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907833 prefixEnd_907833 := by exact prefixLift 907833
  have htrace : WordTrace (prefixWord ++ tailWord_907833) baseStart_907833 baseEnd_907833 := by
    simpa [prefixWord, tailWord_907833, baseEnd_907833] using wordTrace_append hprefix tailTrace_907833
  have hstable : (prefixWord ++ tailWord_907833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907833).length < 2 ^ (prefixWord ++ tailWord_907833).sum := by decide
  have hdescent : baseEnd_907833 < baseStart_907833 := by decide
  rcases family_descends (prefixWord ++ tailWord_907833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907836 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_907836 : Nat := 118140960795 + 907836 * 2 ^ 59
def prefixEnd_907836 : Nat := 4983230072969 + 3 ^ 40 * 907836 * 2
def baseEnd_907836 : Nat := 207180543757873476077753

theorem tailTrace_907836 : CollatzResearch.WordTrace tailWord_907836 prefixEnd_907836 207180543757873476077753 := by
  unfold tailWord_907836
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555749569536346445031681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22074332759381795260042241 16555749569536346445031681)
  ·
    refine ⟨12416812177152259833773761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16555749569536346445031681 12416812177152259833773761)
    ·
      refine ⟨9312609132864194875330321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12416812177152259833773761 9312609132864194875330321)
      ·
        refine ⟨6984456849648146156497741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9312609132864194875330321 6984456849648146156497741)
        ·
          refine ⟨2619171318618054808686653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6984456849648146156497741 2619171318618054808686653)
          ·
            refine ⟨982189244481770553257495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2619171318618054808686653 982189244481770553257495)
            ·
              refine ⟨1473283866722655829886243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982189244481770553257495 1473283866722655829886243)
              ·
                refine ⟨2209925800083983744829365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1473283866722655829886243 2209925800083983744829365)
                ·
                  refine ⟨207180543757873476077753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209925800083983744829365 207180543757873476077753)
                  ·
                    rfl

theorem cell21_907836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_907836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907836 prefixEnd_907836 := by exact prefixLift 907836
  have htrace : WordTrace (prefixWord ++ tailWord_907836) baseStart_907836 baseEnd_907836 := by
    simpa [prefixWord, tailWord_907836, baseEnd_907836] using wordTrace_append hprefix tailTrace_907836
  have hstable : (prefixWord ++ tailWord_907836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907836).length < 2 ^ (prefixWord ++ tailWord_907836).sum := by decide
  have hdescent : baseEnd_907836 < baseStart_907836 := by decide
  rcases family_descends (prefixWord ++ tailWord_907836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907850 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_907850 : Nat := 118140960795 + 907850 * 2 ^ 59
def prefixEnd_907850 : Nat := 4983230072969 + 3 ^ 40 * 907850 * 2
def baseEnd_907850 : Nat := 207183738748612562844391

theorem tailTrace_907850 : CollatzResearch.WordTrace tailWord_907850 prefixEnd_907850 207183738748612562844391 := by
  unfold tailWord_907850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8278002440255493320268251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22074673174014648854048669 8278002440255493320268251)
  ·
    refine ⟨12417003660383239980402377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8278002440255493320268251 12417003660383239980402377)
    ·
      refine ⟨9312752745287429985301783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12417003660383239980402377 9312752745287429985301783)
      ·
        refine ⟨13969129117931144977952675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312752745287429985301783 13969129117931144977952675)
        ·
          refine ⟨20953693676896717466929013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13969129117931144977952675 20953693676896717466929013)
          ·
            refine ⟨1964408782209067262524595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20953693676896717466929013 1964408782209067262524595)
            ·
              refine ⟨2946613173313600893786893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964408782209067262524595 2946613173313600893786893)
              ·
                refine ⟨1104979939992600335170085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946613173313600893786893 1104979939992600335170085)
                ·
                  refine ⟨207183738748612562844391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1104979939992600335170085 207183738748612562844391)
                  ·
                    rfl

theorem cell21_907850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_907850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907850 prefixEnd_907850 := by exact prefixLift 907850
  have htrace : WordTrace (prefixWord ++ tailWord_907850) baseStart_907850 baseEnd_907850 := by
    simpa [prefixWord, tailWord_907850, baseEnd_907850] using wordTrace_append hprefix tailTrace_907850
  have hstable : (prefixWord ++ tailWord_907850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907850).length < 2 ^ (prefixWord ++ tailWord_907850).sum := by decide
  have hdescent : baseEnd_907850 < baseStart_907850 := by decide
  rcases family_descends (prefixWord ++ tailWord_907850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907943 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 6]
def baseStart_907943 : Nat := 118140960795 + 907943 * 2 ^ 59
def prefixEnd_907943 : Nat := 4983230072969 + 3 ^ 40 * 907943 * 2
def baseEnd_907943 : Nat := 207204962615665067794201

theorem tailTrace_907943 : CollatzResearch.WordTrace tailWord_907943 prefixEnd_907943 207204962615665067794201 := by
  unfold tailWord_907943
  simp only [CollatzResearch.WordTrace]
  refine ⟨33115401749685050164208483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22076934499790033442805655 33115401749685050164208483)
  ·
    refine ⟨49673102624527575246312725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33115401749685050164208483 49673102624527575246312725)
    ·
      refine ⟨2328426685524730089670909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49673102624527575246312725 2328426685524730089670909)
      ·
        refine ⟨873160007071773783626591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2328426685524730089670909 873160007071773783626591)
        ·
          refine ⟨1309740010607660675439887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873160007071773783626591 1309740010607660675439887)
          ·
            refine ⟨1964610015911491013159831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309740010607660675439887 1964610015911491013159831)
            ·
              refine ⟨2946915023867236519739747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964610015911491013159831 2946915023867236519739747)
              ·
                refine ⟨4420372535800854779609621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2946915023867236519739747 4420372535800854779609621)
                ·
                  refine ⟨207204962615665067794201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4420372535800854779609621 207204962615665067794201)
                  ·
                    rfl

theorem cell21_907943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].length) (baseStart_907943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907943 prefixEnd_907943 := by exact prefixLift 907943
  have htrace : WordTrace (prefixWord ++ tailWord_907943) baseStart_907943 baseEnd_907943 := by
    simpa [prefixWord, tailWord_907943, baseEnd_907943] using wordTrace_append hprefix tailTrace_907943
  have hstable : (prefixWord ++ tailWord_907943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907943).length < 2 ^ (prefixWord ++ tailWord_907943).sum := by decide
  have hdescent : baseEnd_907943 < baseStart_907943 := by decide
  rcases family_descends (prefixWord ++ tailWord_907943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907999 : List Nat := [1, 1, 2, 3, 2, 3, 9]
def baseStart_907999 : Nat := 118140960795 + 907999 * 2 ^ 59
def prefixEnd_907999 : Nat := 4983230072969 + 3 ^ 40 * 907999 * 2
def baseEnd_907999 : Nat := 23024193619846823873417

theorem tailTrace_907999 : CollatzResearch.WordTrace tailWord_907999 prefixEnd_907999 23024193619846823873417 := by
  unfold tailWord_907999
  simp only [CollatzResearch.WordTrace]
  refine ⟨33117444237482171728247051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22078296158321447818831367 33117444237482171728247051)
  ·
    refine ⟨49676166356223257592370577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33117444237482171728247051 49676166356223257592370577)
    ·
      refine ⟨37257124767167443194277933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49676166356223257592370577 37257124767167443194277933)
      ·
        refine ⟨13971421787687791197854225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37257124767167443194277933 13971421787687791197854225)
        ·
          refine ⟨10478566340765843398390669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13971421787687791197854225 10478566340765843398390669)
          ·
            refine ⟨3929462377787191274396501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10478566340765843398390669 3929462377787191274396501)
            ·
              refine ⟨23024193619846823873417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3929462377787191274396501 23024193619846823873417)
              ·
                rfl

theorem cell21_907999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 9].length) (baseStart_907999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_907999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_907999 prefixEnd_907999 := by exact prefixLift 907999
  have htrace : WordTrace (prefixWord ++ tailWord_907999) baseStart_907999 baseEnd_907999 := by
    simpa [prefixWord, tailWord_907999, baseEnd_907999] using wordTrace_append hprefix tailTrace_907999
  have hstable : (prefixWord ++ tailWord_907999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907999).length < 2 ^ (prefixWord ++ tailWord_907999).sum := by decide
  have hdescent : baseEnd_907999 < baseStart_907999 := by decide
  rcases family_descends (prefixWord ++ tailWord_907999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908005 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 3]
def baseStart_908005 : Nat := 118140960795 + 908005 * 2 ^ 59
def prefixEnd_908005 : Nat := 4983230072969 + 3 ^ 40 * 908005 * 2
def baseEnd_908005 : Nat := 207219111860366737760741

theorem tailTrace_908005 : CollatzResearch.WordTrace tailWord_908005 prefixEnd_908005 207219111860366737760741 := by
  unfold tailWord_908005
  simp only [CollatzResearch.WordTrace]
  refine ⟨33117663075460434752965469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22078442050306956501976979 33117663075460434752965469)
  ·
    refine ⟨12419123653297663032362051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33117663075460434752965469 12419123653297663032362051)
    ·
      refine ⟨18628685479946494548543077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12419123653297663032362051 18628685479946494548543077)
      ·
        refine ⟨3492878527489967727851827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18628685479946494548543077 3492878527489967727851827)
        ·
          refine ⟨5239317791234951591777741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492878527489967727851827 5239317791234951591777741)
          ·
            refine ⟨1964744171713106846916653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5239317791234951591777741 1964744171713106846916653)
            ·
              refine ⟨736779064392415067593745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1964744171713106846916653 736779064392415067593745)
              ·
                refine ⟨552584298294311300695309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736779064392415067593745 552584298294311300695309)
                ·
                  refine ⟨207219111860366737760741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552584298294311300695309 207219111860366737760741)
                  ·
                    rfl

theorem cell21_908005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_908005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908005 prefixEnd_908005 := by exact prefixLift 908005
  have htrace : WordTrace (prefixWord ++ tailWord_908005) baseStart_908005 baseEnd_908005 := by
    simpa [prefixWord, tailWord_908005, baseEnd_908005] using wordTrace_append hprefix tailTrace_908005
  have hstable : (prefixWord ++ tailWord_908005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908005).length < 2 ^ (prefixWord ++ tailWord_908005).sum := by decide
  have hdescent : baseEnd_908005 < baseStart_908005 := by decide
  rcases family_descends (prefixWord ++ tailWord_908005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908047 : List Nat := [1, 1, 2, 1, 1, 1, 6, 5, 3]
def baseStart_908047 : Nat := 118140960795 + 908047 * 2 ^ 59
def prefixEnd_908047 : Nat := 4983230072969 + 3 ^ 40 * 908047 * 2
def baseEnd_908047 : Nat := 207228696832583998060655

theorem tailTrace_908047 : CollatzResearch.WordTrace tailWord_908047 prefixEnd_908047 207228696832583998060655 := by
  unfold tailWord_908047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33119194941308275925994395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22079463294205517283996263 33119194941308275925994395)
  ·
    refine ⟨49678792411962413888991593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33119194941308275925994395 49678792411962413888991593)
    ·
      refine ⟨37259094308971810416743695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49678792411962413888991593 37259094308971810416743695)
      ·
        refine ⟨55888641463457715625115543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37259094308971810416743695 55888641463457715625115543)
        ·
          refine ⟨83832962195186573437673315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55888641463457715625115543 83832962195186573437673315)
          ·
            refine ⟨125749443292779860156509973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83832962195186573437673315 125749443292779860156509973)
            ·
              refine ⟨5894505154349055944836405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125749443292779860156509973 5894505154349055944836405)
              ·
                refine ⟨552609858220223994828413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5894505154349055944836405 552609858220223994828413)
                ·
                  refine ⟨207228696832583998060655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552609858220223994828413 207228696832583998060655)
                  ·
                    rfl

theorem cell21_908047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 3].length) (baseStart_908047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908047 prefixEnd_908047 := by exact prefixLift 908047
  have htrace : WordTrace (prefixWord ++ tailWord_908047) baseStart_908047 baseEnd_908047 := by
    simpa [prefixWord, tailWord_908047, baseEnd_908047] using wordTrace_append hprefix tailTrace_908047
  have hstable : (prefixWord ++ tailWord_908047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908047).length < 2 ^ (prefixWord ++ tailWord_908047).sum := by decide
  have hdescent : baseEnd_908047 < baseStart_908047 := by decide
  rcases family_descends (prefixWord ++ tailWord_908047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908064 : List Nat := [2, 1, 1, 5, 1, 3, 1, 4, 3]
def baseStart_908064 : Nat := 118140960795 + 908064 * 2 ^ 59
def prefixEnd_908064 : Nat := 4983230072969 + 3 ^ 40 * 908064 * 2
def baseEnd_908064 : Nat := 207232576464195746277287

theorem tailTrace_908064 : CollatzResearch.WordTrace tailWord_908064 prefixEnd_908064 207232576464195746277287 := by
  unfold tailWord_908064
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559907491123343914681623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22079876654831125219575497 16559907491123343914681623)
  ·
    refine ⟨24839861236685015872022435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16559907491123343914681623 24839861236685015872022435)
    ·
      refine ⟨37259791855027523808033653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24839861236685015872022435 37259791855027523808033653)
      ·
        refine ⟨3493105486408830357003155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37259791855027523808033653 3493105486408830357003155)
        ·
          refine ⟨5239658229613245535504733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493105486408830357003155 5239658229613245535504733)
          ·
            refine ⟨1964871836104967075814275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5239658229613245535504733 1964871836104967075814275)
            ·
              refine ⟨2947307754157450613721413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964871836104967075814275 2947307754157450613721413)
              ·
                refine ⟨552620203904521990072765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2947307754157450613721413 552620203904521990072765)
                ·
                  refine ⟨207232576464195746277287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552620203904521990072765 207232576464195746277287)
                  ·
                    rfl

theorem cell21_908064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_908064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908064 prefixEnd_908064 := by exact prefixLift 908064
  have htrace : WordTrace (prefixWord ++ tailWord_908064) baseStart_908064 baseEnd_908064 := by
    simpa [prefixWord, tailWord_908064, baseEnd_908064] using wordTrace_append hprefix tailTrace_908064
  have hstable : (prefixWord ++ tailWord_908064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908064).length < 2 ^ (prefixWord ++ tailWord_908064).sum := by decide
  have hdescent : baseEnd_908064 < baseStart_908064 := by decide
  rcases family_descends (prefixWord ++ tailWord_908064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908109 : List Nat := [1, 6, 1, 2, 2, 1, 8]
def baseStart_908109 : Nat := 118140960795 + 908109 * 2 ^ 59
def prefixEnd_908109 : Nat := 4983230072969 + 3 ^ 40 * 908109 * 2
def baseEnd_908109 : Nat := 23026982897476185336355

theorem tailTrace_908109 : CollatzResearch.WordTrace tailWord_908109 prefixEnd_908109 23026982897476185336355 := by
  unfold tailWord_908109
  simp only [CollatzResearch.WordTrace]
  refine ⟨33121456267083660514751381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22080970844722440343167587 33121456267083660514751381)
  ·
    refine ⟨1552568262519546586628971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33121456267083660514751381 1552568262519546586628971)
    ·
      refine ⟨2328852393779319879943457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552568262519546586628971 2328852393779319879943457)
      ·
        refine ⟨1746639295334489909957593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2328852393779319879943457 1746639295334489909957593)
        ·
          refine ⟨1309979471500867432468195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746639295334489909957593 1309979471500867432468195)
          ·
            refine ⟨1964969207251301148702293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309979471500867432468195 1964969207251301148702293)
            ·
              refine ⟨23026982897476185336355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1964969207251301148702293 23026982897476185336355)
              ·
                rfl

theorem cell21_908109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 8].length) (baseStart_908109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908109 prefixEnd_908109 := by exact prefixLift 908109
  have htrace : WordTrace (prefixWord ++ tailWord_908109) baseStart_908109 baseEnd_908109 := by
    simpa [prefixWord, tailWord_908109, baseEnd_908109] using wordTrace_append hprefix tailTrace_908109
  have hstable : (prefixWord ++ tailWord_908109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908109).length < 2 ^ (prefixWord ++ tailWord_908109).sum := by decide
  have hdescent : baseEnd_908109 < baseStart_908109 := by decide
  rcases family_descends (prefixWord ++ tailWord_908109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908168 : List Nat := [2, 1, 3, 3, 2, 3, 7]
def baseStart_908168 : Nat := 118140960795 + 908168 * 2 ^ 59
def prefixEnd_908168 : Nat := 4983230072969 + 3 ^ 40 * 908168 * 2
def baseEnd_908168 : Nat := 23028478964568297393749

theorem tailTrace_908168 : CollatzResearch.WordTrace tailWord_908168 prefixEnd_908168 23028478964568297393749 := by
  unfold tailWord_908168
  simp only [CollatzResearch.WordTrace]
  refine ⟨16561804086934956795574579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22082405449246609060766105 16561804086934956795574579)
  ·
    refine ⟨24842706130402435193361869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16561804086934956795574579 24842706130402435193361869)
    ·
      refine ⟨9316014798900913197510701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24842706130402435193361869 9316014798900913197510701)
      ·
        refine ⟨3493505549587842449066513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9316014798900913197510701 3493505549587842449066513)
        ·
          refine ⟨2620129162190881836799885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3493505549587842449066513 2620129162190881836799885)
          ·
            refine ⟨982548435821580688799957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2620129162190881836799885 982548435821580688799957)
            ·
              refine ⟨23028478964568297393749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 982548435821580688799957 23028478964568297393749)
              ·
                rfl

theorem cell21_908168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 7].length) (baseStart_908168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908168 prefixEnd_908168 := by exact prefixLift 908168
  have htrace : WordTrace (prefixWord ++ tailWord_908168) baseStart_908168 baseEnd_908168 := by
    simpa [prefixWord, tailWord_908168, baseEnd_908168] using wordTrace_append hprefix tailTrace_908168
  have hstable : (prefixWord ++ tailWord_908168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908168).length < 2 ^ (prefixWord ++ tailWord_908168).sum := by decide
  have hdescent : baseEnd_908168 < baseStart_908168 := by decide
  rcases family_descends (prefixWord ++ tailWord_908168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908188 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 4]
def baseStart_908188 : Nat := 118140960795 + 908188 * 2 ^ 59
def prefixEnd_908188 : Nat := 4983230072969 + 3 ^ 40 * 908188 * 2
def baseEnd_908188 : Nat := 207260874953599086210367

theorem tailTrace_908188 : CollatzResearch.WordTrace tailWord_908188 prefixEnd_908188 207260874953599086210367 := by
  unfold tailWord_908188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16562168816898728503438609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22082891755864971337918145 16562168816898728503438609)
  ·
    refine ⟨12421626612674046377578957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16562168816898728503438609 12421626612674046377578957)
    ·
      refine ⟨4658109979752767391592109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12421626612674046377578957 4658109979752767391592109)
      ·
        refine ⟨1746791242407287771847041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4658109979752767391592109 1746791242407287771847041)
        ·
          refine ⟨1310093431805465828885281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746791242407287771847041 1310093431805465828885281)
          ·
            refine ⟨982570073854099371663961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1310093431805465828885281 982570073854099371663961)
            ·
              refine ⟨736927555390574528747971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982570073854099371663961 736927555390574528747971)
              ·
                refine ⟨1105391333085861793121957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736927555390574528747971 1105391333085861793121957)
                ·
                  refine ⟨207260874953599086210367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105391333085861793121957 207260874953599086210367)
                  ·
                    rfl

theorem cell21_908188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_908188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908188 prefixEnd_908188 := by exact prefixLift 908188
  have htrace : WordTrace (prefixWord ++ tailWord_908188) baseStart_908188 baseEnd_908188 := by
    simpa [prefixWord, tailWord_908188, baseEnd_908188] using wordTrace_append hprefix tailTrace_908188
  have hstable : (prefixWord ++ tailWord_908188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908188).length < 2 ^ (prefixWord ++ tailWord_908188).sum := by decide
  have hdescent : baseEnd_908188 < baseStart_908188 := by decide
  rcases family_descends (prefixWord ++ tailWord_908188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908244 : List Nat := [2, 4, 1, 2, 1, 2, 3, 6]
def baseStart_908244 : Nat := 118140960795 + 908244 * 2 ^ 59
def prefixEnd_908244 : Nat := 4983230072969 + 3 ^ 40 * 908244 * 2
def baseEnd_908244 : Nat := 69091218305518477758973

theorem tailTrace_908244 : CollatzResearch.WordTrace tailWord_908244 prefixEnd_908244 69091218305518477758973 := by
  unfold tailWord_908244
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563190060797289285457893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22084253414396385713943857 16563190060797289285457893)
  ·
    refine ⟨3105598136399491741023355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16563190060797289285457893 3105598136399491741023355)
    ·
      refine ⟨4658397204599237611535033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105598136399491741023355 4658397204599237611535033)
      ·
        refine ⟨3493797903449428208651275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4658397204599237611535033 3493797903449428208651275)
        ·
          refine ⟨5240696855174142312976913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493797903449428208651275 5240696855174142312976913)
          ·
            refine ⟨3930522641380606734732685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5240696855174142312976913 3930522641380606734732685)
            ·
              refine ⟨1473945990517727525524757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3930522641380606734732685 1473945990517727525524757)
              ·
                refine ⟨69091218305518477758973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1473945990517727525524757 69091218305518477758973)
                ·
                  rfl

theorem cell21_908244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_908244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908244 prefixEnd_908244 := by exact prefixLift 908244
  have htrace : WordTrace (prefixWord ++ tailWord_908244) baseStart_908244 baseEnd_908244 := by
    simpa [prefixWord, tailWord_908244, baseEnd_908244] using wordTrace_append hprefix tailTrace_908244
  have hstable : (prefixWord ++ tailWord_908244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908244).length < 2 ^ (prefixWord ++ tailWord_908244).sum := by decide
  have hdescent : baseEnd_908244 < baseStart_908244 := by decide
  rcases family_descends (prefixWord ++ tailWord_908244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908272 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_908272 : Nat := 118140960795 + 908272 * 2 ^ 59
def prefixEnd_908272 : Nat := 4983230072969 + 3 ^ 40 * 908272 * 2
def baseEnd_908272 : Nat := 207280044898033606810195

theorem tailTrace_908272 : CollatzResearch.WordTrace tailWord_908272 prefixEnd_908272 207280044898033606810195 := by
  unfold tailWord_908272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563700682746569676467535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22084934243662092901956713 16563700682746569676467535)
  ·
    refine ⟨24845551024119854514701303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16563700682746569676467535 24845551024119854514701303)
    ·
      refine ⟨37268326536179781772051955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24845551024119854514701303 37268326536179781772051955)
      ·
        refine ⟨55902489804269672658077933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37268326536179781772051955 55902489804269672658077933)
        ·
          refine ⟨20963433676601127246779225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55902489804269672658077933 20963433676601127246779225)
          ·
            refine ⟨15722575257450845435084419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20963433676601127246779225 15722575257450845435084419)
            ·
              refine ⟨23583862886176268152626629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15722575257450845435084419 23583862886176268152626629)
              ·
                refine ⟨4421974291158050278617493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23583862886176268152626629 4421974291158050278617493)
                ·
                  refine ⟨207280044898033606810195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4421974291158050278617493 207280044898033606810195)
                  ·
                    rfl

theorem cell21_908272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_908272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908272 prefixEnd_908272 := by exact prefixLift 908272
  have htrace : WordTrace (prefixWord ++ tailWord_908272) baseStart_908272 baseEnd_908272 := by
    simpa [prefixWord, tailWord_908272, baseEnd_908272] using wordTrace_append hprefix tailTrace_908272
  have hstable : (prefixWord ++ tailWord_908272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908272).length < 2 ^ (prefixWord ++ tailWord_908272).sum := by decide
  have hdescent : baseEnd_908272 < baseStart_908272 := by decide
  rcases family_descends (prefixWord ++ tailWord_908272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908289 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 6]
def baseStart_908289 : Nat := 118140960795 + 908289 * 2 ^ 59
def prefixEnd_908289 : Nat := 4983230072969 + 3 ^ 40 * 908289 * 2
def baseEnd_908289 : Nat := 207283924529645355026827

theorem tailTrace_908289 : CollatzResearch.WordTrace tailWord_908289 prefixEnd_908289 207283924529645355026827 := by
  unfold tailWord_908289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33128021406431551256303921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22085347604287700837535947 33128021406431551256303921)
  ·
    refine ⟨24846016054823663442227941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33128021406431551256303921 24846016054823663442227941)
    ·
      refine ⟨4658628010279436895417739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24846016054823663442227941 4658628010279436895417739)
      ·
        refine ⟨6987942015419155343126609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4658628010279436895417739 6987942015419155343126609)
        ·
          refine ⟨5240956511564366507344957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6987942015419155343126609 5240956511564366507344957)
          ·
            refine ⟨1965358691836637440254359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5240956511564366507344957 1965358691836637440254359)
            ·
              refine ⟨2948038037754956160381539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965358691836637440254359 2948038037754956160381539)
              ·
                refine ⟨4422057056632434240572309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948038037754956160381539 4422057056632434240572309)
                ·
                  refine ⟨207283924529645355026827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4422057056632434240572309 207283924529645355026827)
                  ·
                    rfl

theorem cell21_908289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_908289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908289 prefixEnd_908289 := by exact prefixLift 908289
  have htrace : WordTrace (prefixWord ++ tailWord_908289) baseStart_908289 baseEnd_908289 := by
    simpa [prefixWord, tailWord_908289, baseEnd_908289] using wordTrace_append hprefix tailTrace_908289
  have hstable : (prefixWord ++ tailWord_908289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908289).length < 2 ^ (prefixWord ++ tailWord_908289).sum := by decide
  have hdescent : baseEnd_908289 < baseStart_908289 := by decide
  rcases family_descends (prefixWord ++ tailWord_908289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908444 : List Nat := [2, 2, 3, 2, 1, 3, 2, 3, 3]
def baseStart_908444 : Nat := 118140960795 + 908444 * 2 ^ 59
def prefixEnd_908444 : Nat := 4983230072969 + 3 ^ 40 * 908444 * 2
def baseEnd_908444 : Nat := 207319297641399529943177

theorem tailTrace_908444 : CollatzResearch.WordTrace tailWord_908444 prefixEnd_908444 207319297641399529943177 := by
  unfold tailWord_908444
  simp only [CollatzResearch.WordTrace]
  refine ⟨16566837360435006364098193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22089116480580008485464257 16566837360435006364098193)
  ·
    refine ⟨12425128020326254773073645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16566837360435006364098193 12425128020326254773073645)
    ·
      refine ⟨4659423007622345539902617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12425128020326254773073645 4659423007622345539902617)
      ·
        refine ⟨3494567255716759154926963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4659423007622345539902617 3494567255716759154926963)
        ·
          refine ⟨5241850883575138732390445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494567255716759154926963 5241850883575138732390445)
          ·
            refine ⟨1965694081340677024646417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5241850883575138732390445 1965694081340677024646417)
            ·
              refine ⟨1474270561005507768484813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965694081340677024646417 1474270561005507768484813)
              ·
                refine ⟨552851460377065413181805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474270561005507768484813 552851460377065413181805)
                ·
                  refine ⟨207319297641399529943177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552851460377065413181805 207319297641399529943177)
                  ·
                    rfl

theorem cell21_908444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_908444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908444 prefixEnd_908444 := by exact prefixLift 908444
  have htrace : WordTrace (prefixWord ++ tailWord_908444) baseStart_908444 baseEnd_908444 := by
    simpa [prefixWord, tailWord_908444, baseEnd_908444] using wordTrace_append hprefix tailTrace_908444
  have hstable : (prefixWord ++ tailWord_908444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908444).length < 2 ^ (prefixWord ++ tailWord_908444).sum := by decide
  have hdescent : baseEnd_908444 < baseStart_908444 := by decide
  rcases family_descends (prefixWord ++ tailWord_908444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908458 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 6]
def baseStart_908458 : Nat := 118140960795 + 908458 * 2 ^ 59
def prefixEnd_908458 : Nat := 4983230072969 + 3 ^ 40 * 908458 * 2
def baseEnd_908458 : Nat := 207322492632138616709815

theorem tailTrace_908458 : CollatzResearch.WordTrace tailWord_908458 prefixEnd_908458 207322492632138616709815 := by
  unfold tailWord_908458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8283546335704823279801507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22089456895212862079470685 8283546335704823279801507)
  ·
    refine ⟨12425319503557234919702261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8283546335704823279801507 12425319503557234919702261)
    ·
      refine ⟨1164873703458490773722087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12425319503557234919702261 1164873703458490773722087)
      ·
        refine ⟨1747310555187736160583131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164873703458490773722087 1747310555187736160583131)
        ·
          refine ⟨2620965832781604240874697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747310555187736160583131 2620965832781604240874697)
          ·
            refine ⟨1965724374586203180656023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620965832781604240874697 1965724374586203180656023)
            ·
              refine ⟨2948586561879304770984035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965724374586203180656023 2948586561879304770984035)
              ·
                refine ⟨4422879842818957156476053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2948586561879304770984035 4422879842818957156476053)
                ·
                  refine ⟨207322492632138616709815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4422879842818957156476053 207322492632138616709815)
                  ·
                    rfl

theorem cell21_908458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 6].length) (baseStart_908458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908458 prefixEnd_908458 := by exact prefixLift 908458
  have htrace : WordTrace (prefixWord ++ tailWord_908458) baseStart_908458 baseEnd_908458 := by
    simpa [prefixWord, tailWord_908458, baseEnd_908458] using wordTrace_append hprefix tailTrace_908458
  have hstable : (prefixWord ++ tailWord_908458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908458).length < 2 ^ (prefixWord ++ tailWord_908458).sum := by decide
  have hdescent : baseEnd_908458 < baseStart_908458 := by decide
  rcases family_descends (prefixWord ++ tailWord_908458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908503 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 3]
def baseStart_908503 : Nat := 118140960795 + 908503 * 2 ^ 59
def prefixEnd_908503 : Nat := 4983230072969 + 3 ^ 40 * 908503 * 2
def baseEnd_908503 : Nat := 207332762245228538459723

theorem tailTrace_908503 : CollatzResearch.WordTrace tailWord_908503 prefixEnd_908503 207332762245228538459723 := by
  unfold tailWord_908503
  simp only [CollatzResearch.WordTrace]
  refine ⟨33135826627656265804594163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22090551085104177203062775 33135826627656265804594163)
  ·
    refine ⟨49703739941484398706891245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33135826627656265804594163 49703739941484398706891245)
    ·
      refine ⟨18638902478056649515084217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49703739941484398706891245 18638902478056649515084217)
      ·
        refine ⟨13979176858542487136313163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18638902478056649515084217 13979176858542487136313163)
        ·
          refine ⟨20968765287813730704469745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13979176858542487136313163 20968765287813730704469745)
          ·
            refine ⟨15726573965860298028352309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20968765287813730704469745 15726573965860298028352309)
            ·
              refine ⟨1474366309299402940158029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15726573965860298028352309 1474366309299402940158029)
              ·
                refine ⟨552887365987276102559261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474366309299402940158029 552887365987276102559261)
                ·
                  refine ⟨207332762245228538459723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552887365987276102559261 207332762245228538459723)
                  ·
                    rfl

theorem cell21_908503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 3].length) (baseStart_908503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908503 prefixEnd_908503 := by exact prefixLift 908503
  have htrace : WordTrace (prefixWord ++ tailWord_908503) baseStart_908503 baseEnd_908503 := by
    simpa [prefixWord, tailWord_908503, baseEnd_908503] using wordTrace_append hprefix tailTrace_908503
  have hstable : (prefixWord ++ tailWord_908503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908503).length < 2 ^ (prefixWord ++ tailWord_908503).sum := by decide
  have hdescent : baseEnd_908503 < baseStart_908503 := by decide
  rcases family_descends (prefixWord ++ tailWord_908503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908520 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 3]
def baseStart_908520 : Nat := 118140960795 + 908520 * 2 ^ 59
def prefixEnd_908520 : Nat := 4983230072969 + 3 ^ 40 * 908520 * 2
def baseEnd_908520 : Nat := 207336641876840286676355

theorem tailTrace_908520 : CollatzResearch.WordTrace tailWord_908520 prefixEnd_908520 207336641876840286676355 := by
  unfold tailWord_908520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568223334297338853981507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22090964445729785138642009 16568223334297338853981507)
  ·
    refine ⟨24852335001446008280972261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16568223334297338853981507 24852335001446008280972261)
    ·
      refine ⟨4659812812771126552682299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24852335001446008280972261 4659812812771126552682299)
      ·
        refine ⟨6989719219156689829023449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659812812771126552682299 6989719219156689829023449)
        ·
          refine ⟨5242289414367517371767587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6989719219156689829023449 5242289414367517371767587)
          ·
            refine ⟨7863434121551276057651381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5242289414367517371767587 7863434121551276057651381)
            ·
              refine ⟨737196948895432130404817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7863434121551276057651381 737196948895432130404817)
              ·
                refine ⟨552897711671574097803613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737196948895432130404817 552897711671574097803613)
                ·
                  refine ⟨207336641876840286676355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552897711671574097803613 207336641876840286676355)
                  ·
                    rfl

theorem cell21_908520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_908520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908520 prefixEnd_908520 := by exact prefixLift 908520
  have htrace : WordTrace (prefixWord ++ tailWord_908520) baseStart_908520 baseEnd_908520 := by
    simpa [prefixWord, tailWord_908520, baseEnd_908520] using wordTrace_append hprefix tailTrace_908520
  have hstable : (prefixWord ++ tailWord_908520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908520).length < 2 ^ (prefixWord ++ tailWord_908520).sum := by decide
  have hdescent : baseEnd_908520 < baseStart_908520 := by decide
  rcases family_descends (prefixWord ++ tailWord_908520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908531 : List Nat := [1, 1, 1, 2, 2, 6, 2, 6]
def baseStart_908531 : Nat := 118140960795 + 908531 * 2 ^ 59
def prefixEnd_908531 : Nat := 4983230072969 + 3 ^ 40 * 908531 * 2
def baseEnd_908531 : Nat := 69113050742235570664333

theorem tailTrace_908531 : CollatzResearch.WordTrace tailWord_908531 prefixEnd_908531 69113050742235570664333 := by
  unfold tailWord_908531
  simp only [CollatzResearch.WordTrace]
  refine ⟨33136847871554826586613447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22091231914369884391075631 33136847871554826586613447)
  ·
    refine ⟨49705271807332239879920171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33136847871554826586613447 49705271807332239879920171)
    ·
      refine ⟨74557907710998359819880257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49705271807332239879920171 74557907710998359819880257)
      ·
        refine ⟨55918430783248769864910193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74557907710998359819880257 55918430783248769864910193)
        ·
          refine ⟨41938823087436577398682645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55918430783248769864910193 41938823087436577398682645)
          ·
            refine ⟨1965882332223589565563249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41938823087436577398682645 1965882332223589565563249)
            ·
              refine ⟨1474411749167692174172437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965882332223589565563249 1474411749167692174172437)
              ·
                refine ⟨69113050742235570664333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1474411749167692174172437 69113050742235570664333)
                ·
                  rfl

theorem cell21_908531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_908531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908531 prefixEnd_908531 := by exact prefixLift 908531
  have htrace : WordTrace (prefixWord ++ tailWord_908531) baseStart_908531 baseEnd_908531 := by
    simpa [prefixWord, tailWord_908531, baseEnd_908531] using wordTrace_append hprefix tailTrace_908531
  have hstable : (prefixWord ++ tailWord_908531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908531).length < 2 ^ (prefixWord ++ tailWord_908531).sum := by decide
  have hdescent : baseEnd_908531 < baseStart_908531 := by decide
  rcases family_descends (prefixWord ++ tailWord_908531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908579 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 3]
def baseStart_908579 : Nat := 118140960795 + 908579 * 2 ^ 59
def prefixEnd_908579 : Nat := 4983230072969 + 3 ^ 40 * 908579 * 2
def baseEnd_908579 : Nat := 207350106480669295192901

theorem tailTrace_908579 : CollatzResearch.WordTrace tailWord_908579 prefixEnd_908579 207350106480669295192901 := by
  unfold tailWord_908579
  simp only [CollatzResearch.WordTrace]
  refine ⟨33138598575380930784360791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22092399050253953856240527 33138598575380930784360791)
  ·
    refine ⟨49707897863071396176541187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33138598575380930784360791 49707897863071396176541187)
    ·
      refine ⟨74561846794607094264811781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49707897863071396176541187 74561846794607094264811781)
      ·
        refine ⟨13980346273988830174652209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74561846794607094264811781 13980346273988830174652209)
        ·
          refine ⟨10485259705491622630989157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13980346273988830174652209 10485259705491622630989157)
          ·
            refine ⟨1965986194779679243310467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10485259705491622630989157 1965986194779679243310467)
            ·
              refine ⟨2948979292169518864965701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965986194779679243310467 2948979292169518864965701)
              ·
                refine ⟨552933617281784787181069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2948979292169518864965701 552933617281784787181069)
                ·
                  refine ⟨207350106480669295192901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 552933617281784787181069 207350106480669295192901)
                  ·
                    rfl

theorem cell21_908579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 3].length) (baseStart_908579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908579 prefixEnd_908579 := by exact prefixLift 908579
  have htrace : WordTrace (prefixWord ++ tailWord_908579) baseStart_908579 baseEnd_908579 := by
    simpa [prefixWord, tailWord_908579, baseEnd_908579] using wordTrace_append hprefix tailTrace_908579
  have hstable : (prefixWord ++ tailWord_908579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908579).length < 2 ^ (prefixWord ++ tailWord_908579).sum := by decide
  have hdescent : baseEnd_908579 < baseStart_908579 := by decide
  rcases family_descends (prefixWord ++ tailWord_908579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908593 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 4]
def baseStart_908593 : Nat := 118140960795 + 908593 * 2 ^ 59
def prefixEnd_908593 : Nat := 4983230072969 + 3 ^ 40 * 908593 * 2
def baseEnd_908593 : Nat := 207353301471408381959539

theorem tailTrace_908593 : CollatzResearch.WordTrace tailWord_908593 prefixEnd_908593 207353301471408381959539 := by
  unfold tailWord_908593
  simp only [CollatzResearch.WordTrace]
  refine ⟨33139109197330211175370433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22092739464886807450246955 33139109197330211175370433)
  ·
    refine ⟨24854331897997658381527825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33139109197330211175370433 24854331897997658381527825)
    ·
      refine ⟨18640748923498243786145869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24854331897997658381527825 18640748923498243786145869)
      ·
        refine ⟨6990280846311841419804701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18640748923498243786145869 6990280846311841419804701)
        ·
          refine ⟨2621355317366940532426763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6990280846311841419804701 2621355317366940532426763)
          ·
            refine ⟨3932032976050410798640145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621355317366940532426763 3932032976050410798640145)
            ·
              refine ⟨2949024732037808098980109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932032976050410798640145 2949024732037808098980109)
              ·
                refine ⟨1105884274514178037117541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2949024732037808098980109 1105884274514178037117541)
                ·
                  refine ⟨207353301471408381959539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1105884274514178037117541 207353301471408381959539)
                  ·
                    rfl

theorem cell21_908593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_908593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908593 prefixEnd_908593 := by exact prefixLift 908593
  have htrace : WordTrace (prefixWord ++ tailWord_908593) baseStart_908593 baseEnd_908593 := by
    simpa [prefixWord, tailWord_908593, baseEnd_908593] using wordTrace_append hprefix tailTrace_908593
  have hstable : (prefixWord ++ tailWord_908593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908593).length < 2 ^ (prefixWord ++ tailWord_908593).sum := by decide
  have hdescent : baseEnd_908593 < baseStart_908593 := by decide
  rcases family_descends (prefixWord ++ tailWord_908593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908630 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_908630 : Nat := 118140960795 + 908630 * 2 ^ 59
def prefixEnd_908630 : Nat := 4983230072969 + 3 ^ 40 * 908630 * 2
def baseEnd_908630 : Nat := 207361745375504539842797

theorem tailTrace_908630 : CollatzResearch.WordTrace tailWord_908630 prefixEnd_908630 207361745375504539842797 := by
  unfold tailWord_908630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071278668637260405904209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22093639132130777662978229 2071278668637260405904209)
  ·
    refine ⟨1553459001477945304428157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2071278668637260405904209 1553459001477945304428157)
    ·
      refine ⟨582547125554229489160559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1553459001477945304428157 582547125554229489160559)
      ·
        refine ⟨873820688331344233740839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582547125554229489160559 873820688331344233740839)
        ·
          refine ⟨1310731032497016350611259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873820688331344233740839 1310731032497016350611259)
          ·
            refine ⟨1966096548745524525916889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310731032497016350611259 1966096548745524525916889)
            ·
              refine ⟨1474572411559143394437667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1966096548745524525916889 1474572411559143394437667)
              ·
                refine ⟨2211858617338715091656501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474572411559143394437667 2211858617338715091656501)
                ·
                  refine ⟨207361745375504539842797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2211858617338715091656501 207361745375504539842797)
                  ·
                    rfl

theorem cell21_908630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_908630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908630 prefixEnd_908630 := by exact prefixLift 908630
  have htrace : WordTrace (prefixWord ++ tailWord_908630) baseStart_908630 baseEnd_908630 := by
    simpa [prefixWord, tailWord_908630, baseEnd_908630] using wordTrace_append hprefix tailTrace_908630
  have hstable : (prefixWord ++ tailWord_908630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908630).length < 2 ^ (prefixWord ++ tailWord_908630).sum := by decide
  have hdescent : baseEnd_908630 < baseStart_908630 := by decide
  rcases family_descends (prefixWord ++ tailWord_908630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908666 : List Nat := [3, 1, 1, 1, 1, 1, 2, 11]
def baseStart_908666 : Nat := 118140960795 + 908666 * 2 ^ 59
def prefixEnd_908666 : Nat := 4983230072969 + 3 ^ 40 * 908666 * 2
def baseEnd_908666 : Nat := 69123320355325492414241

theorem tailTrace_908666 : CollatzResearch.WordTrace tailWord_908666 prefixEnd_908666 69123320355325492414241 := by
  unfold tailWord_908666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8285442931516436160694463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22094514484043829761851901 8285442931516436160694463)
  ·
    refine ⟨12428164397274654241041695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8285442931516436160694463 12428164397274654241041695)
    ·
      refine ⟨18642246595911981361562543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12428164397274654241041695 18642246595911981361562543)
      ·
        refine ⟨27963369893867972042343815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18642246595911981361562543 27963369893867972042343815)
        ·
          refine ⟨41945054840801958063515723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27963369893867972042343815 41945054840801958063515723)
          ·
            refine ⟨62917582261202937095273585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41945054840801958063515723 62917582261202937095273585)
            ·
              refine ⟨47188186695902202821455189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62917582261202937095273585 47188186695902202821455189)
              ·
                refine ⟨69123320355325492414241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 47188186695902202821455189 69123320355325492414241)
                ·
                  rfl

theorem cell21_908666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_908666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908666 prefixEnd_908666 := by exact prefixLift 908666
  have htrace : WordTrace (prefixWord ++ tailWord_908666) baseStart_908666 baseEnd_908666 := by
    simpa [prefixWord, tailWord_908666, baseEnd_908666] using wordTrace_append hprefix tailTrace_908666
  have hstable : (prefixWord ++ tailWord_908666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908666).length < 2 ^ (prefixWord ++ tailWord_908666).sum := by decide
  have hdescent : baseEnd_908666 < baseStart_908666 := by decide
  rcases family_descends (prefixWord ++ tailWord_908666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908748 : List Nat := [2, 2, 1, 4, 2, 1, 4, 2, 3]
def baseStart_908748 : Nat := 118140960795 + 908748 * 2 ^ 59
def prefixEnd_908748 : Nat := 4983230072969 + 3 ^ 40 * 908748 * 2
def baseEnd_908748 : Nat := 207388674583162556875889

theorem tailTrace_908748 : CollatzResearch.WordTrace tailWord_908748 prefixEnd_908748 207388674583162556875889 := by
  unfold tailWord_908748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16572381255884336323631449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22096508341179115098175265 16572381255884336323631449)
  ·
    refine ⟨12429285941913252242723587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16572381255884336323631449 12429285941913252242723587)
    ·
      refine ⟨18643928912869878364085381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12429285941913252242723587 18643928912869878364085381)
      ·
        refine ⟨3495736671163102193266009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18643928912869878364085381 3495736671163102193266009)
        ·
          refine ⟨2621802503372326644949507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495736671163102193266009 2621802503372326644949507)
          ·
            refine ⟨3932703755058489967424261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621802503372326644949507 3932703755058489967424261)
            ·
              refine ⟨737381954073466868892049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3932703755058489967424261 737381954073466868892049)
              ·
                refine ⟨553036465555100151669037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737381954073466868892049 553036465555100151669037)
                ·
                  refine ⟨207388674583162556875889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553036465555100151669037 207388674583162556875889)
                  ·
                    rfl

theorem cell21_908748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_908748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908748 prefixEnd_908748 := by exact prefixLift 908748
  have htrace : WordTrace (prefixWord ++ tailWord_908748) baseStart_908748 baseEnd_908748 := by
    simpa [prefixWord, tailWord_908748, baseEnd_908748] using wordTrace_append hprefix tailTrace_908748
  have hstable : (prefixWord ++ tailWord_908748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908748).length < 2 ^ (prefixWord ++ tailWord_908748).sum := by decide
  have hdescent : baseEnd_908748 < baseStart_908748 := by decide
  rcases family_descends (prefixWord ++ tailWord_908748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908807 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 3]
def baseStart_908807 : Nat := 118140960795 + 908807 * 2 ^ 59
def prefixEnd_908807 : Nat := 4983230072969 + 3 ^ 40 * 908807 * 2
def baseEnd_908807 : Nat := 207402139186991565392435

theorem tailTrace_908807 : CollatzResearch.WordTrace tailWord_908807 prefixEnd_908807 207402139186991565392435 := by
  unfold tailWord_908807
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146914418554925723660675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22097942945703283815773783 33146914418554925723660675)
  ·
    refine ⟨49720371627832388585491013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33146914418554925723660675 49720371627832388585491013)
    ·
      refine ⟨9322569680218572859779565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49720371627832388585491013 9322569680218572859779565)
      ·
        refine ⟨3495963630081964822417337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9322569680218572859779565 3495963630081964822417337)
        ·
          refine ⟨2621972722561473616813003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495963630081964822417337 2621972722561473616813003)
          ·
            refine ⟨3932959083842210425219505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621972722561473616813003 3932959083842210425219505)
            ·
              refine ⟨2949719312881657818914629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3932959083842210425219505 2949719312881657818914629)
              ·
                refine ⟨553072371165310841046493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2949719312881657818914629 553072371165310841046493)
                ·
                  refine ⟨207402139186991565392435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553072371165310841046493 207402139186991565392435)
                  ·
                    rfl

theorem cell21_908807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 3].length) (baseStart_908807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908807 prefixEnd_908807 := by exact prefixLift 908807
  have htrace : WordTrace (prefixWord ++ tailWord_908807) baseStart_908807 baseEnd_908807 := by
    simpa [prefixWord, tailWord_908807, baseEnd_908807] using wordTrace_append hprefix tailTrace_908807
  have hstable : (prefixWord ++ tailWord_908807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908807).length < 2 ^ (prefixWord ++ tailWord_908807).sum := by decide
  have hdescent : baseEnd_908807 < baseStart_908807 := by decide
  rcases family_descends (prefixWord ++ tailWord_908807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908835 : List Nat := [1, 1, 1, 4, 5, 1, 1, 7]
def baseStart_908835 : Nat := 118140960795 + 908835 * 2 ^ 59
def prefixEnd_908835 : Nat := 4983230072969 + 3 ^ 40 * 908835 * 2
def baseEnd_908835 : Nat := 69136176389489912975237

theorem tailTrace_908835 : CollatzResearch.WordTrace tailWord_908835 prefixEnd_908835 69136176389489912975237 := by
  unfold tailWord_908835
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147935662453486505679959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22098623774968991003786639 33147935662453486505679959)
  ·
    refine ⟨49721903493680229758519939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33147935662453486505679959 49721903493680229758519939)
    ·
      refine ⟨74582855240520344637779909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49721903493680229758519939 74582855240520344637779909)
      ·
        refine ⟨13984285357597564619583733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74582855240520344637779909 13984285357597564619583733)
        ·
          refine ⟨1311026752274771683085975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13984285357597564619583733 1311026752274771683085975)
          ·
            refine ⟨1966540128412157524628963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311026752274771683085975 1966540128412157524628963)
            ·
              refine ⟨2949810192618236286943445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966540128412157524628963 2949810192618236286943445)
              ·
                refine ⟨69136176389489912975237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2949810192618236286943445 69136176389489912975237)
                ·
                  rfl

theorem cell21_908835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_908835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908835 prefixEnd_908835 := by exact prefixLift 908835
  have htrace : WordTrace (prefixWord ++ tailWord_908835) baseStart_908835 baseEnd_908835 := by
    simpa [prefixWord, tailWord_908835, baseEnd_908835] using wordTrace_append hprefix tailTrace_908835
  have hstable : (prefixWord ++ tailWord_908835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908835).length < 2 ^ (prefixWord ++ tailWord_908835).sum := by decide
  have hdescent : baseEnd_908835 < baseStart_908835 := by decide
  rcases family_descends (prefixWord ++ tailWord_908835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908880 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_908880 : Nat := 118140960795 + 908880 * 2 ^ 59
def prefixEnd_908880 : Nat := 4983230072969 + 3 ^ 40 * 908880 * 2
def baseEnd_908880 : Nat := 207418798781559660675619

theorem tailTrace_908880 : CollatzResearch.WordTrace tailWord_908880 prefixEnd_908880 207418798781559660675619 := by
  unfold tailWord_908880
  simp only [CollatzResearch.WordTrace]
  refine ⟨16574788473645229595534047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22099717964860306127378729 16574788473645229595534047)
  ·
    refine ⟨24862182710467844393301071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16574788473645229595534047 24862182710467844393301071)
    ·
      refine ⟨37293274065701766589951607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24862182710467844393301071 37293274065701766589951607)
      ·
        refine ⟨55939911098552649884927411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37293274065701766589951607 55939911098552649884927411)
        ·
          refine ⟨83909866647828974827391117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55939911098552649884927411 83909866647828974827391117)
          ·
            refine ⟨31466199992935865560271669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83909866647828974827391117 31466199992935865560271669)
            ·
              refine ⟨2949956249337737396275469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31466199992935865560271669 2949956249337737396275469)
              ·
                refine ⟨1106233593501651523603301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2949956249337737396275469 1106233593501651523603301)
                ·
                  refine ⟨207418798781559660675619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106233593501651523603301 207418798781559660675619)
                  ·
                    rfl

theorem cell21_908880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_908880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908880 prefixEnd_908880 := by exact prefixLift 908880
  have htrace : WordTrace (prefixWord ++ tailWord_908880) baseStart_908880 baseEnd_908880 := by
    simpa [prefixWord, tailWord_908880, baseEnd_908880] using wordTrace_append hprefix tailTrace_908880
  have hstable : (prefixWord ++ tailWord_908880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908880).length < 2 ^ (prefixWord ++ tailWord_908880).sum := by decide
  have hdescent : baseEnd_908880 < baseStart_908880 := by decide
  rcases family_descends (prefixWord ++ tailWord_908880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908917 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 3]
def baseStart_908917 : Nat := 118140960795 + 908917 * 2 ^ 59
def prefixEnd_908917 : Nat := 4983230072969 + 3 ^ 40 * 908917 * 2
def baseEnd_908917 : Nat := 207427242685655818558877

theorem tailTrace_908917 : CollatzResearch.WordTrace tailWord_908917 prefixEnd_908917 207427242685655818558877 := by
  unfold tailWord_908917
  simp only [CollatzResearch.WordTrace]
  refine ⟨33150926448156414510165005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22100617632104276340110003 33150926448156414510165005)
  ·
    refine ⟨12431597418058655441311877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33150926448156414510165005 12431597418058655441311877)
    ·
      refine ⟨2330924515885997895245977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12431597418058655441311877 2330924515885997895245977)
      ·
        refine ⟨1748193386914498421434483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330924515885997895245977 1748193386914498421434483)
        ·
          refine ⟨2622290080371747632151725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748193386914498421434483 2622290080371747632151725)
          ·
            refine ⟨983358780139405362056897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2622290080371747632151725 983358780139405362056897)
            ·
              refine ⟨737519085104554021542673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983358780139405362056897 737519085104554021542673)
              ·
                refine ⟨553139313828415516157005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737519085104554021542673 553139313828415516157005)
                ·
                  refine ⟨207427242685655818558877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 553139313828415516157005 207427242685655818558877)
                  ·
                    rfl

theorem cell21_908917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 3].length) (baseStart_908917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908917 prefixEnd_908917 := by exact prefixLift 908917
  have htrace : WordTrace (prefixWord ++ tailWord_908917) baseStart_908917 baseEnd_908917 := by
    simpa [prefixWord, tailWord_908917, baseEnd_908917] using wordTrace_append hprefix tailTrace_908917
  have hstable : (prefixWord ++ tailWord_908917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908917).length < 2 ^ (prefixWord ++ tailWord_908917).sum := by decide
  have hdescent : baseEnd_908917 < baseStart_908917 := by decide
  rcases family_descends (prefixWord ++ tailWord_908917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908942 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_908942 : Nat := 118140960795 + 908942 * 2 ^ 59
def prefixEnd_908942 : Nat := 4983230072969 + 3 ^ 40 * 908942 * 2
def baseEnd_908942 : Nat := 207432948026261330642159

theorem tailTrace_908942 : CollatzResearch.WordTrace tailWord_908942 prefixEnd_908942 207432948026261330642159 := by
  unfold tailWord_908942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143979784133230472478135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22101225515377229186550053 4143979784133230472478135)
  ·
    refine ⟨6215969676199845708717203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4143979784133230472478135 6215969676199845708717203)
    ·
      refine ⟨9323954514299768563075805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6215969676199845708717203 9323954514299768563075805)
      ·
        refine ⟨3496482942862413211153427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9323954514299768563075805 3496482942862413211153427)
        ·
          refine ⟨5244724414293619816730141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496482942862413211153427 5244724414293619816730141)
          ·
            refine ⟨1966771655360107431273803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5244724414293619816730141 1966771655360107431273803)
            ·
              refine ⟨2950157483040161146910705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966771655360107431273803 2950157483040161146910705)
              ·
                refine ⟨2212618112280120860183029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2950157483040161146910705 2212618112280120860183029)
                ·
                  refine ⟨207432948026261330642159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2212618112280120860183029 207432948026261330642159)
                  ·
                    rfl

theorem cell21_908942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_908942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908942 prefixEnd_908942 := by exact prefixLift 908942
  have htrace : WordTrace (prefixWord ++ tailWord_908942) baseStart_908942 baseEnd_908942 := by
    simpa [prefixWord, tailWord_908942, baseEnd_908942] using wordTrace_append hprefix tailTrace_908942
  have hstable : (prefixWord ++ tailWord_908942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908942).length < 2 ^ (prefixWord ++ tailWord_908942).sum := by decide
  have hdescent : baseEnd_908942 < baseStart_908942 := by decide
  rcases family_descends (prefixWord ++ tailWord_908942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908990 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_908990 : Nat := 118140960795 + 908990 * 2 ^ 59
def prefixEnd_908990 : Nat := 4983230072969 + 3 ^ 40 * 908990 * 2
def baseEnd_908990 : Nat := 207443902280223913842061

theorem tailTrace_908990 : CollatzResearch.WordTrace tailWord_908990 prefixEnd_908990 207443902280223913842061 := by
  unfold tailWord_908990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4144198622111493497196553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22102392651261298651714949 4144198622111493497196553)
  ·
    refine ⟨3108148966583620122897415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4144198622111493497196553 3108148966583620122897415)
    ·
      refine ⟨4662223449875430184346123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108148966583620122897415 4662223449875430184346123)
      ·
        refine ⟨6993335174813145276519185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662223449875430184346123 6993335174813145276519185)
        ·
          refine ⟨5245001381109858957389389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6993335174813145276519185 5245001381109858957389389)
          ·
            refine ⟨1966875517916197109021021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5245001381109858957389389 1966875517916197109021021)
            ·
              refine ⟨737578319218573915882883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1966875517916197109021021 737578319218573915882883)
              ·
                refine ⟨1106367478827860873824325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737578319218573915882883 1106367478827860873824325)
                ·
                  refine ⟨207443902280223913842061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1106367478827860873824325 207443902280223913842061)
                  ·
                    rfl

theorem cell21_908990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_908990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_908990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_908990 prefixEnd_908990 := by exact prefixLift 908990
  have htrace : WordTrace (prefixWord ++ tailWord_908990) baseStart_908990 baseEnd_908990 := by
    simpa [prefixWord, tailWord_908990, baseEnd_908990] using wordTrace_append hprefix tailTrace_908990
  have hstable : (prefixWord ++ tailWord_908990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908990).length < 2 ^ (prefixWord ++ tailWord_908990).sum := by decide
  have hdescent : baseEnd_908990 < baseStart_908990 := by decide
  rcases family_descends (prefixWord ++ tailWord_908990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909015 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_909015 : Nat := 118140960795 + 909015 * 2 ^ 59
def prefixEnd_909015 : Nat := 4983230072969 + 3 ^ 40 * 909015 * 2
def baseEnd_909015 : Nat := 207449607620829425925343

theorem tailTrace_909015 : CollatzResearch.WordTrace tailWord_909015 prefixEnd_909015 207449607620829425925343 := by
  unfold tailWord_909015
  simp only [CollatzResearch.WordTrace]
  refine ⟨33154500801801377247232499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22103000534534251498154999 33154500801801377247232499)
  ·
    refine ⟨49731751202702065870848749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33154500801801377247232499 49731751202702065870848749)
    ·
      refine ⟨18649406701013274701568281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49731751202702065870848749 18649406701013274701568281)
      ·
        refine ⟨13987055025759956026176211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18649406701013274701568281 13987055025759956026176211)
        ·
          refine ⟨20980582538639934039264317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13987055025759956026176211 20980582538639934039264317)
          ·
            refine ⟨7867718451989975264724119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20980582538639934039264317 7867718451989975264724119)
            ·
              refine ⟨11801577677984962897086179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7867718451989975264724119 11801577677984962897086179)
              ·
                refine ⟨17702366516977444345629269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11801577677984962897086179 17702366516977444345629269)
                ·
                  refine ⟨207449607620829425925343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17702366516977444345629269 207449607620829425925343)
                  ·
                    rfl

theorem cell21_909015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_909015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909015 prefixEnd_909015 := by exact prefixLift 909015
  have htrace : WordTrace (prefixWord ++ tailWord_909015) baseStart_909015 baseEnd_909015 := by
    simpa [prefixWord, tailWord_909015, baseEnd_909015] using wordTrace_append hprefix tailTrace_909015
  have hstable : (prefixWord ++ tailWord_909015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909015).length < 2 ^ (prefixWord ++ tailWord_909015).sum := by decide
  have hdescent : baseEnd_909015 < baseStart_909015 := by decide
  rcases family_descends (prefixWord ++ tailWord_909015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909021 : List Nat := [1, 4, 3, 3, 2, 1, 7]
def baseStart_909021 : Nat := 118140960795 + 909021 * 2 ^ 59
def prefixEnd_909021 : Nat := 4983230072969 + 3 ^ 40 * 909021 * 2
def baseEnd_909021 : Nat := 23050108544730527647259

theorem tailTrace_909021 : CollatzResearch.WordTrace tailWord_909021 prefixEnd_909021 23050108544730527647259 := by
  unfold tailWord_909021
  simp only [CollatzResearch.WordTrace]
  refine ⟨33154719639779640271950917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22103146426519760181300611 33154719639779640271950917)
  ·
    refine ⟨6216509932458682550990797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33154719639779640271950917 6216509932458682550990797)
    ·
      refine ⟨2331191224672005956621549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6216509932458682550990797 2331191224672005956621549)
      ·
        refine ⟨874196709252002233733081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2331191224672005956621549 874196709252002233733081)
        ·
          refine ⟨655647531939001675299811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874196709252002233733081 655647531939001675299811)
          ·
            refine ⟨983471297908502512949717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655647531939001675299811 983471297908502512949717)
            ·
              refine ⟨23050108544730527647259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 983471297908502512949717 23050108544730527647259)
              ·
                rfl

theorem cell21_909021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 7].length) (baseStart_909021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909021 prefixEnd_909021 := by exact prefixLift 909021
  have htrace : WordTrace (prefixWord ++ tailWord_909021) baseStart_909021 baseEnd_909021 := by
    simpa [prefixWord, tailWord_909021, baseEnd_909021] using wordTrace_append hprefix tailTrace_909021
  have hstable : (prefixWord ++ tailWord_909021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909021).length < 2 ^ (prefixWord ++ tailWord_909021).sum := by decide
  have hdescent : baseEnd_909021 < baseStart_909021 := by decide
  rcases family_descends (prefixWord ++ tailWord_909021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909032 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_909032 : Nat := 118140960795 + 909032 * 2 ^ 59
def prefixEnd_909032 : Nat := 4983230072969 + 3 ^ 40 * 909032 * 2
def baseEnd_909032 : Nat := 207453487252441174141975

theorem tailTrace_909032 : CollatzResearch.WordTrace tailWord_909032 prefixEnd_909032 207453487252441174141975 := by
  unfold tailWord_909032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16577560421369894575300675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22103413895159859433734233 16577560421369894575300675)
  ·
    refine ⟨24866340632054841862951013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16577560421369894575300675 24866340632054841862951013)
    ·
      refine ⟨4662438868510282849303315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24866340632054841862951013 4662438868510282849303315)
      ·
        refine ⟨6993658302765424273954973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4662438868510282849303315 6993658302765424273954973)
        ·
          refine ⟨2622621863537034102733115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6993658302765424273954973 2622621863537034102733115)
          ·
            refine ⟨3933932795305551154099673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622621863537034102733115 3933932795305551154099673)
            ·
              refine ⟨2950449596479163365574755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933932795305551154099673 2950449596479163365574755)
              ·
                refine ⟨4425674394718745048362133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2950449596479163365574755 4425674394718745048362133)
                ·
                  refine ⟨207453487252441174141975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4425674394718745048362133 207453487252441174141975)
                  ·
                    rfl

theorem cell21_909032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_909032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_909032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_909032 prefixEnd_909032 := by exact prefixLift 909032
  have htrace : WordTrace (prefixWord ++ tailWord_909032) baseStart_909032 baseEnd_909032 := by
    simpa [prefixWord, tailWord_909032, baseEnd_909032] using wordTrace_append hprefix tailTrace_909032
  have hstable : (prefixWord ++ tailWord_909032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909032).length < 2 ^ (prefixWord ++ tailWord_909032).sum := by decide
  have hdescent : baseEnd_909032 < baseStart_909032 := by decide
  rcases family_descends (prefixWord ++ tailWord_909032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
